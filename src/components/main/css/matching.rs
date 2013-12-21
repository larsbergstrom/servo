/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// High-level interface to CSS selector matching.

use css::node_style::StyledNode;
use layout::incremental;
use layout::util::LayoutDataAccess;
use layout::wrapper::LayoutNode;

use extra::arc::{Arc, RWArc};
use std::cast;
use std::libc::uintptr_t;
use std::rt;
use std::vec;
use style::{TNode, Stylist, cascade};

pub trait MatchMethods {
    fn match_node(&self, stylist: &Stylist);
    fn match_subtree(&self, stylist: RWArc<Stylist>);

    fn cascade_node(&self, parent: Option<LayoutNode>);
    fn cascade_subtree(&self, parent: Option<LayoutNode>);
}

impl<'ln> MatchMethods for LayoutNode<'ln> {
    fn match_node(&self, stylist: &Stylist) {
        let applicable_declarations = self.with_element(|element| {
            let style_attribute = match *element.style_attribute() {
                None => None,
                Some(ref style_attribute) => Some(style_attribute)
            };
            stylist.get_applicable_declarations(self, style_attribute, None)
        });

        match *self.mutate_layout_data().ptr {
            Some(ref mut layout_data) => {
                layout_data.applicable_declarations = applicable_declarations
            }
            None => fail!("no layout data")
        }
    }
    fn match_subtree(&self, stylist: RWArc<Stylist>) {
        let num_tasks = rt::default_sched_threads() * 2;
        let mut node_count = 0;
        let mut nodes_per_task = vec::from_elem(num_tasks, ~[]);

        for node in self.traverse_preorder() {
            if node.is_element() {
                nodes_per_task[node_count % num_tasks].push(node);
                node_count += 1;
            }
        }

        let (port, chan) = SharedChan::new();
        let mut num_spawned = 0;

        for nodes in nodes_per_task.move_iter() {
            if nodes.len() > 0 {
                let chan = chan.clone();
                let stylist = stylist.clone();
               
                // FIXME(pcwalton): This transmute is to work around the fact that we have no
                // mechanism for safe fork/join parallelism. If we had such a thing, then we could
                // close over the lifetime-bounded `LayoutNode`. But we can't, so we force it with
                // a transmute.
                let evil: uintptr_t = unsafe {
                    cast::transmute(nodes)
                };

                let evil = Some(evil);
                spawn(proc() {
                    let mut evil = evil;
                    stylist.read(|stylist| {
                        let nodes: ~[LayoutNode] = unsafe {
                            cast::transmute(evil.take_unwrap())
                        };

                        for node in nodes.move_iter() {
                            node.match_node(stylist);
                        }
                    });
                    chan.send(());
                });
                num_spawned += 1;
            }
        }
        for _ in range(0, num_spawned) {
            port.recv();
        }
    }

    fn cascade_node(&self, parent: Option<LayoutNode>) {
        let parent_style = match parent {
            Some(ref parent) => Some(parent.style()),
            None => None
        };

        let computed_values = unsafe {
            Arc::new(cascade(self.borrow_layout_data_unchecked()
                                 .as_ref()
                                 .unwrap()
                                 .applicable_declarations,
                             parent_style.map(|parent_style| parent_style.get())))
        };

        match *self.mutate_layout_data().ptr {
            None => fail!("no layout data"),
            Some(ref mut layout_data) => {
                let style = &mut layout_data.style;
                match *style {
                    None => (),
                    Some(ref previous_style) => {
                        layout_data.restyle_damage =
                            Some(incremental::compute_damage(previous_style.get(),
                                                             computed_values.get()).to_int())
                    }
                }
                *style = Some(computed_values)
            }
        }
    }

    fn cascade_subtree(&self, parent: Option<LayoutNode>) {
        self.cascade_node(parent);

        for kid in self.children() {
            if kid.is_element() {
                kid.cascade_subtree(Some(*self));
            }
        }
    }
}
