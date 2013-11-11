/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

//! Creates flows and boxes from a DOM tree via a bottom-up, incremental traversal of the DOM.
//!
//! Each step of the traversal considers the node and existing flow, if there is one. If a node is
//! not dirty and an existing flow exists, then the traversal reuses that flow. Otherwise, it
//! proceeds to construct either a flow or a `ConstructionItem`. A construction item is a piece of
//! intermediate data that goes with a DOM node and hasn't found its "home" yet—maybe it's a render
//! box, maybe it's an absolute or fixed position thing that hasn't found its containing block yet.
//! Construction items bubble up the tree from children to parents until they find their homes.
//!
//! TODO(pcwalton): There is no incremental reflow yet. This scheme requires that nodes either have
//! weak references to flows or that there be some mechanism to efficiently (O(1) time) "blow
//! apart" a flow tree and have the flows migrate "home" to their respective DOM nodes while we
//! perform flow tree construction. The precise mechanism for this will take some experimentation
//! to get right.
//!
//! TODO(pcwalton): This scheme should be amenable to parallelization, but, of course, that's not
//! yet implemented.

use css::node_style::StyledNode;
use layout::block::BlockFlow;
use layout::box::{GenericRenderBox, ImageRenderBox, RenderBox, RenderBoxBase};
use layout::box::{UnscannedTextRenderBox};
use layout::context::LayoutContext;
use layout::flow::{FlowContext, FlowData, MutableFlowUtils};
use layout::inline::InlineFlow;
use layout::text::TextRunScanner;
use layout::util::LayoutDataAccess;

use script::dom::element::HTMLImageElementTypeId;
use script::dom::node::{AbstractNode, CommentNodeTypeId, DoctypeNodeTypeId};
use script::dom::node::{DocumentFragmentNodeTypeId, DocumentNodeTypeId, ElementNodeTypeId};
use script::dom::node::{LayoutView, PostorderNodeTraversal, TextNodeTypeId};
use servo_net::local_image_cache::LocalImageCache;
use servo_util::slot::Slot;
use servo_util::tree::{TreeNode, TreeNodeRef};
use std::util;
use style::computed_values::{display, float};

/// The results of flow construction for a DOM node.
pub enum ConstructionResult {
    /// This node contributes nothing at all (`display: none`). Alternately, this is what newly
    /// created nodes have their `ConstructionResult` set to.
    NoConstructionResult,

    /// This node contributed a flow at the proper position in the tree. Nothing more needs to be
    /// done for this node.
    FlowConstructionResult(~FlowContext:),

    /// This node contributed some object or objects that will be needed to construct a proper flow
    /// later up the tree, but these objects have not yet found their home.
    ConstructionItemConstructionResult(ConstructionItem),
}

/// Represents the output of flow construction for a DOM node that has not yet resulted in a
/// complete flow. Construction items bubble up the tree until they find a `FlowContext` to be
/// attached to.
enum ConstructionItem {
    /// Inline boxes that have not yet found flows.
    ///
    /// TODO(pcwalton): Small vector optimization.
    InlineBoxesConstructionItem(~[@RenderBox]),
}

/// An object that knows how to create flows.
pub struct FlowConstructor<'self> {
    /// The layout context.
    ///
    /// FIXME(pcwalton): Why does this contain `@`??? That destroys parallelism!!!
    layout_context: &'self LayoutContext,

    /// The next flow ID to assign.
    ///
    /// FIXME(pcwalton): This is going to have to be atomic; can't we do something better?
    next_flow_id: Slot<int>,

    /// The next box ID to assign.
    ///
    /// FIXME(pcwalton): This is going to have to be atomic; can't we do something better?
    next_box_id: Slot<int>,
}

impl<'self> FlowConstructor<'self> {
    /// Creates a new flow constructor.
    pub fn init<'a>(layout_context: &'a LayoutContext) -> FlowConstructor<'a> {
        FlowConstructor {
            layout_context: layout_context,
            next_flow_id: Slot::init(0),
            next_box_id: Slot::init(0),
        }
    }

    /// Returns the next flow ID and bumps the internal counter.
    fn next_flow_id(&self) -> int {
        let id = self.next_flow_id.get();
        self.next_flow_id.set(id + 1);
        id
    }

    /// Returns the next render box ID and bumps the internal counter.
    fn next_box_id(&self) -> int {
        let id = self.next_box_id.get();
        self.next_box_id.set(id + 1);
        id
    }

    /// Builds a `RenderBox` for the given image. This is out of line to guide inlining.
    fn build_box_for_image(&self, base: RenderBoxBase, node: AbstractNode<LayoutView>)
                           -> @RenderBox {
        // FIXME(pcwalton): Don't copy URLs.
        let url = node.with_imm_image_element(|image_element| {
            image_element.image.as_ref().map(|url| (*url).clone())
        });

        match url {
            None => @GenericRenderBox::new(base) as @RenderBox,
            Some(url) => {
                // FIXME(pcwalton): The fact that image render boxes store the cache in the
                // box makes little sense to me.
                @ImageRenderBox::new(base, url, self.layout_context.image_cache) as @RenderBox
            }
        }
    }

    /// Builds a `RenderBox` for the given node.
    fn build_box_for_node(&self, node: AbstractNode<LayoutView>) -> @RenderBox {
        let base = RenderBoxBase::new(node, self.next_box_id());
        match node.type_id() {
            ElementNodeTypeId(HTMLImageElementTypeId) => self.build_box_for_image(base, node),
            TextNodeTypeId => @UnscannedTextRenderBox::new(base) as @RenderBox,
            _ => @GenericRenderBox::new(base) as @RenderBox,
        }
    }

    /// Builds a flow for an unfloated node with `display: block`. This yields a `BlockFlow` with
    /// possibly other `BlockFlow`s or `InlineFlow`s underneath it, depending on whether {ib}
    /// splits needed to happen.
    fn build_flow_for_unfloated_block(&self, node: AbstractNode<LayoutView>) {
        // Create the initial flow.
        let base = FlowData::new(self.next_flow_id(), node);
        let box = self.build_box_for_node(node);
        let mut flow = ~BlockFlow::from_box(base, box) as ~FlowContext:;

        // Gather up boxes for the inline flow we might need to create.
        let mut opt_boxes_for_inline_flow = None;

        // Attach block flows and gather up boxes.
        for kid in node.children() {
            match kid.swap_out_construction_result() {
                NoConstructionResult => {}
                FlowConstructionResult(kid_flow) => flow.add_new_child(kid_flow),
                ConstructionItemConstructionResult(InlineBoxesConstructionItem(boxes)) => {
                    // Add the boxes to the list we're maintaining.
                    match opt_boxes_for_inline_flow {
                        None => opt_boxes_for_inline_flow = Some(boxes),
                        Some(ref mut boxes_for_inline_flow) => {
                            boxes_for_inline_flow.push_all_move(boxes)
                        }
                    }
                }
            }
        }

        // Were there any inline boxes? If so, create the inline flow.
        //
        // FIXME(pcwalton): This is not right as it doesn't handle {ib} splits correctly.
        match opt_boxes_for_inline_flow {
            None => {}
            Some(boxes) => {
                let inline_base = FlowData::new(self.next_flow_id(), node);
                let mut inline_flow = ~InlineFlow::from_boxes(inline_base, boxes) as ~FlowContext:;
                TextRunScanner::new().scan_for_runs(self.layout_context, inline_flow);
                flow.add_new_child(inline_flow)
            }
        }

        node.set_flow_construction_result(FlowConstructionResult(flow))
    }

    /// Concatenates the boxes of kids, adding in our own borders/padding/margins if necessary.
    fn build_boxes_for_inline_that_renders_kids(&self, node: AbstractNode<LayoutView>) {
        // First, concatenate all the render boxes of our kids.
        let mut opt_box_accumulator = None;
        for kid in node.children() {
            match kid.swap_out_construction_result() {
                NoConstructionResult => {}
                FlowConstructionResult(_) => {
                    // TODO(pcwalton): {ib} split. Handle this.
                }
                ConstructionItemConstructionResult(InlineBoxesConstructionItem(boxes)) => {
                    match opt_box_accumulator {
                        None => opt_box_accumulator = Some(boxes),
                        Some(ref mut box_accumulator) => box_accumulator.push_all_move(boxes),
                    }
                }
            }
        }

        // Pull out the box accumulator.
        let box_accumulator = match opt_box_accumulator {
            None => ~[],
            Some(box_accumulator) => box_accumulator,
        };

        // TODO(pcwalton): Add in our own borders/padding/margins if necessary.

        // Finally, make a new construction result.
        let item = InlineBoxesConstructionItem(box_accumulator);
        node.set_flow_construction_result(ConstructionItemConstructionResult(item))
    }

    /// Builds one or more render boxes for a node with `display: inline`. This yields a
    /// `InlineBoxesConstructionItem`.
    fn build_boxes_for_inline(&self, node: AbstractNode<LayoutView>) {
        // Does this node render its kids?
        if node.renders_kids() {
            // Go to a path that concatenates our kids' boxes.
            return self.build_boxes_for_inline_that_renders_kids(node)
        }

        // Otherwise, just nuke our kids' boxes, create our `RenderBox`, and be done with it.
        for kid in node.children() {
            kid.set_flow_construction_result(NoConstructionResult)
        }
        let item = InlineBoxesConstructionItem(~[ self.build_box_for_node(node) ]);
        node.set_flow_construction_result(ConstructionItemConstructionResult(item))
    }
}

impl<'self> PostorderNodeTraversal for FlowConstructor<'self> {
    // `#[inline(always)]` because this is always called from the traversal function and for some
    // reason LLVM's inlining heuristics go awry here.
    #[inline(always)]
    fn process(&self, node: AbstractNode<LayoutView>) -> bool {
        // Get the `display` property for this node, and determine whether this node is floated.
        let (display, float) = match node.type_id() {
            ElementNodeTypeId(_) => (node.style().Box.display, node.style().Box.float),
            TextNodeTypeId => (display::inline, float::none),
            CommentNodeTypeId |
            DoctypeNodeTypeId |
            DocumentFragmentNodeTypeId |
            DocumentNodeTypeId(_) => (display::none, float::none),
        };

        // Switch on display and floatedness.
        match (display, float) {
            // `display: none` contributes no flow construction result. Nuke the flow construction
            // results of children.
            (display::none, _) => {
                for child in node.children() {
                    child.set_flow_construction_result(NoConstructionResult)
                }
            }

            // Block flows that are not floated contribute block flow construction results.
            (display::block, float::none) => self.build_flow_for_unfloated_block(node),

            // Inline items contribute render boxes.
            (display::inline, _) => self.build_boxes_for_inline(node),

            // TODO(pcwalton): Handle these.
            _ => {
                for child in node.children() {
                    child.set_flow_construction_result(NoConstructionResult)
                }
            }
        }

        true
    }
}

/// A utility trait with some useful methods for node queries.
trait NodeUtils {
    /// Returns true if this node renders its kids and false otherwise.
    ///
    /// FIXME(pcwalton): Surely this has a name in the CSS spec. Is this what is known by "replaced
    /// content", perhaps?
    fn renders_kids(self) -> bool;

    /// Sets the construction result of a flow.
    fn set_flow_construction_result(self, result: ConstructionResult);

    /// Replaces the flow construction result in a node with `NoConstructionResult` and returns the
    /// old value.
    fn swap_out_construction_result(self) -> ConstructionResult;
}

impl NodeUtils for AbstractNode<LayoutView> {
    fn renders_kids(self) -> bool {
        match self.type_id() {
            TextNodeTypeId |
            CommentNodeTypeId |
            DoctypeNodeTypeId |
            DocumentFragmentNodeTypeId |
            DocumentNodeTypeId(_) |
            ElementNodeTypeId(HTMLImageElementTypeId) => false,
            ElementNodeTypeId(_) => true
        }
    }

    #[inline(always)]
    fn set_flow_construction_result(self, result: ConstructionResult) {
        match *self.mutate_layout_data().ptr {
            Some(ref mut layout_data) => layout_data.flow_construction_result = result,
            None => fail!("no layout data"),
        }
    }

    #[inline(always)]
    fn swap_out_construction_result(self) -> ConstructionResult {
        match *self.mutate_layout_data().ptr {
            Some(ref mut layout_data) => {
                util::replace(&mut layout_data.flow_construction_result, NoConstructionResult)
            }
            None => fail!("no layout data"),
        }
    }
}

