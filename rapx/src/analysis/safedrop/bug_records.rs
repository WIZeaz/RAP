use rustc_data_structures::fx::FxHashMap;
use rustc_span::Span;

use crate::rap_warn;
use crate::utils::log::are_spans_in_same_file;
use rustc_span::symbol::Symbol;

use annotate_snippets::Level;
use annotate_snippets::Renderer;
use annotate_snippets::Snippet;

use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};

#[derive(Debug)]
pub struct TyBug {
    pub drop_bb: usize,
    pub drop_id: usize,
    pub trigger_bb: usize,
    pub trigger_id: usize,
    pub span: Span,
    pub confidence: usize,
}

/*
 * For each bug in the HashMap, the key is local of the value.
 */
pub struct BugRecords {
    pub df_bugs: FxHashMap<usize, TyBug>,
    pub df_bugs_unwind: FxHashMap<usize, TyBug>,
    pub uaf_bugs: FxHashMap<usize, TyBug>,
    pub dp_bugs: FxHashMap<usize, TyBug>,
    pub dp_bugs_unwind: FxHashMap<usize, TyBug>,
}

impl BugRecords {
    pub fn new() -> BugRecords {
        BugRecords {
            df_bugs: FxHashMap::default(),
            df_bugs_unwind: FxHashMap::default(),
            uaf_bugs: FxHashMap::default(),
            dp_bugs: FxHashMap::default(),
            dp_bugs_unwind: FxHashMap::default(),
        }
    }

    pub fn is_bug_free(&self) -> bool {
        self.df_bugs.is_empty()
            && self.df_bugs_unwind.is_empty()
            && self.uaf_bugs.is_empty()
            && self.dp_bugs.is_empty()
            && self.dp_bugs_unwind.is_empty()
    }

    pub fn df_bugs_output(&self, fn_name: Symbol, span: Span) {
        let code_source = span_to_source_code(span);
        let filename = span_to_filename(span);
        let renderer = Renderer::styled();
        if !self.df_bugs.is_empty() {
            rap_warn!("Double free detected in function {:}", fn_name);
            for (_i, bug) in self.df_bugs.iter() {
                if are_spans_in_same_file(span, bug.span) {
                    let detail = format!(
                        "Double free (confidence {}%):
                         | Value dropped at mir BB{} via _{} 
                         | Triggered at mir BB{} via _{}, 
                         | Location in source code: {}:{}",
                        bug.confidence,
                        bug.drop_bb,
                        bug.drop_id,
                        bug.trigger_bb,
                        bug.trigger_id,
                        span_to_filename(bug.span),
                        span_to_line_number(bug.span),
                    );
                    let mut snippet = Snippet::source(&code_source)
                        .line_start(span_to_line_number(span))
                        .origin(&filename)
                        .fold(false);
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, bug.span))
                            .label(&detail),
                    );
                    let message = Level::Warning
                        .title("Double free detected.")
                        .snippet(snippet);
                    println!("{}", renderer.render(message));
                }
            }
        }
        if !self.df_bugs_unwind.is_empty() {
            rap_warn!("Double free detected in function {:}", fn_name);
            for (_i, bug) in self.df_bugs_unwind.iter() {
                if are_spans_in_same_file(span, bug.span) {
                    let detail = format!(
                        "Double free (confidence {}%):
                         | Value dropped at mir BB{} via _{} 
                         | Triggered at mir BB{} via _{}, 
                         | Location in source code: {}:{}",
                        bug.confidence,
                        bug.drop_bb,
                        bug.drop_id,
                        bug.trigger_bb,
                        bug.trigger_id,
                        span_to_filename(bug.span),
                        span_to_line_number(bug.span),
                    );
                    let mut snippet = Snippet::source(&code_source)
                        .line_start(span_to_line_number(span))
                        .origin(&filename)
                        .fold(false);
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, bug.span))
                            .label(&detail),
                    );
                    let message = Level::Warning
                        .title("Double free detected during unwinding.")
                        .snippet(snippet);
                    println!("{}", renderer.render(message));
                }
            }
        }
    }

    pub fn uaf_bugs_output(&self, fn_name: Symbol, span: Span) {
        let renderer = Renderer::styled();
        if !self.uaf_bugs.is_empty() {
            rap_warn!("Use after free detected in function {:?}", fn_name);
            let code_source = span_to_source_code(span);
            let filename = span_to_filename(span);
            for (_local, bug) in self.uaf_bugs.iter() {
                //todo: remove this condition
                if are_spans_in_same_file(span, bug.span) {
                    let detail = format!(
                        "Use-after-free (confidence {}%):
                         | Value dropped at mir BB{} via _{} 
                         | Triggered at mir BB{} via _{}, 
                         | Location in source code: {}:{}",
                        bug.confidence,
                        bug.drop_bb,
                        bug.drop_id,
                        bug.trigger_bb,
                        bug.trigger_id,
                        span_to_filename(bug.span),
                        span_to_line_number(bug.span),
                    );
                    let mut snippet = Snippet::source(&code_source)
                        .line_start(span_to_line_number(span))
                        .origin(&filename)
                        .fold(false);
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, bug.span))
                            .label(&detail),
                    );
                    let message = Level::Warning
                        .title("Use-after-free detected.")
                        .snippet(snippet);
                    println!("{}", renderer.render(message));
                }
            }
        }
    }

    pub fn dp_bug_output(&self, fn_name: Symbol, span: Span) {
        let code_source = span_to_source_code(span);
        let filename = span_to_filename(span);
        let renderer = Renderer::styled();
        if !self.dp_bugs.is_empty() {
            rap_warn!("Dangling pointer detected in function {:?}", fn_name);
            for (_local, bug) in self.dp_bugs.iter() {
                if are_spans_in_same_file(span, bug.span) {
                    let detail = format!(
                        "Dangling pointer (confidence {}%):
                         | Value dropped at mir BB{} via _{} 
                         | Triggered at mir via _{}, 
                         | Location in source code: {}:{}",
                        bug.confidence,
                        bug.drop_bb,
                        bug.drop_id,
                        bug.trigger_id,
                        span_to_filename(bug.span),
                        span_to_line_number(bug.span),
                    );
                    let mut snippet = Snippet::source(&code_source)
                        .line_start(span_to_line_number(span))
                        .origin(&filename)
                        .fold(false);
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, bug.span))
                            .label(&detail),
                    );
                    let message = Level::Warning
                        .title("Dangling pointer detected.")
                        .snippet(snippet);
                    println!("{}", renderer.render(message));
                }
            }
        }
        if !self.dp_bugs_unwind.is_empty() {
            rap_warn!(
                "Dangling pointer detected in function {:?} during unwinding.",
                fn_name
            );
            for (_local, bug) in self.dp_bugs_unwind.iter() {
                if are_spans_in_same_file(span, bug.span) {
                    let detail = format!(
                        "Dangling pointer (confidence {}%):
                         | Value dropped at mir BB{} via _{} 
                         | Triggered at mir via _{}, 
                         | Location in source code: {}:{}",
                        bug.confidence,
                        bug.drop_bb,
                        bug.drop_id,
                        bug.trigger_id,
                        span_to_filename(bug.span),
                        span_to_line_number(bug.span),
                    );
                    let mut snippet = Snippet::source(&code_source)
                        .line_start(span_to_line_number(span))
                        .origin(&filename)
                        .fold(false);
                    snippet = snippet.annotation(
                        Level::Warning
                            .span(relative_pos_range(span, bug.span))
                            .label(&detail),
                    );
                    let message = Level::Warning
                        .title("Dangling pointer detected during unwinding.")
                        .snippet(snippet);
                    println!("{}", renderer.render(message));
                }
            }
        }
    }
}
