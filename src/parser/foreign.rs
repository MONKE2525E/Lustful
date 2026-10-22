use super::*;

impl Parser<'_> {
    /// The native subset keeps foreign declarations as declarations. In
    /// particular, a missing body must never become an empty Rust function.
    pub(super) fn foreign_block(&mut self, start: Span, qual: FnQual, vis: &Vis) -> PResult<ExternBlockDef> {
        if self.in_body {
            return Err(not_yet(C_EXTERN, start, "extern blocks inside function bodies"));
        }
        if *vis != Vis::Private {
            return Err(vis_not_permitted(start));
        }
        if !qual.is_unsafe || qual.is_const || qual.is_async {
            return Err(Diag::new(
                C_EXTERN,
                start,
                "native imports require `unsafe extern \"C\"`",
                "Declare an unsafe C ABI block at module scope.",
            ));
        }
        let abi = qual.abi.filter(|&i| i != u32::MAX);
        if abi.is_none_or(|i| self.ast.strings[i as usize] != "C") {
            return Err(not_yet(C_EXTERN, start, "this foreign ABI (only explicit C is supported)"));
        }
        self.expect(Tok::LBrace, "`{`")?;
        let mut items = Vec::new();
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `}`, found end of file"));
            }
            let attrs = self.attributes()?;
            // Foreign cfg stripping and link attributes need their own
            // resolver path. Reject them until that path exists rather
            // than accepting an attribute whose effect would be lost.
            if !attrs.attrs.is_empty() {
                return Err(not_yet(C_EXTERN, attrs.attrs[0].span, "attributes on foreign declarations"));
            }
            let vis = self.vis()?;
            // An explicit `unsafe fn` inside the unsafe block has the
            // same contract as an unqualified foreign fn. `safe fn`
            // and the remaining foreign-item forms stay unsupported.
            self.eat(Tok::Unsafe);
            if self.peek() != Tok::Fn {
                return Err(not_yet(C_EXTERN, self.span(), "this foreign item (only function declarations are supported)"));
            }
            let mut def = self.fn_def_inner(true)?;
            if def.body.is_some() || def.self_param.is_some() || !def.generics.params.is_empty() || !def.where_clause.preds.is_empty() {
                return Err(not_yet(C_EXTERN, def.name_span, "foreign functions with bodies, receivers or generics"));
            }
            attrs::check_target(&attrs.attrs, "functions", 0, self.interner)?;
            if attrs.is_test {
                return Err(syntax(def.name_span, "foreign functions cannot be tests"));
            }
            def.attrs.extend(attrs.attrs);
            def.vis = vis;
            def.qual = FnQual { is_unsafe: true, abi, ..FnQual::default() };
            items.push(ForeignItem::Fn(def));
        }
        self.bump();
        Ok(ExternBlockDef { abi, is_unsafe: true, items, span: start.to(self.prev_span()) })
    }
}
