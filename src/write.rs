use crate::types::*;
use crate::{Global, MizPath};
use enum_map::{Enum, EnumMap};
use quick_xml::events::attributes::Attribute;
use quick_xml::events::{BytesEnd, BytesStart, Event};
use std::borrow::Cow;
use std::fs::File;
use std::io::{self, BufWriter, Write};

const INDENT: usize = 0;

struct MizWriter {
  w: quick_xml::Writer<BufWriter<File>>,
  pending: Option<Elem>,
  depth: u32,
}

impl MizPath {
  fn create_xml(&self, new_prel: bool, ext: &str) -> io::Result<MizWriter> {
    let w = BufWriter::new(self.create(new_prel, ext)?);
    let mut w = quick_xml::Writer::new_with_indent(w, b' ', INDENT);
    w.write(b"<?xml version=\"1.0\"?>\n").unwrap();
    Ok(MizWriter { w, pending: None, depth: 0 })
  }

  pub fn write_dfr(&self, new_prel: bool, vocs: &Vocabularies, formats: &[Format]) {
    let mut w = self.create_xml(new_prel, "dfr").unwrap();
    w.with0(b"Formats", |w| {
      w.write_vocabularies(vocs);
      formats.iter().for_each(|fmt| w.write_format(fmt));
    });
    w.finish()
  }

  pub fn write_dco(
    &self, new_prel: bool, base: &ConstructorsBase,
    DepConstructors { sig, counts, constrs }: &DepConstructors,
  ) {
    let mut w = self.create_xml(new_prel, "dco").unwrap();
    w.with0(b"Constructors", |w| {
      w.write_signature(sig);
      w.with0(b"ConstrCounts", |w| {
        w.write_constr_count(b'M', counts.mode);
        w.write_constr_count(b'L', counts.struct_mode);
        w.write_constr_count(b'V', counts.attribute);
        w.write_constr_count(b'R', counts.predicate);
        w.write_constr_count(b'K', counts.functor);
        w.write_constr_count(b'U', counts.selector);
        w.write_constr_count(b'G', counts.aggregate);
      });
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, c) in constrs.attribute.enum_iter() {
        w.write_ty_constructor(art, (b'V', i.0), base.attribute, c)
      }
      for (i, c) in constrs.functor.enum_iter() {
        w.write_ty_constructor(art, (b'K', i.0), base.functor, c)
      }
      for (i, c) in constrs.mode.enum_iter() {
        w.write_ty_constructor(art, (b'M', i.0), base.mode, c)
      }
      for (i, c) in constrs.predicate.enum_iter() {
        w.write_constructor(art, (b'R', i.0), base.predicate, c, |_| {}, |_| {})
      }
      for (i, c) in constrs.struct_mode.enum_iter() {
        let attrs = |w: &mut Elem| w.attr_str(b"structmodeaggrnr", c.aggr.0 + 1);
        w.write_constructor(art, (b'L', i.0), base.struct_mode, c, attrs, |w| {
          w.write_types(&c.parents);
          w.write_fields(&c.fields);
        })
      }
      for (i, c) in constrs.aggregate.enum_iter() {
        let attrs = |w: &mut Elem| w.attr_str(b"aggregbase", c.base);
        w.write_constructor(art, (b'G', i.0), base.aggregate, c, attrs, |w| {
          w.write_type(&c.ty);
          w.write_fields(&c.fields)
        })
      }
      for (i, c) in constrs.selector.enum_iter() {
        w.write_ty_constructor(art, (b'U', i.0), base.selector, c)
      }
    });
    w.finish()
  }

  pub fn write_dno(&self, new_prel: bool, DepNotation { sig, vocs, pats }: &DepNotation) {
    let mut w = self.create_xml(new_prel, "dno").unwrap();
    w.with0(b"Notations", |w| {
      w.write_signature(sig);
      w.write_vocabularies(vocs);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      let mut counts = EnumMap::<_, u32>::default();
      for pat in pats {
        let rel_nr = counts[pat.kind.class()].fresh();
        let (kind, nr) = match pat.kind {
          PatternKind::Mode(ModeId(n)) => (b'M', n + 1),
          PatternKind::ExpandableMode { .. } => (b'M', 0),
          PatternKind::Struct(StructId(n)) => (b'L', n + 1),
          PatternKind::Attr(AttrId(n)) => (b'V', n + 1),
          PatternKind::Pred(PredId(n)) => (b'R', n + 1),
          PatternKind::Func(FuncId(n)) => (b'K', n + 1),
          PatternKind::Sel(SelId(n)) => (b'U', n + 1),
          PatternKind::Aggr(AggrId(n)) => (b'G', n + 1),
          PatternKind::SubAggr(StructId(n)) => (b'J', n + 1),
        };
        let attrs = |w: &mut Elem| {
          w.attr(b"kind", &[kind][..]);
          w.attr_str(b"nr", rel_nr + 1);
          w.attr(b"aid", art);
          w.attr(b"constrkind", &[kind][..]);
          w.attr_str(b"constrnr", nr);
          if !pat.pos {
            w.attr(b"antonymic", &b"true"[..])
          }
          // w.attr_str(b"redefnr", redefines);
        };
        w.with(b"Pattern", attrs, |w| {
          w.write_format(&pat.fmt);
          w.write_arg_types(&pat.primary);
          w.write_loci(b"Visible", &pat.visible);
          if let PatternKind::ExpandableMode { expansion } = &pat.kind {
            w.with0(b"Expansion", |w| w.write_type(expansion))
          }
        })
      }
    });
    w.finish()
  }

  pub fn write_dcl(&self, new_prel: bool, DepClusters { sig, cl }: &DepClusters) {
    let mut w = self.create_xml(new_prel, "dcl").unwrap();
    w.with0(b"Registrations", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, cl) in cl.registered.iter().enumerate() {
        w.write_cluster(b"RCluster", art, i, cl, |w| {
          w.write_type(&cl.ty);
          w.write_attrs(&cl.consequent.0)
        })
      }
      for (i, cl) in cl.functor.iter().enumerate() {
        w.write_cluster(b"FCluster", art, i, cl, |w| {
          w.write_term(&cl.term);
          w.write_attrs(&cl.consequent.0);
          if let Some(ty) = &cl.ty {
            w.write_type(ty)
          }
        })
      }
      for (i, cl) in cl.conditional.iter().enumerate() {
        w.write_cluster(b"CCluster", art, i, cl, |w| {
          w.write_attrs(&cl.antecedent);
          w.write_type(&cl.ty);
          w.write_attrs(&cl.consequent.0)
        })
      }
    });
    w.finish()
  }

  pub fn write_def(&self, new_prel: bool, sig: &[Article], def: &[Definiens]) {
    let mut w = self.create_xml(new_prel, "def").unwrap();
    w.with0(b"Definientia", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      for def in def {
        let attrs = |w: &mut Elem| {
          let (kind, nr) = def.constr.discr_nr();
          w.attr(b"constrkind", &[kind][..]);
          w.attr_str(b"constrnr", nr + 1);
          w.attr(b"aid", art.as_bytes());
          w.attr_str(b"defnr", def.def_nr.0 + 1);
          // w.attr_str(b"vid", lab_id);
          // w.attr_str(b"relnr", rel_nr);
        };
        w.with(b"Definiens", attrs, |w| {
          w.write_types(&def.primary);
          w.write_loci(b"Essentials", &def.essential);
          if !matches!(def.assumptions, Formula::True) {
            w.write_formula(&def.assumptions)
          }
          match &def.value {
            DefValue::Term(body) => w.write_def_body(b'e', body, |w, t| w.write_term(t)),
            DefValue::Formula(body) => w.write_def_body(b'm', body, |w, f| w.write_formula(f)),
          }
        })
      }
    });
    w.finish()
  }

  pub fn write_did(&self, new_prel: bool, sig: &[Article], ids: &[IdentifyFunc]) {
    let mut w = self.create_xml(new_prel, "did").unwrap();
    w.with0(b"IdentifyRegistrations", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, id) in ids.iter().enumerate() {
        let attrs = |w: &mut Elem| {
          w.attr(b"aid", art);
          w.attr_str(b"nr", i + 1);
          w.attr(b"constrkind", &b"K"[..]);
        };
        w.with(b"Identify", attrs, |w| {
          w.write_types(&id.primary);
          w.write_term(&id.lhs);
          w.write_term(&id.rhs);
          w.with0(b"EqArgs", |w| {
            for &(x, y) in &*id.eq_args {
              w.with_attr(b"Pair", |w| {
                w.attr_str(b"x", x.0 + 1);
                w.attr_str(b"y", y.0 + 1)
              })
            }
          })
        })
      }
    });
    w.finish()
  }

  pub fn write_drd(&self, new_prel: bool, sig: &[Article], reds: &[Reduction]) {
    let mut w = self.create_xml(new_prel, "drd").unwrap();
    w.with0(b"ReductionRegistrations", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, red) in reds.iter().enumerate() {
        let attrs = |w: &mut Elem| {
          w.attr(b"aid", art);
          w.attr_str(b"nr", i + 1);
        };
        w.with(b"Reduction", attrs, |w| {
          w.write_types(&red.primary);
          w.write_term(&red.terms[0]);
          w.write_term(&red.terms[1])
        })
      }
    });
    w.finish()
  }

  pub fn write_dpr(&self, new_prel: bool, sig: &[Article], props: &[Property]) {
    let mut w = self.create_xml(new_prel, "dpr").unwrap();
    w.with0(b"PropertyRegistration", |w| {
      w.write_signature(sig);
      let art = self.art.as_str().to_ascii_uppercase();
      let art = art.as_bytes();
      for (i, prop) in props.iter().enumerate() {
        let attrs = |w: &mut Elem| {
          w.attr(b"aid", art);
          w.attr_str(b"nr", i + 1);
          w.attr_str(b"x", prop.kind as u8 + 1);
        };
        w.with(b"Property", attrs, |w| {
          w.write_arg_types(&prop.primary);
          w.write_type(&prop.ty)
        })
      }
    });
    w.finish()
  }

  pub fn write_the(&self, new_prel: bool, DepTheorems { sig, thm }: &DepTheorems) {
    let mut w = self.create_xml(new_prel, "the").unwrap();
    w.with0(b"Theorems", |w| {
      w.write_signature(sig);
      for Theorem { pos: _, kind, stmt } in thm {
        let attrs = |w: &mut Elem| {
          let k = match kind {
            TheoremKind::Thm | TheoremKind::CanceledThm => b'T',
            TheoremKind::Def(_) | TheoremKind::CanceledDef => b'D',
          };
          w.attr(b"kind", &[k][..]);
          if let TheoremKind::Def(c) = &kind {
            let (k, nr) = c.discr_nr();
            w.attr(b"constrkind", &[k][..]);
            w.attr_str(b"constrnr", nr + 1);
          }
        };
        w.with(b"Theorem", attrs, |w| w.write_formula(stmt))
      }
    });
    w.finish()
  }

  pub fn write_sch(&self, new_prel: bool, DepSchemes { sig, sch }: &DepSchemes) {
    let mut w = self.create_xml(new_prel, "sch").unwrap();
    w.with0(b"Schemes", |w| {
      w.write_signature(sig);
      for sch in sch {
        if let Some(sch) = sch {
          w.with0(b"Scheme", |w| {
            w.write_arg_types(&sch.sch_funcs);
            w.write_formula(&sch.thesis);
            w.write_formulas(&sch.prems)
          })
        } else {
          w.with0(b"Canceled", |_| {})
        }
      }
    });
    w.finish()
  }
}

struct Elem(BytesStart<'static>);

impl Elem {
  fn attr<'a>(&mut self, key: &[u8], value: impl Into<Cow<'a, [u8]>>) {
    self.0.push_attribute(Attribute { key, value: value.into() })
  }
  fn attr_str(&mut self, key: &[u8], value: impl ToString) {
    self.attr(key, value.to_string().into_bytes())
  }
  fn opt_attr_str(&mut self, key: &[u8], value: Option<impl ToString>) {
    if let Some(value) = value {
      self.attr_str(key, value)
    }
  }
}

impl MizWriter {
  fn clear_pending(&mut self) {
    if let Some(elem) = self.pending.take() {
      self.w.write_event(Event::Start(elem.0)).unwrap()
    }
  }

  fn start(&mut self, tag: &'static [u8]) -> &mut Elem {
    self.clear_pending();
    self.pending.insert(Elem(BytesStart::borrowed_name(tag)))
  }

  fn finish(mut self) {
    assert!(self.pending.is_none());
    self.w.write(b"\n").unwrap();
    self.w.inner().flush().unwrap()
  }

  #[inline]
  fn with(
    &mut self, tag: &'static [u8], attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    attrs(self.start(tag));
    body(self);
    self.end_tag(tag)
  }

  #[inline]
  fn with0(&mut self, tag: &'static [u8], body: impl FnOnce(&mut Self)) {
    self.with(tag, |_| {}, body);
  }

  #[inline]
  fn with_attr(&mut self, tag: &'static [u8], attrs: impl FnOnce(&mut Elem)) {
    self.with(tag, attrs, |_| {})
  }

  fn end_tag(&mut self, tag: &'static [u8]) {
    match self.pending.take() {
      Some(elem) => self.w.write_event(Event::Empty(elem.0)).unwrap(),
      None => self.w.write_event(Event::End(BytesEnd::borrowed(tag))).unwrap(),
    }
  }

  fn write_signature(&mut self, sig: &[Article]) {
    self.with0(b"Signature", |w| {
      for art in sig {
        w.with_attr(b"ArticleID", |e| e.attr_str(b"name", art.as_str().to_ascii_uppercase()))
      }
    })
  }

  fn write_vocabularies(&mut self, vocs: &Vocabularies) {
    self.with0(b"Vocabularies", |w| {
      for (art, symbols) in &vocs.0 {
        w.with0(b"Vocabulary", |w| {
          w.with_attr(b"ArticleID", |e| e.attr_str(b"name", art.as_str().to_ascii_uppercase()));
          for (c, &n) in &symbols.0 {
            w.with_attr(b"SymbolCount", |e| {
              e.attr(b"kind", &[c.discr()][..]);
              e.attr_str(b"nr", n);
            })
          }
        })
      }
    })
  }

  fn write_format(&mut self, fmt: &Format) {
    self.with_attr(b"Format", |e| {
      e.attr(b"kind", &[fmt.discr()][..]);
      let (sym, args, left, rsym) = match *fmt {
        Format::Aggr(FormatAggr { sym: StructSymId(sym), args })
        | Format::Struct(FormatStruct { sym: StructSymId(sym), args })
        | Format::Mode(FormatMode { sym: ModeSymId(sym), args })
        | Format::Attr(FormatAttr { sym: AttrSymId(sym), args }) => (sym + 1, args, None, None),
        Format::SubAggr(StructSymId(sym)) | Format::Sel(SelSymId(sym)) => (sym + 1, 1, None, None),
        Format::Func(FormatFunc::Bracket { lsym, rsym, args }) =>
          (lsym.0 + 1, args, None, Some(rsym.0 + 1)),
        Format::Func(FormatFunc::Func { sym: FuncSymId(sym), left, right })
        | Format::Pred(FormatPred { sym: PredSymId(sym), left, right }) =>
          (sym + 1, left + right, Some(left), None),
      };
      e.attr_str(b"symbolnr", sym);
      e.attr_str(b"argnr", args);
      e.opt_attr_str(b"leftargnr", left);
      e.opt_attr_str(b"rightsymbolnr", rsym);
    })
  }

  fn write_constr_count(&mut self, kind: u8, value: u32) {
    if value != 0 {
      self.with_attr(b"ConstrCount", |w| {
        w.attr(b"kind", &[kind][..]);
        w.attr_str(b"nr", value);
      })
    }
  }

  fn write_constructor<I: Idx>(
    &mut self, art: &[u8], (kind, nr): (u8, u32), base: u32, c: &Constructor<I>,
    attrs: impl FnOnce(&mut Elem), body: impl FnOnce(&mut Self),
  ) {
    let attrs = |w: &mut Elem| {
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", nr + 1);
      w.attr(b"aid", art);
      w.attr_str(b"relnr", base + nr + 1);
      if let Some(redef) = c.redefines {
        w.attr_str(b"redefnr", redef.into_usize() + 1);
        w.attr_str(b"superfluous", c.superfluous);
      }
      attrs(w)
    };
    self.with(b"Constructor", attrs, |w| {
      let attrs = |w: &mut Elem| {
        let arg1 = if c.properties.uses_arg1() { c.properties.arg1 + 1 } else { 0 };
        w.attr_str(b"propertyarg1", arg1);
        let arg2 = if c.properties.uses_arg2() { c.properties.arg2 + 1 } else { 0 };
        w.attr_str(b"propertyarg2", arg2);
      };
      if c.properties.properties != PropertySet::EMPTY {
        w.with(b"Properties", attrs, |w| {
          for prop in (0..PropertyKind::LENGTH).map(PropertyKind::from_usize) {
            if c.properties.properties.get(prop) {
              w.with0(prop.to_upper(), |_| {})
            }
          }
        })
      }
      w.write_arg_types(&c.primary);
      body(w)
    })
  }

  fn write_ty_constructor<I: Idx>(
    &mut self, art: &[u8], kind: (u8, u32), base: u32, c: &TyConstructor<I>,
  ) {
    self.write_constructor(art, kind, base, c, |_| {}, |w| w.write_type(&c.ty))
  }

  fn write_fields(&mut self, fields: &[SelId]) {
    self.with0(b"Fields", |w| {
      fields.iter().for_each(|field| w.with_attr(b"Field", |w| w.attr_str(b"nr", field.0 + 1)))
    })
  }

  fn write_cluster(
    &mut self, tag: &'static [u8], art: &[u8], nr: usize, cl: &Cluster,
    body: impl FnOnce(&mut Self),
  ) {
    let attrs = |w: &mut Elem| {
      w.attr(b"aid", art);
      w.attr_str(b"nr", nr + 1);
    };
    self.with(tag, attrs, |w| {
      w.write_arg_types(&cl.primary);
      body(w)
    })
  }

  fn write_def_body<T>(
    &mut self, kind: u8, body: &DefBody<T>, mut elem: impl FnMut(&mut Self, &T),
  ) {
    let attrs = |w: &mut Elem| w.attr(b"kind", &[kind][..]);
    self.with(b"DefMeaning", attrs, |w| {
      for case in &*body.cases {
        w.with0(b"PartialDef", |w| {
          elem(w, &case.case);
          w.write_formula(&case.guard)
        })
      }
      if let Some(ow) = &body.otherwise {
        elem(w, ow)
      }
    })
  }

  fn write_attrs(&mut self, attrs: &Attrs) {
    let Attrs::Consistent(attrs) = attrs else { unreachable!() };
    self.with0(b"Cluster", |w| {
      for attr in attrs {
        let attrs = |w: &mut Elem| {
          w.attr_str(b"nr", attr.nr.0 + 1);
          if !attr.pos {
            w.attr(b"value", &b"false"[..])
          }
          // w.attr_str(b"pid", pat_nr);
        };
        w.with(b"Adjective", attrs, |w| w.write_terms(&attr.args))
      }
    })
  }

  fn write_type(&mut self, ty: &Type) {
    let attrs = |w: &mut Elem| {
      let (kind, n) = match ty.kind {
        TypeKind::Struct(n) => (b'G', n.0),
        TypeKind::Mode(n) => (b'M', n.0),
      };
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", n + 1)
    };
    self.with(b"Typ", attrs, |w| {
      w.write_attrs(&ty.attrs.0);
      w.write_terms(&ty.args)
    })
  }

  fn write_types(&mut self, tys: &[Type]) { tys.iter().for_each(|ty| self.write_type(ty)) }

  fn write_arg_types(&mut self, tys: &[Type]) { self.with0(b"ArgTypes", |w| w.write_types(tys)) }

  fn write_term(&mut self, tm: &Term) {
    match tm {
      Term::Numeral(n) => self.with_attr(b"Num", |w| w.attr_str(b"nr", *n)),
      Term::Locus(n) => self.with_attr(b"LocusVar", |w| w.attr_str(b"nr", n.0 + 1)),
      Term::Bound(n) => self.with_attr(b"Var", |w| w.attr_str(b"nr", n.0 + 1)),
      Term::Const(n) => self.with_attr(b"Const", |w| w.attr_str(b"nr", n.0 + 1)),
      Term::SchFunc { nr, args } => self.write_func(b"Func", b'F', nr.0, args),
      Term::Aggregate { nr, args } => self.write_func(b"Func", b'G', nr.0, args),
      Term::PrivFunc { nr, args, value } => {
        let attrs = |w: &mut Elem| w.attr_str(b"nr", nr.0 + 1);
        self.with(b"PrivFunc", attrs, |w| {
          w.write_term(value);
          w.write_terms(args)
        })
      }
      Term::Functor { nr, args } => self.write_func(b"Func", b'K', nr.0, args),
      Term::Selector { nr, args } => self.write_func(b"Func", b'U', nr.0, args),
      Term::The { ty } => self.with0(b"Choice", |w| w.write_type(ty)),
      Term::Fraenkel { args, scope, compr } => self.with0(b"Fraenkel", |w| {
        for ty in &**args {
          w.write_type(ty);
          w.depth += 1;
        }
        w.write_term(scope);
        w.write_formula(compr);
        w.depth -= args.len() as u32
      }),
      Term::EqClass(_)
      | Term::EqMark(_)
      | Term::Infer(_)
      | Term::FreeVar(_)
      | Term::Qua { .. }
      | Term::It => unreachable!(),
    }
  }
  fn write_terms(&mut self, tys: &[Term]) { tys.iter().for_each(|ty| self.write_term(ty)) }

  fn write_func(&mut self, tag: &'static [u8], kind: u8, nr: u32, args: &[Term]) {
    let attrs = |w: &mut Elem| {
      w.attr(b"kind", &[kind][..]);
      w.attr_str(b"nr", nr + 1)
    };
    self.with(tag, attrs, |w| w.write_terms(args))
  }

  fn write_formula(&mut self, f: &Formula) {
    match f {
      Formula::SchPred { nr, args } => self.write_func(b"Pred", b'P', nr.0, args),
      Formula::Pred { nr, args } => self.write_func(b"Pred", b'R', nr.0, args),
      Formula::Attr { nr, args } => self.write_func(b"Pred", b'V', nr.0, args),
      Formula::PrivPred { nr, args, value } => {
        let attrs = |w: &mut Elem| w.attr_str(b"nr", nr.0 + 1);
        self.with(b"PrivPred", attrs, |w| {
          w.write_terms(args);
          w.write_formula(value)
        })
      }
      Formula::Is { term, ty } => self.with0(b"Is", |w| {
        w.write_term(term);
        w.write_type(ty)
      }),
      Formula::Neg { f } => self.with0(b"Not", |w| w.write_formula(f)),
      Formula::And { args } => self.with0(b"And", |w| w.write_formulas(args)),
      Formula::ForAll { dom, scope } => {
        let attrs = |_: &mut Elem| {
          // w.attr_str(b"vid", var_id)
        };
        self.with(b"For", attrs, |w| {
          w.write_type(dom);
          w.depth += 1;
          w.write_formula(scope);
          w.depth -= 1;
        })
      }
      Formula::FlexAnd { nat, le, terms, scope } =>
        self.write_formula(&Global::into_legacy_flex_and(
          &mut nat.clone(),
          *le,
          &mut terms.clone(),
          &mut scope.clone(),
          self.depth,
        )),
      Formula::LegacyFlexAnd { orig, terms, expansion } => self.with0(b"FlexFrm", |w| {
        w.write_formulas(&**orig);
        w.write_terms(&**terms);
        w.write_formula(expansion)
      }),
      Formula::True => self.with0(b"Verum", |_| {}),
    }
  }

  fn write_formulas(&mut self, fs: &[Formula]) { fs.iter().for_each(|ty| self.write_formula(ty)) }

  fn write_loci(&mut self, tag: &'static [u8], args: &[LocusId]) {
    self
      .with0(tag, |w| args.iter().for_each(|n| w.with_attr(b"Int", |w| w.attr_str(b"x", n.0 + 1))))
  }
}
