
fn get_underlying_type(ty: Type) -> Option<Type> {
  ty.get_declaration()
    .and_then(|e| e.get_typedef_underlying_type())
}

fn get_canonical_type_if_different(ty: Type) -> Option<Type> {
  let can_ty = ty.get_canonical_type();
  if can_ty == ty {
    None
  } else {
    Some(can_ty)
  }
}

#[allow(clippy::option_map_unit_fn)]
fn visit_type<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  ty: Type<'tu>,
  depth: usize,
) -> Option<()> {
  if ty.get_kind() == TypeKind::Pointer {
    if let Some(pointee_ty) = ty.get_pointee_type() {
      if pointee_ty.get_kind() == TypeKind::FunctionPrototype {
        let proto_slot = defs.get_type_entry(ty).function_prototype();
        let prev = proto_slot.replace(pointee_ty);
        assert!(prev.is_none());
      }
    }
  }

  static mut tag: &'static str = "";
  let prev_tag = unsafe { tag };
  fn set_tag(t: &'static str) {
    unsafe {
      tag = t;
    }
  }
  let name = ty.get_display_name();
  let indent = std::iter::repeat("  ").take(depth).collect::<String>();
  println!("{}{} {:?}: {}", indent, prev_tag, ty.get_kind(), name);

  let mut recurse = |ty: Type<'tu>| {
    maybe_visit_type(defs, ty, depth + 1);
  };
  ty.get_pointee_type().map({
    set_tag("pointee");
    &mut recurse
  });
  if let Some(vec) = ty.get_argument_types() {
    vec.into_iter().for_each({
      set_tag("argument");
      &mut recurse
    })
  }
  ty.get_result_type().map({
    set_tag("result");
    &mut recurse
  });

  ty.get_class_type().map({
    set_tag("class");
    &mut recurse
  });
  ty.get_element_type().map({
    set_tag("element");
    &mut recurse
  });
  ty.get_fields().map(|vec| {
    vec.into_iter().filter_map(|e| e.get_type()).for_each({
      set_tag("field");
      &mut recurse
    });
  });

  ty.get_modified_type().map({
    set_tag("modified");
    &mut recurse
  });
  ty.get_elaborated_type().map({
    set_tag("elaborated");
    &mut recurse
  });
  get_underlying_type(ty).map({
    set_tag("underlying");
    &mut recurse
  });
  get_canonical_type_if_different(ty).map({
    set_tag("canonical");
    &mut recurse
  });
  set_tag(prev_tag);
  Some(())
}

fn maybe_visit_type<'tu>(
  defs: &'_ mut ClassDefIndex<'tu>,
  ty: Type<'tu>,
  depth: usize,
) -> Option<()> {
  let def = defs.get_type_entry(ty);
  if !replace(def.visited(), true) {
    visit_type(defs, ty, depth)
  } else {
    None
  }
}