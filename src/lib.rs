use std::marker::PhantomData;
use std::ptr;
use std::ptr::NonNull;

// *** Shims ****

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Local<'a, T>(NonNull<T>, PhantomData<&'a ()>);

pub struct Value([u8; 0]);
pub struct Isolate([u8; 0]);
pub struct HandleScope<'a>(&'a mut Isolate);

pub trait UnitType: Sized {
  fn get() -> Self {
    assert_eq!(std::mem::size_of::<Self>(), 0);
    unsafe { std::mem::MaybeUninit::<Self>::zeroed().assume_init() }
  }
}
impl<T: Sized> UnitType for T {}

// *** Support ***

trait CxxCallback<F = Self>: UnitType {
  type CxxFn;
  fn cxx_fn() -> Self::CxxFn;
  fn cxx_fn_from_val(&'_ self) -> Self::CxxFn {
    Self::cxx_fn()
  }
}

// *** MyCallback ***

pub trait MyCallback:
  UnitType
  + for<'a> FnOnce(
    &mut HandleScope<'a>,
    Local<'a, Value>,
    i32,
  ) -> Local<'a, Value>
{
}
impl<F> MyCallback for F where
  F: UnitType
    + for<'a> FnOnce(
      &mut HandleScope<'a>,
      Local<'a, Value>,
      i32,
    ) -> Local<'a, Value>
{
}

#[macro_export]
macro_rules! impl_my_callback {
  () => {
    impl MyCallback
      + for<'a> FnOnce(
        &mut HandleScope<'a>,
        Local<'a, Value>,
        i32
      ) -> Local<'a, Value>
  };
}

type CxxMyCallback = for<'a> extern "C" fn(
  *mut Local<'a, Value>,
  *mut Isolate,
  Local<'a, Value>,
  i32,
) -> *mut Local<'a, Value>;

impl<F: MyCallback> CxxCallback for F {
  type CxxFn = CxxMyCallback;

  fn cxx_fn() -> Self::CxxFn {
    #[inline(always)]
    fn signature_adapter<'a, F: MyCallback>(
      isolate: *mut Isolate,
      a: Local<'a, Value>,
      b: i32,
    ) -> Local<'a, Value> {
      let hs = &mut HandleScope(unsafe { &mut *isolate });
      (F::get())(hs, a, b)
    }

    #[inline(always)]
    extern "C" fn abi_adapter<'a, F: MyCallback>(
      ret: *mut Local<'a, Value>,
      isolate: *mut Isolate,
      a: Local<'a, Value>,
      b: i32,
    ) -> *mut Local<'a, Value> {
      unsafe { ptr::write(ret, signature_adapter::<F>(isolate, a, b)) };
      ret
    }

    abi_adapter::<F>
  }
}

#[cfg(test)]
mod my_callback_test {
  use super::*;

  #[test]
  fn my_callback_test() {
    fn callback<'s>(
      _hs: &mut HandleScope<'s>,
      _a: Local<'s, Value>,
      _b: i32,
    ) -> Local<'s, Value> {
      unimplemented!()
    }

    let _ = pass_to_fn_as_type_param(&callback);
    let _ = pass_to_fn_as_impl_trait(callback);
    let _ = pass_to_fn_as_impl_trait_fn_once(callback);

    // Rust apparently does not use all information available from supertraits.
    // It can't deduce the proper lifetime for a closure return value from a
    // `F: MyCallback` bound or an `impl MyCallback` type.
    // The consequence is that these lines cause compile time errors:
    //    `let _ = pass_to_fn_as_type_param(|_, a, _| a);`
    //    `let _ = pass_to_fn_as_impl_trait(|_, a, _| a);`
    // However if we use an explicit `F: FnOnce( ... ) -> ...` bound, it does
    // infer the correct lifetimes. As replicating that complicated type in
    // many places is error prone and hurts readability, this crate exports
    // a macro that produces the full `impl FnOnce( ... ) -> ...` impl trait.
    let _ = pass_to_fn_as_impl_trait_fn_once(|_, a, _| a);
  }

  fn pass_to_fn_as_type_param<F: MyCallback>(
    _: &F,
  ) -> <F as CxxCallback>::CxxFn {
    F::cxx_fn()
  }

  fn pass_to_fn_as_impl_trait(f: impl MyCallback) -> CxxMyCallback {
    f.cxx_fn_from_val()
  }

  fn pass_to_fn_as_impl_trait_fn_once(f: impl_my_callback!()) -> CxxMyCallback {
    f.cxx_fn_from_val()
  }
}

// *** OtherCallback ***

pub trait OtherCallback<T: Sized>:
  UnitType
  + for<'a> FnOnce(&mut HandleScope<'a>, Local<'a, Value>, &mut T) -> usize
{
}
impl<
    T: Sized,
    F: for<'a> FnOnce(&mut HandleScope<'a>, Local<'a, Value>, &mut T) -> usize,
  > OtherCallback<T> for F
{
}
type CxxOtherCallback<T> =
  for<'a> extern "C" fn(*mut Isolate, Local<'a, Value>, *mut T) -> usize;

impl<T: Sized, F: OtherCallback<T>> CxxCallback<CxxOtherCallback<T>> for F {
  type CxxFn = CxxOtherCallback<T>;

  fn cxx_fn() -> Self::CxxFn {
    #[inline(always)]
    fn signature_adapter<'a, T: Sized, F: OtherCallback<T>>(
      isolate: *mut Isolate,
      a: Local<'a, Value>,
      b: *mut T,
    ) -> usize {
      let hs = &mut HandleScope(unsafe { &mut *isolate });
      let b = unsafe { &mut *b };
      (F::get())(hs, a, b)
    }

    #[inline(always)]
    extern "C" fn abi_adapter<'a, T: Sized, F: OtherCallback<T>>(
      isolate: *mut Isolate,
      a: Local<'a, Value>,
      b: *mut T,
    ) -> usize {
      signature_adapter::<T, F>(isolate, a, b)
    }

    abi_adapter::<T, F>
  }
}
