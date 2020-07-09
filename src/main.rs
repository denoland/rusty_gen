#[derive(Copy, Clone)]
pub struct Local<'a>(&'a ());
pub struct HandleScope<'a>(&'a mut Isolate);
impl<'a> HandleScope<'a> {
  fn new_local(&'_ mut self) -> Local<'a> {
    Local(&())
  }
}

fn main() {}

pub struct Isolate([u8; 0]);

////// Generic

use std::borrow::Borrow;
use std::ffi::c_void;
use std::ptr;

pub trait Unit: Sized {
  fn get() -> Self {
    assert_eq!(std::mem::size_of::<Self>(), 0);
    unsafe { std::mem::MaybeUninit::<Self>::zeroed().assume_init() }
  }
}

impl<T: Sized> Unit for T {}

trait CxxCallback<F>: Unit {
  type CxxFn;
  fn cxx_callback() -> Self::CxxFn;
}

///// MyCallback

pub trait MyCallback:
  Unit + for<'a> FnOnce(&mut HandleScope<'a>, Local<'a>, i32) -> Local<'a>
{
}
impl<F: for<'a> FnOnce(&mut HandleScope<'a>, Local<'a>, i32) -> Local<'a>>
  MyCallback for F
{
}
type CxxMyCallback = for<'a> extern "C" fn(
  *mut Local<'a>,
  *mut Isolate,
  Local<'a>,
  i32,
) -> *mut Local<'a>;

impl<F: MyCallback> CxxCallback<Self> for F {
  type CxxFn = CxxMyCallback;

  fn cxx_callback() -> Self::CxxFn {
    #[inline(always)]
    fn signature_adapter<'a, F: MyCallback>(
      isolate: *mut Isolate,
      a: Local<'a>,
      b: i32,
    ) -> Local<'a> {
      let hs = &mut HandleScope(unsafe { &mut *isolate });
      (F::get())(hs, a, b)
    }

    #[inline(always)]
    extern "C" fn abi_adapter<'a, F: MyCallback>(
      ret: *mut Local<'a>,
      isolate: *mut Isolate,
      a: Local<'a>,
      b: i32,
    ) -> *mut Local<'a> {
      unsafe { ptr::write(ret, signature_adapter::<F>(isolate, a, b)) };
      ret
    }

    abi_adapter::<F>
  }
}

impl<F: MyCallback> Borrow<CxxMyCallback> for F {
  fn borrow(&self) -> CxxMyCallback {
    F::cxx_callback()
  }
}

mod my_callback_tests {
  use super::*;

  fn test() {
    let _ = convert_to_cxx(&callback);
  }

  fn convert_to_cxx<F: MyCallback>(_: &F) -> CxxMyCallback {
    F::cxx_callback()
  }

  fn callback<'s>(
    _hs: &mut HandleScope<'s>,
    _a: Local<'s>,
    _b: i32,
  ) -> Local<'s> {
    unimplemented!()
  }
}

///// OtherCallback

pub trait OtherCallback<T: Sized>:
  Unit + for<'a> FnOnce(&mut HandleScope<'a>, Local<'a>, &mut T) -> usize
{
}
impl<
    T: Sized,
    F: for<'a> FnOnce(&mut HandleScope<'a>, Local<'a>, &mut T) -> usize,
  > OtherCallback<T> for F
{
}
type CxxOtherCallback<T> =
  for<'a> extern "C" fn(*mut Isolate, Local<'a>, *mut T) -> usize;

impl<T: Sized, F: OtherCallback<T>> CxxCallback<CxxOtherCallback<T>> for F {
  type CxxFn = CxxOtherCallback<T>;

  fn cxx_callback() -> Self::CxxFn {
    #[inline(always)]
    fn signature_adapter<'a, T: Sized, F: OtherCallback<T>>(
      isolate: *mut Isolate,
      a: Local<'a>,
      b: *mut T,
    ) -> usize {
      let hs = &mut HandleScope(unsafe { &mut *isolate });
      let b = unsafe { &mut *b };
      (F::get())(hs, a, b)
    }

    #[inline(always)]
    extern "C" fn abi_adapter<'a, T: Sized, F: OtherCallback<T>>(
      isolate: *mut Isolate,
      a: Local<'a>,
      b: *mut T,
    ) -> usize {
      signature_adapter::<T, F>(isolate, a, b)
    }

    abi_adapter::<T, F>
  }
}
