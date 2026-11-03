//@ [lean] known-failure
//@ [!lean] skip
// A `c"..."` literal is lifted into an anonymous constant of type `CStr` whose value is an
// aggregate, not a scalar. Reading such a constant has no value representation here, so the
// translator must name the item and the shape it actually got -- and fail this function only,
// not the whole run.

use std::ffi::CStr;

pub fn first_byte() -> i8 {
    let s: &CStr = c"abc";
    unsafe { *s.as_ptr() }
}

pub fn empty_len() -> usize {
    let s: &CStr = c"";
    s.count_bytes()
}
