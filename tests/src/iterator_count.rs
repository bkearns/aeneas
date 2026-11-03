//@ [!lean] skip

//! Regression test for `Iterator::count`.
//!
//! `count` is a *provided* method of the `Iterator` trait, so a call to it is not a call to
//! anything the crate defines: it names the trait's default body. Two shapes come out of the
//! translator and both need the model to carry `count`:
//!
//! * on a concrete iterator (`xs.iter()`, `0..n`) the call is to the trait default, which is
//!   looked up in the model table;
//! * through a generic `I: Iterator` the iterator's dictionary is not known, so the call is a
//!   projection of the dictionary — a *field* of the `Iterator` structure.
//!
//! Before the model existed the first shape failed the table lookup and the second did not
//! elaborate at all (`Iterator` has no field `count`).

pub fn slice_count(xs: &[u32]) -> u32 {
    xs.iter().count() as u32
}

pub fn range_count(n: u32) -> u32 {
    (0..n).count() as u32
}

pub fn generic_count<I: Iterator>(it: I) -> u64 {
    it.count() as u64
}
