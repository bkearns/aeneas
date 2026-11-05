//@ [coq] skip
//@ [fstar] skip
//@ [hol4] skip

//! Tests for the iterator adapters that return another iterator: `map`, `filter`, `chain`, plus the
//! consuming `collect` and `find`.
//!
//! Two shapes come out of the translator and both need the model to carry the fields:
//!
//! * an `impl Iterator` literal the crate itself causes to be emitted (the crate-defined `Counter`
//!   below, and any adapter the library does not model) sets a field for every provided method the
//!   translator translated -- `chain`, `map`, `filter`, `collect`, `find`. A field the `Iterator`
//!   structure does not have is a hard error in code that never mentions the method.
//! * a call through a generic `I: Iterator` is a *projection* of the dictionary, so the struct has
//!   to carry the method as a field for the call to elaborate at all.
//!
//! Lean-only: the other backends have no model of these adapters, so they cannot name `Map`,
//! `Filter` or `Chain` at all.
//!
//! Owned `Vec` rather than slices on purpose: a slice iterator's method signatures relate a
//! higher-ranked lifetime to the iterator's own, which this version of the translator rejects
//! before any of the above is reached.

/// `map` over a vector of scalars
fn map_scaled(v: Vec<u32>) -> Vec<u32> {
    let mut out = Vec::new();
    for x in v.into_iter().map(|x| x + 1) {
        out.push(x);
    }
    out
}

/// `filter` keeps the even elements
fn filter_even(v: Vec<u32>) -> Vec<u32> {
    let mut out = Vec::new();
    for x in v.into_iter().filter(|x| *x % 2 == 0) {
        out.push(x);
    }
    out
}

/// `chain` walks the first vector then the second
fn chain_two(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let mut out = Vec::new();
    for x in a.into_iter().chain(b.into_iter()) {
        out.push(x);
    }
    out
}

/// `map` then `filter` then `chain`
fn mixed(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let mut out = Vec::new();
    for x in a
        .into_iter()
        .map(|x| x * 2)
        .filter(|x| *x > 2)
        .chain(b.into_iter())
    {
        out.push(x);
    }
    out
}

/// `collect` into a vector from a range
fn collect_range(n: u32) -> Vec<u32> {
    (0u32..n).collect()
}

/// `map` then `collect`
fn collect_mapped(v: Vec<u32>) -> Vec<u32> {
    v.into_iter().map(|x| x + 1).collect()
}

/// `filter` then `collect`
fn collect_filtered(v: Vec<u32>) -> Vec<u32> {
    v.into_iter().filter(|x| *x > 1).collect()
}

// ============================================================================
// Generic dictionaries: these project the `Iterator` fields directly
// ============================================================================

/// `find` through a dictionary: the body is a projection of the `find` field.
pub fn find_generic<I: Iterator<Item = u32>>(mut it: I) -> Option<u32> {
    it.find(|x| *x > 2)
}

/// `map` and `collect` through a dictionary.
pub fn map_collect_generic<I: Iterator<Item = u32>>(it: I) -> Vec<u32> {
    it.map(|x| x + 1).collect()
}

/// `chain` through dictionaries: the body projects the `chain` field, then `collect`.
pub fn chain_collect_generic<I: Iterator<Item = u32>, J: Iterator<Item = u32>>(
    a: I,
    b: J,
) -> Vec<u32> {
    a.chain(b).collect()
}

/// `filter` through a dictionary.
pub fn filter_collect_generic<I: Iterator<Item = u32>>(mut it: I) -> Vec<u32> {
    it.filter(|x| *x > 1).collect()
}

// ============================================================================
// An iterator the crate defines itself
// ============================================================================

/// A hand-written iterator, so the `impl Iterator` literal the translator emits for a type the
/// library does not model carries the adapter fields.
pub struct Counter {
    pub n: u32,
}

impl Counter {
    pub fn new(n: u32) -> Counter {
        Counter { n }
    }
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        if self.n == 0 {
            None
        } else {
            self.n = self.n - 1;
            Some(self.n)
        }
    }
}

/// `chain` on a crate-defined iterator
pub fn counter_chain_sum(a: u32, b: u32) -> u32 {
    let mut s = 0u32;
    for x in Counter::new(a).chain(Counter::new(b)) {
        s = s + x;
    }
    s
}

/// `map` then `collect` on a crate-defined iterator
pub fn counter_map_collect(n: u32) -> Vec<u32> {
    Counter::new(n).map(|x| x + 1).collect()
}

/// `filter` on a crate-defined iterator
pub fn counter_filter_sum(n: u32) -> u32 {
    let mut s = 0u32;
    for x in Counter::new(n).filter(|x| *x > 2) {
        s = s + x;
    }
    s
}

/// `find` on a crate-defined iterator: the concrete call resolves to the trait's default body.
pub fn counter_find(n: u32) -> Option<u32> {
    let mut it = Counter::new(n);
    it.find(|x| *x > 2)
}
