//@ [!lean] skip
//! Returning `impl Iterator` over borrowed items from a hand-written function.
//!
//! Charon resolves a return-position `impl Trait` to the concrete type the
//! function returns, so `impl Iterator<Item = &'_ str>` becomes (for instance)
//! `Map<Iter<'a, String>, for<'b> String::as_str<'b>>`. The second argument is a
//! *function item*: a zero-sized type that binds regions of its own and
//! instantiates them at every call.
//!
//! Aeneas used to reject such a type -- "Unimplemented" for the signature, and
//! "found an occurrence of a lifetime constraint relating a higher-ranked
//! lifetime to a free lifetime" for the `FnMut`/`FnOnce` impls of the item --
//! which made ordinary iterator-returning functions untranslatable. The
//! treatment (see `TypesUtils.ty_is_rty`, `TypesAnalysis`, `RegionsHierarchy`
//! and `SymbolicToPureTypes.translate_fwd_ty`) is to read the item's own
//! regions as belonging to the item: they are never borrows of the signature,
//! so they stay out of the region hierarchy, are never projected, and are
//! erased by the pure encoding. A value of the item's type is translated as the
//! item's arrow type, and a call to the item is a call to the translation of
//! the function it denotes.
//!
//! The Lean-only marker matches the other iterator-adaptor tests
//! (`iter_adapters.rs`): the adaptors are modelled in the Lean standard library
//! and are only nameable there. This test stops at one adaptor on purpose:
//! chaining two of them also reaches `impl Iterator for Map`, whose dictionary
//! has `chain`/`map` fields that `Aeneas/Std/Core/Iter.lean` does not model yet
//! (the translator warns about exactly that: "the model defined in the Lean
//! library seems to be missing the corresponding field"). That gap is in the
//! library model, not in the translation of the item's type.

pub struct Metadata {
    pub partition_key: Vec<String>,
    pub clustering_key: Vec<String>,
}

impl Metadata {
    /// A method: the elided lifetime is the one of `&self`.
    pub fn primary_key(&self) -> impl Iterator<Item = &'_ str> {
        self.partition_key.iter().map(String::as_str)
    }

    /// The same, with the lifetime written out.
    pub fn all_keys<'a>(&'a self) -> impl Iterator<Item = &'a str> {
        self.clustering_key.iter().map(String::as_str)
    }
}

/// A free function over a borrow of its argument.
pub fn names(m: &Metadata) -> impl Iterator<Item = &'_ str> {
    m.partition_key.iter().map(String::as_str)
}
