//! Two traits that mention each other *and* take each other's dictionary as an argument, with
//! different parameter counts because one of them has an associated type.
//!
//! This is serde's shape: `Serializer::serialize` takes the `Serialize` dictionary, `Serialize`
//! declares the associated types that become `Serializer`'s extra parameters, and the pair is one
//! recursive group. A `mutual` block cannot hold it -- Lean requires every member of a mutual
//! group to take the same parameters ("Invalid mutually inductive types"), and once the parameters
//! are levelled the dictionary argument is a negative occurrence, which the kernel also refuses.
//!
//! The model keeps both traits and every method; what changes is that a dictionary is passed as a
//! parameter instead of being embedded in the sibling's type.

pub trait Writer {
    type Sink;

    // Returns an instance of the associated type -- the position that becomes a positive
    // occurrence, mirroring `Serializer::serialize_seq`.
    fn open(&self) -> Self::Sink;

    // Takes the *other* dictionary as an argument -- the negative occurrence.
    fn sync<R: Reader>(&self, r: &R) -> u32;
}

pub trait Reader {
    fn read(&self) -> u32;

    // Mentions Writer, which closes the cycle.
    fn make<W: Writer>(&self) -> u32;
}
