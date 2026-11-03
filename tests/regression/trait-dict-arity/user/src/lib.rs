//! Uses the pair only through bounds, so both declarations arrive as transitive external items --
//! the position a downstream crate has with respect to serde.

pub fn drive<W: dep::Writer, R: dep::Reader>(w: &W, r: &R) -> u32 {
    let _ = w.open();
    w.sync(r) + r.make::<W>()
}
