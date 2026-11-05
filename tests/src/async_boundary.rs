//@ [coq,fstar,hol4] skip
//@ charon-args=--opaque async_boundary::_::block_on

// A synchronous entry point that awaits an asynchronous function through a
// run-time handle.
//
// The value an `async fn` returns has no translation: Charon gives it an error
// type, so the caller that hands it to the runtime used to be dropped whole.
// It is modelled as an assumption instead - see
// [PrePasses.model_awaited_computations]: the value is an opaque `Future`, the
// `async fn` keeps its signature and loses its body, and the run-time call is
// the synchronous boundary.

use core::future::Future;

pub struct Handle;

impl Handle {
    // Opaque: the run-time is not part of the model. Its contract is
    // `block_on(f)` evaluates `f` to completion and returns its output; no
    // other effect is observable.
    pub fn block_on<F: Future>(&self, fut: F) -> F::Output {
        let _ = fut;
        unimplemented!("the run-time is not modelled")
    }
}

async fn doubled(x: u32) -> u32 {
    x + x
}

pub fn run(h: &Handle, x: u32) -> u32 {
    h.block_on(doubled(x))
}
