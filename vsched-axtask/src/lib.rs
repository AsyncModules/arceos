#![cfg_attr(not(test), no_std)]
#![feature(doc_cfg)]
#![feature(linkage)]
#![feature(unsafe_cell_access)]

#[macro_use]
extern crate log;
extern crate alloc;

mod api;
mod mem;

#[macro_use]
mod run_queue;
mod task;

#[cfg(test)]
mod tests;

#[cfg(feature = "irq")]
mod timers;
mod wait_queue;

pub use api::*;
