pub mod core;
pub mod opt;
pub mod rcanary;
pub mod safedrop;
pub mod senryx;
pub mod unsafety_isolation;
pub mod utils;

pub trait Analysis<Q, R> {
    /// Returns the name of the analysis.
    fn name(&self) -> &'static str;

    /// returns the result for the given query.
    fn get(&mut self, query: Q) -> R;
}
