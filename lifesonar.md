# LifeSonar: Detecting Lifetime-unsoundness Bugs in Rust Libraries

LifeSonar is an automated tool to detect lifetime-unsoundness bugs and synthesize executable Proof-of-Concepts (PoCs). Our tool automatically performs the entire bug detection process, including analyzing crates, constructing the API dependency graph, program synthesis, program checking, and reduction for the tested crate. 

LifeSonar is developed as a fork of the Rust Analysis Platform with Extensions ([RAPx](https://github.com/safer-rust/RAPx)). 

# Quick Start
To run LifeSonar, first run `./install.sh` from the root directory of the project to install LifeSonar.

Once LifeSonar is installed, you are only one step away from running LifeSonar. Create a `.ltgenconfig` in the root directory of the tested crate, or in any parent directory up to `/`. LifeSonar will automatically detect `.ltgenconfig` from the project directory up to `/`.

Here is a `.ltgenconfig` example to reproduce our evaluation:

```toml
max_complexity = 16
max_iteration = 1000
max_run = 10000
override = true
timeout = 60 
# terminate_on_ub = true # use for debug
```

For more configuration information, please check `rapx/src/analysis/testgen/driver.rs`. 

Finally, you just need to run `cargo run -testgen` on the tested project to start LifeSonar.

# Bug Reports


| #   | Crate               | Issue                                                          | UB                          | Status    |
| --- | ------------------- | -------------------------------------------------------------- | --------------------------- | --------- |
| 1   | crossbeam-utils     | [#1203](https://github.com/crossbeam-rs/crossbeam/issues/1203) | dangling reference          | Denied    |
| 2   | aliasable           | [#9](https://github.com/avitex/rust-aliasable/issues/9)        | pointer not deferencable    | Confirmed |
| 3   | bitmaps             | [#33](https://github.com/bodil/bitmaps/issues/33)              | unavailable target features | Pending   |
| 4   | apache/arraw-buffer | [#9286](https://github.com/apache/arrow-rs/issues/9286)        | pointer not deferencable    | Confirmed |
| 5   | apache/arraw-buffer | [#9287](https://github.com/apache/arrow-rs/issues/9287)        | unaligned value             | Confirmed |

