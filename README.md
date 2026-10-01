# LifeSonar: Lifetime-aware Program Synthesis for Rust Libraries

## Quick Start

To run Lifesonar, first run `./install.sh` from the root directory of the project to install it. Our tool rely on a specific Rust toolchain version `nightly-2025-12-06`. If you install `rustup`, the official Rust toolchain installer, it will automatically install the toolchain with the corresponding version.

Once LifeSonar is installed, you are only one step away from running LifeSonar. Create a `.ltgenconfig` in the root directory of the tested crate, or in any parent directory up to `/`. LifeSonar will automatically detect `.ltgenconfig` from the project directory up to `/`.

Here is a `.ltgenconfig` example to reproduce our evaluation:

```toml
max_complexity = 16
max_iteration = 1000
max_run = 10000
override = true
timeout = 60 
# terminate_on_ub = true # use for debug
# mode = "dryrun" # use for RQ1
```

For more configuration information, please check `rapx/src/analysis/testgen/driver.rs`. 

Finally, run `cargo rapx test` on the tested project directory to start LifeSonar. LifeSonar automatically synthesize programs for the tested library, execute them with Miri and report the results.

To run the conservative checker, use `cargo rapx test --naive-check`.

## Micro-benchmark

Our micro-benchmark is release at `lifetime-bench`, includes 5 positive tests (prefix with `p`), and 2 negative tests (prefix with `n`).
