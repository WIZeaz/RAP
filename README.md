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

## Issue Links

| Crate | Status | Link |
|-------|--------|------|
| aliasable-0.1.3 | Confirmed | [avitex/rust-aliasable#9](https://github.com/avitex/rust-aliasable/issues/9) |
| arrow-buffer-57.2.0 | Confirmed | [apache/arrow-rs#9286](https://github.com/apache/arrow-rs/issues/9286) |
| arrow-buffer-57.2.1 | Confirmed | [apache/arrow-rs#9287](https://github.com/apache/arrow-rs/issues/9287) |
| compact_str-0.9.0 | Confirmed | [ParkMyCar/compact_str#452](https://github.com/ParkMyCar/compact_str/issues/452) |
| pxfm-0.1.28 | Confirmed | [awxkee/pxfm#87](https://github.com/awxkee/pxfm/issues/87) |
| pxfm-0.1.28 | Confirmed | [awxkee/pxfm#88](https://github.com/awxkee/pxfm/issues/88) |
| str_stack-0.1.0 | Confirmed | [Stebalien/str_stack#4](https://github.com/Stebalien/str_stack/issues/4) |
| redox_syscall-0.7.3 | Confirmed | contacted by email |
| orbclient-0.3.54 | Confirmed | contacted by email |
| bitmaps-3.2.1 | Pending | [bodil/bitmaps#33](https://github.com/bodil/bitmaps/issues/33) |
| widestring-1.2.1 | Pending | [VoidStarKat/widestring-rs#51](https://github.com/VoidStarKat/widestring-rs/issues/51) |
| quick-protobuf-0.8.1 | Pending | [tafia/quick-protobuf#272](https://github.com/tafia/quick-protobuf/issues/272) |