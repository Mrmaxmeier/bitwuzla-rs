# Bitwuzla

[![crates.io](https://img.shields.io/crates/v/bitwuzla.svg)](https://crates.io/crates/bitwuzla)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/cdisselkoen/bitwuzla-rs/main/LICENSE)

Safe high-level bindings for the [Bitwuzla] SMT solver, version 3.2.2.

## Installation

This crate relies on the [`bitwuzla-sys`] crate, so you will need to follow
its directions for installation as well. In particular, you can either:
  - compile and install Bitwuzla 3.2.2 on your system as a shared library; or
  - activate the `vendor-cadical` feature on this crate, which will automatically
    build a static bitwuzla and link to it. E.g.,
    ```toml
    [dependencies]
    bitwuzla = { version = "0.1.0", features = ["vendor-cadical"] }
    ```
For more details, see the [`bitwuzla-sys`] README.

[Bitwuzla]: https://bitwuzla.github.io
[`bitwuzla-sys`]: https://crates.io/crates/bitwuzla-sys

## Caveats

These bindings are not necessarily complete; there may be some features
present in [`bitwuzla-sys`] which are not directly exposed here, e.g.,
uninterpreted functions (`bitwuzla_uf()`). Contributions are welcome.

This crate currently requires Rust 1.41+.
