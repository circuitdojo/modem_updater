# nRF91 Modem Updater using `probe-rs`

## Summary

This is a tool to update the nRF91 modem firmware using the `probe-rs` crate. It provides both a CLI and library interface. Used in production on the [nRF9160 Feather](https://www.circuitdojo.com/products/nrf9160-feather) and [nRF9151 Feather](https://www.circuitdojo.com/products/nrf9151-feather).

Validated working on:

- nRF9160
- nRF9151
- nRF9161

## Getting Started

### 1. Install the Rust toolchain

Install Rust using [`rustup`](https://rustup.rs/).

On macOS and Linux:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

On Windows download and run the installer from [rustup.rs](https://rustup.rs/), then open a new PowerShell or Command Prompt window.

After installation, confirm the toolchain is available:

```bash
rustc --version
cargo --version
```

### 2. Clone this repository

```bash
git clone https://github.com/circuitdojo/modem_updater.git
cd modem_updater
```

### 3. Build the project

Build a release binary locally:

```bash
cargo build --release
```

The resulting executable is located in `target/release/`.

### 4. Install probe dependencies

- **Linux:** ensure `libusb-1.0` is present (`sudo apt install libusb-1.0-0`).
- **macOS:** install [Homebrew](https://brew.sh/) and run `brew install libusb` if it is not already available.
- **Windows:** if necessary, use [Zadig](https://zadig.akeo.ie/) to install a WinUSB driver for your debug probe.

## CLI Usage

To verify the modem firmware, run:

```bash
cargo run --bin updater -- verify <path_to_firmware_zip>
```

To program and verify the modem firmware, run:

```bash
cargo run --bin updater -- program <path_to_firmware_zip>
```

### Install the CLI globally

```bash
cargo install --path .
```

This places the `modem_updater` binary in `~/.cargo/bin` (or the equivalent on Windows).

## Acknowledgements

This project is based on the work of [**@maxd-nordic**](https://github.com/maxd-nordic) in the [pyOCD](https://github.com/pyocd/pyOCD/blob/5166025ae5da5e093d6cfe2b26cae5e1334476e4/pyocd/target/family/target_nRF91.py#L629) project.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or
  http://opensource.org/licenses/MIT) at your option.
