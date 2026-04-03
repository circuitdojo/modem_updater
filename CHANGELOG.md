# Changelog

All notable changes to this project will be documented in this file.

## [0.1.4] - 2026-04-03

- Added explicit `nrf9151` and `nrf9160` target profiles to the updater flow.
- Added nRF91 part-number detection so the CLI auto-selects `nrf9151` vs `nrf9160`.
- Aligned updater pre-attach recovery with the working recovery flow, including CTRL-AP `AP4` erase/reset handling for locked devices.

## [0.1.2] - 2025-09-25

- Added a CLI progress bar and explicit verification reporting during modem updates.
- Exposed a library progress callback so other tools can surface flash status updates.
- Authored `AGENTS.md` to outline project structure and contributor expectations.

## [0.1.1] - 2025-09-24

- Added a GitHub Actions workflow to build release binaries for macOS, Windows, and Linux.
- Documented onboarding steps for new developers, including Rust toolchain installation and probe dependencies.

## [0.1.0]

- Initial release.
