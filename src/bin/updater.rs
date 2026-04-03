// Copyright 2025 Jared Wolff
//
// Licensed under the Apache License, Version 2.0 (the "Apache License")
// with the following modification; you may not use this file except in
// compliance with the Apache License and the following modification to it:
// Section 6. Trademarks. is deleted and replaced with:
//
// 6. Trademarks. This License does not grant permission to use the trade
//    names, trademarks, service marks, or product names of the Licensor
//    and its affiliates, except as required to comply with Section 4(c) of
//    the License and to reproduce the content of the NOTICE file.
//
// You may obtain a copy of the Apache License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the Apache License with the above modification is
// distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. See the Apache License for the specific
// language governing permissions and limitations under the Apache License.
//
// Alternatively, you may use this file under the terms of the MIT license,
// which is:
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use std::{thread, time::Duration};

use chrono::Utc;
use indicatif::{HumanBytes, ProgressBar, ProgressState, ProgressStyle};
use modem_updater::{ModemUpdater, TargetProfile};
use probe_rs::{
    architecture::arm::{
        ap::{ApRegister, CSW, IDR},
        dp::DpAddress,
        sequences::DefaultArmSequence,
        ArmDebugInterface, FullyQualifiedApAddress,
    },
    probe::{list::Lister, DebugProbeSelector, Probe},
    Error, Permissions, Session,
};

fn print_usage() {
    println!("Modem Updater Usage:");
    println!("  updater <operation> <firmware_path>");
    println!("\nOperations:");
    println!("  verify   - Verify firmware at the specified path");
    println!("  program  - Program and verify firmware at the specified path");
    println!("\nExample:");
    println!("  updater program _bin/mfw_nrf91x1_2.0.2.zip");
}

struct Args {
    operation: String,
    path: String,
}

const PROBE_VENDOR_ID: u16 = 0x2e8a;
const PROBE_PRODUCT_ID: u16 = 0x000c;
const APP_MEM: FullyQualifiedApAddress = FullyQualifiedApAddress::v1_with_default_dp(0);
const CTRL_AP: FullyQualifiedApAddress = FullyQualifiedApAddress::v1_with_default_dp(4);
const FICR_INFO_PART: u64 = 0x00FF0140;
const CTRL_ERASEALL: u64 = 0x004;
const CTRL_ERASEALLSTATUS: u64 = 0x008;
const CTRL_RESET: u64 = 0x000;
const UNLOCK_RETRIES: u32 = 3;
const ERASE_TIMEOUT_MS: u64 = 5000;
const DHCSR: u64 = 0xE000_EDF0;
const C_HALT: u32 = 0x2;
const C_DEBUGEN: u32 = 0x1;
const DBGKEY: u32 = 0xA05F_0000;

fn parse_args() -> Result<Args, String> {
    let mut positional: Vec<_> = std::env::args().skip(1).collect();

    if positional.len() != 2 {
        return Err("expected <operation> <firmware_path>".to_string());
    }

    Ok(Args {
        operation: positional.remove(0),
        path: positional.remove(0),
    })
}

fn open_probe(lister: &Lister) -> Probe {
    let start = Utc::now().timestamp_millis();

    let selector = DebugProbeSelector {
        vendor_id: PROBE_VENDOR_ID,
        product_id: PROBE_PRODUCT_ID,
        interface: None,
        serial_number: None,
    };

    // Suppress panic output from probe-rs internals (e.g. Glasgow driver)
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    loop {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            lister.open(selector.clone())
        }));

        match result {
            Ok(Ok(mut probe)) => {
                std::panic::set_hook(default_hook);
                probe.set_speed(12000).unwrap();
                return probe;
            }
            Ok(Err(_)) | Err(_) => {
                let now = Utc::now().timestamp_millis();
                if now > start + 2000 {
                    std::panic::set_hook(default_hook);

                    // Check if the probe is visible on USB but failed to open
                    let probes = lister.list(Some(&selector));
                    if probes.is_empty() {
                        eprintln!("\nError: No debug probe detected.");
                        eprintln!("Please check that the programmer is connected via USB and powered on.");
                    } else {
                        eprintln!("\nError: Debug probe found but unable to initialize.");
                        eprintln!("Please check that the target board is connected to the programmer.");
                    }
                    std::process::exit(1);
                }

                thread::sleep(Duration::from_millis(100));
            }
        }
    }
}

fn should_try_recover(err: &Error) -> bool {
    matches!(err, Error::Arm(_) | Error::MissingPermissions(_))
}

fn detect_target_profile(mut probe: Probe) -> Result<TargetProfile, Error> {
    probe.attach_to_unspecified()?;
    let mut iface = probe
        .try_into_arm_debug_interface(DefaultArmSequence::create())
        .map_err(|(_, err)| Error::from(err))?;

    iface.select_debug_port(DpAddress::Default)?;

    let mut memory = iface.memory_interface(&APP_MEM).map_err(Error::from)?;
    let part_info = format!("{:08X}", memory.read_word_32(FICR_INFO_PART)?);

    match part_info.as_str() {
        "00009160" => Ok(TargetProfile::Nrf9160),
        "00009151" => Ok(TargetProfile::Nrf9151),
        _ => panic!("Unknown nRF91 part number: {}", part_info),
    }
}

fn detect_target_profile_with_recovery(lister: &Lister) -> TargetProfile {
    match detect_target_profile(open_probe(lister)) {
        Ok(chip) => chip,
        Err(err) if should_try_recover(&err) => {
            log::warn!(
                "Initial chip detection failed: {}. Trying nRF91 unlock sequence.",
                err
            );

            restore_debug_access(open_probe(lister)).unwrap_or_else(|recover_err| {
                panic!(
                    "Unable to restore debug access before chip detection: {}",
                    recover_err
                )
            });

            detect_target_profile(open_probe(lister)).unwrap_or_else(|retry_err| {
                panic!(
                    "Unable to detect target chip after recovery! Error: {}",
                    retry_err
                )
            })
        }
        Err(err) => panic!("Unable to detect target chip! Error: {}", err),
    }
}

fn halt_cpu_if_possible(iface: &mut dyn ArmDebugInterface) {
    match iface.write_raw_ap_register(&APP_MEM, DHCSR, DBGKEY | C_DEBUGEN | C_HALT) {
        Ok(_) => {
            log::info!("CPU halted successfully");
            thread::sleep(Duration::from_millis(10));
        }
        Err(err) => {
            log::warn!("Could not halt CPU (device may be locked): {}", err);
        }
    }
}

fn check_debug_access(iface: &mut dyn ArmDebugInterface) -> Result<bool, Error> {
    let csw = iface.read_raw_ap_register(&APP_MEM, CSW::ADDRESS)?;
    let dbg_status = (csw >> 6) & 1;
    log::info!("CSW: 0x{:08X}, DbgStatus: {}", csw, dbg_status);
    Ok(dbg_status == 1)
}

fn perform_device_reset(iface: &mut dyn ArmDebugInterface) -> Result<(), Error> {
    iface.write_raw_ap_register(&CTRL_AP, CTRL_RESET, 1)?;
    thread::sleep(Duration::from_millis(1));
    iface.write_raw_ap_register(&CTRL_AP, CTRL_RESET, 0)?;
    thread::sleep(Duration::from_millis(20));
    log::info!("Performed soft reset");
    Ok(())
}

fn rapid_chip_erase(iface: &mut dyn ArmDebugInterface, timeout_ms: u64) -> Result<(), Error> {
    iface.write_raw_ap_register(&CTRL_AP, CTRL_ERASEALL, 1)?;
    log::warn!("Started CTRL-AP ERASEALL");

    let start = std::time::Instant::now();
    let timeout = Duration::from_millis(timeout_ms);

    while start.elapsed() < Duration::from_millis(100) {
        if iface.read_raw_ap_register(&CTRL_AP, CTRL_ERASEALLSTATUS)? == 0 {
            log::info!("Erase completed in {:?}", start.elapsed());
            return Ok(());
        }
        thread::sleep(Duration::from_millis(10));
    }

    while start.elapsed() < timeout {
        if iface.read_raw_ap_register(&CTRL_AP, CTRL_ERASEALLSTATUS)? == 0 {
            log::info!("Erase completed in {:?}", start.elapsed());
            return Ok(());
        }
        thread::sleep(Duration::from_millis(100));
    }

    Err(Error::Timeout)
}

fn restore_debug_access(mut probe: Probe) -> Result<(), Error> {
    probe.attach_to_unspecified()?;
    let mut iface = probe
        .try_into_arm_debug_interface(DefaultArmSequence::create())
        .map_err(|(_, err)| Error::from(err))?;

    iface.select_debug_port(DpAddress::Default)?;
    halt_cpu_if_possible(&mut *iface);

    if let Ok(true) = check_debug_access(&mut *iface) {
        log::info!("Device already unlocked");
        return Ok(());
    }

    let idr = iface
        .read_raw_ap_register(&CTRL_AP, IDR::ADDRESS)
        .unwrap_or(0);
    log::info!("CTRL-AP IDR: 0x{:08X}", idr);
    if idr == 0 {
        return Err(Error::Other(
            "CTRL-AP not accessible, check connections".to_string(),
        ));
    }

    for attempt in 1..=UNLOCK_RETRIES {
        log::warn!("Unlock attempt {}/{}", attempt, UNLOCK_RETRIES);
        rapid_chip_erase(&mut *iface, ERASE_TIMEOUT_MS)?;
        perform_device_reset(&mut *iface)?;

        let verify_start = std::time::Instant::now();
        let verify_timeout = Duration::from_secs(2);

        while verify_start.elapsed() < verify_timeout {
            match check_debug_access(&mut *iface) {
                Ok(true) => {
                    log::info!("Device unlocked successfully");
                    return Ok(());
                }
                Ok(false) if verify_start.elapsed() > Duration::from_millis(500) => {
                    log::warn!("Debug access not enabled after reset");
                    break;
                }
                Ok(false) => thread::sleep(Duration::from_millis(50)),
                Err(err) => {
                    log::warn!("Error checking debug status: {}", err);
                    thread::sleep(Duration::from_millis(100));
                }
            }
        }

        if attempt < UNLOCK_RETRIES {
            thread::sleep(Duration::from_millis(1000));
        }
    }

    Err(Error::Other(
        "Failed to unlock device after all retries".to_string(),
    ))
}

fn attach_session(lister: &Lister, chip: TargetProfile) -> Session {
    let probe = open_probe(lister);

    match probe.attach(
        chip.probe_rs_target_name(),
        Permissions::new().allow_erase_all(),
    ) {
        Ok(session) => session,
        Err(err) if should_try_recover(&err) => {
            log::warn!(
                "Initial attach to {} failed: {}. Trying nRF91 unlock sequence.",
                chip,
                err
            );

            restore_debug_access(open_probe(lister)).unwrap_or_else(|recover_err| {
                panic!("Unable to restore debug access: {}", recover_err)
            });

            let probe = open_probe(lister);
            probe
                .attach(
                    chip.probe_rs_target_name(),
                    Permissions::new().allow_erase_all(),
                )
                .unwrap_or_else(|retry_err| {
                    panic!(
                        "Unable to attach to probe after recovery! Error: {}",
                        retry_err
                    )
                })
        }
        Err(err) => panic!("Unable to attach to probe! Error: {}", err),
    }
}

fn main() {
    env_logger::init();

    let args = match parse_args() {
        Ok(args) => args,
        Err(err) => {
            eprintln!("Argument error: {err}");
            print_usage();
            std::process::exit(1);
        }
    };

    if args.operation != "verify" && args.operation != "program" {
        println!("\nError: Unknown operation '{}'", args.operation);
        print_usage();
        std::process::exit(1);
    }

    let lister = Lister::new();
    let chip = detect_target_profile_with_recovery(&lister);

    let mut session = attach_session(&lister, chip);

    // Get updater
    let mut updater = ModemUpdater::new_with_target(&mut session, chip);

    if args.operation == "verify" {
        match updater.verify(&args.path) {
            Ok(true) => println!("Firmware verification succeeded."),
            Ok(false) => {
                eprintln!("Firmware verification failed. Inspect device logs for details.");
                std::process::exit(2);
            }
            Err(err) => {
                eprintln!("Verification error: {err}");
                std::process::exit(2);
            }
        }
    } else if args.operation == "program" {
        let progress_bar = ProgressBar::new(0);
        progress_bar.set_style(
            ProgressStyle::with_template(
                "{spinner:.green} [{elapsed_precise}] [{wide_bar:.cyan/blue}] {bytes}/{total_bytes} ({eta})",
            )
            .unwrap()
            .with_key("bytes", |state: &ProgressState, w: &mut dyn std::fmt::Write| {
                let _ = write!(w, "{}", HumanBytes(state.pos()));
            })
            .with_key("total_bytes", |state: &ProgressState, w: &mut dyn std::fmt::Write| {
                if let Some(len) = state.len() {
                    let _ = write!(w, "{}", HumanBytes(len));
                } else {
                    let _ = w.write_str("0 B");
                }
            })
            .progress_chars("=>-"),
        );
        progress_bar.enable_steady_tick(Duration::from_millis(100));

        updater.set_progress_callback({
            let progress = progress_bar.clone();
            let mut initialized = false;
            move |current, total| {
                if !initialized {
                    progress.set_length(total);
                    initialized = true;
                }

                progress.set_position(current.min(total));

                if current >= total {
                    progress.finish_and_clear();
                }
            }
        });

        match updater.program_and_verify(&args.path) {
            Ok(true) => {
                progress_bar.finish_and_clear();
                println!("Programming complete. Firmware verification succeeded.");
            }
            Ok(false) => {
                progress_bar.finish_and_clear();
                eprintln!(
                    "Programming finished but firmware verification failed. Re-run verify for details."
                );
                std::process::exit(3);
            }
            Err(err) => {
                progress_bar.finish_and_clear();
                eprintln!("Programming error: {err}");
                std::process::exit(3);
            }
        }
    }
}
