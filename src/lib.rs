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

//! Modem firmware update utility for nRF91 Series
//!
//! This crate provides functionality to update modem firmware on nRF91 Series devices
//! using probe-rs for debugging interface access. It supports both verification and
//! programming operations.
//!
//! # Example
//! ```no_run
//! use probe_rs::{
//!     probe::{list::Lister, DebugProbeSelector},
//!     Permissions,
//! };
//! use modem_updater::ModemUpdater;
//!
//! let lister = Lister::new();
//! let probe = lister.open(DebugProbeSelector {
//!     vendor_id: 0x2e8a,
//!     product_id: 0x000c,
//!     serial_number: None,
//! }).unwrap();
//! let mut session = probe.attach("nRF9160_xxAA", Permissions::new().allow_erase_all()).unwrap();
//! let mut updater = ModemUpdater::new(&mut session);
//! updater.program_and_verify("modem_update.zip").unwrap();
//! ```

use bin_file::BinFile;
use chrono::Utc;
use probe_rs::flashing::{self};
use probe_rs::{MemoryInterface, Session};
use regex::Regex;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::PathBuf;
use std::time::Duration;
use tempfile::TempDir;
use zip::read::ZipArchive;

/// Maximum time in seconds to wait for mass erase operation
const MASS_ERASE_TIMEOUT: i64 = 30;

/// Address of the fault event register
const FAULT_EVENT: u64 = 0x4002A100;
/// Address of the command event register  
const COMMAND_EVENT: u64 = 0x4002A108;
/// Address of the data event register
const DATA_EVENT: u64 = 0x4002A110;

/// Maximum buffer size for pipelined operations
const IPC_PIPELINED_MAX_BUFFER_SIZE: usize = 0xE000;
/// Maximum buffer size for non-pipelined operations
const IPC_MAX_BUFFER_SIZE: usize = 0x10000;

/// Main struct for performing modem firmware updates
pub struct ModemUpdater<'a> {
    session: &'a mut Session,
    pipelined: bool,
    segments: BTreeMap<String, PathBuf>,
    firmware_update_digest: Option<String>,
}

/// Converts a byte slice into a 32-bit word using little-endian ordering
fn bytes_to_word(bts: &[u8]) -> u32 {
    let mut result: u32 = 0;
    for (i, b) in bts.iter().enumerate() {
        result |= (*b as u32) << (8 * i);
    }
    result
}

/// Changes the endianness of a 32-bit word, operating on n bytes
fn change_endianness(x: u32, n: u32) -> u32 {
    let mut result = 0;
    for i in 0..n {
        result |= ((x >> (8 * i)) & 0xFF) << (8 * (n - i - 1));
    }
    result
}

impl<'a> ModemUpdater<'a> {
    /// Creates a new ModemUpdater instance
    pub fn new(session: &'a mut Session) -> Self {
        Self {
            session,
            pipelined: false,
            segments: BTreeMap::new(),
            firmware_update_digest: None,
        }
    }

    /// Verifies the modem firmware from a zip file without programming
    ///
    /// # Arguments
    /// * `mfw_zip` - Path to the modem firmware zip file
    ///
    /// # Returns
    /// * `Ok(true)` if verification succeeded
    /// * `Ok(false)` if verification failed
    /// * `Err` if an error occurred during verification
    pub fn verify(&mut self, mfw_zip: &str) -> Result<bool, io::Error> {
        let mut result = false;

        // Get temporary directory
        let temp_dir = TempDir::new().unwrap();

        self.setup_device();
        self.process_zip_file(mfw_zip, &temp_dir)?;

        log::info!("Verifying modem firmware.");
        match self._verify() {
            Ok(v) => {
                if !v {
                    log::info!("Modem firmware verification failed!");
                } else {
                    log::info!("Modem firmware verified.");
                    result = true;
                }
            }
            Err(e) => {
                log::error!("Modem firmware verification failed! Error: {}", e);
            }
        };

        // Reset
        self.session.core(0).unwrap().reset().unwrap();

        Ok(result)
    }

    /// Programs and verifies modem firmware from a zip file
    ///
    /// # Arguments
    /// * `mfw_zip` - Path to the modem firmware zip file
    ///
    /// # Returns
    /// * `Ok(())` if programming and verification succeeded
    /// * `Err` if an error occurred during programming or verification
    pub fn program_and_verify(&mut self, mfw_zip: &str) -> Result<(), io::Error> {
        // Get temporary directory
        let temp_dir = TempDir::new().unwrap();

        self.setup_device();
        self.process_zip_file(mfw_zip, &temp_dir)?;

        log::info!("Programming modem firmware..");

        for s in self.segments.values().cloned().collect::<Vec<PathBuf>>() {
            self.program_segment(&s)?;
        }

        log::info!("Modem firmware programmed.");

        log::info!("Verifying modem firmware.");
        match self._verify() {
            Ok(v) => {
                if !v {
                    log::info!("Modem firmware verification failed!");
                } else {
                    log::info!("Modem firmware verified.");
                }
            }
            Err(e) => {
                log::error!("Modem firmware verification failed! Error: {}", e);
            }
        };

        // Reset
        self.session.core(0).unwrap().reset().unwrap();

        Ok(())
    }

    /// Reads the key digest from the device
    fn read_key_digest(&mut self) -> Result<String, io::Error> {
        self.wait_and_ack_events()?;

        let mut core = self.session.core(0).unwrap();
        let digest_data = change_endianness(core.read_word_32(0x20000010).unwrap(), 4);
        Ok(format!("{:08X}", digest_data)[..7].to_string())
    }

    /// Programs a single firmware segment
    ///
    /// # Arguments
    /// * `segment` - Path to the segment file to program
    fn program_segment(&mut self, segment: &PathBuf) -> Result<(), io::Error> {
        let bufsz = if self.pipelined {
            IPC_PIPELINED_MAX_BUFFER_SIZE
        } else {
            IPC_MAX_BUFFER_SIZE
        };

        log::info!("Programming segment: {}", segment.display());

        // Reader for the hex file
        let hex = BinFile::from_file(segment).unwrap();

        // Cet chunks
        let chunks = hex.segments().chunks(Some(bufsz), None).unwrap();
        let chunks_len = chunks.len();

        // Create chunks
        for (i, (addr, data)) in chunks.into_iter().enumerate() {
            log::info!("Reading segment: {} with size {}", addr, data.len());

            if self.pipelined {
                if i == 0 {
                    self.write_chunk(&data, (i % 2) as u32);
                    self.commit_chunk(addr as u32, data.len(), (i % 2) as u32);
                    log::info!("Wrote chunk: {}:{} for bank {}", i, addr, i % 2);
                    continue;
                }

                self.write_chunk(&data, (i % 2) as u32);
                self.wait_and_ack_events()?;
                self.commit_chunk(addr as u32, data.len(), (i % 2) as u32);
                log::info!("Wrote chunk: {}:{} for bank {}", i, addr, i % 2);

                // If it's the last wait for ack
                if i == chunks_len - 1 {
                    self.wait_and_ack_events()?;
                }
            } else {
                self.write_chunk(&data, 0);
                self.commit_chunk(addr as u32, data.len(), 0);
                self.wait_and_ack_events()?;
            }
        }

        Ok(())
    }

    /// Writes a chunk of data to device RAM
    ///
    /// # Arguments
    /// * `data` - Data chunk to write
    /// * `bank` - Bank number for pipelined operations
    fn write_chunk(&mut self, data: &[u8], bank: u32) {
        let ram_address = if self.pipelined {
            0x2000001C + IPC_PIPELINED_MAX_BUFFER_SIZE * bank as usize
        } else {
            0x20000018
        };

        // Get the core
        let mut core = self.session.core(0).unwrap();

        // Write all the words
        let data_words = data.chunks(4).map(bytes_to_word).collect::<Vec<u32>>();

        log::info!(
            "Writing {} words to address {:08X}",
            data_words.len(),
            ram_address
        );

        core.write_32(ram_address as u64, &data_words).unwrap();
    }

    /// Commits a written chunk to flash memory
    ///
    /// # Arguments
    /// * `addr` - Target flash address
    /// * `data_len` - Length of data to commit
    /// * `bank` - Bank number for pipelined operations
    fn commit_chunk(&mut self, addr: u32, data_len: usize, bank: u32) {
        // Get the core
        let mut core = self.session.core(0).unwrap();

        let buffer_offset = bank * IPC_PIPELINED_MAX_BUFFER_SIZE as u32;
        core.write_word_32(0x20000010, addr).unwrap();
        core.write_word_32(0x20000014, data_len as u32).unwrap();
        if self.pipelined {
            core.write_word_32(0x20000018, buffer_offset).unwrap();
        }
        if self.pipelined {
            // command = PIPELINE_WRITE
            core.write_word_32(0x2000000C, 0x9).unwrap();
        } else {
            // command = WRITE
            core.write_word_32(0x2000000C, 0x3).unwrap();
        }
        // start IPC task
        core.write_word_32(0x4002A004, 1).unwrap();
    }

    /// Internal verification function
    fn _verify(&mut self) -> Result<bool, io::Error> {
        let mut ranges_to_verify = Vec::new();
        for s in self.segments.values() {
            // Reader for the hex file
            let hex = BinFile::from_file(s).unwrap();

            for s in hex.segments() {
                let (addr, data) = s.get_tuple();

                if addr < 0x1000000 {
                    log::info!("Verifying segment: {}", addr);
                    ranges_to_verify.push((addr, addr + data.len()));
                }
            }
        }

        {
            // Get the core
            let mut core = self.session.core(0).unwrap();

            // Write given start, size pairs and number of entries
            core.write_word_32(0x20000010, ranges_to_verify.len() as u32)
                .unwrap();
            for (i, range) in ranges_to_verify.iter().enumerate() {
                core.write_word_32(0x20000014 + (8 * i) as u64, range.0 as u32)
                    .unwrap();
                core.write_word_32(0x20000018 + (8 * i) as u64, (range.1 - range.0) as u32)
                    .unwrap();
            }

            // command = VERIFY
            core.write_word_32(0x2000000C, 0x7).unwrap();
            // start IPC task
            core.write_word_32(0x4002A004, 1).unwrap();
        }

        self.wait_and_ack_events()?;

        {
            // Get the core
            let mut core = self.session.core(0).unwrap();

            let response = core.read_word_32(0x2000000C).unwrap();
            if (response & 0xFF000000) == 0x5A000000 {
                panic!("Error while verifying: {:08X}", response & 0xFFFFFF);
            }

            // Generate array of addresses from 0x20000010 to 0x2000002D with step of 4
            let sequence = (0x20000010..0x2000002D).step_by(4_usize);
            let digest_data: Vec<u32> = sequence
                .map(|entry| core.read_word_32(entry).unwrap())
                .collect();

            // Generate string from digest data
            let digest_str = digest_data.iter().fold(String::new(), |mut acc, x| {
                acc.push_str(&format!("{:08X}", x));
                acc
            });

            // Compare digest strings
            let firmware_update_digest = self.firmware_update_digest.clone().unwrap();
            if digest_str != firmware_update_digest {
                log::info!(
                    "checksum mismatch: {} != {}",
                    digest_str,
                    firmware_update_digest
                );
            } else {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Waits for and acknowledges device events
    ///
    /// # Returns
    /// * `Ok(())` if events were received and acknowledged
    /// * `Err` if a timeout or error occurred
    fn wait_and_ack_events(&mut self) -> Result<(), io::Error> {
        // Loop until we get an ACK or NACK with timeout
        let start = Utc::now().timestamp_millis();

        // Get the core
        let mut core = self.session.core(0).unwrap();

        // Fault
        let mut fault = false;

        loop {
            // Check if we've timed out
            if Utc::now().timestamp_millis() - start > MASS_ERASE_TIMEOUT * 1000 {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Timeout waiting for ACK or NACK response",
                ));
            }

            // If fault is not 0, we have a fault
            if let Ok(response) = core.read_word_32(FAULT_EVENT) {
                if response != 0 {
                    fault = true;
                    break;
                }
            }

            if let Ok(response) = core.read_word_32(COMMAND_EVENT) {
                if response != 0 {
                    break;
                }
            }

            if let Ok(response) = core.read_word_32(DATA_EVENT) {
                if response != 0 {
                    break;
                }
            }
        }

        // Reset events
        core.write_word_32(FAULT_EVENT, 0).unwrap();
        core.write_word_32(COMMAND_EVENT, 0).unwrap();
        core.write_word_32(DATA_EVENT, 0).unwrap();

        let response = core.read_word_32(0x2000000C).unwrap();
        if (response & 0xFF000000) == 0xA5000000 {
            log::info!("ACK response, code {:08X}", response);
        } else if (response & 0xFF000000) == 0x5A000000 {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!("NACK response, code {:08X}", response),
            ));
        }

        if fault {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "modem triggered FAULT_EVENT",
            ));
        }

        Ok(())
    }

    /// Sets up the device for firmware operations
    ///
    /// Configures UICR settings, IPC, and RAM for firmware updates
    fn setup_device(&mut self) {
        let mut target = self.session.core(0).unwrap();

        // Init UICR.HFXOSR if necessary
        if target.read_word_32(0x00FF801C).unwrap() == 0xFFFFFFFF {
            log::info!("UICR.HFXOSR is not set, setting it to 0x0E");
            target.write_32(0x00FF801C, &[0x0000000E]).unwrap();
        }

        // Init UICR.HFXOCNT if necessary
        if target.read_word_32(0x00FF8020).unwrap() == 0xFFFFFFFF {
            log::info!("UICR.HFXOCNT is not set, setting it to 0x20");
            target.write_word_32(0x00FF8020, 0x00000020).unwrap();
        }

        // Reset and halt
        target.reset_and_halt(Duration::from_secs(30)).unwrap();

        // Configure IPC
        target.write_word_32(0x500038A8, 0x00000002).unwrap();

        // Configure IPC HW for DFU
        target.write_word_32(0x4002A514, 0x00000002).unwrap();
        target.write_word_32(0x4002A51C, 0x00000008).unwrap();
        target.write_word_32(0x4002A610, 0x21000000).unwrap();
        target.write_word_32(0x4002A614, 0x00000000).unwrap();
        target.write_word_32(0x4002A590, 0x00000001).unwrap();
        target.write_word_32(0x4002A598, 0x00000004).unwrap();
        target.write_word_32(0x4002A5A0, 0x00000010).unwrap();

        // Configure RAM as non-secure
        for n in 0..32 {
            target
                .write_word_32(0x50003700 + (n * 4), 0x00000007)
                .unwrap();
        }

        // Allocate memory in RAM
        target.write_word_32(0x20000000, 0x80010000).unwrap();
        target.write_word_32(0x20000004, 0x2100000C).unwrap();
        target.write_word_32(0x20000008, 0x0003FC00).unwrap();

        // Reset the modem
        target.write_word_32(0x50005610, 0).unwrap();
        target.write_word_32(0x50005614, 1).unwrap();
        target.write_word_32(0x50005610, 1).unwrap();
        target.write_word_32(0x50005614, 0).unwrap();
        target.write_word_32(0x50005610, 0).unwrap();
    }

    /// Processes the firmware zip file and extracts necessary components
    ///
    /// # Arguments
    /// * `mfw_zip` - Path to the firmware zip file
    /// * `temp_dir` - Temporary directory for extracted files
    fn process_zip_file(&mut self, mfw_zip: &str, temp_dir: &TempDir) -> Result<(), io::Error> {
        // Unzip to temp dir
        let file = File::open(mfw_zip).unwrap();
        ZipArchive::new(file)
            .unwrap()
            .extract(temp_dir.path())
            .unwrap();

        // Path for loader
        let mut modem_firmware_loader = None;

        // Get digest
        let digest_id = self.read_key_digest()?;

        // Iterate each file
        for entry in std::fs::read_dir(temp_dir).unwrap() {
            let file = entry.unwrap();
            let file_name = file.file_name().into_string().unwrap();
            log::debug!("Processing file: {}", file_name);

            // Process files
            if file_name.starts_with(format!("{}.ipc_dfu.signed_", digest_id).as_str()) {
                modem_firmware_loader = Some(temp_dir.path().join(&file_name));

                // Use regex to get the version
                // m = re.match(r"\.ipc_dfu\.signed_(\d+)\.(\d+)\.(\d+)\.ihex", f[7:])
                let m = Regex::new(r"\.ipc_dfu\.signed_(\d+)\.(\d+)\.(\d+)\.ihex").unwrap();

                // Create a tuple from the match
                let (major, minor, patch) = match m.captures(&file_name) {
                    Some(c) => (
                        c.get(1).unwrap().as_str().parse::<u32>().unwrap(),
                        c.get(2).unwrap().as_str().parse::<u32>().unwrap(),
                        c.get(3).unwrap().as_str().parse::<u32>().unwrap(),
                    ),
                    None => {
                        log::error!("Unable to parse file name: {}", file_name);
                        continue;
                    }
                };

                log::info!(
                    "modem_firmware_loader version: {}.{}.{}",
                    major,
                    minor,
                    patch
                );

                // If > (1,1,2) then we use the pipelined loader
                if (major > 1)
                    || (major == 1 && minor > 1)
                    || (major == 1 && minor == 1 && patch > 2)
                {
                    log::info!("Using pipelined loader");
                    self.pipelined = true;
                }
            }
        }

        // Overwrite with the one we found
        let modem_firmware_loader = match modem_firmware_loader {
            Some(v) => v,
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Unable to find modem firmware loader",
                ))
            }
        };

        for entry in std::fs::read_dir(temp_dir).unwrap() {
            let file = entry.unwrap();
            let file_name = file.file_name().into_string().unwrap();

            // Do regex for this
            // m = re.match(r"firmware\.update\.image\.segments\.(\d+).hex", f)

            let m = Regex::new(r"firmware\.update\.image\.segments\.(\d+).hex").unwrap();
            if let Some(c) = m.captures(&file_name) {
                let segment = c.get(1).unwrap().as_str();

                log::info!("Inserting segment: {}:{}", segment, file_name);

                // Parse string regex into segments
                self.segments
                    .insert(segment.to_string(), temp_dir.path().join(file_name));
            }
        }

        // Check if segments are empty
        if self.segments.is_empty() {
            return Err(io::Error::new(io::ErrorKind::Other, "No segments found!"));
        }

        log::debug!(
            "Opening {}",
            temp_dir
                .path()
                .join("firmware.update.image.digest.txt")
                .display()
        );

        // Parse segment digests
        if let Ok(f) = std::fs::File::open(temp_dir.path().join("firmware.update.image.digest.txt"))
        {
            log::info!("Parsing segment digests");

            let mut reader = std::io::BufReader::new(f);
            let mut line = String::new();

            while let Ok(_sz) = reader.read_line(&mut line) {
                if line.contains("SHA256 of all ranges in ascending address order:") {
                    let m =
                        Regex::new(r"SHA256 of all ranges in ascending address order:\s*(\w{64})")
                            .unwrap();
                    if let Some(c) = m.captures(&line) {
                        log::info!("Firmware digest: {}", c.get(1).unwrap().as_str());
                        self.firmware_update_digest = Some(c.get(1).unwrap().as_str().to_string());
                        break;
                    }
                }
            }

            if self.firmware_update_digest.is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "No firmware digest found!",
                ));
            }
        }

        log::info!(
            "Programming modem firmware loader: {}",
            modem_firmware_loader.display()
        );

        // Program the modem_firmware_loader hex
        flashing::download_file(self.session, modem_firmware_loader, flashing::Format::Hex)
            .unwrap();

        {
            // Start IPC task
            let mut core = self.session.core(0).unwrap();
            core.write_word_32(0x4002A004, 0x00000001).unwrap();
        }

        // Wait for event
        self.wait_and_ack_events()?;

        log::info!("modem_firmware_loader started!");

        Ok(())
    }
}
