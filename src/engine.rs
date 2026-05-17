//! Engine.

// TODO: separate Plover HID protocol

use std::sync::mpsc;

use crate::protocol::plover_hid;

pub struct Engine {
    mode: plover_hid::ChordMode,
    rx: Option<mpsc::Receiver<plover_hid::HidEvent>>,
}

impl Engine {
    pub fn new() -> Self {
        Self {
            mode: plover_hid::ChordMode::FirstUp,
            rx: None,
        }
    }

    /// Try to open and attach to a Plover HID device. Note that it does not refresh the device
    /// list of the HID API. Be sure to refresh it if needed.
    pub fn connect(&mut self, api: &hidapi::HidApi) -> bool {
        if let Some(device) = plover_hid::open_device(api) {
            match device {
                Ok(device) => {
                    self.rx = Some(plover_hid::spawn_hid_thread(device, self.mode));
                    true
                }
                Err(err) => {
                    log::info!("failed to open device: {err}");
                    false
                }
            }
        } else {
            false
        }
    }

    /// Try to open and attach to a Plover HID device, until it succeeds.
    pub fn connect_loop(&mut self, api: &mut hidapi::HidApi) {
        loop {
            if let Err(e) = api.refresh_devices() {
                log::warn!("failed to refresh HID devices: {e}");
            }
            if self.connect(api) {
                return;
            }
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    }
}
