//! A stenography engine in Rust.

use qlover::engine::Engine;

fn main() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    let mut hid = hidapi::HidApi::new().unwrap_or_else(|e| panic!("unable to initialize HID: {e}"));
    let mut engine = Engine::new();

    loop {
        println!("connecting to a new device..");
        engine.connect_loop(&mut hid);
        println!("..connected!");

        // TODO: handle input
        break;
    }
}
