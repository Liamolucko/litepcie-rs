use std::io::{Read, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

use litepcie::dma::{Dma, DmaRegisters};
use litepcie::{LitePcie, SocInfo};
use pci_driver::backends::vfio::VfioPciDevice;
use rand::rngs::StdRng;
use rand::{RngCore, SeedableRng};

fn main() -> anyhow::Result<()> {
    let soc_info: SocInfo = serde_json::from_str(include_str!(
        "/home/liam/src/net_finder/fpga/build/csr.json"
    ))?;
    let device = VfioPciDevice::open("/sys/bus/pci/devices/0000:05:00.0")?;
    let litepcie = LitePcie::new(&soc_info, &device, "pcie")?;
    let dma = Dma::new(&litepcie, "dma0", 8192, true)?;

    let rng = StdRng::from_entropy();
    let tx_count = AtomicUsize::new(0);
    let rx_count = AtomicUsize::new(0);
    thread::scope(|s| {
        let rng = &rng;
        let tx_count = &tx_count;
        let rx_count = &rx_count;

        s.spawn(move || {
            let mut tx = dma.tx.unwrap();
            let mut rng = rng.clone();
            let mut random = [0; 8192];
            loop {
                rng.fill_bytes(&mut random);
                tx.write_all(&random).unwrap();
                tx_count.fetch_add(1, Ordering::Relaxed);
            }
        });

        s.spawn(move || {
            let mut rx = dma.rx.unwrap();
            let mut rng = rng.clone();
            let mut random = [0; 8192];
            let mut read = [0; 8192];
            loop {
                rng.fill_bytes(&mut random);
                rx.read_exact(&mut read).unwrap();
                assert_eq!(read.as_slice(), random.as_slice());
                rx_count.fetch_add(1, Ordering::Relaxed);
            }
        });

        let mut last_tx_count = tx_count.load(Ordering::Relaxed);
        loop {
            let print_interval = Duration::from_millis(200);
            thread::sleep(print_interval);

            // Load `rx_count` first so that if stuff happens between these loads, it'll
            // still be the smaller one.
            let rx_count = rx_count.load(Ordering::Relaxed);
            let tx_count = tx_count.load(Ordering::Relaxed);

            // Calculate the number of bits we've transmitted since we last printed.
            let transmitted = (tx_count - last_tx_count) * 8192 * 8;
            // Then divide it by how long it's been since then.
            let speed_bps = transmitted as f64 / print_interval.as_secs_f64();
            let speed_gbps = speed_bps / 1_000_000_000.0;

            dbg!(litepcie.get_csr_group::<DmaRegisters<'_>>("dma0"));

            println!("tx_count: {tx_count}, rx_count: {rx_count}, speed: {speed_gbps} Gbps");
            assert!(rx_count <= tx_count);

            last_tx_count = tx_count;
        }
    });

    Ok(())
}
