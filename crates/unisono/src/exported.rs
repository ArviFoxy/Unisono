// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The program's metrics, and the address that serves them in the
//! Prometheus text format.

use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener};
use std::sync::Arc;
use std::time::Duration;

use unisono_metrics::{Counter, FloatGauge, RegistrationError, Registry};

/// A counter that is given totals counted elsewhere and adds what each
/// total has grown by.
pub(crate) struct Tally {
    counter: Counter,
    last: u64,
}

impl Tally {
    /// Takes in that `total` is counted now.
    pub(crate) fn update(&mut self, total: u64) {
        if total > self.last {
            self.counter.add(total - self.last);
            self.last = total;
        }
    }
}

/// The metrics of the program, as they are registered.
pub(crate) struct Metrics {
    registry: Registry,
}

impl Metrics {
    pub(crate) fn new() -> Metrics {
        Metrics {
            registry: Registry::new(),
        }
    }

    /// A counter of its own family.
    pub(crate) fn tally(&mut self, name: &str, help: &str) -> Result<Tally, RegistrationError> {
        let family = self.registry.counter_family(name, help, &[])?;
        Ok(Tally {
            counter: self.registry.counter(family, &[])?,
            last: 0,
        })
    }

    /// A gauge of its own family.
    pub(crate) fn gauge(
        &mut self,
        name: &str,
        help: &str,
    ) -> Result<FloatGauge, RegistrationError> {
        let family = self.registry.float_gauge_family(name, help, &[])?;
        self.registry.float_gauge(family, &[])
    }

    /// Serves the metrics at `address`, on a thread of its own, to every
    /// request that comes, whatever it asks for.
    pub(crate) fn serve(self, address: SocketAddr) -> io::Result<()> {
        let listener = TcpListener::bind(address)?;
        let registry = Arc::new(self.registry);
        std::thread::Builder::new()
            .name("unisono-metrics".into())
            .spawn(move || {
                for stream in listener.incoming() {
                    // A client that goes wrong is that client's business.
                    let _ = stream.and_then(|mut stream| answer(&registry, &mut stream));
                }
            })?;
        Ok(())
    }
}

/// Reads a request and answers it with the metrics.
fn answer(registry: &Registry, stream: &mut std::net::TcpStream) -> io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(2)))?;
    let mut request = [0u8; 4_096];
    let mut read = 0;
    while read < request.len() {
        let count = stream.read(&mut request[read..])?;
        if count == 0 {
            break;
        }
        read += count;
        if request[..read].windows(4).any(|end| end == b"\r\n\r\n") {
            break;
        }
    }
    let mut body = Vec::new();
    registry.write_text_io(&mut body)?;
    write!(
        stream,
        "HTTP/1.1 200 OK\r\nContent-Type: text/plain; version=0.0.4\r\n\
         Content-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    )?;
    stream.write_all(&body)
}
