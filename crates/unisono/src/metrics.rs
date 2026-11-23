// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Prometheus metrics definitions and HTTP text-format exporter for `unisono`.

use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use unisono_metrics::{CONTENT_TYPE, Counter, FloatGauge, RegistrationError, Registry};

/// Maximum total time spent reading one HTTP request header.
const REQUEST_TIMEOUT: Duration = Duration::from_secs(2);

/// Maximum time allowed for writing the HTTP response.
const WRITE_TIMEOUT: Duration = Duration::from_secs(2);

/// Poll interval for checking the shutdown flag while waiting for connections.
const ACCEPT_POLL: Duration = Duration::from_millis(10);

/// A counter that is given totals counted elsewhere and adds what each
/// total has grown by.
pub(crate) struct Tally {
    counter: Counter,
    last: u64,
}

impl Tally {
    /// Another handle to the counter, which counts the same.
    pub(crate) fn handle(&self) -> Counter {
        self.counter.clone()
    }

    /// Takes in that `total` is counted now.
    pub(crate) fn update(&mut self, total: u64) {
        if total > self.last {
            self.counter.add(total - self.last);
            self.last = total;
        }
    }
}

/// A running HTTP server for Prometheus metrics; dropping it stops the thread
/// and closes the listening socket.
pub(crate) struct Server {
    #[cfg_attr(not(test), allow(dead_code))]
    address: SocketAddr,
    stop: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
}

impl Server {
    #[cfg(test)]
    pub(crate) fn address(&self) -> SocketAddr {
        self.address
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
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
    pub(crate) fn serve(self, address: SocketAddr) -> io::Result<Server> {
        self.serve_with_timeout(address, REQUEST_TIMEOUT)
    }

    fn serve_with_timeout(
        self,
        address: SocketAddr,
        request_timeout: Duration,
    ) -> io::Result<Server> {
        let listener = TcpListener::bind(address)?;
        let bound = listener.local_addr()?;
        listener.set_nonblocking(true)?;
        let registry = Arc::new(self.registry);
        let stop = Arc::new(AtomicBool::new(false));
        let stopping = Arc::clone(&stop);
        let thread = std::thread::Builder::new()
            .name("unisono-metrics".into())
            .stack_size(crate::STACK)
            .spawn(move || {
                while !stopping.load(Ordering::Acquire) {
                    match listener.accept() {
                        Ok((mut stream, _)) => {
                            // A client that goes wrong is that client's business.
                            let _ = answer(&registry, &mut stream, request_timeout);
                        }
                        Err(error)
                            if matches!(
                                error.kind(),
                                io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                            ) =>
                        {
                            std::thread::sleep(ACCEPT_POLL);
                        }
                        Err(_) => {
                            std::thread::sleep(ACCEPT_POLL);
                        }
                    }
                }
            })?;
        Ok(Server {
            address: bound,
            stop,
            thread: Some(thread),
        })
    }
}

/// Reads a request within a total `request_timeout` deadline and answers it
/// with the metrics.
fn answer(
    registry: &Registry,
    stream: &mut TcpStream,
    request_timeout: Duration,
) -> io::Result<()> {
    stream.set_nonblocking(false)?;
    stream.set_write_timeout(Some(WRITE_TIMEOUT))?;
    let deadline = Instant::now() + request_timeout;
    let mut request = [0u8; 4_096];
    let mut read = 0;
    while read < request.len() {
        let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
            return Err(io::Error::from(io::ErrorKind::TimedOut));
        };
        if remaining.is_zero() {
            return Err(io::Error::from(io::ErrorKind::TimedOut));
        }
        stream.set_read_timeout(Some(remaining))?;
        match stream.read(&mut request[read..]) {
            Ok(0) => break,
            Ok(count) => {
                read += count;
                if request[..read].windows(4).any(|end| end == b"\r\n\r\n") {
                    break;
                }
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    // Immediate EOF without a request (e.g., a TCP liveness probe): nothing to
    // write.
    if read == 0 {
        return Ok(());
    }
    let mut body = Vec::new();
    registry.write_text_io(&mut body)?;
    let header = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: {CONTENT_TYPE}\r\n\
         Content-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    write_all_retry(stream, header.as_bytes())?;
    write_all_retry(stream, &body)
}

/// Writes `bytes` completely, retrying `EINTR`.
fn write_all_retry(stream: &mut TcpStream, mut bytes: &[u8]) -> io::Result<()> {
    while !bytes.is_empty() {
        match stream.write(bytes) {
            Ok(0) => return Err(io::Error::from(io::ErrorKind::WriteZero)),
            Ok(written) => bytes = &bytes[written..],
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::{Read, Write};
    use std::net::{SocketAddr, TcpListener, TcpStream};
    use std::time::Duration;

    use unisono_metrics::CONTENT_TYPE;

    use super::Metrics;

    fn scrape(address: SocketAddr) -> String {
        let mut stream = TcpStream::connect(address).expect("connect");
        stream
            .set_read_timeout(Some(Duration::from_secs(2)))
            .expect("read timeout");
        stream
            .write_all(b"GET /metrics HTTP/1.1\r\nHost: localhost\r\n\r\n")
            .expect("write");
        let mut response = String::new();
        stream.read_to_string(&mut response).expect("read");
        response
    }

    #[test]
    fn serves_metrics_with_content_type_and_closes_port_on_drop() {
        let mut metrics = Metrics::new();
        let mut packets = metrics
            .tally("test_packets_total", "Test packets.")
            .expect("tally");
        packets.update(42);
        let server = metrics
            .serve("127.0.0.1:0".parse().expect("addr"))
            .expect("serve");
        let address = server.address();

        // Immediate EOF connection does not break subsequent scrapes.
        let probe = TcpStream::connect(address).expect("probe");
        drop(probe);

        let response = scrape(address);
        assert!(response.starts_with("HTTP/1.1 200 OK\r\n"), "{response}");
        assert!(
            response.contains(&format!("Content-Type: {CONTENT_TYPE}\r\n")),
            "{response}"
        );
        assert!(response.contains("test_packets_total 42\n"), "{response}");

        // Dropping the server stops the thread and releases the port.
        drop(server);
        let rebound = TcpListener::bind(address).expect("rebind after server drop");
        drop(rebound);
    }

    #[test]
    fn slow_client_hits_total_deadline_without_stalling_server() {
        let mut metrics = Metrics::new();
        let mut counter = metrics
            .tally("test_after_slow_total", "After slow client.")
            .expect("tally");
        counter.update(7);
        let server = metrics
            .serve_with_timeout(
                "127.0.0.1:0".parse().expect("addr"),
                Duration::from_millis(150),
            )
            .expect("serve");
        let address = server.address();

        // Trickle one byte every 60 ms without finishing headers: without a
        // total deadline this would reset a per-read timeout indefinitely.
        let mut slow = TcpStream::connect(address).expect("slow connect");
        for _ in 0..4 {
            let _ = slow.write_all(b"G");
            std::thread::sleep(Duration::from_millis(60));
        }

        // The server timed out the slow client and answers a healthy scrape.
        let response = scrape(address);
        assert!(
            response.contains("test_after_slow_total 7\n"),
            "server should recover after slow client timeout: {response}"
        );
    }
}
