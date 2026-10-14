// `std::net` overlay (docs/ARCH.md section 3.1; W-STD-C phase 2):
// the address types. `TcpStream`, `TcpListener`, `UdpSocket`, and
// the rest of the module stay with W-SHIM (system io); `std::net::X`
// walks into this module only for the names it defines
// (`STD_MODULES` in src/stdmods.rs).
//
// Lust std source with the stable, observable behavior of
// rust-lang/rust 1.99 `std/src/net` (`addr.rs`, `ip_addr.rs`,
// `parser.rs`): values, `Display` text (with padding, through
// `Formatter::pad` as std's buffer form does), parse accepts and
// rejects, and the `AddrParseError` texts. The unstable `ip`
// predicates (`is_global`, `is_reserved`, and kin) are not here.

use core::str::FromStr;

/// Pushes the decimal text of `v` on `out`.
fn push_dec(out: &mut String, v: u32) {
    if v >= 10 {
        push_dec(out, v / 10);
    }
    out.push((b'0' + (v % 10) as u8) as char);
}

/// Pushes the lowercase hex text of `v`, no leading zeros.
fn push_hex(out: &mut String, v: u16) {
    if v >= 16 {
        push_hex(out, v / 16);
    }
    let d = (v % 16) as u8;
    out.push(if d < 10 { (b'0' + d) as char } else { (b'a' + d - 10) as char });
}

/// An IPv4 address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ipv4Addr {
    octets: [u8; 4],
}

/// An IPv6 address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ipv6Addr {
    octets: [u8; 16],
}

/// An IP address, either IPv4 or IPv6.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IpAddr {
    V4(Ipv4Addr),
    V6(Ipv6Addr),
}

/// A socket address: an IPv4 address and a port.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SocketAddrV4 {
    ip: Ipv4Addr,
    port: u16,
}

/// A socket address: an IPv6 address, a port, flow info, and a
/// scope id.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SocketAddrV6 {
    ip: Ipv6Addr,
    port: u16,
    flowinfo: u32,
    scope_id: u32,
}

/// A socket address, either IPv4 or IPv6.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SocketAddr {
    V4(SocketAddrV4),
    V6(SocketAddrV6),
}

// The parse error kinds, in one byte: std's private
// `AddrParseErrorKind`. The numbers only name the texts below.
const ERR_IP: u8 = 0;
const ERR_IPV4: u8 = 1;
const ERR_IPV6: u8 = 2;
const ERR_SOCKET: u8 = 3;
const ERR_SOCKET_V4: u8 = 4;
const ERR_SOCKET_V6: u8 = 5;

/// The error of parsing an IP or socket address.
#[derive(Clone, PartialEq, Eq)]
pub struct AddrParseError {
    kind: u8,
}

impl AddrParseError {
    fn text(&self) -> &'static str {
        match self.kind {
            ERR_IPV4 => "invalid IPv4 address syntax",
            ERR_IPV6 => "invalid IPv6 address syntax",
            ERR_SOCKET_V4 => "invalid IPv4 socket address syntax",
            ERR_SOCKET_V6 => "invalid IPv6 socket address syntax",
            ERR_SOCKET => "invalid socket address syntax",
            _ => "invalid IP address syntax",
        }
    }

    fn kind_name(&self) -> &'static str {
        match self.kind {
            ERR_IPV4 => "Ipv4",
            ERR_IPV6 => "Ipv6",
            ERR_SOCKET_V4 => "SocketV4",
            ERR_SOCKET_V6 => "SocketV6",
            ERR_SOCKET => "Socket",
            _ => "Ip",
        }
    }
}

impl core::fmt::Display for AddrParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.text())
    }
}

impl core::fmt::Debug for AddrParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "AddrParseError({})", self.kind_name())
    }
}

impl core::error::Error for AddrParseError {}

impl Ipv4Addr {
    pub const fn new(a: u8, b: u8, c: u8, d: u8) -> Ipv4Addr {
        Ipv4Addr { octets: [a, b, c, d] }
    }

    pub const LOCALHOST: Ipv4Addr = Ipv4Addr::new(127, 0, 0, 1);
    pub const UNSPECIFIED: Ipv4Addr = Ipv4Addr::new(0, 0, 0, 0);
    pub const BROADCAST: Ipv4Addr = Ipv4Addr::new(255, 255, 255, 255);

    pub const fn octets(&self) -> [u8; 4] {
        self.octets
    }

    pub const fn from_bits(bits: u32) -> Ipv4Addr {
        Ipv4Addr { octets: [(bits >> 24) as u8, (bits >> 16) as u8, (bits >> 8) as u8, bits as u8] }
    }

    pub const fn to_bits(self) -> u32 {
        ((self.octets[0] as u32) << 24) | ((self.octets[1] as u32) << 16) | ((self.octets[2] as u32) << 8) | self.octets[3] as u32
    }

    pub const fn is_unspecified(&self) -> bool {
        self.octets[0] == 0 && self.octets[1] == 0 && self.octets[2] == 0 && self.octets[3] == 0
    }

    pub const fn is_loopback(&self) -> bool {
        self.octets[0] == 127
    }

    pub const fn is_private(&self) -> bool {
        self.octets[0] == 10 || (self.octets[0] == 172 && self.octets[1] >= 16 && self.octets[1] < 32) || (self.octets[0] == 192 && self.octets[1] == 168)
    }

    pub const fn is_link_local(&self) -> bool {
        self.octets[0] == 169 && self.octets[1] == 254
    }

    pub const fn is_multicast(&self) -> bool {
        self.octets[0] >= 224 && self.octets[0] < 240
    }

    pub const fn is_broadcast(&self) -> bool {
        self.octets[0] == 255 && self.octets[1] == 255 && self.octets[2] == 255 && self.octets[3] == 255
    }

    pub const fn is_documentation(&self) -> bool {
        (self.octets[0] == 192 && self.octets[1] == 0 && self.octets[2] == 2)
            || (self.octets[0] == 198 && self.octets[1] == 51 && self.octets[2] == 100)
            || (self.octets[0] == 203 && self.octets[1] == 0 && self.octets[2] == 113)
    }

    pub const fn to_ipv6_compatible(&self) -> Ipv6Addr {
        let o = self.octets;
        Ipv6Addr { octets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o[0], o[1], o[2], o[3]] }
    }

    pub const fn to_ipv6_mapped(&self) -> Ipv6Addr {
        let o = self.octets;
        Ipv6Addr { octets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, o[0], o[1], o[2], o[3]] }
    }

    /// The `Display` text.
    fn text(&self) -> String {
        let mut s = String::new();
        push_dec(&mut s, self.octets[0] as u32);
        s.push('.');
        push_dec(&mut s, self.octets[1] as u32);
        s.push('.');
        push_dec(&mut s, self.octets[2] as u32);
        s.push('.');
        push_dec(&mut s, self.octets[3] as u32);
        s
    }
}

impl Ipv6Addr {
    pub const fn new(a: u16, b: u16, c: u16, d: u16, e: u16, f: u16, g: u16, h: u16) -> Ipv6Addr {
        Ipv6Addr {
            octets: [
                (a >> 8) as u8, a as u8, (b >> 8) as u8, b as u8, (c >> 8) as u8, c as u8, (d >> 8) as u8, d as u8,
                (e >> 8) as u8, e as u8, (f >> 8) as u8, f as u8, (g >> 8) as u8, g as u8, (h >> 8) as u8, h as u8,
            ],
        }
    }

    pub const LOCALHOST: Ipv6Addr = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1);
    pub const UNSPECIFIED: Ipv6Addr = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);

    pub const fn segments(&self) -> [u16; 8] {
        let o = self.octets;
        [
            ((o[0] as u16) << 8) | o[1] as u16,
            ((o[2] as u16) << 8) | o[3] as u16,
            ((o[4] as u16) << 8) | o[5] as u16,
            ((o[6] as u16) << 8) | o[7] as u16,
            ((o[8] as u16) << 8) | o[9] as u16,
            ((o[10] as u16) << 8) | o[11] as u16,
            ((o[12] as u16) << 8) | o[13] as u16,
            ((o[14] as u16) << 8) | o[15] as u16,
        ]
    }

    pub const fn octets(&self) -> [u8; 16] {
        self.octets
    }

    pub const fn from_bits(bits: u128) -> Ipv6Addr {
        Ipv6Addr {
            octets: [
                (bits >> 120) as u8, (bits >> 112) as u8, (bits >> 104) as u8, (bits >> 96) as u8,
                (bits >> 88) as u8, (bits >> 80) as u8, (bits >> 72) as u8, (bits >> 64) as u8,
                (bits >> 56) as u8, (bits >> 48) as u8, (bits >> 40) as u8, (bits >> 32) as u8,
                (bits >> 24) as u8, (bits >> 16) as u8, (bits >> 8) as u8, bits as u8,
            ],
        }
    }

    pub const fn to_bits(self) -> u128 {
        let o = self.octets;
        ((o[0] as u128) << 120) | ((o[1] as u128) << 112) | ((o[2] as u128) << 104) | ((o[3] as u128) << 96)
            | ((o[4] as u128) << 88) | ((o[5] as u128) << 80) | ((o[6] as u128) << 72) | ((o[7] as u128) << 64)
            | ((o[8] as u128) << 56) | ((o[9] as u128) << 48) | ((o[10] as u128) << 40) | ((o[11] as u128) << 32)
            | ((o[12] as u128) << 24) | ((o[13] as u128) << 16) | ((o[14] as u128) << 8) | o[15] as u128
    }

    pub const fn is_unspecified(&self) -> bool {
        let s = self.segments();
        s[0] == 0 && s[1] == 0 && s[2] == 0 && s[3] == 0 && s[4] == 0 && s[5] == 0 && s[6] == 0 && s[7] == 0
    }

    pub const fn is_loopback(&self) -> bool {
        let s = self.segments();
        s[0] == 0 && s[1] == 0 && s[2] == 0 && s[3] == 0 && s[4] == 0 && s[5] == 0 && s[6] == 0 && s[7] == 1
    }

    pub const fn is_multicast(&self) -> bool {
        self.segments()[0] & 0xff00 == 0xff00
    }

    /// The IPv4 address of an IPv4-mapped address (`::ffff:a.b.c.d`).
    pub const fn to_ipv4_mapped(&self) -> Option<Ipv4Addr> {
        let s = self.segments();
        if s[0] == 0 && s[1] == 0 && s[2] == 0 && s[3] == 0 && s[4] == 0 && s[5] == 0xffff {
            Some(Ipv4Addr { octets: [self.octets[12], self.octets[13], self.octets[14], self.octets[15]] })
        } else {
            None
        }
    }

    /// The IPv4 address of an IPv4-compatible or IPv4-mapped
    /// address.
    pub const fn to_ipv4(&self) -> Option<Ipv4Addr> {
        let s = self.segments();
        if s[0] == 0 && s[1] == 0 && s[2] == 0 && s[3] == 0 && s[4] == 0 && (s[5] == 0 || s[5] == 0xffff) {
            Some(Ipv4Addr { octets: [self.octets[12], self.octets[13], self.octets[14], self.octets[15]] })
        } else {
            None
        }
    }

    /// The `Display` text: std's form. An IPv4-mapped address
    /// prints its last 32 bits as IPv4; otherwise the longest run
    /// of two or more zero segments (the first, on a tie) becomes
    /// `::`.
    fn text(&self) -> String {
        let seg = self.segments();
        if let Some(v4) = self.to_ipv4_mapped() {
            let mut s = String::new();
            s.push_str("::ffff:");
            s.push_str(&v4.text());
            return s;
        }
        // The best zero run: (start, len), len at least 2.
        let mut best_start = 8usize;
        let mut best_len = 1usize;
        let mut cur_start = 8usize;
        let mut cur_len = 0usize;
        let mut i = 0;
        while i < 8 {
            if seg[i] == 0 {
                if cur_len == 0 {
                    cur_start = i;
                }
                cur_len += 1;
                if cur_len > best_len {
                    best_start = cur_start;
                    best_len = cur_len;
                }
            } else {
                cur_len = 0;
                cur_start = 8;
            }
            i += 1;
        }
        let mut s = String::new();
        let mut i = 0;
        let mut need_colon = false;
        while i < 8 {
            if i == best_start {
                if need_colon {
                    s.push(':');
                }
                s.push(':');
                need_colon = false;
                i += best_len;
                if i >= 8 {
                    break;
                }
                continue;
            }
            if need_colon {
                s.push(':');
            }
            push_hex(&mut s, seg[i]);
            need_colon = true;
            i += 1;
        }
        s
    }
}

impl IpAddr {
    pub const fn is_ipv4(&self) -> bool {
        match self {
            IpAddr::V4(_) => true,
            IpAddr::V6(_) => false,
        }
    }

    pub const fn is_ipv6(&self) -> bool {
        match self {
            IpAddr::V4(_) => false,
            IpAddr::V6(_) => true,
        }
    }

    pub const fn is_unspecified(&self) -> bool {
        match self {
            IpAddr::V4(a) => a.is_unspecified(),
            IpAddr::V6(a) => a.is_unspecified(),
        }
    }

    pub const fn is_loopback(&self) -> bool {
        match self {
            IpAddr::V4(a) => a.is_loopback(),
            IpAddr::V6(a) => a.is_loopback(),
        }
    }

    pub const fn is_multicast(&self) -> bool {
        match self {
            IpAddr::V4(a) => a.is_multicast(),
            IpAddr::V6(a) => a.is_multicast(),
        }
    }

    fn text(&self) -> String {
        match self {
            IpAddr::V4(a) => a.text(),
            IpAddr::V6(a) => a.text(),
        }
    }
}

impl SocketAddrV4 {
    pub const fn new(ip: Ipv4Addr, port: u16) -> SocketAddrV4 {
        SocketAddrV4 { ip, port }
    }

    pub const fn ip(&self) -> &Ipv4Addr {
        &self.ip
    }

    pub fn set_ip(&mut self, new_ip: Ipv4Addr) {
        self.ip = new_ip;
    }

    pub const fn port(&self) -> u16 {
        self.port
    }

    pub fn set_port(&mut self, new_port: u16) {
        self.port = new_port;
    }

    fn text(&self) -> String {
        let mut s = self.ip.text();
        s.push(':');
        push_dec(&mut s, self.port as u32);
        s
    }
}

impl SocketAddrV6 {
    pub const fn new(ip: Ipv6Addr, port: u16, flowinfo: u32, scope_id: u32) -> SocketAddrV6 {
        SocketAddrV6 { ip, port, flowinfo, scope_id }
    }

    pub const fn ip(&self) -> &Ipv6Addr {
        &self.ip
    }

    pub fn set_ip(&mut self, new_ip: Ipv6Addr) {
        self.ip = new_ip;
    }

    pub const fn port(&self) -> u16 {
        self.port
    }

    pub fn set_port(&mut self, new_port: u16) {
        self.port = new_port;
    }

    pub const fn flowinfo(&self) -> u32 {
        self.flowinfo
    }

    pub fn set_flowinfo(&mut self, new_flowinfo: u32) {
        self.flowinfo = new_flowinfo;
    }

    pub const fn scope_id(&self) -> u32 {
        self.scope_id
    }

    pub fn set_scope_id(&mut self, new_scope_id: u32) {
        self.scope_id = new_scope_id;
    }

    fn text(&self) -> String {
        let mut s = String::new();
        s.push('[');
        s.push_str(&self.ip.text());
        if self.scope_id != 0 {
            s.push('%');
            push_dec(&mut s, self.scope_id);
        }
        s.push_str("]:");
        push_dec(&mut s, self.port as u32);
        s
    }
}

impl SocketAddr {
    pub const fn ip(&self) -> IpAddr {
        match self {
            SocketAddr::V4(a) => IpAddr::V4(*a.ip()),
            SocketAddr::V6(a) => IpAddr::V6(*a.ip()),
        }
    }

    pub fn set_ip(&mut self, new_ip: IpAddr) {
        match (self, new_ip) {
            (SocketAddr::V4(a), IpAddr::V4(ip)) => a.set_ip(ip),
            (SocketAddr::V6(a), IpAddr::V6(ip)) => a.set_ip(ip),
            (me, IpAddr::V4(ip)) => *me = SocketAddr::V4(SocketAddrV4::new(ip, me.port())),
            (me, IpAddr::V6(ip)) => {
                let port = me.port();
                *me = SocketAddr::V6(SocketAddrV6::new(ip, port, 0, 0));
            }
        }
    }

    pub const fn port(&self) -> u16 {
        match self {
            SocketAddr::V4(a) => a.port(),
            SocketAddr::V6(a) => a.port(),
        }
    }

    pub fn set_port(&mut self, new_port: u16) {
        match self {
            SocketAddr::V4(a) => a.set_port(new_port),
            SocketAddr::V6(a) => a.set_port(new_port),
        }
    }

    pub const fn is_ipv4(&self) -> bool {
        match self {
            SocketAddr::V4(_) => true,
            SocketAddr::V6(_) => false,
        }
    }

    pub const fn is_ipv6(&self) -> bool {
        match self {
            SocketAddr::V4(_) => false,
            SocketAddr::V6(_) => true,
        }
    }

    fn text(&self) -> String {
        match self {
            SocketAddr::V4(a) => a.text(),
            SocketAddr::V6(a) => a.text(),
        }
    }
}

// `Display` and `Debug` print the same text, with the formatter's
// padding, as std's do.

impl core::fmt::Display for Ipv4Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Debug for Ipv4Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Display for Ipv6Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Debug for Ipv6Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Display for IpAddr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Debug for IpAddr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Display for SocketAddrV4 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Debug for SocketAddrV4 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Display for SocketAddrV6 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Debug for SocketAddrV6 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Display for SocketAddr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl core::fmt::Debug for SocketAddr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad(&self.text())
    }
}

impl From<[u8; 4]> for Ipv4Addr {
    fn from(octets: [u8; 4]) -> Ipv4Addr {
        Ipv4Addr { octets }
    }
}

impl From<[u8; 4]> for IpAddr {
    fn from(octets: [u8; 4]) -> IpAddr {
        IpAddr::V4(Ipv4Addr { octets })
    }
}

impl From<[u16; 8]> for Ipv6Addr {
    fn from(seg: [u16; 8]) -> Ipv6Addr {
        Ipv6Addr::new(seg[0], seg[1], seg[2], seg[3], seg[4], seg[5], seg[6], seg[7])
    }
}

impl From<[u16; 8]> for IpAddr {
    fn from(seg: [u16; 8]) -> IpAddr {
        IpAddr::V6(Ipv6Addr::from(seg))
    }
}

impl From<[u8; 16]> for Ipv6Addr {
    fn from(octets: [u8; 16]) -> Ipv6Addr {
        Ipv6Addr { octets }
    }
}

impl From<[u8; 16]> for IpAddr {
    fn from(octets: [u8; 16]) -> IpAddr {
        IpAddr::V6(Ipv6Addr { octets })
    }
}

impl From<Ipv4Addr> for IpAddr {
    fn from(a: Ipv4Addr) -> IpAddr {
        IpAddr::V4(a)
    }
}

impl From<Ipv6Addr> for IpAddr {
    fn from(a: Ipv6Addr) -> IpAddr {
        IpAddr::V6(a)
    }
}

impl From<u32> for Ipv4Addr {
    fn from(bits: u32) -> Ipv4Addr {
        Ipv4Addr::from_bits(bits)
    }
}

impl From<u128> for Ipv6Addr {
    fn from(bits: u128) -> Ipv6Addr {
        Ipv6Addr::from_bits(bits)
    }
}

impl From<SocketAddrV4> for SocketAddr {
    fn from(a: SocketAddrV4) -> SocketAddr {
        SocketAddr::V4(a)
    }
}

impl From<SocketAddrV6> for SocketAddr {
    fn from(a: SocketAddrV6) -> SocketAddr {
        SocketAddr::V6(a)
    }
}

impl From<(Ipv4Addr, u16)> for SocketAddrV4 {
    fn from(pair: (Ipv4Addr, u16)) -> SocketAddrV4 {
        SocketAddrV4::new(pair.0, pair.1)
    }
}

impl From<(Ipv6Addr, u16)> for SocketAddrV6 {
    fn from(pair: (Ipv6Addr, u16)) -> SocketAddrV6 {
        SocketAddrV6::new(pair.0, pair.1, 0, 0)
    }
}

impl From<(Ipv4Addr, u16)> for SocketAddr {
    fn from(pair: (Ipv4Addr, u16)) -> SocketAddr {
        SocketAddr::V4(SocketAddrV4::new(pair.0, pair.1))
    }
}

impl From<(Ipv6Addr, u16)> for SocketAddr {
    fn from(pair: (Ipv6Addr, u16)) -> SocketAddr {
        SocketAddr::V6(SocketAddrV6::new(pair.0, pair.1, 0, 0))
    }
}

impl From<(IpAddr, u16)> for SocketAddr {
    fn from(pair: (IpAddr, u16)) -> SocketAddr {
        match pair.0 {
            IpAddr::V4(a) => SocketAddr::V4(SocketAddrV4::new(a, pair.1)),
            IpAddr::V6(a) => SocketAddr::V6(SocketAddrV6::new(a, pair.1, 0, 0)),
        }
    }
}

// Parsing, with std's accepts and rejects (std/src/net/parser.rs).
// A byte walk; every error is the one kind of its caller. The
// bytes of the input come from the `sys_str_as_bytes` intrinsic,
// as the platform crate reads them (`str::as_bytes` is not a
// method of the subset yet).

/// The bytes of `s`.
fn bytes_of(s: &str) -> &[u8] {
    core::intrinsics::sys_str_as_bytes(s)
}

/// One IPv4 number at `b[*i..]`: digits, no empty run, no leading
/// zero on more than one digit, at most 255.
fn read_v4_part(b: &[u8], i: &mut usize) -> Option<u8> {
    let start = *i;
    let mut value: u32 = 0;
    let mut digits = 0usize;
    while *i < b.len() && b[*i] >= b'0' && b[*i] <= b'9' {
        value = value * 10 + (b[*i] - b'0') as u32;
        if value > 255 {
            return None;
        }
        digits += 1;
        *i += 1;
    }
    if digits == 0 || (digits > 1 && b[start] == b'0') {
        return None;
    }
    Some(value as u8)
}

/// An IPv4 address from all of `b`.
fn parse_v4(b: &[u8]) -> Option<Ipv4Addr> {
    let mut i = 0usize;
    let a = read_v4_part(b, &mut i)?;
    if i >= b.len() || b[i] != b'.' {
        return None;
    }
    i += 1;
    let c = read_v4_part(b, &mut i)?;
    if i >= b.len() || b[i] != b'.' {
        return None;
    }
    i += 1;
    let d = read_v4_part(b, &mut i)?;
    if i >= b.len() || b[i] != b'.' {
        return None;
    }
    i += 1;
    let e = read_v4_part(b, &mut i)?;
    if i != b.len() {
        return None;
    }
    Some(Ipv4Addr::new(a, c, d, e))
}

/// The value of one hex digit.
fn hex_val(c: u8) -> Option<u16> {
    if c >= b'0' && c <= b'9' {
        Some((c - b'0') as u16)
    } else if c >= b'a' && c <= b'f' {
        Some((c - b'a') as u16 + 10)
    } else if c >= b'A' && c <= b'F' {
        Some((c - b'A') as u16 + 10)
    } else {
        None
    }
}

/// The groups of one side of an IPv6 text: `b` is the whole side
/// with no `::`. An IPv4 tail is allowed only as the last group and
/// only when `tail_ok`; it counts as two groups. Writes the groups
/// into `out` from index 0 and returns their count.
fn read_v6_side(b: &[u8], tail_ok: bool, out: &mut [u16; 8]) -> Option<usize> {
    if b.is_empty() {
        return Some(0);
    }
    let mut n = 0usize;
    let mut i = 0usize;
    loop {
        // One group: read to the next ':' or the end.
        let mut j = i;
        let mut has_dot = false;
        while j < b.len() && b[j] != b':' {
            if b[j] == b'.' {
                has_dot = true;
            }
            j += 1;
        }
        if has_dot {
            if !tail_ok || j != b.len() || n + 1 >= 8 {
                return None;
            }
            let v4 = parse_v4(&b[i..j])?;
            let o = v4.octets;
            out[n] = ((o[0] as u16) << 8) | o[1] as u16;
            out[n + 1] = ((o[2] as u16) << 8) | o[3] as u16;
            return Some(n + 2);
        }
        if j == i || j - i > 4 || n >= 8 {
            return None;
        }
        let mut value: u16 = 0;
        let mut k = i;
        while k < j {
            value = (value << 4) | hex_val(b[k])?;
            k += 1;
        }
        out[n] = value;
        n += 1;
        if j == b.len() {
            return Some(n);
        }
        i = j + 1;
        if i >= b.len() {
            return None;
        }
    }
}

/// An IPv6 address from all of `b`.
fn parse_v6(b: &[u8]) -> Option<Ipv6Addr> {
    // The `::` position, if any; a second one is an error.
    let mut ellipsis: Option<usize> = None;
    let mut i = 0usize;
    while i + 1 < b.len() {
        if b[i] == b':' && b[i + 1] == b':' {
            if ellipsis.is_some() {
                return None;
            }
            ellipsis = Some(i);
            i += 2;
        } else {
            i += 1;
        }
    }
    let mut seg = [0u16; 8];
    match ellipsis {
        None => {
            if read_v6_side(b, true, &mut seg)? != 8 {
                return None;
            }
        }
        Some(at) => {
            let left = read_v6_side(&b[..at], false, &mut seg)?;
            let mut rseg = [0u16; 8];
            let right = read_v6_side(&b[at + 2..], true, &mut rseg)?;
            if left + right > 7 {
                return None;
            }
            let mut k = 0usize;
            while k < right {
                seg[8 - right + k] = rseg[k];
                k += 1;
            }
        }
    }
    Some(Ipv6Addr::new(seg[0], seg[1], seg[2], seg[3], seg[4], seg[5], seg[6], seg[7]))
}

/// A port from all of `b`: digits, at most 65535.
fn parse_port(b: &[u8]) -> Option<u16> {
    if b.is_empty() {
        return None;
    }
    let mut value: u32 = 0;
    let mut i = 0usize;
    while i < b.len() {
        if b[i] < b'0' || b[i] > b'9' {
            return None;
        }
        value = value * 10 + (b[i] - b'0') as u32;
        if value > 65535 {
            return None;
        }
        i += 1;
    }
    Some(value as u16)
}

/// A scope id from all of `b`: digits that fit a `u32`.
fn parse_scope(b: &[u8]) -> Option<u32> {
    if b.is_empty() {
        return None;
    }
    let mut value: u64 = 0;
    let mut i = 0usize;
    while i < b.len() {
        if b[i] < b'0' || b[i] > b'9' {
            return None;
        }
        value = value * 10 + (b[i] - b'0') as u64;
        if value > 4294967295 {
            return None;
        }
        i += 1;
    }
    Some(value as u32)
}

/// A v4 socket address from all of `b`.
fn parse_sa4(b: &[u8]) -> Option<SocketAddrV4> {
    let mut colon: Option<usize> = None;
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b':' {
            if colon.is_some() {
                return None;
            }
            colon = Some(i);
        }
        i += 1;
    }
    let at = colon?;
    let ip = parse_v4(&b[..at])?;
    let port = parse_port(&b[at + 1..])?;
    Some(SocketAddrV4::new(ip, port))
}

/// A v6 socket address from all of `b`: `[` ip (`%` scope)? `]`
/// `:` port.
fn parse_sa6(b: &[u8]) -> Option<SocketAddrV6> {
    if b.is_empty() || b[0] != b'[' {
        return None;
    }
    let mut close: Option<usize> = None;
    let mut i = 1usize;
    while i < b.len() {
        if b[i] == b']' {
            close = Some(i);
            break;
        }
        i += 1;
    }
    let close = close?;
    if close + 1 >= b.len() || b[close + 1] != b':' {
        return None;
    }
    let inner = &b[1..close];
    let mut pct: Option<usize> = None;
    let mut j = 0usize;
    while j < inner.len() {
        if inner[j] == b'%' {
            if pct.is_some() {
                return None;
            }
            pct = Some(j);
        }
        j += 1;
    }
    let (ip, scope) = match pct {
        Some(p) => (parse_v6(&inner[..p])?, parse_scope(&inner[p + 1..])?),
        None => (parse_v6(inner)?, 0),
    };
    let port = parse_port(&b[close + 2..])?;
    Some(SocketAddrV6::new(ip, port, 0, scope))
}

impl FromStr for Ipv4Addr {
    type Err = AddrParseError;
    fn from_str(s: &str) -> Result<Ipv4Addr, AddrParseError> {
        match parse_v4(bytes_of(s)) {
            Some(a) => Ok(a),
            None => Err(AddrParseError { kind: ERR_IPV4 }),
        }
    }
}

impl FromStr for Ipv6Addr {
    type Err = AddrParseError;
    fn from_str(s: &str) -> Result<Ipv6Addr, AddrParseError> {
        match parse_v6(bytes_of(s)) {
            Some(a) => Ok(a),
            None => Err(AddrParseError { kind: ERR_IPV6 }),
        }
    }
}

impl FromStr for IpAddr {
    type Err = AddrParseError;
    fn from_str(s: &str) -> Result<IpAddr, AddrParseError> {
        if let Some(a) = parse_v4(bytes_of(s)) {
            return Ok(IpAddr::V4(a));
        }
        match parse_v6(bytes_of(s)) {
            Some(a) => Ok(IpAddr::V6(a)),
            None => Err(AddrParseError { kind: ERR_IP }),
        }
    }
}

impl FromStr for SocketAddrV4 {
    type Err = AddrParseError;
    fn from_str(s: &str) -> Result<SocketAddrV4, AddrParseError> {
        match parse_sa4(bytes_of(s)) {
            Some(a) => Ok(a),
            None => Err(AddrParseError { kind: ERR_SOCKET_V4 }),
        }
    }
}

impl FromStr for SocketAddrV6 {
    type Err = AddrParseError;
    fn from_str(s: &str) -> Result<SocketAddrV6, AddrParseError> {
        match parse_sa6(bytes_of(s)) {
            Some(a) => Ok(a),
            None => Err(AddrParseError { kind: ERR_SOCKET_V6 }),
        }
    }
}

impl FromStr for SocketAddr {
    type Err = AddrParseError;
    fn from_str(s: &str) -> Result<SocketAddr, AddrParseError> {
        if let Some(a) = parse_sa4(bytes_of(s)) {
            return Ok(SocketAddr::V4(a));
        }
        match parse_sa6(bytes_of(s)) {
            Some(a) => Ok(SocketAddr::V6(a)),
            None => Err(AddrParseError { kind: ERR_SOCKET }),
        }
    }
}



