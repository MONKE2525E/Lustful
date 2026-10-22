// Declaration-only admission matrix; runtime ABI peers live in src/native.rs.
// Unused imports must not require a native definition at link time.
mod native {
    pub type SignedByte = i8;
    pub type UnsignedByte = u8;
    pub type Count = usize;
    unsafe extern "C" {
        pub fn ptr_i8_const(a: *const SignedByte, b: *mut SignedByte) -> *const SignedByte;
        pub fn ptr_i8_mut(a: *const SignedByte, b: *mut SignedByte) -> *mut SignedByte;
        pub fn ptr_u8_const(a: *const UnsignedByte, b: *mut UnsignedByte) -> *const UnsignedByte;
        pub fn ptr_u8_mut(a: *const UnsignedByte, b: *mut UnsignedByte) -> *mut UnsignedByte;
        pub fn ptr_i32_const(a: *const i32, b: *mut i32) -> *const i32;
        pub fn ptr_i32_mut(a: *const i32, b: *mut i32) -> *mut i32;
        pub fn ptr_u32_const(a: *const u32, b: *mut u32) -> *const u32;
        pub fn ptr_u32_mut(a: *const u32, b: *mut u32) -> *mut u32;
        pub fn ptr_i64_const(a: *const i64, b: *mut i64) -> *const i64;
        pub fn ptr_i64_mut(a: *const i64, b: *mut i64) -> *mut i64;
        pub fn ptr_u64_const(a: *const u64, b: *mut u64) -> *const u64;
        pub fn ptr_u64_mut(a: *const u64, b: *mut u64) -> *mut u64;
        pub fn ptr_isize_const(a: *const isize, b: *mut isize) -> *const isize;
        pub fn ptr_isize_mut(a: *const isize, b: *mut isize) -> *mut isize;
        pub fn ptr_usize_const(a: *const Count, b: *mut Count) -> *const Count;
        pub fn ptr_usize_mut(a: *const Count, b: *mut Count) -> *mut Count;
    }
}
fn main() { println!("primitive pointer declarations: ok"); }
