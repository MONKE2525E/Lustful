# Adapter: smallvec (planned)

Target upstream version: 1.15.1 (docs/ARCH.md section 3.6). Keeps the
real `SmallVec<A: Array>` shape with inline storage and spill to the
Vec core. No intrinsics. Skeleton only in S5.
