# s2r

A toy but my first compiler, implemented in Rust, which convert SysY programming language to RISC-V assembly based on Koopa IR.

## Progress

- Expression - ✅
- Constants and variables - ✅
- Block and scope - ✅
- if/else - ✅
- while/for - ✅
- Function and global variables - ✅
- Arrays - ✅
- Optimization - ✅
  - SSA:
    - SCCP
  - DCE
  - Peekhole Assembly Optimization:
    - Identical Move
    - Redundant Load

## Unimplemented features

Keep track of the things I'm interested in, but have no time to start or finish.

I'm less interested in these topic because I have a more specific target to work on.
But I'll do it if I have spare time for this.:

- Add syntax highlight
- Add custom LSP support
