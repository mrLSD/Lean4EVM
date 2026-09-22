# Checked primitive literals

```lean
import Lean4EVM
open Lean4EVM
open scoped Lean4EVM.Literals

#check 10₆₄                  -- U64
#check 0xFF_ff₁₂₈            -- U128
#check 0b1010₂₅₆             -- U256
#check 10ₕ₁₆₀                -- H160
#check 0xAB_cdₕ₂₅₆           -- H256
#check 10U64
#check 0x10U128
#check 0b10U256
#check 0x10H160
#check 1_234H256
#check 64#1_234              -- U64: width#value
#check U256#0xAB_cd          -- explicit type#value
#check H160#0x10
#check h256"0xFFFF_ffff"
#check u64"0b1010_0011"
```

The suffixes `₆₄`, `₁₂₈`, `₂₅₆` and width prefixes `64#`, `128#`, `256#` select
unsigned integers. The subscript suffixes `ₕ₁₆₀` and `ₕ₂₅₆` select hash types.
Unicode has no capital subscript H: `ₕ` is the subscript small letter h, with the
whole type marker written below the baseline.

Every type (`U64`, `U128`, `U256`, `H160`, `H256`) supports `numberType`,
`Type#number`, and lowercase quoted forms (`u64"..."`, `u128"..."`, `u256"..."`,
`h160"..."`, `h256"..."`). ASCII type names remain ordinary identifiers, so the
notation does not reserve `U64`, `H160`, etc. as keywords. Backslash and underscore
type suffixes are not supported.

The same numeral grammar applies to every form: decimal, hexadecimal (`0x`/`0X`),
binary (`0b`/`0B`), and Lean's octal (`0o`/`0O`), with mixed-case hexadecimal digits
and Lean-style underscore separators. Quoted payloads contain only the numeral,
without signs, whitespace, comments, or expressions.

All forms reject values outside `0 ≤ n < 2^width` during elaboration. Use the
existing `Type.ofNat n` explicitly when modulo reduction is intended. Hash literals
are unsigned numeric values, padded to 20 or 32 bytes and serialized big-endian;
they do not parse Ethereum address checksums. Expansion uses the existing nominal
constructors, with no implicit conversions and no runtime string parsing.

Inside this scope, `64#10` means `U64.ofNat 10`. Lean normally interprets it as
`BitVec.ofNat 10 64`. Use `BitVec.ofNat` explicitly when mixing these APIs, or
restrict `open scoped Lean4EVM.Literals` to a `section`.

The notation is also available through the dedicated import
`Lean4EVM.Primitives.Literals`.
