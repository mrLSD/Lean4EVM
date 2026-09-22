import Lean4EVM.Primitives.Literals

/-!
# Primitive literal regression tests

Definitional equalities check every spelling against the existing constructors. Negative tests
check elaboration diagnostics, nominal isolation, and the explicit scope's BitVec boundary.
-/

open Lean4EVM

-- Importing the module alone preserves Lean's native value#width notation.
example : 64#10 = BitVec.ofNat 10 64 := rfl

section
open scoped Lean4EVM.Literals

example :
    [U64#65_535,
     65_535U64,
     u64"65_535",
     65_535₆₄,
     64#65_535] =
    List.replicate 5 (U64.ofNat 65535) := rfl

example :
    [U64#0xFf_fF,
     0xFf_fFU64,
     u64"0xFf_fF",
     0xFf_fF₆₄,
     64#0xFf_fF] =
    List.replicate 5 (U64.ofNat 65535) := rfl

example :
    [U64#0XfF_Ff,
     0XfF_FfU64,
     u64"0XfF_Ff",
     0XfF_Ff₆₄,
     64#0XfF_Ff] =
    List.replicate 5 (U64.ofNat 65535) := rfl

example :
    [U64#0b1111_1111_1111_1111,
     0b1111_1111_1111_1111U64,
     u64"0b1111_1111_1111_1111",
     0b1111_1111_1111_1111₆₄,
     64#0b1111_1111_1111_1111] =
    List.replicate 5 (U64.ofNat 65535) := rfl

example :
    [U64#0B1111_1111_1111_1111,
     0B1111_1111_1111_1111U64,
     u64"0B1111_1111_1111_1111",
     0B1111_1111_1111_1111₆₄,
     64#0B1111_1111_1111_1111] =
    List.replicate 5 (U64.ofNat 65535) := rfl

example : u64"0" = U64.ofNat 0 := rfl
example : u64"18446744073709551615" = U64.ofNat 18446744073709551615 := rfl

/-- error: primitive literal out of range: value must be smaller than 2^64 -/
#guard_msgs in
#check u64"18446744073709551616"

example :
    [U128#65_535,
     65_535U128,
     u128"65_535",
     65_535₁₂₈,
     128#65_535] =
    List.replicate 5 (U128.ofNat 65535) := rfl

example :
    [U128#0xFf_fF,
     0xFf_fFU128,
     u128"0xFf_fF",
     0xFf_fF₁₂₈,
     128#0xFf_fF] =
    List.replicate 5 (U128.ofNat 65535) := rfl

example :
    [U128#0XfF_Ff,
     0XfF_FfU128,
     u128"0XfF_Ff",
     0XfF_Ff₁₂₈,
     128#0XfF_Ff] =
    List.replicate 5 (U128.ofNat 65535) := rfl

example :
    [U128#0b1111_1111_1111_1111,
     0b1111_1111_1111_1111U128,
     u128"0b1111_1111_1111_1111",
     0b1111_1111_1111_1111₁₂₈,
     128#0b1111_1111_1111_1111] =
    List.replicate 5 (U128.ofNat 65535) := rfl

example :
    [U128#0B1111_1111_1111_1111,
     0B1111_1111_1111_1111U128,
     u128"0B1111_1111_1111_1111",
     0B1111_1111_1111_1111₁₂₈,
     128#0B1111_1111_1111_1111] =
    List.replicate 5 (U128.ofNat 65535) := rfl

example : u128"0" = U128.ofNat 0 := rfl
example : u128"340282366920938463463374607431768211455" =
    U128.ofNat 340282366920938463463374607431768211455 := rfl

/-- error: primitive literal out of range: value must be smaller than 2^128 -/
#guard_msgs in
#check u128"340282366920938463463374607431768211456"

example :
    [U256#65_535,
     65_535U256,
     u256"65_535",
     65_535₂₅₆,
     256#65_535] =
    List.replicate 5 (U256.ofNat 65535) := rfl

example :
    [U256#0xFf_fF,
     0xFf_fFU256,
     u256"0xFf_fF",
     0xFf_fF₂₅₆,
     256#0xFf_fF] =
    List.replicate 5 (U256.ofNat 65535) := rfl

example :
    [U256#0XfF_Ff,
     0XfF_FfU256,
     u256"0XfF_Ff",
     0XfF_Ff₂₅₆,
     256#0XfF_Ff] =
    List.replicate 5 (U256.ofNat 65535) := rfl

example :
    [U256#0b1111_1111_1111_1111,
     0b1111_1111_1111_1111U256,
     u256"0b1111_1111_1111_1111",
     0b1111_1111_1111_1111₂₅₆,
     256#0b1111_1111_1111_1111] =
    List.replicate 5 (U256.ofNat 65535) := rfl

example :
    [U256#0B1111_1111_1111_1111,
     0B1111_1111_1111_1111U256,
     u256"0B1111_1111_1111_1111",
     0B1111_1111_1111_1111₂₅₆,
     256#0B1111_1111_1111_1111] =
    List.replicate 5 (U256.ofNat 65535) := rfl

example : u256"0" = U256.ofNat 0 := rfl
example : u256"115792089237316195423570985008687907853269984665640564039457584007913129639935" =
    U256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 := rfl

/-- error: primitive literal out of range: value must be smaller than 2^256 -/
#guard_msgs in
#check u256"115792089237316195423570985008687907853269984665640564039457584007913129639936"

example :
    [H160#65_535,
     65_535H160,
     65_535ₕ₁₆₀,
     h160"65_535"] =
    List.replicate 4 (H160.ofNat 65535) := rfl

example :
    [H160#0xFf_fF,
     0xFf_fFH160,
     0xFf_fFₕ₁₆₀,
     h160"0xFf_fF"] =
    List.replicate 4 (H160.ofNat 65535) := rfl

example :
    [H160#0XfF_Ff,
     0XfF_FfH160,
     0XfF_Ffₕ₁₆₀,
     h160"0XfF_Ff"] =
    List.replicate 4 (H160.ofNat 65535) := rfl

example :
    [H160#0b1111_1111_1111_1111,
     0b1111_1111_1111_1111H160,
     0b1111_1111_1111_1111ₕ₁₆₀,
     h160"0b1111_1111_1111_1111"] =
    List.replicate 4 (H160.ofNat 65535) := rfl

example :
    [H160#0B1111_1111_1111_1111,
     0B1111_1111_1111_1111H160,
     0B1111_1111_1111_1111ₕ₁₆₀,
     h160"0B1111_1111_1111_1111"] =
    List.replicate 4 (H160.ofNat 65535) := rfl

example : h160"0" = H160.ofNat 0 := rfl
example : h160"1461501637330902918203684832716283019655932542975" =
    H160.ofNat 1461501637330902918203684832716283019655932542975 := rfl

/-- error: primitive literal out of range: value must be smaller than 2^160 -/
#guard_msgs in
#check h160"1461501637330902918203684832716283019655932542976"

example :
    [H256#65_535,
     65_535H256,
     65_535ₕ₂₅₆,
     h256"65_535"] =
    List.replicate 4 (H256.ofNat 65535) := rfl

example :
    [H256#0xFf_fF,
     0xFf_fFH256,
     0xFf_fFₕ₂₅₆,
     h256"0xFf_fF"] =
    List.replicate 4 (H256.ofNat 65535) := rfl

example :
    [H256#0XfF_Ff,
     0XfF_FfH256,
     0XfF_Ffₕ₂₅₆,
     h256"0XfF_Ff"] =
    List.replicate 4 (H256.ofNat 65535) := rfl

example :
    [H256#0b1111_1111_1111_1111,
     0b1111_1111_1111_1111H256,
     0b1111_1111_1111_1111ₕ₂₅₆,
     h256"0b1111_1111_1111_1111"] =
    List.replicate 4 (H256.ofNat 65535) := rfl

example :
    [H256#0B1111_1111_1111_1111,
     0B1111_1111_1111_1111H256,
     0B1111_1111_1111_1111ₕ₂₅₆,
     h256"0B1111_1111_1111_1111"] =
    List.replicate 4 (H256.ofNat 65535) := rfl

example : h256"0" = H256.ofNat 0 := rfl
example : h256"115792089237316195423570985008687907853269984665640564039457584007913129639935" =
    H256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 := rfl

/-- error: primitive literal out of range: value must be smaller than 2^256 -/
#guard_msgs in
#check h256"115792089237316195423570985008687907853269984665640564039457584007913129639936"

-- Separators follow Lean exactly, including repeated underscores and octal notation.
example : u64"1__234" = 1_234₆₄ := rfl
example : u64"0o17" = 15₆₄ := rfl
example : (10₆₄ + 20₆₄).toNat = 30 := by decide
example : h160"0x1234".getByte 18 = 0x12 := by decide
example : h160"0x1234".getByte 19 = 0x34 := by decide
example : h256"0x1234".getByte 0 = 0 := by decide

/-- error: primitive literal out of range: value must be smaller than 2^64 -/
#guard_msgs in
#check 18446744073709551616₆₄

/-- error: primitive literal out of range: value must be smaller than 2^64 -/
#guard_msgs in
#check 64#18446744073709551616

/-- error: primitive literal out of range: value must be smaller than 2^160 -/
#guard_msgs in
#check H160#0x10000000000000000000000000000000000000000

/-- error: unsupported primitive literal type '32'; expected U64, U128, U256, H160 or H256 -/
#guard_msgs in
#check 32#10

/-- error: invalid numeral; expected decimal, hexadecimal (0x) or binary (0b) digits -/
#guard_msgs in
#check u64"0b102"

/-- error: invalid numeral; expected decimal, hexadecimal (0x) or binary (0b) digits -/
#guard_msgs in
#check h160"0x"

/-- error: invalid numeral; expected decimal, hexadecimal (0x) or binary (0b) digits -/
#guard_msgs in
#check h256"0xFF_"

/-- error: expected a quoted natural-number literal without whitespace -/
#guard_msgs in
#check u128"-1"

/-- error: expected a quoted natural-number literal without whitespace -/
#guard_msgs in
#check u64"1 2"

/-- error: expected a quoted natural-number literal without whitespace -/
#guard_msgs in
#check u64""

/-- error: Type mismatch
  U64.ofNat 10
has type
  U64
but is expected to have type
  U128 -/
#guard_msgs in
example : U128 := 10₆₄

/-- error: Type mismatch
  H160.ofNat 10
has type
  H160
but is expected to have type
  H256 -/
#guard_msgs in
example : H256 := h160"10"

-- ASCII suffixes do not reserve the nominal type names as keywords.
example : U64 → U64 := id
example : U128 → U128 := id
example : U256 → U256 := id
example : H160 → H160 := id
example : H256 → H256 := id
example : 10U64 + 20U64 = 30₆₄ := rfl
example : (0x10H160).toNat = 16 := rfl
example : 0x10ₕ₁₆₀ = 0b10000H160 := rfl
example : 0x10ₕ₂₅₆ = h256"16" := rfl

/-- error: primitive literal out of range: value must be smaller than 2^64 -/
#guard_msgs in
#check 0x10000000000000000U64

/-- error: primitive literal out of range: value must be smaller than 2^160 -/
#guard_msgs in
#check 0x10000000000000000000000000000000000000000ₕ₁₆₀

/-- error: primitive literal out of range: value must be smaller than 2^256 -/
#guard_msgs in
#check 0x10000000000000000000000000000000000000000000000000000000000000000H256

-- Removed suffix spellings cannot be parsed as primitive suffixes.
run_cmd do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `primitiveSuffix "U64" with
  | .ok _ => pure ()
  | .error error => throwError "suffix parser unavailable: {error}"
  for suffix in ["\\H160", "\\H256", "\\U64", "\\_U64", "_U64", "_U128", "_U256",
      "_H160", "_H256"] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `primitiveSuffix suffix with
    | .error _ => pure ()
    | .ok _ => throwError "removed suffix still accepted: {suffix}"

end

-- Closing the scope restores the original meaning.
example : 64#10 = BitVec.ofNat 10 64 := rfl
