import Lean4EVM.Primitives.UInt
import Mathlib.Tactic.Ring

/-!
# Fixed-width integer regression tests

Executable boundary checks and proof-API examples for `U64`, `U128`, and `U256`.
-/

open Lean4EVM

section EvmBoundaryTests

example : ((7 : U256) / 0).toNat = 0 := by decide
example : ((7 : U256) % 0).toNat = 0 := by decide
example : (U256.sdiv (U256.ofInt (-7)) 2).toInt = -3 := by decide
example : (U256.smod (U256.ofInt (-7)) 2).toInt = -1 := by decide
example : U256.addmod U256.max 1 U256.max = (1 : U256) := by decide
example : U256.mulmod (U256.ofNat (2 ^ 255)) 2 U256.max = (1 : U256) := by decide
example : U256.exp 0 0 = (1 : U256) := by decide
example : U256.exp 3 5 = (243 : U256) := by decide
set_option maxRecDepth 10000 in
example : U256.exp 2 (U256.ofNat (2 ^ 255)) = (0 : U256) := by decide
example : U256.ult (U256.ofInt (-1)) 0 = false := by decide
example : U256.slt (U256.ofInt (-1)) 0 = true := by decide
example : U256.isZero 0 = true := by decide
example : U256.toBool 1 = true := by decide
example : U256.byteAt 0 (U256.ofNat (0xab * 2 ^ (31 * 8))) = (0xab : U256) := by
  decide
example : U256.byteAt 31 0x1234 = (0x34 : U256) := by decide
example : U256.byteAt 32 U256.max = (0 : U256) := by decide
example : U256.signExtend 0 0x80 = U256.ofInt (-128) := by decide
example : U256.signExtend 32 0x80 = (0x80 : U256) := by decide
example : U256.shl 256 1 = (0 : U256) := by decide
example : U256.shr 256 U256.max = (0 : U256) := by decide
example : U256.sar 256 (U256.ofInt (-1)) = U256.max := by decide

end EvmBoundaryTests

section FixedWidthTests

example : U64.ofNat? (2 ^ 64) = none := by decide
example : U128.ofNat? (2 ^ 128 - 1) = some U128.max := by decide
example : FixedUInt.overflowingAdd U64.max 1 = ((0 : U64), true) := by decide
example : FixedUInt.checkedAdd U128.max 1 = none := by decide
example : FixedUInt.saturatingSub (0 : U64) 1 = 0 := by decide
example : U128.wideningMul U128.max U128.max =
    U256.ofNat ((2 ^ 128 - 1) * (2 ^ 128 - 1)) := by decide
example : U256.fromU128s (U256.highU128 U256.max) (U256.lowU128 U256.max) = U256.max := by
  exact U256.fromU128s_highU128_lowU128 _

end FixedWidthTests

/-! ## Arithmetic examples -/

section ArithmeticExamples

/-- Ordinary arithmetic wraps at the width boundary. -/
example : U64.max + 1 = 0 := by decide

/-- Checked arithmetic reports overflow instead of wrapping. -/
example : FixedUInt.checkedMul U128.max 2 = none := by decide

/-- Saturating arithmetic clamps overflow to the maximum value. -/
example : FixedUInt.saturatingAdd U64.max 1 = U64.max := by decide

/-- Natural casts are explicit modulo conversions. -/
example : (((U256.modulus + 7 : ℕ) : U256)).toNat = 7 := by
  simp [U256.modulus, FixedUInt.modulus]

/-- Width conversions are explicit and checked when narrowing. -/
example : (42 : U64).toU256.toU64? = some (42 : U64) := by decide

/-- An arbitrarily large EVM shift is handled without constructing a huge natural shift. -/
example : U256.shl U256.max 1 = 0 := by decide

end ArithmeticExamples

/-! ## Proof examples -/

section ProofExamples

/-- Ring normalization works directly on fixed-width arithmetic. -/
example (a b : U256) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- The inherited unsigned order supports the standard order library. -/
example (a b : U128) : a ≤ b ∨ b ≤ a :=
  le_total a b

/-- Concrete numeric literals normalize through `simp`. -/
example : (5 : U256).toNat = 5 := by
  simp

/-- The `EXP` specification uses the same canonical modulus form as casts. -/
example : (U256.exp 3 5).toNat = 243 := by
  simp

/-- Boolean equality and propositional equality use the same decision procedure. -/
example (a b : U256) : (a == b) = decide (a = b) :=
  rfl

/-- The EVM oversized-shift rule is available as a reusable theorem. -/
example (shift value : U256) (h : 256 ≤ shift.toNat) : U256.shl shift value = 0 :=
  U256.shl_of_ge_256 shift value h

/-- Widening followed by checked narrowing is a proved round trip. -/
example (value : U64) : value.toU128.toU64? = some value :=
  U128.toU64?_toU128 value

end ProofExamples
