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
example : U64.max.overflowingAdd 1 = ((0 : U64), true) := by decide
example : U128.max.checkedAdd 1 = none := by decide
example : (0 : U64).saturatingSub 1 = 0 := by decide
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
example : U128.max.checkedMul 2 = none := by decide

/-- Saturating arithmetic clamps overflow to the maximum value. -/
example : U64.max.saturatingAdd 1 = U64.max := by decide

/-- Natural casts are explicit modulo conversions. -/
example : (((U256.modulus + 7 : ℕ) : U256)).toNat = 7 := by
  simp

/-- Width conversions are explicit and checked when narrowing. -/
example : (42 : U64).toU256.toU64? = some (42 : U64) := by decide

/-- An arbitrarily large EVM shift is handled without constructing a huge natural shift. -/
example : U256.shl U256.max 1 = 0 := by decide

end ArithmeticExamples

/-! ## U256 arithmetic and overflow policies

Every operator on `U256` wraps at the word boundary, which is the EVM rule. The checked,
overflowing and saturating variants are reached from the value itself, so a caller outside the EVM
word, such as gas accounting, states its policy explicitly at the call site.
-/

section U256Arithmetic

/-! ### The operators on results that fit in a word -/

example : (7 : U256) + 3 = 10 := by decide
example : (7 : U256) - 3 = 4 := by decide
example : (7 : U256) * 3 = 21 := by decide
example : (7 : U256) / 3 = 2 := by decide

/-! ### Wrapping, the default policy: the exact result is taken modulo `2 ^ 256` -/

example : U256.max + 1 = 0 := by decide
example : (0 : U256) - 1 = U256.max := by decide
example : U256.max * 2 = U256.max - 1 := by decide

/-! ### Division never overflows; its only boundary is the EVM rule for a zero divisor -/

example : (7 : U256) / 0 = 0 := by decide
example : (7 : U256) % 0 = 0 := by decide

/-! ### Checked: the exact result, or `none` when it does not fit

The first case is written out step by step to show the shape of a call.
-/

example :
    let x : U256 := 2
    let y : U256 := U256.max
    x.checkedAdd y = none := by decide

example : (7 : U256).checkedAdd 3 = some 10 := by decide
example : (7 : U256).checkedSub 3 = some 4 := by decide
example : (7 : U256).checkedMul 3 = some 21 := by decide
example : (7 : U256).checkedDiv 3 = some 2 := by decide

example : U256.max.checkedAdd 1 = none := by decide
example : (0 : U256).checkedSub 1 = none := by decide
example : U256.max.checkedMul 2 = none := by decide
example : (7 : U256).checkedDiv 0 = none := by decide

/-! ### Overflowing: the wrapped result paired with the flag that reports the loss -/

example : (7 : U256).overflowingAdd 3 = ((10 : U256), false) := by decide
example : U256.max.overflowingAdd 1 = ((0 : U256), true) := by decide
example : (7 : U256).overflowingSub 3 = ((4 : U256), false) := by decide
example : (0 : U256).overflowingSub 1 = (U256.max, true) := by decide
example : (7 : U256).overflowingMul 3 = ((21 : U256), false) := by decide
example : U256.max.overflowingMul 2 = (U256.max - 1, true) := by decide

/-! ### Saturating: clamped to the ends of the representable range -/

example : (7 : U256).saturatingAdd 3 = 10 := by decide
example : U256.max.saturatingAdd 1 = U256.max := by decide
example : (7 : U256).saturatingSub 3 = 4 := by decide
example : (0 : U256).saturatingSub 1 = 0 := by decide
example : (7 : U256).saturatingMul 3 = 21 := by decide
example : U256.max.saturatingMul 2 = U256.max := by decide

/-! ### Quotient and remainder share one checked entry point -/

example : (7 : U256).checkedDivMod 3 = some (2, 1) := by decide
example : (7 : U256).checkedDivMod 0 = none := by decide

end U256Arithmetic

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

/-- The other direction: whatever checked narrowing accepts widens back to its source, which makes
the pair mutually inverse. -/
example {value : U128} {narrowed : U64} (h : value.toU64? = some narrowed) :
    narrowed.toU128 = value :=
  U128.toU128_toU64?_eq_some h

example {value : U256} {narrowed : U64} (h : value.toU64? = some narrowed) :
    narrowed.toU256 = value :=
  U256.toU256_toU64?_eq_some h

example {value : U256} {narrowed : U128} (h : value.toU128? = some narrowed) :
    narrowed.toU256 = value :=
  U256.toU256_toU128?_eq_some h

end ProofExamples
