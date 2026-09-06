import Lean4EVM.Primitives.UInt.Core

/-!
# `U64`

Type-owned construction, widening, and proof API for bounded 64-bit Ethereum quantities.
-/

namespace Lean4EVM
namespace U64

/-- Constructs a `U64` by retaining the low 64 bits. -/
abbrev ofNat (n : ℕ) : U64 := FixedUInt.ofNat n
/-- Constructs a `U64` only when `n` fits in 64 bits. -/
abbrev ofNat? (n : ℕ) : Option U64 := FixedUInt.ofNat? n
/-- Constructs a `U64` with two's-complement wrapping. -/
abbrev ofInt (n : ℤ) : U64 := FixedUInt.ofInt n
/-- Constructs a `U64` only from a representable nonnegative integer. -/
abbrev ofInt? (n : ℤ) : Option U64 := FixedUInt.ofInt? n
/-- Returns the unsigned value. -/
abbrev toNat (value : U64) : ℕ := FixedUInt.toNat value
/-- Reinterprets the bits as a signed two's-complement integer. -/
abbrev toSignedInt (value : U64) : ℤ := FixedUInt.toSignedInt value
/-- Returns the maximum `U64`. -/
abbrev max : U64 := FixedUInt.max
/-- Returns the modulus `2 ^ 64`. -/
abbrev modulus : ℕ := FixedUInt.modulus 64

/-- The `U64` modulus has the canonical power-of-two form. -/
@[simp]
theorem modulus_eq : U64.modulus = 2 ^ 64 :=
  rfl

/-- Natural casts into `U64` reduce modulo `2 ^ 64`. -/
@[simp]
theorem toNat_natCast (n : ℕ) : (n : U64).toNat = n % 2 ^ 64 := by
  exact FixedUInt.toNat_natCast (α := U64) (width := 64) n

/-- Numeric `U64` literals reduce modulo `2 ^ 64`. -/
@[simp]
theorem toNat_ofNat_lit (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : U64).toNat = n % 2 ^ 64 := by
  exact FixedUInt.toNat_ofNat_lit (α := U64) (width := 64) n

/-- Widens a `U64` to `U128` without changing its value. -/
def toU128 (value : U64) : U128 :=
  FixedUInt.ofNat value.toNat

/-- Widens a `U64` to `U256` without changing its value. -/
def toU256 (value : U64) : U256 :=
  FixedUInt.ofNat value.toNat

/-- Widening to `U128` preserves the unsigned value. -/
@[simp]
theorem toNat_toU128 (value : U64) :
    FixedUInt.toNat value.toU128 = value.toNat := by
  rw [toU128, FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (FixedUInt.toNat_lt_modulus value) (by decide)

/-- Widening to `U256` preserves the unsigned value. -/
@[simp]
theorem toNat_toU256 (value : U64) :
    FixedUInt.toNat value.toU256 = value.toNat := by
  rw [toU256, FixedUInt.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans (FixedUInt.toNat_lt_modulus value) (by decide)

/-- Widening from `U64` to `U128` is injective. -/
theorem toU128_injective : Function.Injective toU128 := by
  intro a b h
  apply FixedUInt.toNat_injective
  simpa using congrArg FixedUInt.toNat h

/-- Widening from `U64` to `U256` is injective. -/
theorem toU256_injective : Function.Injective toU256 := by
  intro a b h
  apply FixedUInt.toNat_injective
  simpa using congrArg FixedUInt.toNat h

end U64

end Lean4EVM
