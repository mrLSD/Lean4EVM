import Lean4EVM.Primitives.UInt.U64

/-! # Checked frame gas

Only the remaining budget is stored. Costs stay natural numbers, including costs exceeding U64.
The budget bound is the production interface boundary, not an unrestricted EELS `Uint` model.
-/

namespace Lean4EVM

/-- Nominal remaining frame budget; never uses wrapping arithmetic for accounting. -/
structure Gas where
  /-- Remaining gas, bounded by the production interface width. -/
  remaining : U64
  deriving DecidableEq

namespace Gas

/-- Charges exactly `cost`, or fails without truncating an unaffordable cost. -/
def charge (gas : Gas) (cost : Nat) : Option Gas :=
  if cost ≤ gas.remaining.toNat then
    some ⟨U64.ofNat (gas.remaining.toNat - cost)⟩
  else none

/-- Failure means precisely that the requested cost exceeds the budget. -/
@[simp] theorem charge_eq_none_iff (gas : Gas) (cost : Nat) :
    gas.charge cost = none ↔ gas.remaining.toNat < cost := by
  simp [charge]

/-- Successful charging agrees with exact natural subtraction. -/
theorem charge_spec {gas next : Gas} {cost : Nat} (h : gas.charge cost = some next) :
    cost ≤ gas.remaining.toNat ∧ next.remaining.toNat = gas.remaining.toNat - cost := by
  unfold charge at h
  split at h
  next affordable =>
    cases h
    refine ⟨affordable, ?_⟩
    exact (FixedUInt.toNat_ofNat _).trans (Nat.mod_eq_of_lt
      (lt_of_le_of_lt (Nat.sub_le _ _) (FixedUInt.toNat_lt_modulus gas.remaining)))
  next => contradiction

/-- Projecting the checked result yields exactly the unbounded checked specification. -/
theorem charge_toNat (gas : Gas) (cost : Nat) :
    (gas.charge cost).map (fun next => next.remaining.toNat) =
      if cost ≤ gas.remaining.toNat then some (gas.remaining.toNat - cost) else none := by
  cases h : gas.charge cost with
  | none => simp [Nat.not_le.mpr ((charge_eq_none_iff _ _).mp h)]
  | some next => simp [(charge_spec h).1, (charge_spec h).2]

/-- A successful positive charge strictly decreases the termination measure. -/
theorem charge_lt {gas next : Gas} {cost : Nat} (h : gas.charge cost = some next)
    (positive : 0 < cost) : next.remaining.toNat < gas.remaining.toNat := by
  obtain ⟨affordable, exactCost⟩ := charge_spec h
  rw [exactCost]
  omega

end Gas
end Lean4EVM
