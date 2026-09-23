import Lean4EVM.Interpreter.MachineState

/-! # Arithmetic instructions

ADD checks operands before gas, as SwiftEVM does. Exceptions are finalized by Machine.step;
the failed frame's residual operand stack is diagnostic, not a protocol result.
-/

namespace Lean4EVM.ArithmeticInstructions

/-- ADD consumes two words and three gas, replacing the operands with their modular sum. -/
def add (machine : Machine) : Except ExitError Machine :=
  match operands : machine.stack.popTwo with
  | none => .error .stackUnderflow
  | some (a, b, tail) =>
    match machine.gas.charge 3 with
    | none => .error .outOfGas
    | some gas =>
      -- Two operands were removed, so one result always fits; no dynamic overflow path is needed.
      .ok { machine with
        gas := gas
        pc := machine.pc + 1
        stack := ⟨tail.data.push (a + b), by
          have h := Stack.popTwo_spec operands
          have hb := machine.stack.bounded
          rw [h] at hb
          simp only [Array.size_push] at hb ⊢
          omega⟩ }

/-- Operand failure has priority over gas failure. -/
theorem add_underflow (machine : Machine) (h : machine.stack.popTwo = none) :
    add machine = .error .stackUnderflow := by
  unfold add
  split <;> simp_all

/-- With two operands present, insufficient gas produces out-of-gas. -/
theorem add_outOfGas (machine : Machine) {a b : U256} {tail : Stack}
    (h : machine.stack.popTwo = some (a, b, tail)) (gas : machine.gas.remaining.toNat < 3) :
    add machine = .error .outOfGas := by
  unfold add
  split
  next missing => simp [h] at missing
  next => simp [(Gas.charge_eq_none_iff _ _).mpr gas]

/-- Successful ADD preserves the stack tail and environment, and charges exactly three gas. -/
theorem add_spec {machine next : Machine} (h : add machine = .ok next) :
    ∃ a b : U256, ∃ tail : Stack,
      machine.stack.data = (tail.data.push b).push a ∧
      next.stack.data = tail.data.push (a + b) ∧
      3 ≤ machine.gas.remaining.toNat ∧
      next.gas.remaining.toNat = machine.gas.remaining.toNat - 3 ∧
      next.pc = machine.pc + 1 ∧ next.status = machine.status ∧
      next.code = machine.code ∧ next.hardFork = machine.hardFork := by
  unfold add at h
  split at h
  next => contradiction
  next a b tail operands =>
    split at h
    next => contradiction
    next gas charged =>
      cases h
      exact ⟨a, b, tail, Stack.popTwo_spec operands, rfl,
        (Gas.charge_spec charged).1, (Gas.charge_spec charged).2, rfl, rfl, rfl, rfl⟩

/-- Successful ADD strictly decreases the remaining budget. -/
theorem add_gas_lt {machine next : Machine} (h : add machine = .ok next) :
    next.gas.remaining.toNat < machine.gas.remaining.toNat := by
  obtain ⟨a, b, tail, _, _, affordable, exactCost, _⟩ := add_spec h
  omega

/-- Successful ADD does not change the execution control status. -/
theorem add_status {machine next : Machine} (h : add machine = .ok next) :
    next.status = machine.status := by
  obtain ⟨a, b, tail, _, _, _, _, _, hs, _⟩ := add_spec h
  exact hs

/-- The stack delta and result arithmetic match the Yellow Paper ADD rule. -/
theorem add_stack_effect {machine next : Machine} (h : add machine = .ok next) :
    next.stack.data.size + 1 = machine.stack.data.size ∧
    ∃ a b : U256, next.stack.data.back? = some (a + b) ∧
      (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  obtain ⟨a, b, tail, before, after, _⟩ := add_spec h
  constructor
  · simp [before, after]
  · exact ⟨a, b, by simp [after], FixedUInt.toNat_add a b⟩

/-- ADD succeeds exactly when the stack and gas preconditions hold. -/
theorem add_success_iff (machine : Machine) :
    (∃ next, add machine = .ok next) ↔
      2 ≤ machine.stack.data.size ∧ 3 ≤ machine.gas.remaining.toNat := by
  unfold add
  split
  next missing =>
    have size := (Stack.popTwo_eq_none_iff _).mp missing
    simp; omega
  next a b tail operands =>
    have shape := Stack.popTwo_spec operands
    split
    next noGas =>
      have cost := (Gas.charge_eq_none_iff _ _).mp noGas
      simp; omega
    next gas charged =>
      have cost := (Gas.charge_spec charged).1
      simp [shape, cost]

end Lean4EVM.ArithmeticInstructions
