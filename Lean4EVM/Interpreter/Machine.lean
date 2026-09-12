import Lean4EVM.Interpreter.Instructions.Control
import Lean4EVM.Interpreter.Instructions.Arithmetic
import Mathlib.Logic.Function.Iterate

/-! # Single-frame execution

The SwiftEVM step/evalLoop split is retained. Only ADD continues; STOP, exceptional halts and
unsupported instructions end this partial interpreter. Unsupported is not an Ethereum outcome.
-/

namespace Lean4EVM.Machine

/-- Executes one instruction, or stops at end-of-code; terminal states are fixed points. -/
def step (machine : Machine) : Machine :=
  if machine.status = .running then
    if h : machine.pc < machine.code.size then
      let byte := machine.code[machine.pc]
      match Opcode.decode machine.hardFork byte with
      | .supported .stop => ControlInstructions.stop machine
      | .supported .add =>
        match ArithmeticInstructions.add machine with
        | .ok next => next
        | .error error => machine.fail error
      | .unsupported => { machine with status := .unsupported byte }
      | .invalid => machine.fail (.invalidOpcode byte)
    else { machine with status := .stopped }
  else machine

/-- A halted or unsupported machine cannot be restarted by stepping. -/
theorem step_halted (machine : Machine) (h : machine.status ≠ .running) :
    step machine = machine := by
  simp [step, h]

/-- Falling off the code stops without changing the program counter or budget. -/
theorem step_endOfCode (machine : Machine) (running : machine.status = .running)
    (ended : machine.code.size ≤ machine.pc) :
    step machine = { machine with status := .stopped } := by
  simp [step, running, Nat.not_lt.mpr ended]

/-- Dispatching STOP uses the shared, fork-independent control handler. -/
theorem step_stop (machine : Machine) (running : machine.status = .running)
    (inCode : machine.pc < machine.code.size) (opcode : machine.code[machine.pc] = 0) :
    step machine = ControlInstructions.stop machine := by
  simp [step, running, inCode, opcode, Opcode.decode]

/-- Dispatching ADD preserves its handler result and finalizes any exceptional halt. -/
theorem step_add (machine : Machine) (running : machine.status = .running)
    (inCode : machine.pc < machine.code.size) (opcode : machine.code[machine.pc] = 1) :
    step machine = match ArithmeticInstructions.add machine with
      | .ok next => next
      | .error error => machine.fail error := by
  simp [step, running, inCode, opcode, Opcode.decode]

/-- Every step preserves code and revision, and never increases the frame budget. -/
theorem step_invariants (machine : Machine) :
    (step machine).code = machine.code ∧ (step machine).hardFork = machine.hardFork ∧
    (step machine).gas.remaining.toNat ≤ machine.gas.remaining.toNat := by
  unfold step
  split
  next running =>
    split
    next inCode =>
      cases decoded : Opcode.decode machine.hardFork machine.code[machine.pc] with
      | invalid => simp [decoded, fail]
      | unsupported => simp [decoded]
      | supported opcode =>
        cases opcode with
        | stop => simp [decoded, ControlInstructions.stop]
        | add =>
          cases result : ArithmeticInstructions.add machine with
          | error error => simp [decoded, fail]
          | ok next =>
            obtain ⟨a, b, tail, _, _, _, _, _, _, code, fork⟩ :=
              ArithmeticInstructions.add_spec result
            simpa only [decoded] using
              And.intro code (And.intro fork (le_of_lt (ArithmeticInstructions.add_gas_lt result)))
    next => exact ⟨rfl, rfl, le_rfl⟩
  next => exact ⟨rfl, rfl, le_rfl⟩

/-- Every continuing step of the implemented subset consumes positive gas. -/
theorem step_gas_lt (machine : Machine) (running : machine.status = .running)
    (continues : (step machine).status = .running) :
    (step machine).gas.remaining.toNat < machine.gas.remaining.toNat := by
  unfold step at continues ⊢
  rw [if_pos running] at continues ⊢
  by_cases inCode : machine.pc < machine.code.size
  · simp only [dif_pos inCode] at continues ⊢
    cases decoded : Opcode.decode machine.hardFork machine.code[machine.pc] with
    | invalid => simp [decoded, fail] at continues
    | unsupported => simp [decoded] at continues
    | supported opcode =>
      cases opcode with
      | stop => simp [decoded, ControlInstructions.stop] at continues
      | add =>
        cases result : ArithmeticInstructions.add machine with
        | error error => simp [decoded, result, fail] at continues
        | ok next =>
          simpa [decoded, result] using ArithmeticInstructions.add_gas_lt result
  · simp [inCode] at continues

/-- Executes until STOP, an exceptional halt, or an unsupported instruction, without fuel. -/
def evalLoop (machine : Machine) : Machine :=
  if _running : machine.status = .running then
    if _continues : (step machine).status = .running then
      evalLoop (step machine)
    else step machine
  else machine
termination_by machine.gas.remaining.toNat
decreasing_by exact step_gas_lt machine _running _continues

/-- Execution always returns a non-running state for this instruction subset. -/
theorem evalLoop_halted (machine : Machine) : (evalLoop machine).status ≠ .running := by
  fun_induction evalLoop with
  | case1 machine running continues ih => exact ih
  | case2 machine running stopped => exact stopped
  | case3 machine stopped => exact stopped

/-- Whole-frame execution preserves its environment and cannot create gas. -/
theorem evalLoop_invariants (machine : Machine) :
    (evalLoop machine).code = machine.code ∧
    (evalLoop machine).hardFork = machine.hardFork ∧
    (evalLoop machine).gas.remaining.toNat ≤ machine.gas.remaining.toNat := by
  fun_induction evalLoop with
  | case1 machine running continues ih =>
    obtain ⟨code, fork, gas⟩ := step_invariants machine
    exact ⟨ih.1.trans code, ih.2.1.trans fork, ih.2.2.trans gas⟩
  | case2 machine running stopped => exact step_invariants machine
  | case3 machine stopped => exact ⟨rfl, rfl, le_rfl⟩

/-- Execution is a finite iteration of the public step function. -/
theorem evalLoop_reachable (machine : Machine) :
    ∃ n : Nat, (step^[n]) machine = evalLoop machine := by
  fun_induction evalLoop with
  | case1 machine running continues ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simpa only [Function.iterate_succ_apply] using hn⟩
  | case2 machine running stopped => exact ⟨1, rfl⟩
  | case3 machine stopped => exact ⟨0, rfl⟩

/-- Taking one public step does not change the eventual execution result. -/
theorem evalLoop_step (machine : Machine) : evalLoop (step machine) = evalLoop machine := by
  by_cases running : machine.status = .running
  · conv_rhs => rw [evalLoop]
    simp only [dif_pos running]
    split
    next => rfl
    next stopped => rw [evalLoop]; simp [stopped]
  · rw [step_halted machine running]

/-- Any finite stepping trace reaching a terminal state has the same result as evalLoop. -/
theorem evalLoop_eq_of_halted_iterate (machine : Machine) (n : Nat)
    (halted : ((step^[n]) machine).status ≠ .running) :
    evalLoop machine = (step^[n]) machine := by
  induction n generalizing machine with
  | zero =>
    change machine.status ≠ .running at halted
    rw [evalLoop]
    simp [halted]
  | succ n ih =>
    rw [Function.iterate_succ_apply] at halted ⊢
    rw [← evalLoop_step machine]
    exact ih (step machine) halted

end Lean4EVM.Machine
