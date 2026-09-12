import Lean4EVM.Interpreter.MachineState

/-! # Control instructions -/

namespace Lean4EVM.ControlInstructions

/-- Explicit STOP: no gas charge; terminal pc advances as in EELS Osaka. -/
def stop (machine : Machine) : Machine :=
  { machine with pc := machine.pc + 1, status := .stopped }

/-- STOP changes only the program counter and execution status. -/
theorem stop_spec (machine : Machine) :
    (stop machine).gas = machine.gas ∧ (stop machine).stack = machine.stack ∧
    (stop machine).pc = machine.pc + 1 ∧ (stop machine).status = .stopped := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Lean4EVM.ControlInstructions
