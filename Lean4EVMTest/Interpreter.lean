import Lean4EVM.Interpreter.Machine

/-! # Interpreter regression and proof-use examples

Stacks are bottom-to-top. The differential gate adds randomized and all-byte/all-revision checks.
-/

namespace Lean4EVMTest.Interpreter
open Lean4EVM

/-- Test machine with an explicitly selected revision and a checked initial stack. -/
def fixture (code : List UInt8) (words : Array U256) (gas : U64) : Machine :=
  { code := code.toByteArray, hardFork := .osaka,
    stack := (Stack.ofArray? words).getD Stack.empty, gas := ⟨gas⟩ }

section ExecutionExamples

example : ((fixture [] #[] 0).evalLoop).status = .stopped := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 1 (by decide)]; decide
example : ((fixture [0] #[] 0).evalLoop).pc = 1 := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 1 (by decide)]; decide
example : ((fixture [0, 1] #[2, 3] 0).evalLoop).stack.data = #[2, 3] := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 1 (by decide)]; decide
example : ((fixture [1] #[2, 3] 3).evalLoop).stack.data = #[5] := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 2 (by decide)]; decide
example : ((fixture [1, 0] #[2, 3] 3).evalLoop).pc = 2 := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 2 (by decide)]; decide
example : ((fixture [1, 1] #[1, 2, 3] 6).evalLoop).stack.data = #[6] := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 3 (by decide)]; decide
example : ((fixture [1] #[U256.max, 1] 3).evalLoop).stack.data = #[0] := by
  rw [Machine.evalLoop_eq_of_halted_iterate _ 2 (by decide)]; decide
example : ((fixture [1] #[] 0).step).status = .failed .stackUnderflow := by decide
example : ((fixture [1] #[1] 3).step).status = .failed .stackUnderflow := by decide
example : ((fixture [1] #[1, 2] 2).step).status = .failed .outOfGas := by decide
example : ((fixture [1] #[1, 2] 2).step).gas.remaining.toNat = 0 := by decide
example : ((fixture [2] #[] 3).step).status = .unsupported 2 := by decide
example : ((fixture [12] #[] 3).step).status = .failed (.invalidOpcode 12) := by decide
example : ((fixture [254] #[] 3).step).status = .failed (.invalidOpcode 254) := by decide
example : Opcode.decode .prague 0x1e = .invalid := by decide
example : Opcode.decode .osaka 0x1e = .unsupported := by decide
example : (Gas.mk 21000).charge 21000 = some ⟨0⟩ := by decide
example : (Gas.mk U64.max).charge (2 ^ 64) = none := by decide
example : Stack.ofArray? (Array.replicate 1025 (0 : U256)) = none := by simp
example : Stack.empty.peek 0 = none := by decide
example : (Stack.empty.push 7).bind Stack.pop = some (7, Stack.empty) := by decide

-- Full-size execution is checked by the real-oracle differential vectors. This example
-- proves the boundary size from the semantic law, without reducing a 1024-word proof term.
example (machine next : Machine) (full : machine.stack.data.size = 1024)
    (h : ArithmeticInstructions.add machine = .ok next) : next.stack.data.size = 1023 := by
  have effect := (ArithmeticInstructions.add_stack_effect h).1
  omega

end ExecutionExamples

section ProofExamples

example (gas next : Gas) (h : gas.charge 3 = some next) :
    next.remaining.toNat + 3 = gas.remaining.toNat := by
  obtain ⟨affordable, exactCost⟩ := Gas.charge_spec h
  omega

example (machine : Machine) : (machine.evalLoop).status ≠ .running :=
  Machine.evalLoop_halted machine

example (machine next : Machine) (h : ArithmeticInstructions.add machine = .ok next) :
    next.stack.data.size + 1 = machine.stack.data.size :=
  (ArithmeticInstructions.add_stack_effect h).1

example (machine : Machine) (h : machine.status = .stopped) : machine.step = machine :=
  Machine.step_halted machine (by simp [h])

end ProofExamples
end Lean4EVMTest.Interpreter
