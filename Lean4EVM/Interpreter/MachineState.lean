import Lean4EVM.Interpreter.Gas
import Lean4EVM.Interpreter.Stack
import Lean4EVM.Interpreter.Opcodes

/-! # Shared machine state

This module breaks the dependency cycle: instruction handlers need the state; the dispatcher
imports those handlers. It is not SwiftEVM's transaction-scoped `ExecutionState`.
-/

namespace Lean4EVM

/-- Exceptional halts reachable in the implemented instruction subset. -/
inductive ExitError where
  | stackUnderflow | outOfGas | invalidOpcode (byte : UInt8)
  deriving DecidableEq, Repr

/-- Running, successful STOP, exceptional halt, or an implementation boundary. -/
inductive MachineStatus where
  | running
  | stopped
  | failed (error : ExitError)
  | unsupported (byte : UInt8)
  deriving DecidableEq, Repr

/-- Minimal single-frame machine; code and fork remain unchanged by execution. -/
structure Machine where
  /-- Legacy EVM bytecode. -/
  code : ByteArray
  /-- Explicit revision; no implicit latest-fork policy. -/
  hardFork : HardFork
  /-- Next instruction offset, interpreted as an unbounded natural index. -/
  pc : Nat := 0
  /-- Operand stack, with its size invariant. -/
  stack : Stack := Stack.empty
  /-- Remaining checked budget. -/
  gas : Gas
  /-- Execution control state. -/
  status : MachineStatus := .running

namespace Machine

/-- Finalizes an exceptional halt, consuming the frame budget as EELS does. -/
def fail (machine : Machine) (error : ExitError) : Machine :=
  { machine with gas := ⟨0⟩, status := .failed error }

end Machine
end Lean4EVM
