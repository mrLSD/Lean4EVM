import Lean4EVM.Interpreter.HardFork

/-! # Byte decoding

Availability covers the legacy EVM opcode map through Osaka, independently of implementation
coverage. Undefined bytes and the explicit INVALID instruction are exceptional; known but
unimplemented instructions remain a separate, non-protocol outcome.
-/

namespace Lean4EVM

/-- The two executable instructions in the initial verified interpreter. -/
inductive Opcode where
  | stop | add
  deriving DecidableEq, Repr

namespace Opcode

/-- Encoding of a supported instruction. -/
def toByte : Opcode → UInt8
  | .stop => 0x00
  | .add => 0x01

/-- Whether a byte names an available, non-INVALID instruction in this revision. -/
def available (fork : HardFork) (byte : UInt8) : Bool :=
  let n := byte.toNat
  decide (
    n ≤ 0x0b ∨ (0x10 ≤ n ∧ n ≤ 0x1a) ∨ n = 0x20 ∨
    (0x30 ≤ n ∧ n ≤ 0x3c) ∨ (0x40 ≤ n ∧ n ≤ 0x45) ∨
    (0x50 ≤ n ∧ n ≤ 0x5b) ∨ (0x60 ≤ n ∧ n ≤ 0x9f) ∨
    (0xa0 ≤ n ∧ n ≤ 0xa4) ∨ n = 0xf0 ∨ n = 0xf1 ∨ n = 0xf2 ∨ n = 0xf3 ∨ n = 0xff ∨
    (HardFork.homestead ≤ fork ∧ n = 0xf4) ∨
    (HardFork.byzantium ≤ fork ∧ (n = 0x3d ∨ n = 0x3e ∨ n = 0xfa ∨ n = 0xfd)) ∨
    (HardFork.constantinople ≤ fork ∧ ((0x1b ≤ n ∧ n ≤ 0x1d) ∨ n = 0x3f ∨ n = 0xf5)) ∨
    (HardFork.istanbul ≤ fork ∧ (n = 0x46 ∨ n = 0x47)) ∨
    (HardFork.london ≤ fork ∧ n = 0x48) ∨
    (HardFork.shanghai ≤ fork ∧ n = 0x5f) ∨
    (HardFork.cancun ≤ fork ∧ (n = 0x49 ∨ n = 0x4a ∨ (0x5c ≤ n ∧ n ≤ 0x5e))) ∨
    (HardFork.osaka ≤ fork ∧ n = 0x1e))

/-- Distinguishes executable instructions, implementation gaps, and exceptional bytes. -/
inductive Decoded where
  | supported (opcode : Opcode)
  | unsupported
  | invalid
  deriving DecidableEq, Repr

/-- Decodes without treating missing implementations as protocol-invalid opcodes. -/
def decode (fork : HardFork) (byte : UInt8) : Decoded :=
  if byte = 0 then .supported .stop
  else if byte = 1 then .supported .add
  else if available fork byte then .unsupported else .invalid

/-- Supported instructions round-trip in every revision. -/
@[simp] theorem decode_toByte (fork : HardFork) (opcode : Opcode) :
    decode fork opcode.toByte = .supported opcode := by
  cases opcode <;> simp [decode, toByte]

end Opcode
end Lean4EVM
