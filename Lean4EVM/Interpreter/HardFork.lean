import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Interpreter revisions

Names follow SwiftEVM. This is an opcode-availability index, not a chain activation schedule or
a claim that every rule of these revisions is implemented.
-/

namespace Lean4EVM

/-- Revisions distinguished by the interpreter's opcode availability rules. -/
inductive HardFork where
  | frontier | homestead | tangerine | spuriousDragon | byzantium | constantinople
  | istanbul | berlin | london | paris | shanghai | cancun | prague | osaka
  deriving DecidableEq, Repr

namespace HardFork

/-- Chronological revision index; activation block numbers are deliberately not encoded. -/
def rank : HardFork → Fin 14
  | .frontier => 0 | .homestead => 1 | .tangerine => 2 | .spuriousDragon => 3
  | .byzantium => 4 | .constantinople => 5 | .istanbul => 6 | .berlin => 7
  | .london => 8 | .paris => 9 | .shanghai => 10 | .cancun => 11
  | .prague => 12 | .osaka => 13

/-- Distinct revision names have distinct ranks. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

/-- Revision ordering and its laws are inherited from the injective chronological index. -/
instance : LinearOrder HardFork := LinearOrder.lift' rank rank_injective

end HardFork
end Lean4EVM
