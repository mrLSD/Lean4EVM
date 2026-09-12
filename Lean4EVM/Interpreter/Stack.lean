import Lean4EVM.Primitives.UInt.U256

/-! # Operand stack

The top is the final array element, as in SwiftEVM and EELS. The size bound is carried by the type.
-/

namespace Lean4EVM

/-- EVM operand stack with at most 1024 words. -/
structure Stack where
  /-- Words in bottom-to-top order. -/
  data : Array U256
  /-- The protocol stack limit. -/
  bounded : data.size ≤ 1024
  deriving DecidableEq

namespace Stack

/-- Empty operand stack. -/
def empty : Stack := ⟨#[], by simp⟩

/-- Checks a supplied bottom-to-top stack against the protocol limit. -/
def ofArray? (data : Array U256) : Option Stack :=
  if h : data.size ≤ 1024 then some ⟨data, h⟩ else none

/-- Pushes a word, failing exactly when the stack is full. -/
def push (stack : Stack) (word : U256) : Option Stack :=
  if h : stack.data.size < 1024 then
    some ⟨stack.data.push word, by simp; omega⟩
  else none

/-- Removes the top word; an empty stack fails. -/
def pop (stack : Stack) : Option (U256 × Stack) :=
  match stack.data.back? with
  | none => none
  | some word => some (word, ⟨stack.data.pop, by
      simpa using le_trans (Nat.sub_le stack.data.size 1) stack.bounded⟩)

/-- Reads a word at a zero-based depth from the top without modifying the stack. -/
def peek (stack : Stack) (depth : Nat) : Option U256 :=
  if depth < stack.data.size then stack.data[stack.data.size - 1 - depth]? else none

/-- Underflow is determined before either operand is removed. -/
def popTwo (stack : Stack) : Option (U256 × U256 × Stack) := do
  let (a, rest) ← stack.pop
  let (b, tail) ← rest.pop
  return (a, b, tail)

/-- Checked stack construction rejects exactly oversized arrays. -/
@[simp] theorem ofArray?_eq_none_iff (data : Array U256) :
    ofArray? data = none ↔ 1024 < data.size := by
  simp [ofArray?]

/-- A push fails exactly at the protocol limit. -/
@[simp] theorem push_eq_none_iff (stack : Stack) (word : U256) :
    stack.push word = none ↔ stack.data.size = 1024 := by
  have bounded := stack.bounded
  simp only [push]
  split <;> simp_all <;> omega

/-- A pop fails exactly when there are no operands. -/
@[simp] theorem pop_eq_none_iff (stack : Stack) :
    stack.pop = none ↔ stack.data.size = 0 := by
  simp only [pop]
  cases h : stack.data.back? with
  | none => simpa using Array.size_eq_zero_iff.mpr (Array.back?_eq_none_iff.mp h)
  | some word =>
    obtain ⟨xs, hx⟩ := Array.back?_eq_some_iff.mp h
    simp [hx]

/-- Successful pushes append precisely the supplied word. -/
theorem push_spec {stack next : Stack} {word : U256} (h : stack.push word = some next) :
    next.data = stack.data.push word := by
  unfold push at h
  split at h
  next => cases h; rfl
  next => contradiction

/-- Successful pops remove exactly the final array element. -/
theorem pop_spec {stack rest : Stack} {word : U256}
    (h : stack.pop = some (word, rest)) :
    stack.data = rest.data.push word := by
  unfold pop at h
  split at h
  next => contradiction
  next value hv =>
    cases h
    obtain ⟨xs, hx⟩ := Array.back?_eq_some_iff.mp hv
    simp [hx]

/-- Two pops expose the top two operands and preserve the entire remaining stack. -/
theorem popTwo_spec {stack tail : Stack} {a b : U256}
    (h : stack.popTwo = some (a, b, tail)) :
    stack.data = (tail.data.push b).push a := by
  unfold popTwo at h
  cases hp : stack.pop with
  | none => simp [hp] at h
  | some pair =>
    obtain ⟨x, rest⟩ := pair
    cases hq : rest.pop with
    | none => simp [hp, hq] at h
    | some pair =>
      obtain ⟨y, finalStack⟩ := pair
      have same : x = a ∧ y = b ∧ finalStack = tail := by simpa [hp, hq] using h
      obtain ⟨rfl, rfl, rfl⟩ := same
      rw [pop_spec hp, pop_spec hq]

/-- Binary instructions underflow exactly when fewer than two operands are present. -/
@[simp] theorem popTwo_eq_none_iff (stack : Stack) :
    stack.popTwo = none ↔ stack.data.size < 2 := by
  cases hp : stack.pop with
  | none =>
    have size := (pop_eq_none_iff stack).mp hp
    simp [popTwo, hp, size]
  | some pair =>
    obtain ⟨a, rest⟩ := pair
    have shape := pop_spec hp
    cases hq : rest.pop with
    | none =>
      have size := (pop_eq_none_iff rest).mp hq
      simp [popTwo, hp, hq, shape, size]
    | some pair =>
      obtain ⟨b, tail⟩ := pair
      have restShape := pop_spec hq
      simp [popTwo, hp, hq, shape, restShape]

/-- Popping a successfully pushed word restores the previous stack. -/
theorem pop_push {stack next : Stack} {word : U256} (h : stack.push word = some next) :
    next.pop = some (word, stack) := by
  have shape := push_spec h
  cases stack
  cases next
  simp_all [pop]

/-- Reading beyond the available top-relative depth fails exactly at the stack size. -/
@[simp] theorem peek_eq_none_iff (stack : Stack) (depth : Nat) :
    stack.peek depth = none ↔ stack.data.size ≤ depth := by
  unfold peek
  split <;> simp_all
  omega

/-- The most recently pushed word is at depth zero. -/
theorem peek_push {stack next : Stack} {word : U256} (h : stack.push word = some next) :
    next.peek 0 = some word := by
  simp [peek, push_spec h]

end Stack
end Lean4EVM
