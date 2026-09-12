import Lean4EVM

/-! # Text adapter for the real-oracle differential gate -/

open Lean4EVM

/-- Hexadecimal words in the test protocol, without a prefix. -/
def wordNat (s : String) : Nat :=
  s.foldl (fun n c => n * 16 +
    (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

/-- Fork order used by the external availability vectors. -/
def forks : Array HardFork := #[.frontier, .homestead, .tangerine, .spuriousDragon,
  .byzantium, .constantinople, .istanbul, .berlin, .london, .paris, .shanghai, .cancun,
  .prague, .osaka]

/-- Encodes the result class without conflating implementation gaps and exceptional halts. -/
def statusText : MachineStatus → String
  | .running => "running"
  | .stopped => "stopped"
  | .unsupported _ => "unsupported"
  | .failed .stackUnderflow => "underflow"
  | .failed .outOfGas => "oog"
  | .failed (.invalidOpcode _) => "invalid"

/-- Evaluates one validated gate input; malformed inputs fail rather than wrap the budget. -/
def row (line : String) : IO String := do
  let [mode, budget, codeText, words] := line.splitOn "|" | throw (IO.userError "bad row")
  if mode = "decode" then
    let some fork := forks[budget.toNat!]? | throw (IO.userError "unknown fork")
    let byte := UInt8.ofNat codeText.toNat!
    return match Opcode.decode fork byte with
      | .supported _ => "supported"
      | .unsupported => "unsupported"
      | .invalid => "invalid"
  let some gasWord := U64.ofNat? budget.toNat! | throw (IO.userError "gas overflow")
  let gas : Gas := ⟨gasWord⟩
  if mode = "charge" then
    return match gas.charge codeText.toNat! with
      | none => "none"
      | some next => toString next.remaining.toNat
  let data := if words.isEmpty then #[] else
    ((words.splitOn ",").map (U256.ofNat ∘ wordNat)).toArray
  let some stack := Stack.ofArray? data | throw (IO.userError "stack overflow")
  let code := if codeText.isEmpty then ByteArray.empty else
    ((codeText.splitOn ",").map (UInt8.ofNat ∘ String.toNat!)).toByteArray
  let machine : Machine := { code, hardFork := .osaka, stack, gas }
  let next := if mode = "step" then machine.step else machine.evalLoop
  let words := next.stack.data.toList.map fun word =>
    let digits := String.ofList (Nat.toDigits 16 word.toNat)
    String.ofList (List.replicate (64 - digits.length) '0') ++ digits
  return "|".intercalate [statusText next.status, toString next.gas.remaining.toNat,
    toString next.pc, ",".intercalate words]

/-- Reads vectors and writes one result per input line. -/
def main (args : List String) : IO Unit := do
  let [input, output] := args | throw (IO.userError "expected input and output paths")
  let lines := ((← IO.FS.readFile input).splitOn "\n").filter (· ≠ "")
  let results ← lines.mapM row
  IO.FS.writeFile output ("\n".intercalate results ++ "\n")
