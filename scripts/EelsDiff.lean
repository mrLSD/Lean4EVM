import Lean4EVM

/-!
# Differential evaluator

Evaluates Lean4EVM primitives on the vectors written by `scripts/eels_diff.py`, which owns the EELS
reference semantics and the comparison. Run as `lake env lean --run scripts/EelsDiff.lean <dir>`:
reads `<dir>/ops.txt` (hex `a b c` per line) and `<dir>/bytes.txt` (`size` and hex `n` per line),
writes `<dir>/ops.out` and `<dir>/bytes.out` with one space-separated result row per vector.
-/

open Lean4EVM

def parseHex (s : String) : Nat :=
  s.foldl (fun acc c =>
    acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def flag (b : Bool) : String := if b then "1" else "0"

def optNat : Option U64 → String
  | none => "none"
  | some x => toString x.toNat

def hexBytes (bytes : ByteArray) : String :=
  if bytes.isEmpty then "-" else
    String.join <| bytes.toList.map fun b =>
      let digits := Nat.toDigits 16 b.toNat
      String.ofList (if digits.length = 1 then '0' :: digits else digits)

/-- U256 word operations, U64 fixed-width operations, and the U128 split for one `a b c` vector. -/
def opsRow (line : String) : String :=
  match line.splitOn " " with
  | [sa, sb, sc] =>
    let na := parseHex sa
    let nb := parseHex sb
    let a : U256 := U256.ofNat na
    let b : U256 := U256.ofNat nb
    let c : U256 := U256.ofNat (parseHex sc)
    let shift : U256 := U256.ofNat (na % 1024)
    let ua : U64 := U64.ofNat na
    let ub : U64 := U64.ofNat nb
    " ".intercalate [
      toString (a + b).toNat, toString (a - b).toNat, toString (a * b).toNat,
      toString (a / b).toNat, toString (a % b).toNat,
      toString (U256.sdiv a b).toNat, toString (U256.smod a b).toNat,
      toString (U256.addmod a b c).toNat, toString (U256.mulmod a b c).toNat,
      toString (U256.exp a b).toNat,
      toString (U256.signExtend a b).toNat, toString (U256.byteAt a b).toNat,
      toString (U256.shl shift b).toNat, toString (U256.shr shift b).toNat,
      toString (U256.sar shift b).toNat,
      flag (U256.ult a b), flag (U256.ugt a b), flag (U256.slt a b), flag (U256.sgt a b),
      flag (a == b), flag (U256.isZero a),
      toString (a &&& b).toNat, toString (a ||| b).toNat, toString (a ^^^ b).toNat,
      toString (~~~a).toNat, toString (U256.clz a).toNat, toString (-a).toNat,
      toString (U256.toSignedInt a), toString (U256.ofInt (U256.toSignedInt a)).toNat,
      toString (ua + ub).toNat, toString (ua - ub).toNat, toString (ua * ub).toNat,
      optNat (FixedUInt.checkedAdd ua ub), optNat (FixedUInt.checkedSub ua ub),
      optNat (FixedUInt.checkedMul ua ub),
      toString (FixedUInt.saturatingAdd ua ub).toNat,
      toString (FixedUInt.saturatingSub ua ub).toNat,
      toString (FixedUInt.saturatingMul ua ub).toNat,
      flag (FixedUInt.overflowingMul ua ub).2, toString (ua ^ (nb % 100)).toNat,
      toString (FixedUInt.leadingZeros ua), toString (FixedUInt.trailingZeros ua),
      toString (FixedUInt.countOnes ua), toString (FixedUInt.rotateLeft ua (nb % 200)).toNat,
      toString (U256.lowU128 a).toNat, toString (U256.highU128 a).toNat,
      toString (U256.fromU128s (U256.highU128 a) (U256.lowU128 a)).toNat, FixedUInt.toHex a]
  | _ => "PARSE_ERROR"

/-- Big-endian codec of `FixedBytes size` and the `Address`/`H256` word conversions for `size n`. -/
def bytesRow (line : String) : String :=
  match line.splitOn " " with
  | [ss, sn] =>
    let size := ss.toNat!
    let n := parseHex sn
    let value := FixedBytes.ofNat size n
    let encoded := value.toByteArray
    let word := U256.ofNat n
    let address := Address.ofU256 word
    let hash := H256.ofU256 word
    " ".intercalate [
      hexBytes encoded, toString value.toNat,
      flag (FixedBytes.ofByteArray? size encoded == some value),
      flag (FixedBytes.ofByteArray? (size + 1) encoded).isNone,
      flag ((List.range size).all fun i => value.getByte i == encoded.get! i),
      toString address.toNat,
      (match Address.ofU256? word with
        | some checked => toString checked.toNat
        | none => "none"),
      toString hash.toNat, hexBytes address.toByteArray, hexBytes hash.toByteArray, value.toHex]
  | _ => "PARSE_ERROR"

def evaluate (dir kind : String) (row : String → String) : IO Unit := do
  let input ← IO.FS.readFile s!"{dir}/{kind}.txt"
  let lines := (input.splitOn "\n").filter (· ≠ "")
  IO.FS.writeFile s!"{dir}/{kind}.out" ("\n".intercalate (lines.map row) ++ "\n")
  IO.println s!"{kind}: evaluated {lines.length} vectors"

def main (args : List String) : IO Unit := do
  let dir := args.head!
  evaluate dir "ops" opsRow
  evaluate dir "bytes" bytesRow
