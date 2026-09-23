import Lean4EVM.Primitives.UInt
import Lean4EVM.Primitives.FixedBytes
import Lean

/-!
# Checked primitive literals

Activate with `open scoped Lean4EVM.Literals`. Literals reject overflow during elaboration and
expand to the owning type's `ofNat`; they introduce no runtime parsing or implicit conversions.
Hash numbers denote unsigned values serialized in big-endian order, padded to the exact width.

`64#10` deliberately overrides Lean's opposite-order BitVec notation inside this scope.
Use `BitVec.ofNat` explicitly when mixing both APIs. Compact ASCII suffixes such as `10U64`
and Unicode suffixes such as `10₆₄` and `10ₕ₁₆₀` select the same nominal constructors.
Unicode has no capital subscript H, so the hash suffix uses the subscript small letter `ₕ`.
-/

namespace Lean4EVM.Literals

open Lean Elab Term

/-- Numeric payloads use Lean's numeral grammar, including radix prefixes and separators. -/
declare_syntax_cat primitiveNumeral
/-- A single Lean numeral, excluding expressions and scientific notation. -/
syntax num : primitiveNumeral

/-- Explicit suffixes select a nominal primitive; bare widths select only unsigned integers. -/
declare_syntax_cat primitiveSuffix (behavior := symbol)
/-- Width subscripts, hash subscripts, and non-reserved ASCII type suffixes. -/
syntax ("₆₄" <|> "₁₂₈" <|> "₂₅₆" <|> "ₕ₁₆₀" <|> "ₕ₂₅₆"
  <|> &"U64" <|> &"U128" <|> &"U256" <|> &"H160" <|> &"H256") : primitiveSuffix

/-- Quoted numeric payloads carry an explicit primitive type. -/
declare_syntax_cat primitiveQuote
/-- Lowercase type markers for quoted literals. -/
syntax ("u64" <|> "u128" <|> "u256" <|> "h160" <|> "h256") : primitiveQuote

/-- A numeral followed by an explicit primitive suffix, checked for overflow. -/
scoped syntax (name := suffixed) num primitiveSuffix : term
/-- A width followed by a numeric payload; enabled only in the literal scope. -/
scoped syntax (name := widthPrefixed) (priority := high) num "#" num : term
/-- A nominal type name followed by a numeric payload. -/
scoped syntax (name := typePrefixed) ident "#" num : term
/-- A quoted Lean numeral with an explicit nominal type. -/
scoped syntax (name := quoted) primitiveQuote str : term

private def primitive (tag : String) : TermElabM (Name × Nat) :=
  match tag with
  | "64" | "₆₄" | "U64" | "u64" => pure (``U64.ofNat, 64)
  | "128" | "₁₂₈" | "U128" | "u128" => pure (``U128.ofNat, 128)
  | "256" | "₂₅₆" | "U256" | "u256" => pure (``U256.ofNat, 256)
  | "H160" | "h160" | "ₕ₁₆₀" => pure (``H160.ofNat, 160)
  | "H256" | "h256" | "ₕ₂₅₆" => pure (``H256.ofNat, 256)
  | _ => throwError "unsupported primitive literal type '{tag}'; \
      expected U64, U128, U256, H160 or H256"

private def expandLiteral (tag : String) (n : Nat) : TermElabM Expr := do
  let (ctor, width) ← primitive tag
  unless n < 2 ^ width do
    throwError "primitive literal out of range: value must be smaller than 2^{width}"
  return mkApp (mkConst ctor) (mkNatLit n)

private def numeralValue (stx : Syntax) : TermElabM Nat := do
  match stx.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected a natural-number literal"

@[term_elab suffixed] private def elabSuffixed : TermElab := fun stx _ => do
  let tag := stx[1][0][0].getAtomVal
  expandLiteral tag (← numeralValue stx[0])

@[term_elab widthPrefixed] private def elabWidthPrefixed : TermElab := fun stx _ => do
  expandLiteral (toString (← numeralValue stx[0])) (← numeralValue stx[2])

@[term_elab typePrefixed] private def elabTypePrefixed : TermElab := fun stx _ => do
  expandLiteral stx[0].getId.toString (← numeralValue stx[2])

@[term_elab quoted] private def elabQuoted : TermElab := fun stx _ => do
  let some text := stx[1].isStrLit? | throwErrorAt stx[1] "expected a string literal"
  -- Exclude whitespace and comments: only numeral characters belong in a quoted literal.
  unless !text.isEmpty && text.toList.all (fun c => c.isAlphanum || c == '_') do
    throwErrorAt stx[1] "expected a quoted natural-number literal without whitespace"
  match Parser.runParserCategory (← getEnv) `primitiveNumeral text with
  | .error _ => throwErrorAt stx[1] "invalid numeral; \
      expected decimal, hexadecimal (0x), binary (0b), or octal (0o) digits"
  | .ok parsed => expandLiteral stx[0][0][0].getAtomVal (← numeralValue parsed[0])

end Lean4EVM.Literals
