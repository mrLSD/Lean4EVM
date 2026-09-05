import Lean4EVM.Primitives.FixedBytes

/-!
# Fixed-size byte regression tests

Executable boundary checks and proof-API examples for exact-size byte primitives.
-/

open Lean4EVM

section FixedBytesTests

example : (FixedBytes.ofNat 0 0).toHex = "0x" := by decide
example : FixedBytes.getByte (FixedBytes.ofNat 4 0x12345678) 0 = 0x12 := by decide
example : FixedBytes.getByte (FixedBytes.ofNat 4 0x12345678) 3 = 0x78 := by decide
example : FixedBytes.getByte (FixedBytes.ofNat 4 0x12345678) 4 = 0 := by decide
example :
    FixedBytes.ofByteArray? 4 (ByteArray.mk #[0x12, 0x34, 0x56, 0x78]) =
      some (FixedBytes.ofNat 4 0x12345678) := by decide
example :
    (FixedBytes.toByteArray (FixedBytes.ofNat 4 0x12345678)).data =
      #[0x12, 0x34, 0x56, 0x78] := by decide
example (value : FixedBytes 32) :
    FixedBytes.ofByteArray? 32 value.toByteArray = some value :=
  FixedBytes.ofByteArray?_toByteArray value

#synth LawfulBEq (FixedBytes 32)
#synth Hashable (FixedBytes 32)
#synth Ord (FixedBytes 32)

example : H160.ofNat? (2 ^ 160) = none := by decide
example : H160.getByte (H160.ofNat (0xab * 2 ^ 152)) 0 = 0xab := by decide
example (value : H160) : H160.ofByteArray? value.toByteArray = some value :=
  H160.ofByteArray?_toByteArray value
example (a b : H160) : (a &&& b).toNat = a.toNat &&& b.toNat := by
  simp [H160.toNat]

example : H256.ofNat? (2 ^ 256) = none := by decide
example (value : U256) : (H256.ofU256 value).toU256 = value :=
  H256.toU256_ofU256 value
example (value : H256) : H256.ofByteArray? value.toByteArray = some value :=
  H256.ofByteArray?_toByteArray value

example (value : U256) : (Bytes32.ofU256 value).toU256 = value :=
  Bytes32.toU256_ofU256 value
example (value : H256) : (Bytes32.ofH256 value).toH256 = value :=
  Bytes32.toH256_ofH256 value
example (value : Bytes32) : Bytes32.ofByteArray? value.toByteArray = some value :=
  Bytes32.ofByteArray?_toByteArray value

example (value : Address) : Address.ofH160 value.toH160 = value :=
  Address.ofH160_toH160 value
example (value : Address) : Address.ofU256 value.toU256 = value :=
  Address.ofU256_toU256 value
example (value : Address) : Address.ofU256? value.toU256 = some value :=
  Address.ofU256?_toU256 value
example : Address.ofU256? (U256.ofNat (2 ^ 160)) = none := by decide

#synth LawfulBEq H160
#synth LawfulBEq H256
#synth LawfulBEq Bytes32
#synth LawfulBEq Address
#synth Hashable H160
#synth Hashable H256
#synth Hashable Bytes32
#synth Hashable Address
#synth Ord H160
#synth Ord H256
#synth Ord Bytes32
#synth Ord Address

example {bytes : ByteArray} {value : H256} (h : H256.ofByteArray? bytes = some value) :
    value.toByteArray = bytes :=
  H256.toByteArray_ofByteArray?_eq_some h
example {bytes : ByteArray} {value : Address} (h : Address.ofByteArray? bytes = some value) :
    value.toByteArray = bytes :=
  Address.toByteArray_ofByteArray?_eq_some h

end FixedBytesTests
