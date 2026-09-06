import Lean4EVM.Primitives.FixedBytes.H160
import Lean4EVM.Primitives.FixedBytes.H256
import Lean4EVM.Primitives.FixedBytes.Bytes32
import Lean4EVM.Primitives.FixedBytes.Address

/-!
# Fixed-size Ethereum byte values

Public entry point for exact-size byte primitives. `Core` owns `FixedBytes size`, big-endian
serialization, and the shared proofs. `H160`, `H256`, `Bytes32`, and `Address` are separate nominal
types whose operations, conversions, and laws remain in their respective modules.

The family is named `FixedBytes` because exact byte width is its defining invariant; equal widths do
not imply semantic interchangeability.
-/
