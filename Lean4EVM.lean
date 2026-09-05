import Lean4EVM.Primitives.UInt
import Lean4EVM.Primitives.FixedBytes

/-!
# Lean4EVM

Lean definitions of Ethereum EVM and their verified executable operations.

`Primitives.UInt` and `Primitives.FixedBytes` are family façades. Their `Core` modules own shared
representations and proofs; modules named after public types own width- or meaning-specific APIs.
-/
