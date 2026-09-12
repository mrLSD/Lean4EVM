[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Lean Action CI](https://github.com/mrLSD/Lean4EVM/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mrLSD/Lean4EVM/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.33.1-4B3FA8.svg)](https://lean-lang.org)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.1-2C7A6B.svg)](https://github.com/leanprover-community/mathlib4)

<div align="center">
  <img src=".github/Lean4EVM.png" alt="Lean4EVM" />

  <h1>mrLSD<code>/Lean4EVM</code></h1>
  <p><strong>A pure Lean 4 implementation of the Ethereum Virtual Machine, formally verified in Lean</strong></p>
</div>

---

**Lean4EVM** implements the Ethereum Virtual Machine entirely in Lean 4, so that the executable code
and its correctness proofs are one and the same artifact. Every primitive is a nominal fixed-width
type whose wrapping arithmetic, zero-divisor semantics, byte order and conversion boundaries are
stated as machine-checked theorems instead of assumed, and the semantics are held to the Ethereum
execution specification by a differential test on every commit. The result is meant to serve as both
a reference implementation and the foundation for proving properties of transaction and block
execution.

The interpreter currently executes **STOP and ADD only**, with checked gas, a bounded operand stack,
explicit fork availability and a proved terminating single-frame loop. Other available instructions
return a distinct unsupported result; this is not yet a complete Ethereum executor.
See [interpreter scope, proofs, SwiftEVM correspondence and real-oracle gates](docs/INTERPRETER.md).

## [MIT LICENSE](LICENSE)
