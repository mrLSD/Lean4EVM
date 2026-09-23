# Verified interpreter: first increment

## Scope and observation boundary

Executable legacy instructions: **STOP and ADD only**. No memory, storage, host callbacks, CALL,
transaction decoding or refund accounting is implemented. HardFork describes opcode availability,
not a mainnet activation schedule or full historical-fork support. `pc : Nat` and `Gas.remaining :
U64` are explicit representation choices; unrestricted EELS states above the budget width are
outside the production interface. Costs remain `Nat` and are never narrowed before comparison.

`Unsupported byte` is an implementation boundary, not an Ethereum exceptional halt. Execution
terminates there without claiming a protocol result. Undefined/inactive instructions and explicit
INVALID instead produce `failed (invalidOpcode byte)` and consume the remaining frame budget.

The array stack is bottom-to-top and carries its `size ≤ 1024` invariant. Pure state transitions
preserve the recognizable SwiftEVM flow without mutable object aliases or unsafe memory.
`Machine/Basic.lean` owns the frame state that the handlers and the dispatcher importing them
share. It is Swift's `Machine`, not its transaction-scoped `ExecutionState`.

## Source-to-source map

Swift references below are pinned to `6a37ced490ada61304393f04366a4a0efda44b86`.
EELS references are pinned to `abbe05777ab83fb94ce18c425daaa7ab79e779c1` (Osaka).
Oracle preparation reads the checkouts named by `SWIFT_EVM_SOURCE` and `EELS_SOURCE`, exports those
pinned commits rather than local uncommitted edits, and does not write into either checkout. The
SwiftEVM pin is currently reachable only from a feature branch, so it must be re-pinned once that
work lands on the default branch.

| Responsibility | Lean implementation / contract | Swift source and retained design |
|---|---|---|
| Revision selection | `Interpreter/HardFork.lean`: `HardFork`, `rank`, inherited linear order | [HardFork.swift:1](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/HardFork.swift#L1): same revision names; Lean uses one ordered API and requires an explicit fork. |
| Machine state | `Interpreter/Machine/Basic.lean`: `Machine`, `MachineStatus`, `ExitError` | [Machine.swift:16](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Machine.swift#L16): code, pc, stack, gas, fork and execution status retain their responsibilities; unused context fields are omitted. |
| Single step | `Interpreter/Machine.lean`: `step`, `step_stop`, `step_add`, `step_endOfCode` | [Machine.step:425](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Machine.swift#L425): fetch → decode → handler → next state. Lean uses a match instead of a closure table. |
| Run loop | `Machine.evalLoop`, `evalLoop_halted`, `evalLoop_step`, `evalLoop_eq_of_halted_iterate` | [Machine.evalLoop:477](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Machine.swift#L477): repeatedly step until termination. Lean uses kernel-checked well-founded recursion, without fuel or execution replacement. |
| Stack | `Interpreter/Stack.lean`: `push`, `pop`, `popTwo`, `peek`, shape/underflow laws | [MachineStack.swift:4](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/MachineStack.swift#L4): array, top at the end, 1024-word limit. Two-pop shape proves that ADD's result fits without a redundant overflow check. |
| Gas | `Interpreter/Gas.lean`: `charge`, `charge_spec`, `charge_toNat`, `charge_lt`, `GasConstant.veryLow` | [Gas.recordCost:71](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Gas.swift#L71) and [GasConstant.VERYLOW:139](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Gas.swift#L139): checked budget consumption and tier-named prices. Lean accepts natural costs, including costs too large for U64. |
| STOP | `Instructions/Control.lean`: `stop`, `stop_spec` | [ControlInstructions.stop:24](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Instructions/Control.swift#L24): successful termination without charging gas. |
| ADD | `Instructions/Arithmetic.lean`: `add`, `add_spec`, `add_success_iff`, `add_stack_effect` | [ArithmeticInstructions.add:18](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Instructions/Arithmetic.swift#L18): check operands → charge → modular sum → push result. Pure failure does not expose partially consumed stack. |

### Deliberate differences

- Explicit STOP increments pc, following [EELS stop:25](https://github.com/ethereum/execution-specs/blob/abbe05777ab83fb94ce18c425daaa7ab79e779c1/src/ethereum/forks/osaka/vm/instructions/control_flow.py#L25).
  Swift leaves terminal pc unchanged. Falling off the code does not increment pc.
- Lean finalizes exceptional halts immediately in `Machine.fail`, with zero remaining gas.
  [EELS process_message:291](https://github.com/ethereum/execution-specs/blob/abbe05777ab83fb94ce18c425daaa7ab79e779c1/src/ethereum/forks/osaka/vm/interpreter.py#L291)
  does so in its exception handler. Swift's instruction layer only reports the error; its
  [Executor.execute:14](https://github.com/mrLSD/evm-swift/blob/6a37ced490ada61304393f04366a4a0efda44b86/Sources/Interpreter/Executor.swift#L14)
  is not a completed frame finalizer.
- [EELS add:27](https://github.com/ethereum/execution-specs/blob/abbe05777ab83fb94ce18c425daaa7ab79e779c1/src/ethereum/forks/osaka/vm/instructions/arithmetic.py#L27)
  removes operands before charging. Swift/Lean preserve the original operand stack on failure.
  Failed-frame stack/pc are diagnostic, not compared as protocol outputs. Error category is compared;
  finalized gas is compared against the actual EELS message path, not normalized away.
- Terminal Lean machines are fixed points under step; there is no implicit restart.
- No Swift Runtime, Executor, Backend, memory pointers or declaration-generating macros were copied.

## Verification contracts and Yellow Paper review

The [Yellow Paper instruction set](https://github.com/ethereum/yellowpaper/blob/master/Paper.tex)
defines STOP's zero cost, ADD's 2→1 stack effect and modulo-2^256 result, and the very-low gas tier.
Its execution model supplies the stack bound, exceptional-halt conditions and end-of-code STOP.
These applicable rules are connected to executable definitions by the named Lean contracts above;
`step_invariants` and `evalLoop_invariants` additionally preserve code/fork and prohibit gas creation.

This is a reviewed semantic mapping, not an automated proof about the LaTeX document. The Yellow
Paper is not a complete Osaka oracle. New revision-dependent availability is checked against EELS.
No claim is made that testing Python/Swift proves their formal equivalence to Lean.

The terminating loop uses the strict decrease from successful ADD (three gas). STOP, exceptional
halt, end-of-code and Unsupported terminate. This proof is for the current **single-frame subset**;
it is not reused as a proof of a future nested CALL executor without additional reasoning.

Proof-quality review: ADD reuses `Stack.popTwo_spec` and `Gas.charge_spec`; arithmetic reuses the
existing `FixedUInt.toNat_add`. Stack reconstruction uses `Array.back?_eq_some_iff`. Whole execution
properties reuse the one-step contracts. The 1024-word boundary example uses the semantic size law
instead of expanding a large concrete proof term. Tests contain separate execution/proof sections.

## Running the gates

Requirements: Lean/Lake, Python ≥3.11, uv, Swift ≥6.0, and the two reference git checkouts containing
the pinned commits. CI prepares them explicitly. macOS is the tested Swift-oracle platform.

```console
export EELS_SOURCE=/path/to/execution-specs SWIFT_EVM_SOURCE=/path/to/evm-swift
make prepare-oracles   # explicit network/dependency preparation, writes only under .lake
make check             # all old gates plus the real machine differential gate
```

Both source variables are required; there is no implicit default, so the gate cannot read an
unrelated working copy. `make check` first verifies that the prepared oracles exist and otherwise
fails immediately with the preparation command, rather than after the build; preparation itself is
never run implicitly. `make prepare-oracles-eels` and `make machine-diff-eels` select the Python
oracle alone. The Makefile serves local development; CI performs its own explicit checkouts and
preparation steps and runs the Python oracle on every pull request, the Swift comparator on master
and on demand. No global uv upgrade is required.

The Lean adapters run with `LEAN_ABORT_ON_PANIC=1`, so a `panic!` aborts the gate instead of
returning a default value with exit code 0. `scripts/MachineDiff.lean` parses every field with
checked readers, and `machine_diff.py` confirms that an oversized opcode byte, a malformed decimal,
a malformed hexadecimal word and an unknown mode are each rejected. The real gate refuses to skip missing oracles. EELS is imported from the pinned
export, not a possibly unrelated installed `ethereum` package. The Swift harness compiles unchanged
upstream interpreter sources in its own executable module, avoiding upstream visibility changes.
Its fork is explicitly Osaka; comparisons cover only the actually shared instruction subset.

`scripts/machine_diff.py` checks:

- instruction / initial-state execution: real EELS handlers and Swift step/evalLoop, with preset stacks;
- real EELS `process_message` snapshot/finalization for empty-stack message inputs;
- all 256 bytes across 14 revisions, using each upstream EELS `Ops` enumeration;
- actual EELS `charge_gas`, including natural costs above the 64-bit budget range.

Full-message successful ADD is deliberately **not** claimed: real messages start with an empty
stack and need PUSH, which is outside this increment. Successful ADD is compared at the initialized
machine/handler boundary. No handwritten replacement for the EELS finalizer is used.

Success compares gas, stack and pc against EELS; Swift excludes only terminal pc. Exceptions compare
classes; EELS full-message cases additionally compare finalized gas. Raw exceptions are never used
to assert a finalized gas value. The older primitive transcription gate remains separate.

The matrix includes exact/insufficient/zero/maximal gas, modular overflow, stack sizes 0/1/2/1024,
short programs, undefined bytes, explicit INVALID, and Prague/Osaka CLZ classification. Unsupported
MUL and inactive/unsupported CLZ also have kernel-checked regression examples.

