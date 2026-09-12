#!/usr/bin/env python3
"""Real EELS/Swift differential checks, with explicit observation boundaries.

No arithmetic or gas oracle is transcribed here. Instruction mode invokes upstream handlers;
message mode invokes upstream process_message (including its actual exceptional finalizer).
Swift compares only the common implemented subset, excluding error residuals and halted pc.
"""

import importlib
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent
EELS = ROOT / ".lake/oracles/eels/src"
PYTHON = ROOT / ".lake/eels-venv/bin/python"
SWIFT = ROOT / ".lake/oracles/swift/.build/release/SwiftOracle"


def main():
    if not EELS.is_dir() or not SWIFT.is_file():
        raise SystemExit("Run python3 scripts/prepare_oracles.py first; real oracles are required")
    sys.path.insert(0, str(EELS))
    from ethereum_types.numeric import Uint, U256
    from ethereum.forks.osaka.vm import Evm
    from ethereum.forks.osaka.vm.gas import charge_gas
    from ethereum.forks.osaka.vm.instructions import Ops, op_implementation
    from ethereum.forks.osaka.vm.exceptions import ExceptionalHalt, InvalidOpcode
    from ethereum.forks.osaka.vm.interpreter import process_message
    from ethereum.forks.osaka.state_tracker import BlockState, TransactionState

    assert Path(importlib.import_module(charge_gas.__module__).__file__).is_relative_to(EELS)

    def make_evm(gas, code, stack):
        return Evm(pc=Uint(0), stack=[U256(x) for x in stack], memory=bytearray(),
                   code=bytes(code), gas_left=Uint(gas), valid_jump_destinations=set(),
                   logs=(), refund_counter=0, running=True, message=None, output=b"",
                   accounts_to_delete=set(), return_data=b"", error=None,
                   accessed_addresses=set(), accessed_storage_keys=set())

    def error_name(error):
        return {"StackUnderflowError": "underflow", "OutOfGasError": "oog",
                "InvalidOpcode": "invalid"}[type(error).__name__]

    def upstream_instruction(gas, code, stack, mode):
        evm = make_evm(gas, code, stack)
        try:
            while evm.running and int(evm.pc) < len(code):
                try:
                    opcode = Ops(code[evm.pc])
                except ValueError:
                    raise InvalidOpcode(code[evm.pc]) from None
                op_implementation[opcode](evm)
                if mode == "step":
                    break
        except ExceptionalHalt as error:
            # Only classify here. We do not imitate process_message's finalizer.
            return error_name(error), None, None, None
        stopped = not evm.running or (mode == "run" and int(evm.pc) >= len(code)) or not code
        return ("stopped" if stopped else "running", int(evm.gas_left), int(evm.pc),
                [int(x) for x in evm.stack])

    def upstream_message(gas, code):
        # The selected code never accesses host state or transfers value. A genuine empty
        # transaction overlay is still supplied so EELS runs its real snapshot/restore path.
        state = TransactionState(parent=BlockState(pre_state=None))
        message = SimpleNamespace(tx_env=SimpleNamespace(state=state), depth=Uint(0),
                                  code=bytes(code), gas=Uint(gas), accessed_addresses=set(),
                                  accessed_storage_keys=set(), should_transfer_value=False,
                                  value=U256(0), code_address=None)
        evm = process_message(message)
        return (error_name(evm.error) if evm.error else "stopped", int(evm.gas_left),
                int(evm.pc), [int(x) for x in evm.stack])

    rng = random.Random(20260912)
    cases = []
    for mode in ["step", "run"]:
        for code in [[], [0], [1], [1, 0], [1, 1], [0, 1], [12], [239], [254]]:
            for gas in [0, 2, 3, 4, 6, 2**64 - 1]:
                for stack in [[], [1], [1, 2], [2**256 - 1, 1], [9, 5, 4], [1] * 1024]:
                    cases.append((mode, gas, code, stack))
    for _ in range(200):
        cases.append((rng.choice(["step", "run"]), rng.randrange(20),
                      [1] * rng.randrange(1, 8) + [0],
                      [rng.getrandbits(256) for _ in range(rng.randrange(16))]))

    def encode(case):
        mode, gas, code, stack = case
        return f"{mode}|{gas}|{','.join(map(str, code))}|{','.join(format(x, 'x') for x in stack)}"

    fork_modules = ["frontier", "homestead", "tangerine_whistle", "spurious_dragon",
                    "byzantium", "constantinople", "istanbul", "berlin", "london",
                    "paris", "shanghai", "cancun", "prague", "osaka"]
    decode_rows, decode_expected = [], []
    for i, fork in enumerate(fork_modules):
        ops = importlib.import_module(f"ethereum.forks.{fork}.vm.instructions").Ops
        valid = {x.value for x in ops} - {254}
        for byte in range(256):
            decode_rows.append(f"decode|{i}|{byte}|")
            decode_expected.append("supported" if byte in [0, 1] else
                                   "unsupported" if byte in valid else "invalid")
    charge_rows, charge_expected = [], []
    for budget in [0, 1, 3, 21000, 2**64 - 1]:
        for cost in [0, 1, 3, 21000, 2**64 - 1, 2**64, 2**256]:
            charge_rows.append(f"charge|{budget}|{cost}|")
            evm = make_evm(budget, [], [])
            try:
                charge_gas(evm, Uint(cost))
                charge_expected.append(str(evm.gas_left))
            except ExceptionalHalt:
                charge_expected.append("none")

    rows = list(map(encode, cases))
    with tempfile.TemporaryDirectory(prefix="lean4evm-machine-") as directory:
        inp, out = Path(directory) / "input", Path(directory) / "output"
        inp.write_text("\n".join(rows + decode_rows + charge_rows) + "\n")
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                        "scripts/MachineDiff.lean", str(inp), str(out)], cwd=ROOT, check=True)
        actual = out.read_text().splitlines()
    assert len(actual) == len(rows) + len(decode_rows) + len(charge_rows)
    assert actual[len(rows):len(rows) + len(decode_rows)] == decode_expected, "opcode map mismatch"
    assert actual[-len(charge_rows):] == charge_expected, "charge mismatch"

    swift = subprocess.run([str(SWIFT)], input="\n".join(rows) + "\n", text=True,
                           capture_output=True, check=True).stdout.splitlines()
    assert len(swift) == len(cases)

    def parse(line):
        status, gas, pc, words = line.split("|")
        return status, int(gas), int(pc), [int(x, 16) for x in words.split(",") if x]

    messages = 0
    for i, ((mode, gas, code, stack), lean_line, swift_line) in enumerate(zip(cases, actual, swift)):
        lean, swift_result = parse(lean_line), parse(swift_line)
        expected = upstream_instruction(gas, code, stack, mode)
        assert lean[0] == expected[0] == swift_result[0], (i, "status", lean, expected, swift_result)
        if lean[0] in ["running", "stopped"]:
            assert lean == expected, (i, "EELS success", lean, expected)
            assert (lean[0], lean[1], lean[3]) == (swift_result[0], swift_result[1], swift_result[3])
            if lean[0] == "running":
                assert lean[2] == swift_result[2], (i, "Swift running pc")
        if mode == "run" and not stack:
            full = upstream_message(gas, code)
            assert lean[:2] == full[:2], (i, "real message finalization", lean, full)
            messages += 1
    print(f"machine differential: {len(cases)} real EELS/Swift cases; {messages} real message "
          f"finalizations; {len(decode_rows)} fork/byte classifications; "
          f"{len(charge_rows)} real EELS charges; 0 mismatch")


if __name__ == "__main__":
    if Path(sys.prefix) != PYTHON.parent.parent:
        if not PYTHON.is_file():
            raise SystemExit("Prepare the EELS oracle virtualenv first")
        os.execv(str(PYTHON), [str(PYTHON), __file__])
    main()
