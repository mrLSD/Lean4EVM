#!/usr/bin/env python3
"""Differential test of Lean4EVM primitives against the EELS reference semantics.

The reference below is transcribed from ethereum/execution-specs
(`forks/osaka/vm/instructions/{arithmetic,bitwise,comparison}.py`) and from the big-endian byte
conventions of `ethereum_types`. Vectors are generated deterministically, evaluated by
`scripts/EelsDiff.lean` through `lake env lean --run`, and every output field is compared.
"""

import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
M = 2**256
M64 = 2**64
SPECIAL = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257,
           2**64 - 1, 2**64, 2**64 + 1, 2**128 - 1, 2**128, 2**128 + 1, 2**192,
           2**255 - 1, 2**255, 2**255 + 1, M - 1, M - 2, M - 2**128, M - 2**64, M - 2**255 + 5]


def random_word(rng):
    k = rng.random()
    if k < 0.3:
        return rng.getrandbits(256)
    if k < 0.45:
        return rng.getrandbits(rng.randint(1, 12))
    if k < 0.6:
        return rng.getrandbits(64)
    if k < 0.7:
        return rng.getrandbits(128)
    if k < 0.8:
        return rng.choice(SPECIAL)
    if k < 0.9:
        return M - 1 - rng.getrandbits(rng.randint(1, 64))
    return rng.getrandbits(rng.randint(1, 255))


def ops_vectors(rng, extra=3000):
    vectors = [(a, b, rng.choice(SPECIAL)) for a in SPECIAL for b in SPECIAL]
    for _ in range(extra):
        c = rng.choice([0, 1, 2, M - 1]) if rng.random() < 0.15 else random_word(rng)
        vectors.append((random_word(rng), random_word(rng), c))
    return vectors


def bytes_vectors(rng, per_size=12):
    vectors = []
    for size in range(0, 41):
        bound = 2 ** (8 * size)
        for _ in range(per_size):
            k = rng.random()
            if k < 0.6:
                n = rng.getrandbits(8 * size) if size else 0
            elif k < 0.8:
                n = rng.getrandbits(8 * size + rng.randint(1, 64))
            else:
                n = rng.choice([0, 1, 255, 256, bound - 1, bound, bound + 1])
            vectors.append((size, n))
    return vectors


# --- EELS reference semantics -------------------------------------------------------------------

def to_signed(x):
    return x if x < 2**255 else x - M


def from_signed(v):
    return v % M


def sign(v):
    return -1 if v < 0 else (0 if v == 0 else 1)


def sdiv(a, b):  # arithmetic.sdiv
    x, y = to_signed(a), to_signed(b)
    if y == 0:
        q = 0
    elif x == -2**255 and y == -1:
        q = -2**255
    else:
        q = sign(x * y) * (abs(x) // abs(y))
    return from_signed(q)


def smod(a, b):  # arithmetic.smod
    x, y = to_signed(a), to_signed(b)
    return from_signed(0 if y == 0 else sign(x) * (abs(x) % abs(y)))


def signextend(byte_num, value):  # arithmetic.signextend
    if byte_num > 31:
        return value
    tail = value.to_bytes(32, "big")[31 - byte_num:]
    if tail[0] >> 7 == 0:
        return int.from_bytes(tail, "big")
    return int.from_bytes(b"\xff" * (32 - (byte_num + 1)) + tail, "big")


def get_byte(index, word):  # bitwise.get_byte
    return 0 if index >= 32 else (word >> ((31 - index) * 8)) & 0xFF


def shl(shift, value):  # bitwise.bitwise_shl
    return (value << shift) % M if shift < 256 else 0


def shr(shift, value):  # bitwise.bitwise_shr
    return value >> shift if shift < 256 else 0


def sar(shift, value):  # bitwise.bitwise_sar
    signed = to_signed(value)
    if shift < 256:
        return from_signed(signed >> shift)
    return 0 if signed >= 0 else M - 1


def ctz64(a):
    return 64 if a == 0 else (a & -a).bit_length() - 1


def rotl64(a, r):
    r %= 64
    return ((a << r) | (a >> (64 - r))) & (M64 - 1) if r else a


OPS = ["add", "sub", "mul", "div", "mod", "sdiv", "smod", "addmod", "mulmod", "exp", "signextend",
       "byte", "shl", "shr", "sar", "lt", "gt", "slt", "sgt", "eq", "iszero", "and", "or", "xor",
       "not", "clz", "neg", "toSignedInt", "ofInt_roundtrip", "u64add", "u64sub", "u64mul",
       "u64checkedAdd", "u64checkedSub", "u64checkedMul", "u64satAdd", "u64satSub", "u64satMul",
       "u64overflowingMul", "u64pow", "u64clz", "u64ctz", "u64popcount", "u64rotl", "low128",
       "high128", "fromU128s", "toHex"]


def expected_ops(a, b, c):
    s = a % 1024
    ua, ub = a % M64, b % M64
    B = lambda x: "1" if x else "0"
    O = lambda ok, v: str(v) if ok else "none"
    return [str((a + b) % M), str((a - b) % M), str((a * b) % M),
            str(0 if b == 0 else a // b), str(0 if b == 0 else a % b),
            str(sdiv(a, b)), str(smod(a, b)),
            str(0 if c == 0 else (a + b) % c), str(0 if c == 0 else (a * b) % c), str(pow(a, b, M)),
            str(signextend(a, b)), str(get_byte(a, b)), str(shl(s, b)), str(shr(s, b)), str(sar(s, b)),
            B(a < b), B(a > b), B(to_signed(a) < to_signed(b)), B(to_signed(a) > to_signed(b)),
            B(a == b), B(a == 0),
            str(a & b), str(a | b), str(a ^ b), str((M - 1) ^ a), str(256 - a.bit_length()),
            str((-a) % M), str(to_signed(a)), str(a),
            str((ua + ub) % M64), str((ua - ub) % M64), str((ua * ub) % M64),
            O(ua + ub < M64, ua + ub), O(ua >= ub, ua - ub), O(ua * ub < M64, ua * ub),
            str(min(ua + ub, M64 - 1)), str(max(ua - ub, 0)), str(min(ua * ub, M64 - 1)),
            B(ua * ub >= M64), str(pow(ua, b % 100, M64)),
            str(64 - ua.bit_length()), str(ctz64(ua)), str(bin(ua).count("1")), str(rotl64(ua, b % 200)),
            str(a % 2**128), str(a // 2**128), str(a), "0x" + format(a, "064x")]


BYTES = ["encode", "value", "decode_roundtrip", "reject_wrong_length", "getByte", "address_low160",
         "address_checked", "h256", "address_bytes", "h256_bytes", "toHex"]


def expected_bytes(size, n):
    v = n % 2 ** (8 * size)
    w = n % M
    return [v.to_bytes(size, "big").hex() or "-", str(v), "1", "1", "1",
            str(w % 2**160), str(w) if w < 2**160 else "none", str(w),
            (w % 2**160).to_bytes(20, "big").hex(), w.to_bytes(32, "big").hex(),
            "0x" + (format(v, "0%dx" % (2 * size)) if size else "")]


def compare(kind, names, vectors, rows, expected):
    mismatches = 0
    for vector, got in zip(vectors, rows):
        want = expected(*vector)
        assert len(want) == len(got) == len(names), (kind, vector, len(want), len(got))
        for name, w, g in zip(names, want, got):
            if w != g:
                mismatches += 1
                if mismatches <= 10:
                    print(f"MISMATCH {kind}.{name} vector={vector} eels={w} lean={g}")
    print(f"{kind}: {len(vectors)} vectors x {len(names)} fields, {mismatches} mismatches")
    return mismatches


def main():
    rng = random.Random(20260904)
    ops, byts = ops_vectors(rng), bytes_vectors(rng)
    with tempfile.TemporaryDirectory() as tmp:
        d = Path(tmp)
        (d / "ops.txt").write_text("".join(f"{a:x} {b:x} {c:x}\n" for a, b, c in ops))
        (d / "bytes.txt").write_text("".join(f"{s} {n:x}\n" for s, n in byts))
        subprocess.run(["lake", "env", "lean", "--run", "scripts/EelsDiff.lean", tmp],
                       cwd=ROOT, check=True)
        rows_ops = [l.split() for l in (d / "ops.out").read_text().splitlines() if l]
        rows_bytes = [l.split() for l in (d / "bytes.out").read_text().splitlines() if l]
    assert len(rows_ops) == len(ops) and len(rows_bytes) == len(byts)
    bad = compare("ops", OPS, ops, rows_ops, expected_ops)
    bad += compare("bytes", BYTES, byts, rows_bytes, expected_bytes)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
