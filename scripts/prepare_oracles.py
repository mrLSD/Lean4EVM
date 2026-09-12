#!/usr/bin/env python3
"""Prepare pinned real EELS/Swift oracles under .lake, never editing their source checkouts.

Uses git archive at fixed revisions: local dirty files cannot silently alter the oracle. In CI,
pass clean source checkouts via EELS_SOURCE and SWIFT_EVM_SOURCE. Dependencies install only into
the local virtualenv; uv project management and global tool upgrades are not needed.
"""

import io
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tomllib

ROOT = Path(__file__).resolve().parent.parent
EELS_REV = "abbe05777ab83fb94ce18c425daaa7ab79e779c1"
SWIFT_REV = "6a37ced490ada61304393f04366a4a0efda44b86"


def export(source, revision, destination, paths):
    destination.mkdir(parents=True, exist_ok=True)
    archive = subprocess.check_output(["git", "-C", str(source), "archive", revision, *paths])
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(destination, filter="data")


def main():
    eels = Path(os.environ.get("EELS_SOURCE", "/Users/evgeny/dev/py/execution-specs"))
    swift = Path(os.environ.get("SWIFT_EVM_SOURCE", "/Users/evgeny/dev/swift/evm-swift"))
    target = ROOT / ".lake/oracles"
    export(eels, EELS_REV, target / "eels", ["src", "pyproject.toml"])
    export(swift, SWIFT_REV, target / "swift", ["Sources"])
    # Rename only the copied module directory; no upstream source text is rewritten.
    interpreter = target / "swift/Sources/Interpreter"
    oracle = target / "swift/Sources/SwiftOracle"
    shutil.copytree(interpreter, oracle, dirs_exist_ok=True)
    for name, dest in [("Package.swift", target / "swift/Package.swift"),
                       ("main.swift", oracle / "main.swift")]:
        shutil.copyfile(ROOT / "scripts/oracles" / name, dest)
    env = dict(os.environ, UV_CACHE_DIR=str(ROOT / ".lake/uv-cache"),
               CLANG_MODULE_CACHE_PATH=str(ROOT / ".lake/clang-cache"))
    python = ROOT / ".lake/eels-venv/bin/python"
    if not python.exists():
        subprocess.run(["uv", "venv", str(python.parent.parent), "--python", "python3"],
                       check=True, env=env)
    project = tomllib.loads((target / "eels/pyproject.toml").read_text())
    subprocess.run(["uv", "pip", "install", "--python", str(python),
                    *project["project"]["dependencies"]], check=True, env=env)
    subprocess.run(["swift", "build", "--package-path", str(target / "swift"),
                    "--disable-sandbox", "-c", "release"], check=True, env=env)
    print(f"Prepared EELS {EELS_REV} and SwiftEVM {SWIFT_REV}")


if __name__ == "__main__":
    main()
