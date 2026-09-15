#!/usr/bin/env python3
"""Build the verification-only Comet WASM and describe it to Sunbeam."""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_DIR = SCRIPT_DIR.parents[1]
EXECUTABLE = "target/wasm32v1-none/release/contracts.wasm"
SOURCES = [
    "contracts/src/*.rs",
    "contracts/src/c_pool/**/*.rs",
    "contracts/src/certora_specs/**/*.rs",
    "contracts/Cargo.toml",
    "Cargo.toml",
    "Cargo.lock",
]
BASE_COMMAND = [
    "cargo",
    "build",
    "--release",
    "--package",
    "contracts",
    "--target",
    "wasm32v1-none",
]


def verification_features(extra_features: str) -> str:
    features = {"certora"}
    features.update(extra_features.replace(",", " ").split())
    return ",".join(sorted(features))


def run_build(show_logs: bool, verbose: bool, extra_features: str):
    env = os.environ.copy()
    env["RUSTFLAGS"] = "-C strip=none"
    command = BASE_COMMAND + ["--features", verification_features(extra_features)]

    if verbose:
        print(f"Running {' '.join(command)} in {PROJECT_DIR}", file=sys.stderr)

    if show_logs:
        result = subprocess.run(command, cwd=PROJECT_DIR, env=env, check=False)
        return None, None, result.returncode

    stdout_file = tempfile.NamedTemporaryFile(
        delete=False, mode="w", prefix="certora_build_", suffix=".stdout"
    )
    stderr_file = tempfile.NamedTemporaryFile(
        delete=False, mode="w", prefix="certora_build_", suffix=".stderr"
    )
    try:
        result = subprocess.run(
            command,
            cwd=PROJECT_DIR,
            env=env,
            stdout=stdout_file,
            stderr=stderr_file,
            text=True,
            check=False,
        )
    finally:
        stdout_file.close()
        stderr_file.close()

    return stdout_file.name, stderr_file.name, result.returncode


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compile Comet's Sunbeam verification artifact"
    )
    parser.add_argument("-o", "--output", metavar="FILE")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("-l", "--log", action="store_true")
    parser.add_argument("-v", "--verbose", action="store_true")
    parser.add_argument(
        "--cargo_features",
        default="",
        help="extra comma- or space-separated Cargo features requested by Certora",
    )
    args = parser.parse_args()

    stdout_log, stderr_log, return_code = run_build(
        args.log, args.verbose, args.cargo_features
    )
    output = {
        "project_directory": str(PROJECT_DIR),
        "sources": SOURCES,
        "executables": EXECUTABLE,
        "success": return_code == 0,
        "return_code": return_code,
        "log": {"stdout": stdout_log, "stderr": stderr_log},
    }

    if args.output:
        Path(args.output).write_text(json.dumps(output, indent=4) + "\n")
    if args.json:
        print(json.dumps(output, indent=4))

    return 0 if return_code == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
