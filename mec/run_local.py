#!/usr/bin/env python3
"""User entry point for the existing offline MEC experiment; standard library only.

The underlying world/adversary code is unchanged. Every invocation allocates
new evidence filenames; no previous raw record or log is overwritten.
"""
import argparse
import datetime
import json
from pathlib import Path
import subprocess
import sys
import uuid


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RAW = ROOT / "mec/records"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=256,
                        help="subgroup width; default 256, use 32 for a quick toy smoke test")
    args = parser.parse_args()
    if args.bits < 16:
        parser.error("--bits must be at least 16")

    # Keep printing safe even if the local console cannot display its path.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(errors="backslashreplace")
    RAW.mkdir(parents=True, exist_ok=True)
    while True:
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        name = "mec_h1h2_user_" + stamp + "_" + uuid.uuid4().hex[:8]
        raw = RAW / (name + ".json")
        log_path = RAW / (name + ".log")
        if raw.exists():
            continue
        try:
            log = log_path.open("x", encoding="utf-8", newline="\n")
            break
        except FileExistsError:
            continue

    relative_raw = raw.relative_to(ROOT).as_posix()
    relative_log = log_path.relative_to(ROOT).as_posix()
    command = [sys.executable, "-X", "utf8", "-B", str(HERE / "world.py"),
               "--bits", str(args.bits), "--n", "16", "--seed", "20261009",
               "--b0", "7", "--output", relative_raw]
    status, exit_code = "NOT RUN", 2
    with log:
        log.write("MEC session attacks: local reproduction (artifact)\n")
        log.write("Started UTC: " + datetime.datetime.now(datetime.timezone.utc).isoformat() + "\n")
        shown = ["<python>", *command[1:4], "mec/world.py", *command[5:]]
        log.write("Command argv: " + json.dumps(shown, ensure_ascii=False) + "\n")
        log.write("Working directory: <artifact> (repository root)\n")
        log.write("Execution witness only; see mec/README.md for boundaries.\n")
        log.flush()
        print("Running the existing offline MEC reproduction (bits=" + str(args.bits) + ").", flush=True)
        print("New raw record: " + relative_raw, flush=True)
        try:
            process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                                       errors="backslashreplace")
        except OSError as exc:
            detail = "NOT RUN: could not start Python/world.py: " + str(exc)
            log.write(detail + "\n")
            print(detail, flush=True)
        else:
            for line in process.stdout:
                log.write(line)
                log.flush()
                print(line, end="", flush=True)
            return_code = process.wait()
            log.write("World exit code: " + str(return_code) + "\n")
            status, exit_code = "FAIL", 1
            try:
                evidence = json.loads(raw.read_text(encoding="utf-8"))
                checks = evidence.get("checks", [])
                if return_code == 0 and evidence.get("summary", {}).get("status") == "PASS" and checks and all(
                    item.get("status") == "PASS" for item in checks
                ):
                    status, exit_code = "PASS", 0
            except (OSError, ValueError) as exc:
                log.write("Raw record unavailable or invalid: " + str(exc) + "\n")
        log.write("Launcher result: " + status + "\n")
        log.write("Finished UTC: " + datetime.datetime.now(datetime.timezone.utc).isoformat() + "\n")

    print("RESULT: " + status, flush=True)
    print("Log: " + relative_log, flush=True)
    print("Read mec/README.md for the experiment boundaries.", flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
