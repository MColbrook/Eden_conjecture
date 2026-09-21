"""Check the axiom reports for all final and supporting theorems."""

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
EMPTY_REPORT = re.compile(r"'([^']+)' does not depend on any axioms")


def check(path: str, count: int) -> None:
    expected = re.findall(r"^#print axioms (\S+)\s*$", (ROOT / path).read_text(encoding="utf-8"), re.M)
    if len(expected) != count or len(set(expected)) != count:
        raise SystemExit(f"Unexpected declaration list in {path}")
    result = subprocess.run(
        ["lake", "env", "lean", path], cwd=ROOT, text=True,
        encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    print(result.stdout, end="")
    if result.returncode:
        raise SystemExit(result.returncode)
    reports = REPORT.findall(result.stdout)
    names = [name for name, _ in reports] + EMPTY_REPORT.findall(result.stdout)
    if len(names) != count or set(names) != set(expected):
        raise SystemExit(f"Incomplete axiom report for {path}")
    for name, axioms in reports:
        used = {item.strip() for item in axioms.split(",") if item.strip()}
        if not used <= ALLOWED:
            raise SystemExit(f"Unexpected axioms for {name}: {sorted(used - ALLOWED)}")
    print(f"PASS: {path}: {count} declarations; all axioms permitted.")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    check("checks/FinalAxioms.lean", 219)
    check("checks/SupportingAxioms.lean", 777)
    check("checks/PalomarAxioms.lean", 1)
