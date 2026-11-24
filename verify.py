"""Rebuild the formalization, audit its logical dependencies, and test false controls."""
import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def source_checks():
    # Check every proof module will be imported when the kernel audit runs.
    modules = {file.stem: file for file in (ROOT / "Chain").glob("*.lean")}
    seen = set()
    todo = [ROOT / "Chain.lean"]
    while todo:
        file = todo.pop()
        for name in re.findall(r"^import Chain\.(\w+)\s*$", file.read_text(encoding="utf-8"), re.M):
            if name not in seen:
                seen.add(name)
                todo.append(modules[name])
    if set(modules) != seen:
        raise SystemExit("proof modules outside audit import graph: " + ", ".join(sorted(set(modules) - seen)))
    # Skip Lean strings and arbitrarily nested block comments.
    token = re.compile(r'/\-|\-/|--[^\n]*|"(?:\\.|[^"\\])*"|\b(?:sorry|admit|axiom|unsafe|native_decide)\b')
    for file in [*sorted((ROOT / "Chain").glob("*.lean")), ROOT / "Chain.lean", ROOT / "Audit.lean"]:
        depth = 0
        for match in token.finditer(file.read_text(encoding="utf-8")):
            word = match[0]
            if word == "/-":
                depth += 1
            elif word == "-/":
                depth -= 1
            elif depth == 0 and word[0] not in '-"':
                raise SystemExit(f"disallowed source token {word} in {file.name}")
    print("Source check passed. The kernel dependency audit follows.", flush=True)


def reject(source, expected_diagnostic):
    with tempfile.TemporaryDirectory(prefix="catenary-lean-control-") as temp:
        target = Path(temp) / "Control.lean"
        target.write_text(source, encoding="utf-8")
        test = subprocess.run(["lake", "env", "lean", str(target)], cwd=ROOT,
                              text=True, capture_output=True)
    message = test.stdout + test.stderr
    if test.returncode == 0 or expected_diagnostic not in message:
        raise SystemExit("unexpected negative control result:\n" + message)
    print(f"Negative control rejected as expected ({expected_diagnostic}).", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true",
                        help="Fetch the pinned mathlib binary cache before building.")
    parser.add_argument("--require-classification", action="store_true",
                        help="Require an end-to-end proof of the stated all-n classification.")
    args = parser.parse_args()
    run("lake", "env", "lean", "--version")
    source_checks()
    if args.fetch:
        imports = {line.split()[1] for file in (ROOT / "Chain").glob("*.lean")
                   for line in file.read_text(encoding="utf-8").splitlines()
                   if line.startswith("import Mathlib.")}
        run("lake", "build", "+Cache.Main")
        run("lake", "env", "lean", "--run",
            ".lake/packages/mathlib/Cache/Main.lean", "get", *sorted(imports))
    run("lake", "build", "Chain")
    run("lake", "env", "lean", "Audit.lean")
    run(sys.executable, "four_chambers.py")
    reject("import Chain.Placement\n"
           "example : Catenary.placement 7 1 4 7 := by unfold Catenary.placement; decide\n",
           "is false")
    reject("import Chain.Four\n"
           "example : (Catenary.Four.jacobian 0 Catenary.Four.witnessZ).det = -311041 := by\n"
           "  rw [Catenary.Four.integer_certificates]; decide\n",
           "is false")
    reject("import Chain.AxiomAudit\n"
           "axiom DeliberateExternalFalseAssumption : False\n"
           "theorem Catenary.auditNegativeControl : False := DeliberateExternalFalseAssumption\n"
           "#audit_catenary\n", "depends on disallowed axiom")
    if args.require_classification:
        # The kernel must see an actual proof with exactly the requested type.
        with tempfile.TemporaryDirectory(prefix="catenary-full-check-") as temp:
            target = Path(temp) / "Full.lean"
            target.write_text("import Chain\nexample : Catenary.PhysicalClassification :=\n"
                              "  Catenary.physicalClassificationVerified\n", encoding="utf-8")
            run("lake", "env", "lean", str(target))
    print("Verified the complete physical classification, its boundary examples and negative controls.",
          flush=True)


if __name__ == "__main__":
    main()
