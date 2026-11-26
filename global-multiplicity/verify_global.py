"""Build the reviewed Lean claims from source and rerun independent exact certificates.

Run from any directory with Python 3.9+ and the pinned Lean toolchain on PATH.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCES = HERE / "lean"


def run(args, env=None):
    print("+", " ".join(map(str, args)), flush=True)
    subprocess.run(args, cwd=ROOT, env=env, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true", help="Download pinned mathlib imports first.")
    parser.add_argument("--require-all-n", action="store_true",
                        help="Also require a kernel proof of the full global SharpCount statement.")
    parser.add_argument("--require-third-theorem", action="store_true",
                        help="Require an end-to-end kernel proof of the full third-observation theorem.")
    opts = parser.parse_args()
    files = sorted(SOURCES.glob("*.lean"))
    if not files:
        raise SystemExit("Missing Lean proof sources.")
    tokens = re.compile(r'/\-|\-/|--[^\n]*|"(?:\\.|[^"\\])*"|\b(?:sorry|admit|axiom|unsafe|native_decide)\b')
    for source in files:
        nesting = 0
        for match in tokens.finditer(source.read_text()):
            token = match.group()
            if token == "/-":
                nesting += 1
            elif token == "-/":
                nesting -= 1
            elif not nesting and token[0] not in '-"':
                raise SystemExit(f"{source.name}: disallowed token {token}")
    run(["lake", "env", "lean", "--version"])
    if opts.fetch:
        dependencies = set()
        for f in [*files, *(ROOT / "Chain").glob("*.lean")]:
            dependencies.update(re.findall(r"^import (Mathlib[.\w]*)$", f.read_text(), re.M))
        run(["lake", "build", "+Cache.Main"])
        run(["lake", "env", "lean", "--run", ".lake/packages/mathlib/Cache/Main.lean", "get", *sorted(dependencies)])
    run(["lake", "build", "Chain"])
    with tempfile.TemporaryDirectory(prefix="global-catenary-lean-") as tmp:
        scratch = Path(tmp).resolve()
        env = dict(os.environ, LEAN_PATH=str(scratch))
        # Compile each local import from the sources in this release.
        local_modules = {source.stem for source in files}
        todo = {f.stem: {w for w in re.findall(r"^import (\w+)$", f.read_text(), re.M)
                         if w in local_modules} for f in files}
        done = set()
        while todo:
            ready = sorted(k for k, imports in todo.items() if imports <= done)
            if not ready:
                raise SystemExit(f"Unresolved local imports: {todo}")
            for name in ready:
                run(["lake","env","lean","--root="+str(SOURCES),"-j","2","-s","65536","-o",str(scratch / (name+".olean")),str(SOURCES / (name+".lean"))],env)
                done.add(name)
                del todo[name]
        audit = scratch / "KernelAudit.lean"
        audit.write_text("import Chain.AxiomAudit\n"
                         +"".join(f"import {x}\n" for x in sorted(done))
                         +"#audit_catenary\n"
                         +"#check Catenary.GlobalMultiplicity.SharpCount\n"
                         +"#print axioms Catenary.GlobalMultiplicity.FourAudit.sharp_four_leak_two\n"
                         +"#print axioms Catenary.GlobalFive.five_seed\n"
                         +"#print axioms Catenary.ThirdObservation.uniform_sufficiency\n"
                         +"#print axioms Catenary.ThirdObservation.generic_all_sites\n"
                         +"#print axioms Catenary.ThirdObservation.full_iff_collision_family\n"
                         +"#print axioms Catenary.ThirdObservation.seven_not_uniform\n"
                         +"#print axioms Catenary.ThirdGeneric.generic_physical_unique\n"
                         +"#print axioms Catenary.ThirdExceptional.normalized_slice_two_gains\n")
        run(["lake","env","lean",str(audit)],env)
        bad = scratch / "WrongDet.lean"
        bad.write_text("import GlobalFive\nopen Catenary.GlobalFive\n"
                       "example : (jac first).det = 3457 := first_det\n")
        res = subprocess.run(["lake","env","lean",str(bad)],cwd=ROOT,env=env,
                             capture_output=True,text=True)
        message = (res.stdout+res.stderr).lower()
        if res.returncode == 0 or "type mismatch" not in message or "3457" not in message:
            raise SystemExit("Unexpected negative control result: "+message)
        print("Negative control: Lean rejected 3457 in place of 3456.",flush=True)
        false_unique = scratch / "WrongUniqueness.lean"
        false_unique.write_text("import ThirdObservation\nopen Catenary.ThirdObservation\n"
                                "example : Uniqueness (m:=6) (by decide) 5 4 := seven_not_uniform\n")
        res = subprocess.run(["lake","env","lean",str(false_unique)],cwd=ROOT,env=env,
                             capture_output=True,text=True)
        message = (res.stdout+res.stderr).lower()
        if res.returncode == 0 or "type mismatch" not in message or "uniqueness" not in message:
            raise SystemExit("Unexpected third-output negative control: "+message)
        print("Negative control: Lean distinguished the seven-site collision from uniqueness.",flush=True)
        if opts.require_third_theorem:
            full = scratch / "ThirdClassification.lean"
            full.write_text("".join(f"import {x}\n" for x in sorted(done))
                            +"example : Catenary.ThirdObservation.FullClassification :=\n"
                             "  Catenary.ThirdObservation.fullClassificationVerified\n")
            run(["lake","env","lean",str(full)],env)
        if opts.require_all_n:
            full = scratch / "AllLengths.lean"
            full.write_text("".join(f"import {x}\n" for x in sorted(done))+
                            "example : Catenary.GlobalMultiplicity.SharpCount :=\n"
                            "  Catenary.GlobalMultiplicity.sharpCountVerified\n")
            run(["lake","env","lean",str(full)],env)
    run([sys.executable,str(HERE / "verify_multiplicity.py")])
    print("Passed the stated partial formal audit and exact arithmetic checks.",flush=True)


if __name__ == "__main__":
    main()
