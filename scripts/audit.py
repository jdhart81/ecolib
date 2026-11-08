#!/usr/bin/env python3
"""Re-run EcoLib's axiom audit after `lake build`.

For every module in provenance/modules.json, Lean lists the constants the module declares
and the axioms each depends on. The audit fails if any constant uses an axiom other than
propext, Quot.sound and Classical.choice, or if a theorem stated in a module's source
(``stated`` in provenance/theorems.jsonl) is missing. Lemmas Lean generates on demand,
such as ``congr_simp``, belong to whichever module first needs them, so they are not
compared by module. Written by the viridis-engine `ecolib` workflow.
"""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ELAB = """import Lean
{imports}
open Lean Elab Command

elab "#ecolib_audit " id:ident : command => do
  let env ← getEnv
  let m := id.getId
  let some idx := env.getModuleIdx? m | throwError "ECOLIB_NO_MODULE {{m}}"
  let ok := [``propext, ``Quot.sound, ``Classical.choice]
  let mut nThm := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some idx then continue
    let axs ← liftCoreM (Lean.collectAxioms n)
    let bad := axs.toList.filter (fun a => !ok.contains a)
    if !bad.isEmpty then
      logInfo m!"ECOLIB_BAD {{m}} {{n}}|{{",".intercalate (bad.map toString)}}"
    if n.isInternal then continue
    match ci with
    | .thmInfo _ =>
      nThm := nThm + 1
      logInfo m!"ECOLIB_THM {{m}} {{n}}|{{",".intercalate (axs.toList.map toString)}}"
    | _ => pure ()
  logInfo m!"ECOLIB_DONE {{m}} {{nThm}}"

{commands}
"""


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    modules = [m["module"] for m in json.loads((root / "provenance/modules.json").read_text())["modules"]]
    expected: dict[str, set[str]] = {m: set() for m in modules}
    for line in (root / "provenance/theorems.jsonl").read_text().splitlines():
        if line.strip():
            t = json.loads(line)
            if t.get("stated", True):
                expected.setdefault(t["module"], set()).add(t["name"])
    src = ELAB.format(imports="".join(f"import {m}\n" for m in modules),
                      commands="".join(f"#ecolib_audit {m}\n" for m in modules))
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "EcoLibAudit.lean"
        path.write_text(src, encoding="utf-8")
        proc = subprocess.run(["lake", "env", "lean", "--json", str(path)], cwd=root, capture_output=True, text=True)
    found: dict[str, set[str]] = {m: set() for m in modules}
    done: set[str] = set()
    problems: list[str] = []
    for line in proc.stdout.splitlines():
        if not line.startswith("{"):
            continue
        msg = json.loads(line)
        data = str(msg.get("data", ""))
        if msg.get("severity") == "error":
            problems.append(data[:300])
            continue
        tag, _, rest = data.partition(" ")
        mod, _, rest = rest.partition(" ")
        if tag == "ECOLIB_BAD":
            problems.append(f"{mod}: {rest}")
        elif tag == "ECOLIB_THM":
            found.setdefault(mod, set()).add(rest.partition("|")[0])
        elif tag == "ECOLIB_DONE":
            done.add(mod)
    for m in modules:
        if m not in done:
            problems.append(f"{m}: no audit report")
        elif expected.get(m, set()) - found[m]:
            missing = sorted(expected.get(m, set()) - found[m])
            problems.append(f"{m}: stated theorems missing from the build: {missing[:3]} "
                            f"(see provenance/theorems.jsonl)")
    if proc.returncode != 0 and not problems:
        problems.append(proc.stderr[-500:] or "lean failed")
    n = sum(len(v) for v in found.values())
    if problems:
        print("\n".join(problems[:50]))
        print(f"axiom audit FAILED ({len(problems)} problems)")
        return 1
    print(f"axiom audit passed: {len(modules)} modules, {n} theorems, only propext, Quot.sound, Classical.choice")
    return 0


if __name__ == "__main__":
    sys.exit(main())
