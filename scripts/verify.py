#!/usr/bin/env python3
"""Serial, pinned, repository-local verification of the complete formalization.

Only .lake/, verification/runs/ and the verification lock are written. The
source manifest is a provenance/inventory check, not a substitute for Lean.
Each run gets new evidence; no historical certificate is overwritten.
"""
from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import json
import os
from pathlib import Path
import re
import resource
import secrets
import shutil
import signal
import sys

import resource_guard as guard

ROOT = Path(__file__).resolve().parents[1]
V = ROOT / "verification"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXCLUDED_DISCOVERY_DIRS = {".lake", ".git", "__pycache__"}
PARTIAL_HELPERS = {
    "BestOfBothWorlds.AdaptiveBanditProcess.ObservedHistory._unsafe_rec",
    "BestOfBothWorlds.AdaptiveBanditProcess.Trajectory._unsafe_rec",
    "BestOfBothWorlds.AdaptiveBanditProcess.observe._unsafe_rec",
    "BestOfBothWorlds.AdaptiveBanditProcess.observedHistoryMeasurableSpace._unsafe_rec",
    "BestOfBothWorlds.AdaptiveBanditProcess.trajectoryLaw_isProbabilityMeasure._unsafe_rec",
    "BestOfBothWorlds.AdaptiveBanditProcess.trajectoryMeasurableSpace._unsafe_rec",
    "BestOfBothWorlds.SeededLearner.Learner.play._unsafe_rec",
}


def read_json(path):
    return json.loads(path.read_text())


def strip_lean_comments_strings(text):
    """Preserve line positions while dropping nested comments and strings.

    This conservative static screen complements, and never replaces, the
    compiled-environment axiom/dependency inspection and kernel replay.
    """
    out = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise RuntimeError("Unclosed source comment/string")
    return "".join(out)


def discovered_sources():
    result = set()
    for parent, dirs, files in os.walk(ROOT, followlinks=False):
        rel = Path(parent).relative_to(ROOT)
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED_DISCOVERY_DIRS)
        if rel == Path("verification"):
            dirs[:] = [d for d in dirs if d != "runs"]
        linked = [d for d in dirs if (Path(parent) / d).is_symlink()]
        if linked:
            raise RuntimeError("Unrecognized source-directory symlink(s): " +
                               repr([(rel / d).as_posix() for d in linked]))
        for filename in files:
            if filename.endswith(".lean"):
                path = Path(parent) / filename
                if path.is_symlink():
                    raise RuntimeError("Lean source symlink is not allowed: " + str(path.relative_to(ROOT)))
                result.add(path.relative_to(ROOT).as_posix())
    return result


def inventory():
    manifest = read_json(V / "source-manifest.json")
    modules = manifest["modules"]
    expected_sources = set(modules.values()) | set(manifest["auxiliary_sources"])
    actual_sources = discovered_sources()
    if actual_sources != expected_sources:
        raise RuntimeError("Lean inventory mismatch; unrecognized=" +
                           repr(sorted(actual_sources - expected_sources)) +
                           "; missing=" + repr(sorted(expected_sources - actual_sources)))
    for rel, expected in manifest["files"].items():
        path = ROOT / rel
        if not path.is_file() or path.is_symlink():
            raise RuntimeError("Missing/nonregular pinned source or configuration: " + rel)
        if guard.sha256(path) != expected["sha256"] or path.stat().st_size != expected["bytes"]:
            raise RuntimeError("Source/configuration differs from audited baseline: " + rel)
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Unexpected Lean toolchain pin")
    deps = {}
    mathlib = set()
    findings = []
    for rel in sorted(expected_sources):
        code = strip_lean_comments_strings((ROOT / rel).read_text())
        pattern = r"\b(?:sorry|admit|axiom|unsafe|partial|native_decide|run_elab|run_cmd|elab|implemented_by|extern|initialize|builtin_initialize)\b"
        for match in re.finditer(pattern, code):
            findings.append({"source": rel, "line": code.count("\n", 0, match.start()) + 1,
                             "token": match.group()})
        for match in re.finditer(r"\b(?:Lean\.)?(?:addDecl|addAndCompile|evalConst|ofReduceBool)\b", code):
            findings.append({"source": rel, "line": code.count("\n", 0, match.start()) + 1,
                             "token": match.group()})
        imported = re.findall(r"(?m)^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)", code)
        module = next((n for n, p in modules.items() if p == rel), None)
        if module:
            deps[module] = sorted(set(n for n in imported if n.startswith("BestOfBothWorlds.")))
            for dep in deps[module]:
                if dep not in modules:
                    raise RuntimeError("Unrecognized local dependency: " + dep)
        mathlib.update(n for n in imported if n.startswith("Mathlib."))
    if findings:
        raise RuntimeError("Unproved/unsafe/metaprogramming source screen failed: " + json.dumps(findings))
    root_code = strip_lean_comments_strings((ROOT / "BestOfBothWorlds.lean").read_text())
    if any(not re.fullmatch(r"\s*(?:module|public import BestOfBothWorlds\.[\w.]+)?\s*", line)
           for line in root_code.splitlines()):
        raise RuntimeError("Import-only root now contains an unrecognized command/declaration")
    order = []
    pending = dict(deps)
    while pending:
        ready = sorted(n for n, ds in pending.items() if all(d in order for d in ds))
        if not ready:
            raise RuntimeError("Project import cycle: " + repr(pending))
        order.extend(ready)
        for n in ready:
            del pending[n]
    declared_imports = (V / "mathlib-imports.txt").read_text().splitlines()
    if sorted(mathlib) != declared_imports:
        raise RuntimeError("Direct Mathlib import inventory mismatch")
    return {"modules": modules, "dependencies": deps, "topological_order": order,
            "mathlib_imports": declared_imports, "static_findings": findings,
            "source_files": len(expected_sources), "pinned_files": manifest["files"]}


def inspection_header(order):
    return ("module\n\nimport Lean.Util.FoldConsts\n\n" +
            "\n".join("import all " + name for name in order) +
            "\n\nset_option pp.all true\nset_option pp.proofs true\n"
            "set_option pp.maxSteps 1000000\nset_option format.width 120\n\n")


DECLARATIONS = '''run_cmd do
  let env ← Lean.getEnv
  let entries := env.constants.toList.filter fun (name, _) =>
    let s := name.toString
    s.startsWith "BestOfBothWorlds." || s.startsWith "_private.BestOfBothWorlds."
  let entries := entries.toArray.qsort fun a b => Lean.Name.lt a.1 b.1
  let mut theorems : Nat := 0
  for (name, info) in entries do
    let kind := if info.isTheorem then "theorem" else "other"
    Lean.logInfo m!"AUDIT_DECL={name} KIND={kind} UNSAFE={info.isUnsafe} PARTIAL={info.isPartial}"
    Lean.logInfo m!"{name} : {info.type}"
    let axioms ← Lean.collectAxioms name
    Lean.logInfo m!"AUDIT_AXIOMS {name}: {axioms.qsort Lean.Name.lt |>.map Lean.MessageData.ofConstName |>.toList}"
    if info.isTheorem then theorems := theorems + 1
  Lean.logInfo m!"AUDIT_TOTAL={entries.size} THEOREMS={theorems}"
'''

SAFETY = '''run_cmd do
  let env ← Lean.getEnv
  let mut safeCount : Nat := 0
  let mut badCount : Nat := 0
  for (name, info) in env.constants.toList do
    let s := name.toString
    if (s.startsWith "BestOfBothWorlds." || s.startsWith "_private.BestOfBothWorlds.") &&
        !info.isUnsafe && !info.isPartial then
      safeCount := safeCount + 1
      for used in info.getUsedConstantsAsSet do
        if let some dep := env.find? used then
          if dep.isUnsafe || dep.isPartial then
            badCount := badCount + 1
            Lean.logError m!"AUDIT_BAD_DEPENDENCY {name} -> {used}"
  Lean.logInfo m!"AUDIT_SAFE_CONSTANTS={safeCount} BAD_DEPENDENCIES={badCount}"
'''


class Verification:
    def __init__(self, args, inv):
        self.args = args
        self.inventory = inv
        stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        self.run_dir = V / "runs" / (stamp + f"-{os.getpid()}-" + secrets.token_hex(3))
        self.run_dir.mkdir(parents=True, exist_ok=False)
        (self.run_dir / "logs").mkdir()
        self.state = {"status": "running", "started_utc": guard.now(),
                      "phase": args.phase, "prepare_only": args.prepare_only,
                      "run_directory": self.relative(self.run_dir), "commands": [],
                      "limits": {"concurrent_owned_groups": 1, "LEAN_NUM_THREADS": "1",
                                 "aggregate_rss_watchdog_bytes": 6 * guard.GIB,
                                 "pre_command_MemAvailable_bytes": 7 * guard.GIB,
                                 "runtime_MemAvailable_floor_bytes": guard.GIB,
                                 "cpu_seconds_per_process": 600, "wall_seconds_per_command": 900,
                                 "core_dump_bytes": 0, "RLIMIT_AS": "unchanged; must be unlimited"},
                      "kernel_scope": "Exact project leaf modules, including all proof-bearing private/server parts; imported libraries trusted; no --fresh"}
        self.state["verification_input_sha256"] = {
            rel: guard.sha256(ROOT / rel) for rel in (
                "scripts/verify.sh", "scripts/verify.py", "scripts/resource_guard.py",
                "verification/source-manifest.json", "verification/expected-declarations.json",
                "verification/endpoints.json", "verification/mathlib-imports.txt")}
        self.env = os.environ.copy()
        self.env["LEAN_NUM_THREADS"] = "1"
        # Prevent a development-shell override from silently replacing pins.
        for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_HOME", "LAKE_PATH",
                     "LAKE_PACKAGE_OVERRIDES", "ELAN_TOOLCHAIN"):
            self.env.pop(name, None)
        self.save()
        guard.atomic_json(self.run_dir / "modules.json", inv)

    def relative(self, path):
        return Path(path).relative_to(ROOT).as_posix()

    def save(self):
        guard.atomic_json(self.run_dir / "status.json", self.state)

    def run(self, label, command):
        if guard.available_bytes() < 7 * guard.GIB:
            raise RuntimeError("Need at least 7 GiB MemAvailable before " + label)
        item = {"module": label, "command": [str(x) for x in command], "status": "pending"}
        self.state["commands"].append(item)
        print("START " + label, flush=True)
        log = self.run_dir / "logs" / (label + ".log")
        guard.replay_module(item, self.env, log, 6 * guard.GIB, self.save)
        # Guard uses absolute paths internally; durable evidence is repository-relative.
        item["log"] = self.relative(log)
        self.save()
        print("END " + label + ": " + item["status"] +
              f" ({item['elapsed_seconds']}s)", flush=True)
        if item["status"] != "passed":
            raise RuntimeError(label + " failed: " + item.get("reason", "exit " + str(item.get("exit_code"))) +
                               "; see " + self.relative(log))
        return log.read_text().split("\n", 1)[1]

    def tools(self):
        lean_on_path = shutil.which("lean")
        lake_on_path = shutil.which("lake")
        if not lean_on_path or not lake_on_path:
            raise RuntimeError("lean and lake must be on PATH; install/select the pinned elan toolchain")
        version = self.run("lean-version", [lean_on_path, "--version"]).strip()
        if "version 4.35.0," not in version or ("commit " + LEAN_COMMIT) not in version:
            raise RuntimeError("Wrong Lean installation: " + version)
        prefix = Path(self.run("lean-prefix", [lean_on_path, "--print-prefix"]).strip()).resolve()
        self.lean = prefix / "bin/lean"
        self.lake = prefix / "bin/lake"
        self.checker = prefix / "bin/leanchecker"
        for path in (self.lean, self.lake, self.checker):
            if not path.is_file() or not os.access(path, os.X_OK):
                raise RuntimeError("Pinned installation lacks required executable: " + str(path))
        lake_version = self.run("lake-version", [self.lake, "--version"]).strip()
        if "Lean version 4.35.0" not in lake_version or "eb6cafb" not in lake_version:
            raise RuntimeError("Wrong Lake installation: " + lake_version)
        self.env["PATH"] = str(prefix / "bin") + os.pathsep + self.env.get("PATH", "")
        self.state["versions"] = {"lean": version, "lake": lake_version}
        self.state["toolchain_sha256"] = {"bin/" + p.name: guard.sha256(p)
                                          for p in (self.lean, self.lake, self.checker)}
        self.save()

    def unchanged_pins(self):
        for rel, old in self.inventory["pinned_files"].items():
            if guard.sha256(ROOT / rel) != old["sha256"]:
                raise RuntimeError("Pinned source/configuration changed during verification: " + rel)
        for rel, old in self.state["verification_input_sha256"].items():
            if guard.sha256(ROOT / rel) != old:
                raise RuntimeError("Verification script/inventory changed during run: " + rel)

    def dependency_check(self, label):
        data = read_json(ROOT / "lake-manifest.json")
        packages = data["packages"]
        if len(packages) != 9 or data["packagesDir"] != ".lake/packages":
            raise RuntimeError("Unexpected dependency manifest layout")
        if (ROOT / ".lake").is_symlink() or (ROOT / ".lake/packages").is_symlink():
            raise RuntimeError("Linked .lake/package directories are not an independent checkout")
        rows = []
        for package in sorted(packages, key=lambda x: x["name"]):
            if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
                raise RuntimeError("Unpinned/non-git dependency: " + package["name"])
            rel = ".lake/packages/" + package["name"]
            path = ROOT / rel
            git_dir = path / ".git"
            if path.is_symlink() or not path.is_dir() or git_dir.is_symlink() or not git_dir.is_dir():
                raise RuntimeError("Missing or linked dependency checkout: " + rel)
            head = self.run(label + "-head-" + package["name"],
                            ["git", "--no-optional-locks", "-C", rel, "rev-parse", "HEAD"]).strip()
            if head != package["rev"]:
                raise RuntimeError("Dependency revision mismatch: " + package["name"] + " " + head)
            dirty = self.run(label + "-dirty-" + package["name"],
                             ["git", "--no-optional-locks", "-C", rel, "diff", "--name-only", "HEAD", "--"]).strip()
            if dirty:
                raise RuntimeError("Modified tracked dependency sources: " + package["name"] + ": " + dirty)
            untracked = self.run(label + "-extra-" + package["name"],
                                 ["git", "--no-optional-locks", "-C", rel, "ls-files", "--others",
                                  "--exclude-standard", "--", "*.lean", "lean-toolchain", "lake-manifest.json",
                                  "lakefile.toml", "lakefile.lean"]).strip()
            if untracked:
                raise RuntimeError("Untracked dependency source/configuration files: " + package["name"] + ": " + untracked)
            rows.append({"name": package["name"], "revision": head, "url": package["url"],
                         "tracked_sources_clean": True, "untracked_source_overrides": []})
        self.unchanged_pins()
        guard.atomic_json(self.run_dir / (label + "-dependencies.json"), rows)

    def prepare(self):
        if not self.args.skip_prepare:
            self.run("resolve-deps", [self.lake, "--keep-toolchain", "resolve-deps"])
            self.unchanged_pins()
        self.dependency_check("before-cache")
        for module in self.inventory["mathlib_imports"]:
            p = ROOT / ".lake/packages/mathlib" / (module.replace(".", "/") + ".lean")
            if not p.is_file():
                raise RuntimeError("Pinned Mathlib import source absent: " + module)
        if not self.args.skip_prepare:
            self.run("mathlib-cache", [self.lake, "exe", "cache", "get", *self.inventory["mathlib_imports"]])
            self.unchanged_pins()
        # Check local direct dependencies before any project build. Missing cache
        # is an error, rather than a request to compile all of Mathlib.
        for module in self.inventory["mathlib_imports"]:
            p = ROOT / ".lake/packages/mathlib/.lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            if not p.is_file():
                raise RuntimeError("Required Mathlib cache absent: " + module + "; rerun without --skip-prepare")
        self.state["dependency_preparation"] = "passed" if not self.args.skip_prepare else "validated existing pinned checkouts/cache"
        self.save()

    def build(self):
        for name in self.inventory["topological_order"]:
            self.run("build-" + name, [self.lake, "build", name])
        self.run("build-root", [self.lake, "build", "BestOfBothWorlds"])
        self.unchanged_pins()
        self.state["explicit_leaf_builds"] = len(self.inventory["modules"])
        self.state["import_only_root_build"] = "passed"
        self.save()

    def proof_parts(self):
        build = ROOT / ".lake/build/lib/lean"
        wanted = set(self.inventory["modules"]) | {"BestOfBothWorlds"}
        actual = {".".join(p.relative_to(build).with_suffix("").parts) for p in build.rglob("*.olean")}
        if actual != wanted:
            raise RuntimeError("Compiled inventory mismatch; missing=" + repr(sorted(wanted - actual)) +
                               "; extra=" + repr(sorted(actual - wanted)) + "; run --phase build first")
        parts = {}
        for name in self.inventory["topological_order"]:
            for suffix in (".olean", ".olean.server", ".olean.private"):
                p = build / (name.replace(".", "/") + suffix)
                if not p.is_file():
                    raise RuntimeError("Missing complete proof-bearing compiled part: " + self.relative(p))
                parts[self.relative(p)] = guard.sha256(p)
        return parts

    def axioms(self):
        self.proof_parts()
        header = inspection_header(self.inventory["topological_order"])
        endpoints = read_json(V / "endpoints.json")
        for filename, body in (("AuditDeclarations.lean", DECLARATIONS), ("AuditSafety.lean", SAFETY),
                               ("AuditEndpoints.lean", "".join(f"#check @{n}\n#print axioms {n}\n\n" for n in endpoints))):
            (self.run_dir / filename).write_text(header + body)
        def inspect(label, filename):
            return self.run(label, [self.lake, "env", self.lean, "-j1", "-DwarningAsError=true",
                                    self.relative(self.run_dir / filename)])
        endpoint_log = inspect("endpoints", "AuditEndpoints.lean")
        declaration_log = inspect("declarations", "AuditDeclarations.lean")
        safety_log = inspect("safety", "AuditSafety.lean")
        self.run("historical-auxiliary-axioms", [self.lake, "env", self.lean, "-j1", "-DwarningAsError=true", "CheckAxioms.lean"])
        expected = read_json(V / "expected-declarations.json")
        declarations = re.findall(r"AUDIT_DECL=(\S+) KIND=(\w+) UNSAFE=(true|false) PARTIAL=(true|false)", declaration_log)
        totals = re.findall(r"AUDIT_TOTAL=(\d+) THEOREMS=(\d+)", declaration_log)
        if len(totals) != 1 or len(declarations) != int(totals[0][0]):
            raise RuntimeError("Incomplete compiled declaration inspection")
        if len(set(d[0] for d in declarations)) != len(declarations):
            raise RuntimeError("Duplicate declaration inventory records")
        raw = re.findall(r"AUDIT_AXIOMS ([^\s:]+):\s*\[([^\]]*)\]", declaration_log, re.S)
        axioms = {n: sorted(re.sub(r"\.\{[^}]*\}", "", x.strip())
                            for x in body.split(",") if x.strip()) for n, body in raw}
        names = {d[0] for d in declarations}
        if len(raw) != len(declarations) or set(axioms) != names or names != set(expected):
            raise RuntimeError("Compiled declaration/axiom inventory differs from audited baseline")
        unexpected = {n: sorted(set(xs) - ALLOWED_AXIOMS) for n, xs in axioms.items()
                      if set(xs) - ALLOWED_AXIOMS}
        if unexpected:
            raise RuntimeError("Unexpected transitive logical axiom(s): " + json.dumps(unexpected))
        records = {}
        for name, kind, unsafe, partial in declarations:
            record = {"kind": kind, "unsafe": unsafe == "true", "partial": partial == "true", "axioms": axioms[name]}
            if record != expected[name]:
                raise RuntimeError("Compiled declaration metadata changed: " + name + ": " + json.dumps(record))
            records[name] = record
        unsafe = {d[0] for d in declarations if d[2] == "true"}
        partial = {d[0] for d in declarations if d[3] == "true"}
        if unsafe or partial != PARTIAL_HELPERS or any(d[1] == "theorem" for d in declarations if d[3] == "true"):
            raise RuntimeError("Unexpected unsafe/partial project declaration")
        safety = re.findall(r"AUDIT_SAFE_CONSTANTS=(\d+) BAD_DEPENDENCIES=(\d+)", safety_log)
        if safety != [(str(len(declarations) - len(partial)), "0")]:
            raise RuntimeError("Safe project constants depend on unsafe/partial constants")
        endpoint_axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", endpoint_log, re.S)
        if len(endpoint_axioms) != len(endpoints) or {n for n, _ in endpoint_axioms} != set(endpoints):
            raise RuntimeError("Incomplete principal endpoint #print axioms output")
        for name, body in endpoint_axioms:
            axs = sorted(re.sub(r"\.\{[^}]*\}", "", x.strip()) for x in body.split(",") if x.strip())
            if axs != axioms[name]:
                raise RuntimeError("Endpoint/declaration transitive axiom mismatch: " + name)
        if any("⋯" in text or "..." in text for text in (endpoint_log, declaration_log)):
            raise RuntimeError("Elaborated statement display contains an ellipsis")
        if sum(d[1] == "theorem" for d in declarations) != int(totals[0][1]):
            raise RuntimeError("Inconsistent theorem count")
        guard.atomic_json(self.run_dir / "axiom-audit.json", records)
        guard.atomic_json(self.run_dir / "endpoint-axioms.json", {n: axioms[n] for n in endpoints})
        self.state["axiom_audit"] = {"status": "passed", "declarations": len(declarations),
                                     "theorems": int(totals[0][1]), "principal_endpoints": len(endpoints),
                                     "all_axioms": sorted({x for xs in axioms.values() for x in xs}),
                                     "unsafe_constants": [], "partial_generated_nonproof_helpers": sorted(partial),
                                     "safe_constants_checked_for_unsafe_dependencies": int(safety[0][0]),
                                     "bad_unsafe_or_partial_dependencies": 0}
        self.save()

    def kernel(self):
        parts = self.proof_parts()
        guard.atomic_json(self.run_dir / "kernel-inputs.json", parts)
        for name in self.inventory["topological_order"]:
            output = self.run("kernel-" + name, [self.lake, "env", self.checker, "--verbose", name])
            replayed = re.findall(r"(?m)^replaying (\S+)$", output)
            if replayed != [name]:
                raise RuntimeError("Kernel checker did not replay exactly requested leaf: " + name + ": " + repr(replayed))
        changed = [rel for rel, sha in parts.items() if guard.sha256(ROOT / rel) != sha]
        if changed:
            raise RuntimeError("Compiled proof-bearing replay inputs changed: " + repr(changed))
        self.state["kernel_replay"] = {"status": "passed", "exact_leaf_modules": len(self.inventory["modules"]),
                                        "proof_bearing_parts": len(parts), "all_input_hashes_unchanged": True,
                                        "imported_libraries": "trusted", "partial_runtime_helpers": "excluded by Lean Replay; safety-checked separately"}
        self.save()

    def execute(self):
        if resource.getrlimit(resource.RLIMIT_AS)[0] != resource.RLIM_INFINITY:
            raise RuntimeError("Inherited RLIMIT_AS is finite; run in a shell without an address-space cap")
        self.tools()
        self.prepare()
        if not self.args.prepare_only:
            if self.args.phase in ("all", "build"):
                self.build()
            if self.args.phase in ("all", "axioms"):
                self.axioms()
            if self.args.phase in ("all", "kernel"):
                self.kernel()
        self.dependency_check("final")
        self.unchanged_pins()
        self.state["source_preservation"] = "all pinned mathematical/configuration files unchanged"
        self.state["status"] = "passed"

    def finish(self):
        self.state["finished_utc"] = guard.now()
        self.state["peak_sampled_group_rss_bytes"] = max(
            (x.get("peak_sampled_group_rss_bytes", 0) for x in self.state["commands"]), default=0)
        self.state["command_elapsed_seconds"] = round(sum(x.get("elapsed_seconds", 0)
                                                          for x in self.state["commands"]), 3)
        self.save()
        guard.atomic_json(self.run_dir / "summary.json", self.state)
        print("Verification " + self.state["status"].upper() + ": " + self.relative(self.run_dir / "summary.json"), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase", choices=("all", "build", "axioms", "kernel"), default="all",
                        help="default all; axioms/kernel require existing complete project build")
    parser.add_argument("--prepare-only", action="store_true", help="validate/install pinned dependencies/cache, then stop")
    parser.add_argument("--skip-prepare", action="store_true", help="offline mode: validate already-present pinned dependencies/cache")
    parser.add_argument("--check", action="store_true", help="static source/inventory/configuration screen only; does not invoke Lean")
    args = parser.parse_args()
    guard.PROJECT = ROOT
    if not sys.platform.startswith("linux") or not Path("/proc/meminfo").is_file():
        raise RuntimeError("Supported guarded verification requires Linux /proc, Python fcntl/resource")
    inv = inventory()
    if args.check:
        print(json.dumps({"status": "static-check-passed", "not_a_formal_verification": True,
                          "modules": len(inv["modules"]), "source_files": inv["source_files"],
                          "direct_mathlib_imports": len(inv["mathlib_imports"]),
                          "topological_order": inv["topological_order"]}, indent=2))
        return 0
    V.mkdir(exist_ok=True)
    with (V / "verify.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("Another verifier holds verification/verify.lock; no child started", file=sys.stderr)
            return 2
        check = Verification(args, inv)
        try:
            check.execute()
        except BaseException as exc:
            check.state.update(status="cancelled" if isinstance(exc, KeyboardInterrupt) else "failed",
                               reason=str(exc))
            print("Verification failed: " + str(exc), file=sys.stderr, flush=True)
        finally:
            check.finish()
        return 0 if check.state["status"] == "passed" else 1


if __name__ == "__main__":
    def interrupted(signum, frame):
        raise KeyboardInterrupt("received signal " + str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGHUP, interrupted)
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, KeyError) as exc:
        print("Verification refused: " + str(exc), file=sys.stderr)
        sys.exit(2)
