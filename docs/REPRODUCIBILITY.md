# Reproduce the paper and Lean certificates

For the manuscript, see [paper/README.md](../paper/README.md) and run `python3 scripts/build-paper.py` with Tectonic 0.17.0. The remaining sections describe the unchanged Step 23 Lean verifier. The current combined run is documented in [COMBINED_VERIFICATION.md](COMBINED_VERIFICATION.md); [RELEASE_VERIFICATION.md](RELEASE_VERIFICATION.md) is historical Step 23 evidence.

The supported complete verifier is for **Ubuntu/Linux x86-64**, with Python 3.10 or later, standard Lean/Lake command-line tools, and Linux `/proc` resource information. It does not require VS Code, Codex, the development workspace, a manuscript PDF, or historical verification files. Installation-directory names may contain spaces.

## 1. Install system prerequisites

On a reasonably clean Ubuntu machine:

```sh
sudo apt-get update
sudo apt-get install git curl ca-certificates tar zstd python3 build-essential
```

`build-essential` supplies the C toolchain used when Lake builds executable support tools. The verification scripts themselves use only Python's standard library and Bash; GNU `time` and Docker are not required.

Network access is needed for the official Lean toolchain, the Git dependency checkouts pinned by Lake, and Mathlib's official downloadable cache. GitHub and the cache service must be reachable over HTTPS. Download failures are failures to provision the environment, not evidence that a mathematical theorem failed. No third-party account credentials are required for the public dependencies.

The checked source package is small, but Lean, dependency repositories, and compiled Mathlib artifacts occupy several GiB. Allow substantial additional free disk space for downloads and extraction; **20 GiB free is a planning allowance, not a measured upper bound**. Check `df -h .` before downloading. The independent candidate test's actual sizes are recorded in [RELEASE_VERIFICATION.md](RELEASE_VERIFICATION.md). Do not duplicate an existing cache merely to inspect the source package.

## 2. Install or select elan and the pinned toolchain

If an existing `elan` installation already works, use it. Otherwise the official installer can be downloaded for inspection and then run:

```sh
curl -sSfL https://elan.lean-lang.org/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
. "$HOME/.elan/env"
```

The installer is from the [official elan repository](https://github.com/leanprover/elan). Remove the downloaded installer when no longer needed. Start a new shell or source elan's environment as shown above.

Enter the unpacked source-package directory, then install the exact toolchain:

```sh
elan toolchain install leanprover/lean4:v4.35.0
lean --version
lake --version
lean --print-prefix
```

`lean-toolchain` selects the project toolchain through elan; there is no need to change a global default. Expected versions are:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

The verifier finds `lean` and `lake` on `PATH`, checks the exact Lean version/commit, and resolves the official installation prefix for `leanchecker`. It does not require a repository-local `.tooling` directory. A standard official toolchain already on `PATH` is also supported if it passes these checks.

## 3. Run the complete verifier

From the package root:

```sh
./scripts/verify.sh
```

The script locates the repository relative to itself, so it can also be invoked from another current working directory. It performs these checks in order:

1. Validate the pinned configuration, source hashes, complete module inventory, and placeholder scan.
2. Materialize the locked Git dependencies and retrieve official Mathlib caches for the project's direct Mathlib imports and their dependencies.
3. Explicitly build every one of the 57 source modules in dependency order, one target at a time, followed by the import-only root.
4. Print fully elaborated principal types and their transitive axiom lists; inventory all project public/private declarations; check safe definitions and proof values for unsafe/partial dependencies.
5. Replay exactly each of the 57 project modules with Lean's own kernel checker, requiring all three proof-bearing compiled parts and unchanged input hashes.
6. Write a pass/fail summary, exact commands, exit codes, elapsed times, and sampled process-group memory usage.

Dependencies are resolved from `lake-manifest.json`, which pins nine packages. Mathlib is **v4.35.0**, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Neither `lake update` nor a dependency upgrade is part of this procedure. The verifier checks configuration/lock hashes during preparation and validates each dependency checkout's actual commit. Cache retrieval avoids rebuilding Mathlib from source unnecessarily.

Each nonstatic invocation that passes the preliminary source and lock checks creates a unique `verification/runs/<UTC-time>-<pid>-<random>/` directory. It never overwrites historical run directories. Static `--check`, inventory failures, and lock refusals print an immediate result without creating a run directory. Successful verification output ends with:

```text
Verification PASSED: verification/runs/<run-id>/summary.json
```

For a successful complete run, `summary.json` contains:

```text
status: passed
phase: all
explicit_leaf_builds: 57
import_only_root_build: passed
axiom_audit.declarations: 1742
axiom_audit.theorems: 1425
axiom_audit.principal_endpoints: 19
axiom_audit.bad_unsafe_or_partial_dependencies: 0
kernel_replay.exact_leaf_modules: 57
kernel_replay.proof_bearing_parts: 171
kernel_replay.all_input_hashes_unchanged: true
```

The individual axiom sets are in `axiom-audit.json`; source/build/kernel inputs and exact logs are retained in the same run directory. `summary.json` for a partial phase only certifies that phase. A successful static `--check` is not a formal-verification result.

## Separate preparation and verification phases

The full command above is the recommended entry point. The following commands are useful for diagnosis or a provisioned offline machine:

```sh
./scripts/verify.sh --check
./scripts/verify.sh --prepare-only
./scripts/verify.sh --phase build --skip-prepare
./scripts/verify.sh --phase axioms --skip-prepare
./scripts/verify.sh --phase kernel --skip-prepare
```

Run the phase commands sequentially. Axiom inspection and kernel replay need previously built project artifacts. `--skip-prepare` skips network provisioning, not toolchain, dependency-pin, source, or inventory validation. For an already provisioned environment, the complete offline check is:

```sh
./scripts/verify.sh --skip-prepare
```

For transparency, the underlying dependency/cache commands are:

```sh
lake --keep-toolchain resolve-deps
mapfile -t mathlib_modules < verification/mathlib-imports.txt
lake exe cache get "${mathlib_modules[@]}"
```

The second and third lines use Ubuntu's Bash. `mathlib-imports.txt` contains the 50 direct Mathlib module names, one per line. The wrapper additionally checks pins and resource usage; prefer `--prepare-only` for the supported preparation workflow. Do not run cache retrieval or a full build concurrently with the verifier.

To build a single endpoint module with standard Lake:

```sh
lake build BestOfBothWorlds.P1UpperBounds
```

To see the underlying single-leaf replay command after building:

```sh
lake env leanchecker --verbose BestOfBothWorlds.P1UpperBounds
```

That direct command lacks the wrapper's resource, input-hash, and complete-inventory checks. The complete kernel phase is `./scripts/verify.sh --phase kernel --skip-prepare`. The default bare `lake build` only covers the historical nine-module root and is insufficient for this certificate.

## Resource policy

The verifier serializes its own runs using a repository-local verification lock, sets `LEAN_NUM_THREADS=1`, and starts one owned command group at a time. Before each guarded command it requires at least **7 GiB MemAvailable**. During execution it samples owned process-group RSS, stops its own group at a **6 GiB** sampled threshold, and stops if available system memory falls below **1 GiB**. Limits are **600 CPU seconds per process** and **900 wall seconds per guarded command**, with core dumps disabled. A finite inherited virtual-address-space limit is rejected.

These are Linux watchdog checks, not an operating-system-enforced hard memory cap. Very short peaks can occur between samples. The earlier independent audit observed about 3.70 GiB peak sampled group RSS; other accepted development checks were close to 4 GiB. Neither number guarantees completion under a strict 4 GiB limit. The final independent candidate run records its own observed peak. Close large unrelated applications if the start-memory check fails; do not weaken the verified proof or silently bypass a failed guard.

## Axioms, placeholders, and the kernel's scope

The generated endpoint inspector uses Lean's `#print axioms`. An environment-level inspector independently collects transitive axioms of all 1,742 project declarations, including private/generated names. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Unexpected axioms, including `sorryAx` or a custom mathematical axiom, cause failure with the affected declaration named.

The scripts also scan authored source for `sorry`, `admit`, custom axiom declarations, authored unsafe/partial shortcuts, and known environment-injection/bypass constructs. This text scan complements, and does not replace, the dynamic dependency and kernel checks. A theorem hypothesis is an explicit part of the theorem's type, not an extra logical axiom. A definition introduces an object, not an assumed mathematical proposition. Merely being opaque is not evidence of an unproved theorem: its proof dependencies and compiled proof are what the audit checks.

Lean generates seven partial `._unsafe_rec` runtime helpers from recursive definitions. They are non-theorems; no authored source uses a partial proof. The safety audit checks the types and values of all **1,735 safe nonpartial project constants**, finding no unsafe/partial dependency. Kernel replay intentionally checks safe nonpartial declarations and excludes those seven runtime helpers. It also regenerates/checks inductive machinery. Do not report that all 1,742 individual constants were kernel-replayed.

Imported Lean/Mathlib libraries are trusted dependencies in the pinned installation/cache. The workflow does not run `--fresh`, replay all of Mathlib, or use a different proof assistant's kernel. Source elaboration, transitive axiom inspection, and project-module kernel replay are distinct checks and all are required by the complete command.

## Common failures

| Symptom | Meaning and action |
| --- | --- |
| `lean`/`lake` not found or wrong version | Source elan's environment, enter the package directory, and install the pin. Do not replace `lean-toolchain` with a newer version. |
| Dependency HEAD or lock hash mismatch | Use a fresh source copy and retrieve the pinned dependencies. Do not run `lake update` to make the audit accept an altered dependency set. |
| Cache download fails or is incomplete | Check HTTPS access and disk space, then retry preparation. Keep the failed run logs. Avoid unintentionally rebuilding all of Mathlib. |
| Insufficient available memory or guard stop | Free memory and rerun after the owned process has stopped. The guard reports its reason and preserves logs. |
| Verification lock is held | Another verifier in this copy is running. Let it finish; do not start competing full builds. |
| Source/module inventory mismatch | A file is missing, changed, or newly unrecognized. Restore the exact release sources. Any intentional future inventory exception must be explicit and reviewed; never silently skip a module. |
| Missing `.olean.server` or `.olean.private` | Complete the explicit build phase first; replay needs all three proof-bearing parts. |
| Unexpected axiom or unsafe proof dependency | Treat verification as failed and retain the named declaration/log. Do not change the whitelist to suppress it. |
| Unsupported operating system/architecture | Use the documented Linux x86-64 environment. Support for other platforms has not been tested by this release workflow. |

## Independent reproduction and preservation evidence

[RELEASE_VERIFICATION.md](RELEASE_VERIFICATION.md) describes the actual independent test, including whether a container was used. Its source-only copy starts without project `.lake` artifacts or compiled `.olean` files, retrieves pinned Git dependencies and official caches, and runs the same public command from an arbitrarily named directory. It must not use hidden symlinks or local custom dependency checkouts.

`verification/source-manifest.json` records SHA-256 for every mathematical source and preserved configuration. `verification/manuscript-baseline.json` identifies the frozen corrected TeX by hashes. `verification/RELEASE_VERIFICATION.json` is the compact machine-readable candidate evidence. The original Step 19–22 certificates remain historical evidence outside this lightweight package; their workspace-preservation checks are not dependencies of the public verifier.
