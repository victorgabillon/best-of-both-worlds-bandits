# Release candidate verification record

Candidate: **0.1.0-rc.1**. Verification date: **2026-10-17**.

- **TECHNICALLY REPRODUCIBLE: PASS**
- **LICENSING AND ATTRIBUTION: PENDING**
- **READY FOR PUBLICATION: NO**

The technical verdict concerns the exact source/configuration/script inputs identified below. Rights-holder and contributor approval is a separate, unresolved requirement. No commit, repository creation, push, release publication, public URL, or DOI was created.

## What was checked

The package certifies the six principal named mathematical results of the corrected manuscript: Theorems 1, 2, 4, and 6, Corollary 7, and Lemma 10; Theorem 6 has separate stochastic and adversarial bounds. [THEOREM_MAP.md](THEOREM_MAP.md) gives the exact endpoints, constants, quantifiers, and learner models. It does not claim that the entire manuscript's prose, experiments, arbitrary learner-kernel representations, or cross-interface P1 composition have been machine-checked.

The pins are Lean **4.35.0**, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake **5.0.0-src+eb6cafb**, and Mathlib **v4.35.0**, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All nine dependency checkout revisions were compared with `lake-manifest.json`; result: **PASS — 9 of 9 exact locked revisions; tracked sources clean**. No source, theorem statement, proof body, algorithm, constant, toolchain pin, Mathlib pin, dependency lockfile, or manuscript content was revised.

## Independent test A: source-only host copy and fresh downloads

Run ID: **`20261017T121603Z-122403-ddaaf9`**. Status: **passed**. Start/end UTC: **2026-10-17T12:16:03.209353+00:00 / 2026-10-17T12:34:47.644871+00:00**.

A fresh source-only copy was created under the arbitrary directory name **`renamed certificate with spaces`**, without project `.lake/build`, old compiled `.olean` outputs, development verification logs, or dependency checkouts. The public entry point was invoked from the parent directory, exercising both root discovery and spaces in the installation name:

```sh
"renamed certificate with spaces/scripts/verify.sh"
```

Lake fetched all nine dependencies from their official public Git URLs at the locked revisions. The Mathlib cache was freshly downloaded from the official service into this independent copy; **3262** cache-closure files were obtained. The cache executable was bootstrapped in the new checkout. No development proof build cache, dependency checkout, hidden parent-project symlink, or custom local dependency was supplied. A standard existing **official pinned Lean installation on PATH** was reused and its identity checked; it was not copied into the package or represented as a fresh compiler installation.

Declared upstream internal links: **Batteries docs/README.md points within its own freshly retrieved checkout; no project/dependency parent links**. Such links, if present, remain within the freshly fetched dependency itself and are distinct from a hidden link to the development workspace.

## Independent test B: offline namespace isolation and a second fresh project build

Run ID: **`20261017T123517Z-2-60808b`**. Wrapper evidence ID: **`20261017T123516Z-134804-628e40`**. Status: **passed**. Start/end UTC: **2026-10-17T12:35:17.109632+00:00 / 2026-10-17T12:50:45.013059+00:00**.

After test A completed, a second fresh project source copy was created with **zero transferred project compiled artifacts**. Bubblewrap supplied an isolated mount namespace and unshared user, PID, network, IPC, and UTS namespaces. Host home, root, and mounted-user-data directories and the development workspace were not mounted. The environment was cleared, including `HOME` and Lean/Lake path overrides.

The declared inputs were:

| Mount | Access and origin |
| --- | --- |
| `/usr`, `/bin`, `/lib`, `/lib64`, where present | Read-only host system tools/libraries |
| `/opt/lean` | Read-only official pinned Lean 4.35.0 installation |
| `/workspace` | Second fresh source tree; newly generated project build and verification output permitted |
| `/workspace/.lake/packages` | Read-only nine locked checkouts plus official Mathlib compiled cache fetched by test A |
| `/workspace/.cache/mathlib` | Read-only cache archives/helper files downloaded by test A |
| `/proc`, `/dev`, `/tmp` | Namespace-local process/devices/tmpfs setup |

Network access was disabled inside the namespace. The same public command ran in its documented already-provisioned mode:

```sh
./scripts/verify.sh --skip-prepare
```

This second test **reuses the explicitly declared official dependency/cache inputs fetched by test A**, and independently rebuilds all project sources before repeating the axiom audit and kernel replay. It is not a second dependency download. Namespace preflight result: **PASS — zero initial project oleans; host home, root, and mounted-user-data directories hidden; cleared path overrides**. Read-only mount/source-input checks: **PASS — declared compiler/dependency/cache mounts read-only; copied inputs unchanged**.

These tests run on a Linux host and an isolated view of that host's system tools. They are **not a newly installed Ubuntu machine, a Docker/OCI image build, or an independent implementation of Lean's kernel**. Docker status, if investigated: **Not used: local daemon socket inaccessible. Additional Bubblewrap namespace repetition is documented separately.**.

## Observed results

| Check | Test A | Test B |
| --- | --- | --- |
| Explicit mathematical leaf builds | 57 / 57 | 57 / 57 |
| Import-only root build | passed | passed |
| Declarations inventoried and transitively axiom-inspected | 1742 | 1742 |
| Theorem constants among those declarations | 1425 | 1425 |
| Principal endpoint/variant axiom checks | 19 / 19 | 19 / 19 |
| Safe nonpartial constants checked for unsafe/partial dependencies | 1735 | 1735 |
| Bad unsafe/partial dependencies | 0 | 0 |
| Exact single-leaf kernel replays | 57 / 57 | 57 / 57 |
| Proof-bearing compiled parts required/hashed | 171 / 171 | 171 / 171 |
| Replay input hashes unchanged | true (PASS) | true (PASS) |
| Every guarded command exits zero | PASS — 178 guarded commands, all exit zero | PASS — 176 guarded commands, all exit zero |
| Peak sampled owned-group RSS, bytes (GiB) | 3959336960 (3.687) | 3956891648 (3.685) |
| Sum of guarded command times, seconds | 1122.183 | 925.779 |
| Project build command time, seconds | 541.94 | 503.575 |
| Kernel command time, seconds | 511.446 | 365.774 |

The expected complete inventory is **1,742 declarations**, including **1,425 theorem constants**. Seven compiler-generated partial nonproof `._unsafe_rec` runtime helpers are distinguished from the **1,735 safe nonpartial constants**. No safe project type/proof/definition may refer to an unsafe or partial constant. Lean's replay checks safe nonpartial declarations, including private mathematical proofs; it intentionally excludes those seven runtime helpers. Accordingly, the claim is 1,742 declarations inventoried/axiom-inspected and 57 modules kernel-replayed, not 1,742 individual constants kernel-replayed.

Actual transitive axiom union: **Classical.choice, Quot.sound, propext**. Unexpected axioms: **none (PASS)**. The allowed foundational names are `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom mathematical axiom is permitted. Authored-source placeholder/bypass scan: **PASS — the pinned authored-source inventory passed the production static screen**. Imported Lean/Mathlib libraries remain trusted; no `--fresh`, full-Mathlib, or whole-prefix replay was performed.

Both runs use one owned command group at a time, `LEAN_NUM_THREADS=1`, the verification lock, a 7 GiB available-memory start check, a 6 GiB sampled group-RSS watchdog, a 1 GiB runtime available-memory floor, 600 CPU seconds per process, 900 wall seconds per command, and no core dumps or virtual-address-space cap. These watchdogs do not guarantee a hard 4 GiB or instantaneous memory ceiling.

Disk use after fresh provisioning: dependencies/cache **3060136834** bytes; downloaded cache archives/helpers **193655659** bytes; project compiled outputs **157121314** bytes. These are observed logical sizes with **regular non-symlink logical file bytes in the first independent copy, without the shared official compiler installation**, not universal installation limits.

## Preservation, package boundary, and evidence

- **57 / 57** mathematical module files are byte-identical to the Step 22 SHA-256 baseline.
- Preserved source/configuration files: **62**; root module, historical `CheckAxioms.lean`, `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` remain unchanged.
- Protected existing workspace/evidence files: **3625** checked by SHA-256, byte size, and modification time; changed or missing: **0**.
- Candidate/runtime verifier-input comparison: **PASS — both complete runs match the candidate's seven verifier/manifest input hashes**. No untested verification-script revision is substituted after the successful runs.
- Negative controls and failure diagnostics: **PASS — 11 recorded-log/parser/static fixture controls; no Lean/Lake or bad-proof elaboration claimed**; these are verifier tests in disposable copies, not edits to a mathematical proof.
- Allowlisted package member/path/symlink/credential scan: **Final package/archive scan is performed during packaging; its actual result is in the external Step 23 report**. Scan scope/limits: **allowlisted source package, common credential patterns and path/artifact exclusions; not universal secret detection or a Git-history audit**. Git history was not imported or certified; the eventual Git index/history requires separate review before upload.

Compact public evidence is in:

- [`verification/RELEASE_VERIFICATION.json`](../verification/RELEASE_VERIFICATION.json): candidate verdict, exact pins, observed metrics, dependency/bootstrap/isolation scope, and input hashes.
- [`verification/release-kernel.json`](../verification/release-kernel.json): every replay result and proof-bearing input hashes.
- [`verification/release-endpoint-axioms.json`](../verification/release-endpoint-axioms.json): exact principal endpoint axiom sets.
- [`verification/release-source-preservation.json`](../verification/release-source-preservation.json): Step 22-to-candidate source SHA-256 comparisons.
- [`verification/source-manifest.json`](../verification/source-manifest.json), [`verification/manuscript-baseline.json`](../verification/manuscript-baseline.json), and [`verification/package-manifest.json`](../verification/package-manifest.json): source/configuration, corrected manuscript identity, and final package inventory.

Full logs/status, including unsuccessful provisioning or verifier-control attempts, remain in the permanent external release evidence tree: **independent-test/renamed certificate with spaces/verification/runs/20261017T121603Z-122403-ddaaf9; isolated-test/bob-best-arm-lean/verification/runs/20261017T123517Z-2-60808b; evidence/isolated-wrapper/20261017T123516Z-134804-628e40**. They are excluded from the lightweight source archive. Host full-summary SHA-256: **`0839b2ce26298aa31ea9abcc716503eac54d0ea57e7ae58ff7969d50ce52caae`**. Isolated full-summary SHA-256: **`fdfcd5bac732158fcd436870218a0bbddd734a5a1747d8a04a9dbd9712691182`**.

Lightweight archive filename: **`bob-best-arm-lean-0.1.0-rc.1.tar.gz`**; the adjacent `.sha256` sidecar records its actual digest. The archive's digest is deliberately not embedded in this packaged file, avoiding a self-referential hash. Archive member verification result: **Final archive members are validated during packaging; see the external Step 23 report and adjacent checksum sidecar**.

[Audit finding dispositions](AUDIT_FINDINGS.md) and the [release checklist](RELEASE_CHECKLIST.md) distinguish implemented technical fixes from the remaining rights/attribution approval. **Licensing and attribution remain PENDING; public publication remains unauthorized.**
