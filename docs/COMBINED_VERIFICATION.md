# Combined repository verification

- **MATHEMATICAL FIDELITY: PASS**
- **LEAN REPRODUCIBILITY: PASS**
- **MANUSCRIPT REPRODUCIBILITY: PASS**
- **LICENSE/ATTRIBUTION: PENDING** (Lean Apache-2.0 and neutral attribution implemented; paper/source rights remain pending)
- **READY FOR GITHUB UPLOAD: NO**

The fresh combined source copy contained zero transferred project compiled files. The unchanged public command `./scripts/verify.sh --skip-prepare` ran sequentially inside offline Linux namespaces with the development workspace hidden. Explicit read-only mounts supplied the official pinned compiler and the official dependency/cache inputs fetched during Step 23. No project build cache was supplied. This is a same-host isolated project test, not a new Ubuntu installation, a Docker image or a second download of all dependencies.

All **57 mathematical modules** and the root built. All **1,742 declarations**, including **1,425 theorem constants**, passed the transitive axiom audit; the **19 principal endpoint/variant** checks reported only `propext`, `Classical.choice` and `Quot.sound`. All **1,735 safe nonpartial constants** had zero unsafe/partial dependencies. Seven generated partial nonproof helpers are separately inventoried; imported libraries remain trusted.

All **57 exact-leaf kernel replays** passed, with all **171 proof-bearing compiled parts** rehashed unchanged. Every one of the **176 guarded commands** exited zero. Observed command time was **921.915 seconds** and peak sampled owned-group RSS was **3.684 GiB**. These observations are not a strict memory bound. The unchanged resource limits and Linux support are documented in [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

All 59 Lean sources, three configuration files and seven verifier/manifest inputs retain the Step 23 bytes. The included paper sources, PDF and paper build script also match their tested-copy inputs; documentation and release metadata were finalized afterward and checked separately during packaging. No Lean proof, theorem, constant, algorithm or dependency pin was edited.

The included **43-page** paper compiled with Tectonic 0.17.0 and the v33 resource bundle. A second build from the independent source copy was byte-identical: **`7c6ee873dfa54b67f4b702e2568de2dc4b1f0169d11824a5ce80f12f644c4e2b`**. The reproducible timestamp is fixed. No unresolved citations/references, duplicate labels or missing characters remained. The two existing E3 overfull warnings were unchanged. [MANUSCRIPT_FIDELITY.md](MANUSCRIPT_FIDELITY.md) records the full baseline/editorial comparison.

Machine-readable current evidence: [COMBINED_VERIFICATION.json](../verification/COMBINED_VERIFICATION.json), [manuscript-fidelity.json](../verification/manuscript-fidelity.json) and [repository-manifest.json](../verification/repository-manifest.json). Historical Step 23 records retain their original values and verdicts; [PROVENANCE.md](PROVENANCE.md) distinguishes them from this run.

Final archive/member, staged-file and scoped privacy checks are recorded in the external Step 24 report and archive checksum sidecar. Full raw build, axiom and replay logs remain in the permanent external evidence/test directories, outside the upload package. The verifier can generate new full logs from this repository without those historical files.

GitHub was observed **PUBLIC and EMPTY**. No visibility change, commit, push or publication was performed. Make the repository private before uploading the review candidate, resolve the precise rights items in [LICENSING.md](LICENSING.md), and obtain separate approval for commit/push. See [RELEASE_CHECKLIST.md](RELEASE_CHECKLIST.md).
