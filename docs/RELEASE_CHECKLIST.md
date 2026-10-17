# Initial public publication and later release

The author explicitly authorized the initial public commit and push to **https://github.com/victorgabillon/best-of-both-worlds-bandits** in Step 25, superseding the earlier private-review workflow. The target must remain public. No `v1.0.0` tag, GitHub release, DOI or deposit is created during initial publication.

## Initial publication checks

- Start from the final Step 24B rc.4 package, preserving all Lean proofs, toolchain/dependency pins and verifier inputs.
- Audit the entire proposed Git index for credentials, private material, unintended files, external symlinks and generated artifacts.
- Retain the final acknowledgement, five original authors, original PMLR citation and separate paper/software/dependency licenses.
- Confirm the staged 43-page PDF and source match the approved manuscript and that all required source assets are present.
- Use the configured human Git identity and the target HTTPS origin on `main`.
- Inspect the public remote immediately before pushing. Never overwrite unexpected history or force-push.
- Commit only the intended source files with “Publish corrected paper and verified Lean formalization”.
- Clone from GitHub into a new directory outside development/staging, transfer no project build outputs, and run the public complete sequential verifier and paper build.
- Record the exact commit, file inventory, kernel replay, axiom audit and PDF reproduction results before assessing readiness for an official release.

## Reproduction and review commands

```sh
git status --short
git remote -v
git log -1 --oneline
gh repo view victorgabillon/best-of-both-worlds-bandits --json visibility,isEmpty,defaultBranchRef
./scripts/verify.sh
python3 scripts/build-paper.py
```

The first verifier run retrieves the locked dependencies and official Mathlib cache. For an already provisioned environment, `./scripts/verify.sh --skip-prepare` performs the same complete build/axiom/kernel checks without network preparation. A static `--check` is not a formal certificate. The paper build requires exact Tectonic 0.17.0 and external pinned resources; `--only-cached` supports populated caches. See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) and [paper dependencies](../paper/DEPENDENCIES.md).

After successful GitHub-clone verification, an official versioned release may be considered separately. Initial publication alone does not authorize creating it. If remote history changes unexpectedly, inspect and report it rather than force-pushing or deleting branches.
