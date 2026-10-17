# Best of Both Worlds: Stochastic & Adversarial Best-Arm Identification

This repository contains the corrected COLT 2018 paper, its LaTeX sources and PDF, together with a Lean 4 formalization of its principal mathematical results. The repository publishes the corrected research manuscript and its Lean certificates. The formalization and manuscript have the separate licenses described below.

- [Corrected paper (PDF, 43 pages)](paper/corrected-paper.pdf)
- [Complete LaTeX sources](paper/source/)
- [Paper build instructions](paper/README.md)
- [Theorem-to-Lean map](docs/THEOREM_MAP.md)
- [Lean and manuscript verification instructions](docs/REPRODUCIBILITY.md)
- [Step 24B licensing and packaging audit](docs/STEP24B_AUDIT.md)
- [Step 24 full verification record (historical)](docs/COMBINED_VERIFICATION.md)

## Research

A fixed-budget best-arm learner samples one arm per round and recommends an arm after a fixed horizon. Stochastic rewards favor concentrating observations on promising arms. Adversarial rewards require continued exploration: an arm that looks poor early may later become best.

The paper establishes optimal adversarial uniform sampling, a conditional impossibility result for simultaneous stochastic and adversarial optimality, and the complexity $H_{\rm BOB}$ describing the stochastic cost of adversarial robustness. P1 combines estimated rankings with harmonic exploration, sampling estimated rank $r$ with probability $1/(r\bar{\log}K)$, where $\bar{\log}K=\sum_{r=1}^K1/r$. Its stochastic and adversarial guarantees are stated with their exact assumptions in the theorem map.

The original mathematical research is by **Yasin Abbasi-Yadkori, Peter L. Bartlett, Victor Gabillon, Alan Malek, and Michal Valko**. The corrected manuscript preserves that author list. Citation: *Best of both worlds: Stochastic & adversarial best-arm identification*, COLT 2018, PMLR 75:918–949. [Original publication](https://proceedings.mlr.press/v75/abbasi-yadkori18a.html). The included PDF is the corrected version, not a replacement copy of the original 2018 proceedings PDF.

## Reproduce

For Lean, install the prerequisites and exact toolchain in [REPRODUCIBILITY.md](docs/REPRODUCIBILITY.md), then run:

```sh
./scripts/verify.sh
```

The pins are **Lean 4.35.0**, **Lake 5.0.0-src+eb6cafb**, and **Mathlib v4.35.0**, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The script retrieves locked dependencies and official caches, explicitly builds all 57 mathematical modules, audits transitive axioms, and performs project-only kernel replay. Bare `lake build` covers only the historical nine-import root. Use the complete script for the certificate. Verification is sequential; its Linux resource guard requires at least 7 GiB available memory before each guarded command.

For the paper, install **Tectonic 0.17.0**, then run:

```sh
python3 scripts/build-paper.py
```

The first paper build may download the hash-pinned official COLT author kit and resources from the pinned v33 bundle. Dependencies are cached separately; build outputs go to `paper/rebuild/`. The script checks the rebuilt PDF against the included one. [Paper instructions](paper/README.md) explain offline builds, compiler selection and the reproducible timestamp.

## Certificate scope

The six principal named results—Theorems 1, 2, 4 and 6, Corollary 7 and Lemma 10—have Lean certificates; Theorem 6 has two bounds. The 57 mathematical modules are unchanged from the Step 23 release. The axiom inventory contains 1,742 declarations, including 1,425 theorem constants. Seven compiler-generated partial nonproof helpers are distinguished from 1,735 safe nonpartial constants. All safe types and values are checked for unsafe/partial dependencies; module replay includes private proofs. Only `propext`, `Classical.choice` and `Quot.sound` are allowed as transitive axioms. Imported Lean/Mathlib libraries remain trusted.

The upper bounds use concrete positive-probability observed-history policies. Lower bounds use general measurable private-seed learners, including deterministic actions and zero sampling probabilities. No unrestricted learner-kernel representation theorem or composed P1 bridge between those interfaces is claimed. Theorem 4 retains its conditional hypotheses and actual constructed complexity. Lower-bound witness tables are oblivious.

Lean checks mathematical statements under their explicit hypotheses. It does not certify every sentence, the paper's experiments, editorial choices, or every possible tie-resolution rule. [MANUSCRIPT_FIDELITY.md](docs/MANUSCRIPT_FIDELITY.md) records the historical E3/Step 24 comparison with the frozen mathematical baseline. The [current audit](docs/STEP24B_AUDIT.md) extends that record through the approved acknowledgement correction.

## Attribution and licenses

This Lean formalization was developed with assistance from OpenAI's ChatGPT and Codex. ChatGPT was used for mathematical discussions, proof planning, and reviewing the formalization, while Codex was used to implement and revise the Lean proofs. Victor Gabillon coordinated this work and maintains the repository. AI tools are not human authors. See [AUTHORS.md](AUTHORS.md).

The new Lean formalization uses [Apache-2.0](LICENSE), within the scope in [NOTICE](NOTICE). The published article and its corrected adaptation use **CC BY 4.0**; Victor Gabillon confirmed authority for additional contributions under that license. External LaTeX dependencies retain their own licenses and are not bundled. See [paper/RIGHTS.md](paper/RIGHTS.md), the [file-by-file inventory](verification/LICENSE_INVENTORY.tsv), and [LICENSING.md](docs/LICENSING.md).

The included manuscript retains the author-approved acknowledgement that Victor Gabillon reviewed the AI-assisted changes. The preceding [Step 24B audit](docs/STEP24B_AUDIT.md) records the rights and attribution checks; its earlier private-upload prerequisite was superseded by the author's explicit decision to publish this repository publicly. This initial publication is not an official `v1.0.0` release.
