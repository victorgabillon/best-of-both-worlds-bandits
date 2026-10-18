# Rights and attribution for the corrected manuscript

## Original article

Yasin Abbasi-Yadkori, Peter L. Bartlett, Victor Gabillon, Alan Malek, and Michal Valko. *Best of both worlds: Stochastic & adversarial best-arm identification*. Proceedings of Machine Learning Research **75:918–949**, COLT 2018.

[Original publication and proceedings PDF](https://proceedings.mlr.press/v75/abbasi-yadkori18a.html).

The published article is licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/). The [PMLR publication agreement](https://proceedings.mlr.press/pmlr-license-agreement.html) provides this grant, retains the authors' copyright, and requires citation and a link to the original publication. The agreement's [official 2017 revision](https://github.com/mlresearch/mlresearch.github.io/blob/a2ef1b1ad989662c516c8f0df1d20eb5993e38c6/pmlr-license-agreement.md), predating COLT 2018, has the same text. This audit relies on the publisher's public licensing record; it does not claim to possess a signed agreement.

## Corrected version and modifications

The included [corrected-paper.pdf](corrected-paper.pdf) is a **corrected and editorially revised adaptation**, not the official PMLR-hosted 2018 PDF. It retains all five research authors. Corrections include the stochastic concentration/ranking argument and the lower-bound arguments; the subsequent approved revisions improve exposition and document the Lean formalization. [Manuscript fidelity](../docs/MANUSCRIPT_FIDELITY.md) and [provenance](../docs/PROVENANCE.md) identify the frozen mathematical baseline, approved E1–E3 revisions and repository notice. This licensing audit changes no proof, theorem, algorithm or constant. Following explicit author approval, its sole TeX correction replaces the acknowledgement’s collective review/responsibility claims with “Victor Gabillon reviewed the resulting AI-assisted changes.”

The eight experiment panels derive from the experiments in Figure 3 of the published article, printed page 16. Their labels, horizons and plotted results correspond; the included assets use revised bar colors. No separate third-party rights exclusion was found in the published figure caption or Appendix A. These assets remain exactly as supplied in Step 24; they were not redrawn for this audit.

On 2026-10-17, Victor Gabillon confirmed that he has authority to release any new copyrightable corrections and author-written source material beyond the already licensed article under **CC BY 4.0**. Those contributions, the corrected manuscript, its author-written TeX source, bibliography selection and figure adaptations are distributed under CC BY 4.0, with the original attribution and modification notice above. This statement records the author's confirmation; it does not assert that the maintainer alone owns all research contributions. Bibliographic facts remain facts, and no rights are asserted in third-party titles merely by citing them.

Step 24B removes a nonprinting third-party abstract and an obsolete local attachment-path field from one bibliography entry. All printed bibliography entries remain byte-identical. Before the separately approved acknowledgement correction, the complete PDF also reproduced Step 24 exactly; the Step 24B PDF differed only in the approved acknowledgement text. The subsequent five prose changes of 2026-10-18 are recorded in [provenance](../docs/PROVENANCE.md#approved-expository-update-2026-10-18). No copied abstract is licensed by this notice.

## Separate software and external dependencies

The Lean formalization, original verification tooling and associated formalization documentation use [Apache-2.0](../LICENSE), subject to [NOTICE](../NOTICE). This does not relicense the article. Separately fetched Lean, Mathlib and other software retain their own licenses and notices.

No `.cls`, `.sty` or `.bst` file is bundled in `source/`. The historical JMLR 1.24 runtime files are fetched from the official COLT 2018 author kit and retain their LPPL 1.3-or-later notices. The COLT wrapper is also fetched externally: no explicit wrapper redistribution license was found, and this repository does not distribute or relicense it. An explicit editor-name compatibility adjustment is applied only in the temporary build to preserve the approved PDF. See [DEPENDENCIES.md](DEPENDENCIES.md) for origin, hashes and the exact adjustment. Other TeX packages and bibliography styles come from the external Tectonic bundle under their respective licenses. The [verbatim LPPL text](third-party-licenses/LPPL-1.3c.txt) is retained for reference; it is not relicensed under CC BY.

CC BY 4.0 does not grant rights in excluded third-party material or imply endorsement by PMLR, any author or a software dependency's maintainers. This notice does not grant rights beyond those described by the licenses and the author's confirmation.

## Confirmed review attribution

Victor Gabillon confirmed on 2026-10-17 that **he alone checked the AI-assisted revisions**. He then explicitly approved replacing the collective review/responsibility claims with “Victor Gabillon reviewed the resulting AI-assisted changes.” That correction appeared on Step 24B PDF page 15 and remains unchanged on current PDF page 16. The preceding ChatGPT disclosure, all five research authors, all other acknowledgements and all mathematics are preserved. Two builds reproduce the corrected PDF exactly. The [audit](../docs/STEP24B_AUDIT.md) records the historical approval, source preservation and precise PDF comparison. No additional licensing or acknowledgement approval remains pending.
