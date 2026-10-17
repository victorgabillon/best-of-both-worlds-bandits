# Manuscript fidelity report

**MATHEMATICAL FIDELITY: PASS.** This is a source comparison connecting the approved editorial manuscript to the Step 22 audited baseline; it is not a new Lean theorem or a claim that every sentence is machine-verified.

The 18 baseline TeX hashes match `verification/manuscript-baseline.json`. The completed E3 package has all 60 recorded source/asset hashes intact. Its complete editorial patch reapplied to its exact active baseline with no fuzz or offsets and reproduced all 60 files. All nine E3 improvements remain present.

The included paper uses the 17 TeX files actually loaded by `Main.tex`; `Discussion.tex` was commented out and is excluded. Relative to E3, each included source/asset is byte-identical except one authorized paragraph in `intro.tex`, which now gives the actual GitHub URL with future-tense availability wording. No active manuscript, editorial staging file or existing patch was edited.

## Principal statements

| Result | Included source | Label | Comparison with mathematical baseline |
| --- | --- | --- | --- |
| Theorem 1 | `paper/source/upLowGenAd.tex` | `th:UPARU` | Identical after whitespace/comment normalization |
| Theorem 2 | `paper/source/upLowGenAd.tex` | `th:LOWadPRO` | Identical after whitespace/comment normalization |
| Theorem 4 | `paper/source/lowerBoundBOB.tex` | `th:lowBOB` | Identical after whitespace/comment normalization |
| Theorem 6 | `paper/source/upperBoundBOB.tex` | `th:UpBOB` | Identical after whitespace/comment normalization |
| Corollary 7 | `paper/source/upperBoundBOB.tex` | `coco` | Identical after whitespace/comment normalization |
| Lemma 10 | `paper/source/appTechLem.tex` | `l:transcriptChangeMeas` | Identical after whitespace/comment normalization |

Theorem 6's complete block contains both upper bounds. The theorem map retains the exact Lean declarations, constants, hypotheses and learner models. Theorem 4 remains conditional; lower-bound tables remain oblivious.

## Definitions, algorithms and expressions

The comparison covered **1,350 baseline inline/displayed mathematical spans** across the included TeX files, the complete principal statement blocks, and all restatable/theorem/lemma/corollary/proposition/definition/algorithm/algorithmic blocks. Defining macros in `def.tex` are byte-identical. This covers H_SR, H_BOB, H_UNIF, H_P1, the labelled Delta_3/Delta_4 classes, UNIF/P1, observed-transcript KL, error probabilities, quantifiers and constants.

The expression differences are explicitly enumerated in `verification/manuscript-fidelity.json`: approved prose introduces H_BOB in the abstract, H_SR/H_BOB names in the explanation, and K/24 in the concentration explanation; one old narrative $t$ is removed, and the displayed research question's question mark becomes a sentence stop. No operand, bound, hypothesis or mathematical formula changes. The source check accepts only these exact recorded differences, rather than ignoring arbitrary mathematical edits.

All figures and tables match the audited baseline after whitespace/comment normalization except the earlier approved E2 punctuation correction in Figure 1: the erroneous sentence stop between “gain vector” and its displayed notation was removed. That correction predates E3. Step 24 preserves the E3 Figure 1 and Figure 3 sources exactly. No figure or experiment asset changed in this task. The ProbabilityONE explanation and square-root gap discussion also retain their exact E3 bytes.

All reference/theorem/section numbers and the generated bibliography match E3. The rebuilt paper has 43 pages. Both paper builds have SHA-256 `7c6ee873dfa54b67f4b702e2568de2dc4b1f0169d11824a5ce80f12f644c4e2b`, including the fresh-copy rebuild. Only the two existing E3 overfull warnings remain (1.22124 pt horizontal and 10.71179 pt vertical); no new missing citations, unresolved references, duplicate labels or missing characters were reported.

The machine-readable comparison contains per-result hashes, source hashes, environment hashes and exact expression exceptions: [manuscript-fidelity.json](../verification/manuscript-fidelity.json). Historical E3 reports and current raw compilation/patch logs are retained outside the upload package.
