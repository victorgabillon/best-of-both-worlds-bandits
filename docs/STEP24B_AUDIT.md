# Step 24B: licensing, packaging and approved acknowledgement correction

**Historical Step 24B assessment.** Its private-upload prerequisite was subsequently superseded by the author’s explicit public-publication authorization in Step 25. See [the current publication checklist](RELEASE_CHECKLIST.md). The completed rights, attribution and mathematical checks below remain evidence for the source authority.

This audit covers the original 129-file Step 24 candidate, the pre-approval `0.1.0-rc.3` candidate and the final `0.1.0-rc.4` successor. Victor Gabillon explicitly approved the exact factual acknowledgement replacement and PDF rebuild on 2026-10-17. That correction is applied. No theorem, proof, algorithm, constant, hypothesis or Lean input changed. The original Step 24 directory, rc.3 archive and prior reports remain preserved.

| Assessment | Verdict | Evidence and limits |
| --- | --- | --- |
| Lean reproducibility | **PASS** | Inherited Step 24 full build, axiom audit and project-only kernel replay; all 59 Lean files, three pins and seven verifier inputs match. No new full Lean build was performed. |
| Manuscript reproducibility | **PASS** | Two clean-source builds produce the same revised 43-page, 958,146-byte PDF. |
| Licensing | **RESOLVED** | Published article: CC BY 4.0. Victor confirmed authority for additional contributions under that license. Historical support is fetched externally under its own rights. |
| Attribution accuracy | **PASS** | The exact approved acknowledgement is applied; only Victor is identified as reviewing the AI-assisted changes. |
| Candidate ready for private review | **YES** | Source/PDF, rights, attribution and packaging checks complete. |
| Ready for private GitHub upload now | **NO — remote prerequisite only** | Target was rechecked as PUBLIC and EMPTY. Make it PRIVATE and obtain separate commit/push authorization before an actual upload. No manuscript or licensing approval remains pending. |

## Step 24 blockers and their dispositions

| Exact Step 24 material or issue | Resolution |
| --- | --- |
| Corrected PDF and 17 TeX files | Existing PMLR CC BY 4.0 terms permit adaptation with attribution and a modification notice. Victor separately confirmed authority for additional contributions under CC BY 4.0. See [RIGHTS.md](../paper/RIGHTS.md). No fresh grant for already licensed content is demanded. |
| `biblio.bib` | Same confirmed author-source basis. Only the nonprinting `abstract` and `file` fields in `carpentier2014extreme` were removed: a copied third-party abstract and obsolete private attachment path. The generated bibliography is unchanged, including after the acknowledgement correction. The older path scan missed that syntax; the current scan includes it. |
| Eight experiment PDFs | All eight correspond to published Figure 3, printed page 16: experiment numbers, horizons, bar heights and error bars match visually. Colors are adapted. No separate third-party image credit/exclusion was found in the caption or Appendix A. Additional author contributions are covered by the confirmation. Asset bytes are unchanged. |
| `colt2018.cls` | Official COLT author kit located. No explicit wrapper redistribution grant found. The file is not bundled: fetch the exact pinned external runtime dependency, with the approved editor line restored only in the temporary build. |
| `jmlr.cls`, `jmlrutils.sty` | Exact historical files found in the same official kit; their headers and the contemporary CTAN record identify LPPL. Fetch unchanged externally, avoiding redistribution of an incomplete historical work. The verbatim LPPL reference text is retained. |
| Blanket software licensing | Apache-2.0 is scoped to Lean/tooling/formalization documentation. Paper content uses CC BY 4.0. External packages retain their own licenses. |
| Review by all coauthors | Victor confirmed that only he checked the AI-assisted revisions and explicitly approved the narrow factual correction. It is applied; no collective review/responsibility claim remains in the current acknowledgement. |

The [file-by-file licensing inventory](../verification/LICENSE_INVENTORY.tsv) covers all original 129 paths plus seven added paths. Three original runtime paths are external dependencies; the repository bundles 133 files. [repository-manifest.json](../verification/repository-manifest.json) records current file sizes and hashes. [STEP24B_AUDIT.json](../verification/STEP24B_AUDIT.json) is the current compact record.

`COMBINED_VERIFICATION.json`, the Step 23 certificates and `manuscript-fidelity.json` retain their original bytes as historical evidence, including earlier PDF hashes and superseded pending decisions. The exact source/PDF delta below connects those records to this candidate; their old PDF hashes are not claimed as the current PDF hash.

## Exact approved change

The old acknowledgement on page 15 said:

> The authors reviewed the resulting changes and take full responsibility for the mathematical content and final presentation.

On 2026-10-17 Victor approved replacing those claims with:

> Victor Gabillon reviewed the resulting AI-assisted changes.

The preceding ChatGPT disclosure, all five research authors and all other acknowledgements remain unchanged. The applied patch matches the proposed patch exactly. `Main.tex` differs from Step 24 only by that literal byte replacement; the other 16 TeX files, eight figure assets and 69 Lean/configuration/verifier inputs are byte-identical. The only other source difference from Step 24 is the already audited nonprinting bibliography cleanup. There is no remaining acknowledgement approval to obtain.

## New PDF and reproduction evidence

Current PDF: **43 pages, 958,146 bytes**; SHA-256 `df406d32ccddbd0986803630925f12f3316282d04ac37b682a05ebed5ebe2820`.

Build A generated the approved version from an independent source-only copy under a path containing spaces, containing no previous target PDF or local class/style files. After the source/text/visual review, that PDF was installed as the candidate and checked reference. Build B used the same checked source inputs in a separate output directory and reproduced all bytes exactly. Both use Tectonic 0.17.0, the fixed v33 bundle, `SOURCE_DATE_EPOCH=1792195200`, the pinned external author-kit archive and populated resource caches with `--only-cached`. These are same-host builds using declared cache provisioning, not new OS or bundle installations.

Compared with the prior Step 24 PDF, extracted text on the other **42 pages is byte-identical**. On page 15, the only full-document text difference is the exact approved replacement, after normalizing typographic ligatures, line-end word hyphenation and whitespace. The generated bibliography is byte-identical. Page 15 was rendered and visually checked: the new sentence is clear, without observed clipping or overlap. This is a targeted visual review, not a claim of a new visual review of every unchanged page.

No unresolved citations/references, duplicate labels, missing figures or missing-character diagnostics remain. The two existing warnings are unchanged: 1.22124pt overfull hbox and 10.71179pt overfull vbox. All mathematics retains its source bytes; no new mathematical review or Lean rebuild was needed for this acknowledgement correction.

The earlier rc.3 PDF (`7c6ee873dfa54b67f4b702e2568de2dc4b1f0169d11824a5ce80f12f644c4e2b`) matched Step 24 exactly and remains in the preserved rc.3 archive. It is superseded by this expressly approved text correction. [DEPENDENCIES.md](../paper/DEPENDENCIES.md) retains the earlier author-kit compatibility explanation; the same inputs reproduce the current PDF.

## Rights, external inputs and remaining actions

[RIGHTS.md](../paper/RIGHTS.md) gives the five original authors, PMLR citation/link, CC BY 4.0 terms, author confirmation, modification notice and limitations. [LICENSING.md](LICENSING.md) separates paper, software and third-party rights. No rights-uncertain paper asset remains bundled. The three historical runtime files are already excluded, and [documented external dependencies](../paper/DEPENDENCIES.md) preserve complete manuscript reproduction. A Lean-only distribution remains possible but would not include or reproduce the paper; no such substitute is needed to resolve this candidate's rights.

The only remaining steps concern an actual upload: make/recheck the target as PRIVATE, review final staged contents and separately authorize commit/push. See [RELEASE_CHECKLIST.md](RELEASE_CHECKLIST.md). No commit, push, visibility change, upload, release or deposit has been performed.
