# Component licenses

**Licensing: RESOLVED on the recorded publisher terms and author confirmation. Attribution: approved correction applied. Step 25 explicitly authorizes this initial public repository publication.** See the [current audit](STEP24B_AUDIT.md).

| Component | License and evidence |
| --- | --- |
| New Lean formalization, original verification tooling and associated formalization documentation | [Apache-2.0](../LICENSE), approved by the author; [NOTICE](../NOTICE) defines scope without assigning sole ownership to the maintainer. The standard license text and all Lean proofs remain unchanged. |
| Published article and its corrected adaptation, author-written TeX source, bibliography selection, adapted experiment figures | [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). PMLR's existing grant covers the published article; Victor Gabillon separately confirmed authority to release additional contributions under CC BY 4.0 on 2026-10-17. [RIGHTS.md](../paper/RIGHTS.md) supplies the original five authors, citation, publisher link, modification notice and limits. |
| Historical JMLR runtime files | LPPL 1.3 or later, as specified by Nicola Talbot's 2017 headers and the contemporary CTAN announcement. Fetched unchanged from the official COLT kit, not bundled or relicensed. |
| COLT 2018 class wrapper | No explicit redistribution grant found. Fetched as an official external author-preparation dependency, not bundled or relicensed; an explicit temporary editor-line compatibility adjustment preserves the approved PDF. |
| Other TeX classes, packages, bibliography style and fonts | Their respective upstream licenses; retrieved through the external Tectonic bundle. No common Apache/CC license is asserted for these files. |
| Verbatim LPPL reference text | Its existing notice allows verbatim distribution. Retained unmodified, not relicensed as paper or software content. |
| Separately retrieved Lean, Mathlib and locked Lake dependencies | Existing upstream licenses and notices. Lean/Mathlib and eight locked packages use Apache-2.0; Cli uses MIT. Their repositories, binaries and caches are not included. |

The [complete file-by-file inventory](../verification/LICENSE_INVENTORY.tsv) records the original 129-file set and each added path, including disposition of the three excluded runtime files. Current hashes are in [repository-manifest.json](../verification/repository-manifest.json). [DEPENDENCIES.md](../paper/DEPENDENCIES.md) and its JSON inventories give exact external inputs.

No additional grant is required for material already covered by the published article's CC BY license. The additional-contribution confirmation addresses the distinct issue of rights beyond that original grant. It does not assert ownership of external packages or all work by one author. Historical Step 24 pending-rights findings are preserved in the unchanged Step 24 certificate; they are superseded by the evidence in the current audit.

The author approved the exact factual acknowledgement correction on 2026-10-17, and it is now applied: “Victor Gabillon reviewed the resulting AI-assisted changes.” The Step 24B 43-page PDF reproduced exactly in two builds. The [subsequent five prose changes](PROVENANCE.md#approved-expository-update-2026-10-18) preserve that acknowledgement and all mathematics; the current 44-page PDF also reproduces exactly in two builds. No licensing or acknowledgement permission remains pending. The author subsequently authorized the initial public commit and push in Step 25 and instructed that the target remain PUBLIC. No official versioned release, tag or deposit is included in that authorization.
