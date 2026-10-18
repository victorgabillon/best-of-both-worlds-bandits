# Corrected manuscript

[corrected-paper.pdf](corrected-paper.pdf) is the corrected **44-page** manuscript, an adaptation of the [COLT 2018 publication](https://proceedings.mlr.press/v75/abbasi-yadkori18a.html), not the official proceedings PDF. It retains the five original research authors and the completed E3 editorial revision, followed by the approved acknowledgement correction and five prose changes on 2026-10-18. [RIGHTS.md](RIGHTS.md) provides attribution, the CC BY 4.0 grant, modification notice and separate dependency rights.

## Rebuild

Install **Tectonic 0.17.0** from the [official project](https://tectonic-typesetting.github.io/en-US/install.html); put that exact version on `PATH` or set `TECTONIC` to its executable. Python 3 is also needed. From the repository root:

```sh
python3 scripts/build-paper.py
```

The script verifies the official external author-kit hashes, uses the fixed v33 bundle and `SOURCE_DATE_EPOCH=1792195200`, and builds a temporary copy with `--untrusted`. A hash-checked editor-line compatibility adjustment restores the exact approved historical build input; no manuscript source is edited. All details, including dependency origins and license distinctions, are in [DEPENDENCIES.md](DEPENDENCIES.md).

For populated author-kit and compiler-resource caches:

```sh
python3 scripts/build-paper.py --only-cached
```

`PAPER_DEP_CACHE` selects the author-kit cache (default `.cache/paper-deps`); `XDG_CACHE_HOME` selects the Tectonic cache. Output is `paper/rebuild/`, with logs and summary. `--output PATH` selects another output directory. No compiler binary, archive cache, class/style file or TeX build output is bundled.

The clean-source rebuild matches [corrected-paper.pdf.sha256](corrected-paper.pdf.sha256): **959,734 bytes**, SHA-256 `ddcf0bb137c9fe71abd1317e56ba4f841712edb2f9932fe0055eed5db97cd4d2`. Two builds match this revised PDF byte for byte. The five approved prose changes add explanations to the proof sketches and full proofs of Theorems 2 and 4, and update the introduction's public repository notice. The added text changes pagination from 43 to 44 pages. The generated bibliography is byte-identical to the initial public version. The existing two overfull warnings remain; no unresolved citations/references or missing-character diagnostics remain. Other engines/bundle versions are not certified to give identical bytes.

## Included source and factual issue

`source/` contains exactly 17 TeX files, `biblio.bib` and eight experiment PDFs. Relative to initial public commit `6dedfd811608ff70a39eb49276eb31be4d5db9b6`, exactly five TeX files have the approved prose changes: `upLowGenAd.tex`, `appLOWAd.tex`, `lowerBoundBOB.tex`, `appLOWBOB.tex` and `intro.tex`. Reversing those five replacements recovers the original source bytes. All other TeX, bibliography and figure files are unchanged, including Theorem 6's sketch and full proof. No theorem statement, formula, assumption, constant, algorithm or mathematical derivation changes. Historical nonprinting comments remain as originally published. Unnecessary historical class/style files are supplied externally rather than redistributed.

The acknowledgement, now on page 16, says “Victor Gabillon reviewed the resulting AI-assisted changes.” Victor explicitly approved that exact replacement and a PDF rebuild during Step 24B. The acknowledgement and preceding ChatGPT disclosure are unchanged by the subsequent prose update. See [STEP24B_AUDIT.md](../docs/STEP24B_AUDIT.md) for that historical approval and reproduction record, and [PROVENANCE.md](../docs/PROVENANCE.md#approved-expository-update-2026-10-18) for the current editorial update.
