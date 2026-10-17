# Corrected manuscript

[corrected-paper.pdf](corrected-paper.pdf) is the corrected **43-page** manuscript, an adaptation of the [COLT 2018 publication](https://proceedings.mlr.press/v75/abbasi-yadkori18a.html), not the official proceedings PDF. It retains the five original research authors, the completed E3 editorial revision and Step 24's repository notice. [RIGHTS.md](RIGHTS.md) provides attribution, the CC BY 4.0 grant, modification notice and separate dependency rights.

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

The exact new clean-source rebuild matches [corrected-paper.pdf.sha256](corrected-paper.pdf.sha256): **958,146 bytes**, SHA-256 `df406d32ccddbd0986803630925f12f3316282d04ac37b682a05ebed5ebe2820`. Two builds match this revised PDF byte for byte. Compared with Step 24, only the acknowledgement text on page 15 changes; extracted text on the other 42 pages and the generated bibliography are identical. The comparison normalizes typographic ligatures and line-end word hyphenation when checking the approved sentence. The existing two overfull warnings remain; no unresolved citations/references or missing-character diagnostics remain. Other engines/bundle versions are not certified to give identical bytes.

## Included source and factual issue

`source/` contains exactly 17 TeX files, `biblio.bib` and eight experiment PDFs. Sixteen TeX files and all figure bytes match Step 24. `Main.tex` differs only by the explicitly approved acknowledgement correction. Only two nonprinting bibliography fields were removed: a copied third-party abstract and an old local attachment path. The generated bibliography remains identical. Unnecessary historical class/style files are supplied externally rather than redistributed.

The acknowledgement on page 15 now says “Victor Gabillon reviewed the resulting AI-assisted changes.” Victor explicitly approved that exact replacement and a PDF rebuild. The preceding ChatGPT disclosure and all other manuscript text remain unchanged. See [STEP24B_AUDIT.md](../docs/STEP24B_AUDIT.md) for the complete approval and reproduction record.
