# External manuscript dependencies

`source/` contains 17 author-written TeX files, one bibliography and eight required experiment PDFs: **26 files**. It contains no LaTeX class, style or bibliography-style file, generated build output, backup or unknown-origin asset.

## Historical author kit

The [official COLT 2018 author instructions](https://www.learningtheory.org/colt2018/call.html) link to [Colt2018.zip](https://www.learningtheory.org/colt2018/files/Colt2018.zip). The build downloads that exact archive, verifies its SHA-256, and uses three members in a temporary directory. The archive and extracted members are not part of this repository or its release archive. [dependencies.json](dependencies.json) pins each input and records its provenance and license.

Archive: 595,993 bytes; SHA-256 `e4cacb9d2abbf964735e33314925ba654b5fdab01f9f12c50e87fa7040c59107`.

| Runtime input | Upstream SHA-256 | Rights and treatment |
| --- | --- | --- |
| `colt2018.cls` | `6b4162355f3fbd5b87b511a5c15718f4f381a0a0f0fcf9453c9aa05db115e703` | Official author-preparation wrapper; no explicit redistribution grant found. Fetch externally; do not bundle or relicense. |
| `jmlr.cls` | `f609fecec9cc317dce86075b473362a83a7d955cf486638da12adddda9ad8256` | Historical v1.24, copyright 2017 Nicola Talbot; header grants LPPL 1.3 or later. Unmodified external runtime file. |
| `jmlrutils.sty` | `9ca26b2d15e81082984ea376c941b49781cb37f4e3bb54419c8a41f1b63f79a4` | Same historical work and license; unmodified external runtime file. |

The [2017 CTAN v1.24 announcement](https://www.ctan.org/ctan-ann/id/mailman.367.1501695017.5064.ctan-ann%40ctan.org) independently identifies LPPL licensing. The [current JMLR package](https://ctan.org/pkg/jmlr) is newer and is not substituted for these historical files. Fetching the official author kit avoids redistributing an incomplete historical JMLR work in this source package; it does not claim that an arbitrary extracted subset could be redistributed without observing LPPL.

### Exact compatibility adjustment

The upstream COLT wrapper's printed editor line differs from the approved Step 24 wrapper. The build changes only this literal line in its temporary copy:

```tex
% upstream
\editors{Sebastien Bubeck, Vianney Perchet and Philippe Rigollet}
% approved Step 24 build input
\editors{S\'ebastien Bubeck, Vianney Perchet, and Philippe Rigollet}
```

The resulting whole-file SHA-256 must be `2b13ff9141736521cd2a33efd0a1449a4d05dccfefc12081ded03b3027f9eb4c`, exactly the Step 24 build input. The script checks that the old line occurs exactly once and that the complete result has this hash. This restores the editor accent and comma; it is not a whitespace-only adjustment. Without it, the PDF differs on the printed editor line and correctly fails the identity check. No class file is installed or persisted in `source/`, and no mathematical or manuscript text is edited.

## Compiler, bundle and other support files

Use **Tectonic 0.17.0**, `https://relay.fullyjustified.net/default_bundle_v33.tar`, and `SOURCE_DATE_EPOCH=1792195200`. The tested bundle cache identity is `6ffe055852f8faf66c0acbe1a7fb27f87b869a90bad1204f3bf4d9683f597c7c`. No engine, bundle or font is vendored. [latex-dependencies.json](latex-dependencies.json) lists the 86 `.cls`/`.sty` names and `plainnat.bst` observed in the successful build. Three names come from the author kit; the other 84 class/style/bibliography-style inputs come from the bundle. This is an observed support-file inventory, not a complete font/format resource manifest or a claim that every package has one license. Their upstream licenses apply separately; no Apache or CC grant is assigned to them.

The bibliography log confirms BibTeX 0.99d, `plainnat.bst` and `biblio.bib`. The successful rebuild has no unresolved citations/references, missing figures or missing-character diagnostics. Its two pre-existing overfull warnings are documented in [the audit](../docs/STEP24B_AUDIT.md).

## Commands

From the repository root, with the exact compiler on `PATH`:

```sh
python3 scripts/build-paper.py
python3 scripts/build-paper.py --only-cached
```

The first command may access the official author-kit URL and bundle. `PAPER_DEP_CACHE` selects the author-kit archive cache (default `.cache/paper-deps`); `XDG_CACHE_HOME` selects Tectonic's cache. `TECTONIC` selects the compiler executable. `--only-cached` permits neither an author-kit download nor a Tectonic resource download and fails if an input is absent. A checksum mismatch fails the build. Cached dependencies are provisioning inputs and are not licensed by this repository. Output is isolated under the ignored `paper/rebuild/` directory unless `--output PATH` is supplied.
