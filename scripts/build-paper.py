#!/usr/bin/env python3
"""Build the paper in an isolated output directory; never edit its TeX sources."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = "https://relay.fullyjustified.net/default_bundle_v33.tar"
EPOCH = "1792195200"  # 2026-10-17 00:00:00 UTC


def external_support(work, only_cached):
    """Fetch exact upstream inputs, without vendoring their source in the repo."""
    specification = json.loads((ROOT / "paper/dependencies.json").read_text())
    archive_spec = specification["author_kit"]
    cache = Path(os.environ.get("PAPER_DEP_CACHE", ROOT / ".cache/paper-deps"))
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / (archive_spec["sha256"] + ".zip")
    if not archive.is_file():
        if only_cached:
            raise SystemExit("Official author kit not cached; run once without --only-cached.")
        data = urllib.request.urlopen(archive_spec["url"], timeout=30).read(5_000_001)
        if len(data) > 5_000_000 or hashlib.sha256(data).hexdigest() != archive_spec["sha256"]:
            raise SystemExit("Official author-kit checksum/size mismatch.")
        with tempfile.NamedTemporaryFile(dir=cache, delete=False) as handle:
            handle.write(data)
            temporary = Path(handle.name)
        temporary.replace(archive)
    if hashlib.sha256(archive.read_bytes()).hexdigest() != archive_spec["sha256"]:
        raise SystemExit("Cached official author-kit checksum mismatch.")
    checked = {}
    with zipfile.ZipFile(archive) as upstream:
        for name, expected in specification["build_files"].items():
            if Path(name).name != name or (work / name).exists():
                raise SystemExit("Unexpected/conflicting external support filename.")
            data = upstream.read(name)
            digest = hashlib.sha256(data).hexdigest()
            if digest != expected["sha256"]:
                raise SystemExit("External support checksum mismatch: " + name)
            patch = expected.get("compatibility_patch")
            if patch:
                old, new = patch["old"].encode(), patch["new"].encode()
                if data.count(old) != 1:
                    raise SystemExit("External support compatibility anchor mismatch.")
                data = data.replace(old, new, 1)
                if hashlib.sha256(data).hexdigest() != patch["result_sha256"]:
                    raise SystemExit("External support compatibility result mismatch.")
            (work / name).write_bytes(data)
            checked[name] = {"upstream_sha256": digest,
                             "build_input_sha256": hashlib.sha256(data).hexdigest()}
    return {"archive_sha256": archive_spec["sha256"], "build_files": checked}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only-cached", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "paper/rebuild")
    args = parser.parse_args()
    compiler = shutil.which(os.environ.get("TECTONIC", "tectonic"))
    if not compiler:
        raise SystemExit("Tectonic 0.17.0 is required on PATH (or set TECTONIC).")
    version = subprocess.check_output([compiler, "--version"], text=True).strip()
    if version != "Tectonic 0.17.0":
        raise SystemExit("Expected Tectonic 0.17.0; found " + version)
    output = args.output.resolve()
    source = ROOT / "paper/source"
    if output == source or source in output.parents:
        raise SystemExit("Build output must be outside paper/source.")
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, SOURCE_DATE_EPOCH=EPOCH)
    with tempfile.TemporaryDirectory(prefix="paper-source-", dir=output) as temporary:
        work = Path(temporary)
        for p in source.rglob("*"):
            if p.is_symlink():
                raise SystemExit("Unexpected source symlink: " + str(p.relative_to(source)))
            if p.is_file():
                dest = work / p.relative_to(source)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(p, dest)
        support = external_support(work, args.only_cached)
        command = [compiler, "--bundle", BUNDLE, "--untrusted", "--keep-logs",
                   "--keep-intermediates", "--makefile-rules", "dependencies.mk"]
        if args.only_cached:
            command.append("--only-cached")
        command.append("Main.tex")
        run = subprocess.run(command, cwd=work, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
        (output / "build-output.log").write_text(run.stdout)
        for name in ("Main.log", "Main.aux", "Main.bbl", "Main.blg", "dependencies.mk"):
            if (work / name).is_file():
                shutil.copyfile(work / name, output / name)
        if run.returncode:
            raise SystemExit("Paper build failed; see " + str(output / "build-output.log"))
        log = (work / "Main.log").read_text(errors="replace")
        problems = [line for line in log.splitlines() if line.startswith("!") or
                    re.search(r"undefined references|multiply-defined labels|rerun to get cross-references|missing character|Citation .+ undefined", line, re.I)]
        if problems:
            raise SystemExit("Unresolved manuscript diagnostics: " + "\n".join(problems))
        pdf = output / "corrected-paper.pdf"
        shutil.copyfile(work / "Main.pdf", pdf)
    digest = hashlib.sha256(pdf.read_bytes()).hexdigest()
    intended = ROOT / "paper/corrected-paper.pdf"
    matches = None if not intended.is_file() else pdf.read_bytes() == intended.read_bytes()
    record = {"status": "failed" if matches is False else "passed", "compiler": version, "bundle": BUNDLE,
              "source_date_epoch": int(EPOCH), "bytes": pdf.stat().st_size,
              "sha256": digest, "matches_included_pdf": matches,
              "external_support": support,
              "overfull_warnings": re.findall(r"Overfull \\[hv]box[^\n]*", log)}
    (output / "summary.json").write_text(json.dumps(record, indent=2) + "\n")
    if matches is False:
        raise SystemExit("Rebuilt PDF differs from the included PDF; see " + str(output / "summary.json"))
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
