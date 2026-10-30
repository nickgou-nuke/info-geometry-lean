#!/usr/bin/env python3
"""Embed an exported ancestry packet into the offline HTML explorer."""
import argparse
import hashlib
import json
import shutil
from pathlib import Path


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path("phylogeny.json"))
    parser.add_argument("--template", type=Path,
                        default=Path(__file__).with_name("repository-phylogeny.template.html"))
    parser.add_argument("--out", type=Path, default=Path("repository-phylogeny.html"))
    parser.add_argument("--hodge", type=Path, help="Optional exact Hodge report for this data file")
    args = parser.parse_args(argv)
    companion = Path(__file__).with_name("dna-affinity-viewer.html")
    companion_out = args.out.parent / companion.name
    protected = {args.data.resolve(), args.template.resolve(), companion.resolve()}
    if args.hodge:
        protected.add(args.hodge.resolve())
    if args.out.resolve() in protected or args.out.resolve() == companion_out.resolve():
        parser.error("output must not overwrite an input, template or companion viewer")
    if companion_out.resolve() in protected and companion_out.resolve() != companion.resolve():
        parser.error("companion viewer would overwrite an input file")
    data = json.loads(args.data.read_text(encoding="utf-8"))
    if data.get("schema") not in {"repo-phylogeny/v1", "repo-phylogeny/v2"}:
        parser.error("expected a supported repo-phylogeny/v1 or /v2 export")
    template = args.template.read_text(encoding="utf-8")
    if template.count("__PHYLOGENY_DATA__") != 1:
        parser.error("template must contain exactly one data placeholder")
    if template.count("__HODGE_DATA__") != 1:
        parser.error("template must contain exactly one Hodge placeholder")
    hodge = None
    if args.hodge:
        hodge = json.loads(args.hodge.read_text(encoding="utf-8"))
        if hodge.get("schema") != "ancestry-hodge/v1":
            parser.error("expected an ancestry-hodge/v1 report")
        if hodge.get("source", {}).get("sha256") != hashlib.sha256(args.data.read_bytes()).hexdigest():
            parser.error("Hodge report does not match the exact supplied data bytes")
        checks = hodge.get("checks")
        if hodge.get("all_exact_checks_passed") is not True or not isinstance(checks, dict) or not checks or any(value is not True for value in checks.values()):
            parser.error("Hodge report must contain successful exact checks")
    encoded = json.dumps(data, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
    encoded = encoded.replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    hodge_json = json.dumps(hodge, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
    hodge_json = hodge_json.replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    rendered = template.replace("__PHYLOGENY_DATA__", encoded).replace("__HODGE_DATA__", hodge_json)
    args.out.write_text(rendered, encoding="utf-8")
    if companion.resolve() != companion_out.resolve():
        shutil.copyfile(companion, companion_out)
    print(args.out)


if __name__ == "__main__":
    main()
