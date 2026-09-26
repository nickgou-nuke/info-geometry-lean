#!/usr/bin/env bash
set -euo pipefail

# Verify the repository's reproducible Lean inputs without resolving anything.
# This is intentionally read-only: CI must consume lake-manifest.json as pinned.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

for required in lean-toolchain lakefile.lean lake-manifest.json; do
  if [[ ! -f "$required" ]]; then
    echo "[pin-check] missing required file: $required" >&2
    exit 1
  fi
done

expected_toolchain='leanprover/lean4:v4.28.1'
EXPECTED_MATHLIB_REV='1f9fffd5ff0b854b8a1f1f69adc11c61f05f2515'
actual_toolchain="$(tr -d '\r' < lean-toolchain)"
if [[ "$actual_toolchain" != "$expected_toolchain" ]]; then
  echo "[pin-check] expected $expected_toolchain, found $actual_toolchain" >&2
  exit 1
fi

EXPECTED_MATHLIB_REV="$EXPECTED_MATHLIB_REV" python3 - <<'PY'
import json
import os
import re
from pathlib import Path

manifest = json.loads(Path("lake-manifest.json").read_text(encoding="utf-8"))
packages = manifest.get("packages")
if not isinstance(packages, list):
    raise SystemExit("[pin-check] lake-manifest.json has no packages array")

manifest_revs = {}
mathlib_entries = []
for package in packages:
    if not isinstance(package, dict):
        raise SystemExit("[pin-check] malformed package entry in lake-manifest.json")
    if package.get("type") == "git":
        name = package.get("name")
        rev = package.get("inputRev") or package.get("rev")
        if not isinstance(name, str) or not isinstance(rev, str) or not rev:
            raise SystemExit(f"[pin-check] malformed git package entry: {package!r}")
        manifest_revs[name] = rev
    if package.get("name") == "mathlib":
        mathlib_entries.append(package)

expected_mathlib_rev = os.environ["EXPECTED_MATHLIB_REV"]
if len(mathlib_entries) != 1:
    raise SystemExit("[pin-check] expected exactly one root mathlib manifest entry")
mathlib_rev = mathlib_entries[0].get("inputRev") or mathlib_entries[0].get("rev")
if mathlib_rev != expected_mathlib_rev:
    raise SystemExit(
        f"[pin-check] expected root mathlib {expected_mathlib_rev}, found {mathlib_rev!r}"
    )

source = Path("lakefile.lean").read_text(encoding="utf-8")
# Lake permits quoted identifiers such as «doc-gen4» and line breaks between
# the URL and revision, so match the declaration rather than a single line.
pattern = re.compile(
    r'require\s+(?P<name>«[^»]+»|[A-Za-z_][A-Za-z0-9_]*)\s+'
    r'from\s+git\s+"[^"]+"\s*@\s*"(?P<rev>[^"]+)"',
    re.MULTILINE,
)
declared = {m.group("name"): m.group("rev") for m in pattern.finditer(source)}
if not declared:
    raise SystemExit("[pin-check] no git requirements found in lakefile.lean")

missing = sorted(set(declared) - set(manifest_revs))
if missing:
    raise SystemExit("[pin-check] git requirements missing from manifest: " + ", ".join(missing))

mismatches = []
symbolic = []
for name in sorted(declared):
    source_rev = declared[name]
    manifest_rev = manifest_revs[name]
    if source_rev == manifest_rev:
        continue
    # A tag is resolved to its immutable commit by Lake and recorded in the
    # manifest. We cannot prove tag ownership offline, but we can ensure the
    # resolved commit is present and reserve exact equality for SHA pins.
    if re.fullmatch(r"[0-9a-fA-F]{40}", source_rev):
        mismatches.append(
            f"{name}: lakefile={source_rev!r}, manifest={manifest_rev!r}"
        )
    else:
        symbolic.append(f"{name}={source_rev} -> {manifest_rev}")
if mismatches:
    raise SystemExit("[pin-check] pinned revision mismatch:\n  " + "\n  ".join(mismatches))

print(f"[pin-check] verified Lean {Path('lean-toolchain').read_text().strip()} and {len(declared)} git package pins")
print(f"[pin-check] verified root mathlib revision {expected_mathlib_rev}")
for item in symbolic:
    print(f"[pin-check] resolved symbolic pin: {item}")
PY

# Third-party packages may record their own compatible toolchains. Do not
# rewrite or reject those dependency-owned files; the root project and its
# exact Mathlib checkout are the pinned inputs checked above.
if [[ -d .lake/packages ]]; then
  mathlib_head="$(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || true)"
  if [[ "$mathlib_head" != "$EXPECTED_MATHLIB_REV" ]]; then
    echo "[pin-check] expected mathlib checkout $EXPECTED_MATHLIB_REV, found ${mathlib_head:-missing}" >&2
    exit 1
  fi
else
  echo "[pin-check] .lake/packages absent; skipping checkout revision check"
fi
