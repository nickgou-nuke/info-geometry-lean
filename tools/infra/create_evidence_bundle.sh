#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Create a reproducible legal-evidence bundle for this repository.

Usage:
  tools/infra/create_evidence_bundle.sh [options]

Options:
  --ref <git-ref>           Git ref to archive (default: HEAD)
  --prefix <name>           Archive directory prefix (default: info-geometry-lean)
  --out-dir <dir>           Output directory (default: archive/evidence/<UTC>_<shortsha>)
  --full-state              Archive current working tree state (excluding .git)
  --source-only             Archive only git-tracked source at --ref (default)
  --exclude-list <file>     Path prefixes (repo-relative) excluded from archive
                            (default: tools/infra/archive_excludes.txt if present)
  --no-exclusion-stubs      Do not place README stubs for excluded paths
  --with-pdf                Render certificate PDF with pandoc (if installed)
  --ots-stamp <mode>        OpenTimestamps blockchain stamp target:
                            pdf | archive | both
  --ots-upgrade             Run `ots upgrade` on generated .ots proof files
  --ots-cache-dir <dir>     Override XDG cache dir for ots client
  --lock-readonly           chmod bundle files/directories to read-only at the end
  --lock-immutable          Try chattr +i after read-only lock (Linux/ext fs; may fail)
  --help                    Show this help

Output files:
  <prefix>-<shortsha>-<UTC>.tgz
  <prefix>-<shortsha>-<UTC>.checksums.txt
  <prefix>-<shortsha>-<UTC>.certificate.md
  <prefix>-<shortsha>-<UTC>.metadata.txt
  LICENSE / NOTICE / CITATION.cff copies

Notes:
  - Archive uses `git archive` at a commit, not working tree contents.
  - In `--full-state` mode, the script first snapshots into an isolated temp tree.
  - Hashes: SHA-256, SHA-512, BLAKE2b (b2sum), SHA3-512 (openssl, if available).
  - OpenTimestamps requires `ots` to be installed if `--ots-stamp` is used.
USAGE
}

REF="HEAD"
PREFIX="info-geometry-lean"
OUT_DIR=""
WITH_PDF=0
LOCK_READONLY=0
LOCK_IMMUTABLE=0
EXCLUDE_LIST=""
ARCHIVE_MODE="source-only"
WRITE_STUBS=1
OTS_STAMP_MODE=""
OTS_UPGRADE=0
OTS_CACHE_DIR=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref)
      REF="${2:?missing value for --ref}"
      shift 2
      ;;
    --prefix)
      PREFIX="${2:?missing value for --prefix}"
      shift 2
      ;;
    --out-dir)
      OUT_DIR="${2:?missing value for --out-dir}"
      shift 2
      ;;
    --full-state)
      ARCHIVE_MODE="full-state"
      shift
      ;;
    --source-only)
      ARCHIVE_MODE="source-only"
      shift
      ;;
    --exclude-list)
      EXCLUDE_LIST="${2:?missing value for --exclude-list}"
      shift 2
      ;;
    --no-exclusion-stubs)
      WRITE_STUBS=0
      shift
      ;;
    --with-pdf)
      WITH_PDF=1
      shift
      ;;
    --ots-stamp)
      OTS_STAMP_MODE="${2:?missing value for --ots-stamp}"
      shift 2
      ;;
    --ots-upgrade)
      OTS_UPGRADE=1
      shift
      ;;
    --ots-cache-dir)
      OTS_CACHE_DIR="${2:?missing value for --ots-cache-dir}"
      shift 2
      ;;
    --lock-readonly)
      LOCK_READONLY=1
      shift
      ;;
    --lock-immutable)
      LOCK_IMMUTABLE=1
      LOCK_READONLY=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

case "$OTS_STAMP_MODE" in
  ""|pdf|archive|both) ;;
  *)
    echo "Invalid --ots-stamp value: $OTS_STAMP_MODE (expected pdf|archive|both)" >&2
    exit 2
    ;;
esac

if [[ "$OTS_STAMP_MODE" == "pdf" || "$OTS_STAMP_MODE" == "both" ]]; then
  WITH_PDF=1
fi

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

UTC_NOW="$(date -u +%Y%m%dT%H%M%SZ)"
COMMIT="$(git rev-parse "$REF")"
SHORT_SHA="$(git rev-parse --short=12 "$REF")"
SUBJECT="$(git show -s --format=%s "$REF")"
COMMIT_TIME="$(git show -s --format=%cI "$REF")"

if [[ -z "$OUT_DIR" ]]; then
  OUT_DIR="$ROOT/archive/evidence/${UTC_NOW}_${SHORT_SHA}"
fi
mkdir -p "$OUT_DIR"

if [[ -z "$EXCLUDE_LIST" && -f "$ROOT/tools/infra/archive_excludes.txt" ]]; then
  EXCLUDE_LIST="$ROOT/tools/infra/archive_excludes.txt"
fi

BASENAME="${PREFIX}-${SHORT_SHA}-${UTC_NOW}"
ARCHIVE_PATH="$OUT_DIR/${BASENAME}.tgz"
CHECKSUM_PATH="$OUT_DIR/${BASENAME}.checksums.txt"
CERT_MD_PATH="$OUT_DIR/${BASENAME}.certificate.md"
META_PATH="$OUT_DIR/${BASENAME}.metadata.txt"

TMP_DIR="$(mktemp -d)"
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

if [[ "$ARCHIVE_MODE" == "full-state" ]]; then
  mkdir -p "$TMP_DIR/$PREFIX"
  # Freeze into isolated workspace first to avoid archiving a mutating live tree.
  if command -v rsync >/dev/null 2>&1; then
    rsync -a --delete \
      --exclude='.git' \
      --exclude='archive/evidence' \
      --exclude='archive/public-release' \
      "$ROOT/" "$TMP_DIR/$PREFIX/"
  else
    # Fallback if rsync is unavailable.
    tar -C "$ROOT" \
        --exclude=.git \
        --exclude=archive/evidence \
        --exclude=archive/public-release \
        -cf - . | tar -xf - -C "$TMP_DIR/$PREFIX"
  fi
else
  git archive --format=tar --prefix="${PREFIX}/" "$COMMIT" | tar -xf - -C "$TMP_DIR"
fi

if [[ -n "$EXCLUDE_LIST" && -f "$EXCLUDE_LIST" ]]; then
  while IFS= read -r raw_line; do
    line="$(printf '%s' "$raw_line" | sed 's/#.*$//' | xargs)"
    [[ -z "$line" ]] && continue
    rm -rf "$TMP_DIR/$PREFIX/$line"
    if [[ "$WRITE_STUBS" -eq 1 ]]; then
      stub_dir="$TMP_DIR/$PREFIX/${line%/}"
      mkdir -p "$stub_dir"
      cat > "$stub_dir/README.EXCLUDED.md" <<EOF
# Excluded Path Stub

This path was intentionally excluded from the generated archive bundle.

- Path prefix: \`${line}\`
- Exclusion list: \`${EXCLUDE_LIST}\`
- Archive mode: \`${ARCHIVE_MODE}\`

Reason: third-party or out-of-scope payload separation for legal/compliance release lanes.
EOF
    fi
  done < "$EXCLUDE_LIST"
fi

tar --sort=name \
    --mtime='UTC 1970-01-01' \
    --owner=0 --group=0 --numeric-owner \
    -C "$TMP_DIR" -cf - "$PREFIX" | gzip -n > "$ARCHIVE_PATH"

SHA256="$(sha256sum "$ARCHIVE_PATH" | awk '{print $1}')"
SHA512="$(sha512sum "$ARCHIVE_PATH" | awk '{print $1}')"
B2SUM=""
SHA3_512=""

if command -v b2sum >/dev/null 2>&1; then
  B2SUM="$(b2sum "$ARCHIVE_PATH" | awk '{print $1}')"
fi

if command -v openssl >/dev/null 2>&1; then
  SHA3_512="$(openssl dgst -sha3-512 "$ARCHIVE_PATH" | sed -E 's/^SHA3-512\([^)]+\)= //')"
fi

{
  echo "# checksum manifest"
  echo "# file: $(basename "$ARCHIVE_PATH")"
  echo "# generated_utc: ${UTC_NOW}"
  echo "# git_ref: ${REF}"
  echo "# git_commit: ${COMMIT}"
  echo "# git_commit_time: ${COMMIT_TIME}"
  echo "SHA256 ${SHA256}"
  echo "SHA512 ${SHA512}"
  if [[ -n "$B2SUM" ]]; then
    echo "BLAKE2B-512 ${B2SUM}"
  fi
  if [[ -n "$SHA3_512" ]]; then
    echo "SHA3-512 ${SHA3_512}"
  fi
} > "$CHECKSUM_PATH"

cp LICENSE "$OUT_DIR/LICENSE"
cp NOTICE "$OUT_DIR/NOTICE"
cp CITATION.cff "$OUT_DIR/CITATION.cff"
if [[ -f "$ROOT/tools/infra/verify_evidence_bundle.sh" ]]; then
  cp "$ROOT/tools/infra/verify_evidence_bundle.sh" "$OUT_DIR/verify_evidence_bundle.sh"
  chmod +x "$OUT_DIR/verify_evidence_bundle.sh"
fi
if [[ -f "$ROOT/tools/infra/verify_certificate_hash_binding.sh" ]]; then
  cp "$ROOT/tools/infra/verify_certificate_hash_binding.sh" "$OUT_DIR/verify_certificate_hash_binding.sh"
  chmod +x "$OUT_DIR/verify_certificate_hash_binding.sh"
fi

cat > "$OUT_DIR/VERIFY.md" <<'EOF'
# Bundle Verification (Outside Repo)

Run these commands from any directory (no repo checkout required):

```bash
./verify_evidence_bundle.sh .
./verify_certificate_hash_binding.sh .
```

If OpenTimestamps proof exists:

```bash
ots verify *.certificate.pdf.ots
```
EOF

{
  echo "bundle_name=${BASENAME}"
  echo "archive_file=$(basename "$ARCHIVE_PATH")"
  echo "archive_size_bytes=$(wc -c < "$ARCHIVE_PATH" | tr -d ' ')"
  echo "generated_utc=${UTC_NOW}"
  echo "archive_mode=${ARCHIVE_MODE}"
  echo "git_ref=${REF}"
  echo "git_commit=${COMMIT}"
  echo "git_commit_short=${SHORT_SHA}"
  echo "git_commit_time=${COMMIT_TIME}"
  echo "git_subject=${SUBJECT}"
  echo "repo_root=${ROOT}"
  echo "bundle_self_verify_scripts=verify_evidence_bundle.sh,verify_certificate_hash_binding.sh"
  if [[ -n "$EXCLUDE_LIST" && -f "$EXCLUDE_LIST" ]]; then
    echo "exclude_list=${EXCLUDE_LIST}"
    echo "excluded_paths_begin"
    sed '/^\s*#/d;/^\s*$/d' "$EXCLUDE_LIST"
    echo "excluded_paths_end"
  fi
  echo "remotes_begin"
  git remote -v
  echo "remotes_end"
} > "$META_PATH"

ORIGIN_URL="$(git remote get-url origin 2>/dev/null || true)"
UPSTREAM_URL="$(git remote get-url upstream 2>/dev/null || true)"

{
  echo "# Archive Evidence Certificate"
  echo
  echo "This certificate binds a reproducible source archive to repository metadata,"
  echo "copyright metadata, and cryptographic checksums."
  echo
  echo "## Repository Identity"
  echo "- Project: \`${PREFIX}\`"
  echo "- Commit: \`${COMMIT}\`"
  echo "- Commit timestamp: \`${COMMIT_TIME}\`"
  echo "- Commit subject: ${SUBJECT}"
  echo "- Archive mode: \`${ARCHIVE_MODE}\`"
  if [[ -n "$ORIGIN_URL" ]]; then
    echo "- Origin remote: \`${ORIGIN_URL}\`"
  fi
  if [[ -n "$UPSTREAM_URL" ]]; then
    echo "- Upstream remote: \`${UPSTREAM_URL}\`"
  fi
  echo
  echo "## Legal Metadata (copied into bundle)"
  echo "- License: Apache-2.0 (\`LICENSE\`)"
  echo "- Notice/copyright: \`NOTICE\`"
  echo "- Citation metadata: \`CITATION.cff\`"
  echo "- Copyright holders (per NOTICE):"
  echo "  - Nikolay Goutev"
  echo "  - Dimitar Tonev"
  echo
  echo "## Archive Object"
  echo "- File: \`$(basename "$ARCHIVE_PATH")\`"
  echo "- Size (bytes): \`$(wc -c < "$ARCHIVE_PATH" | tr -d ' ')\`"
  echo "- Generated UTC: \`${UTC_NOW}\`"
  if [[ -n "$EXCLUDE_LIST" && -f "$EXCLUDE_LIST" ]]; then
    echo "- Exclusion policy file: \`${EXCLUDE_LIST}\`"
    echo "- Excluded path prefixes:"
    sed '/^\s*#/d;/^\s*$/d;s/^/  - /' "$EXCLUDE_LIST"
  fi
  echo
  echo "## Checksums"
  echo "- SHA-256: \`${SHA256}\`"
  echo "- SHA-512: \`${SHA512}\`"
  if [[ -n "$B2SUM" ]]; then
    echo "- BLAKE2b-512: \`${B2SUM}\`"
  fi
  if [[ -n "$SHA3_512" ]]; then
    echo "- SHA3-512: \`${SHA3_512}\`"
  fi
  echo
  echo "## Qualified Electronic Signature Block"
  echo "- Signer 1: Nikolay Goutev"
  echo "- Signer 2: Dimitar Tonev"
  echo "- Signature format/container: ______________________________"
  echo "- Qualified trust service provider (QTSP): __________________"
  echo "- Signature timestamp (UTC): _______________________________"
  echo
  echo "## External Time Anchors"
  echo "- RFC3161 timestamp token file: _____________________________"
  echo "- Blockchain network: _______________________________________"
  echo "- Transaction ID / anchor proof: ____________________________"
  echo
  echo "## Verification Notes"
  echo "- Recompute hashes from the archive and compare to this certificate."
  echo "- Validate QES signatures against the signer certificate chain."
  echo "- Validate RFC3161 and blockchain anchor proofs independently."
} > "$CERT_MD_PATH"

if [[ "$WITH_PDF" -eq 1 ]]; then
  if command -v pandoc >/dev/null 2>&1; then
    pandoc "$CERT_MD_PATH" -o "${CERT_MD_PATH%.md}.pdf"
  else
    echo "WARN: --with-pdf set but pandoc not found; skipping PDF render." >&2
  fi
fi

OTS_PROOF_LIST=()
if [[ -n "$OTS_STAMP_MODE" ]]; then
  if ! command -v ots >/dev/null 2>&1; then
    echo "ERROR: --ots-stamp requested but 'ots' command is not installed." >&2
    echo "Install OpenTimestamps client and rerun." >&2
    exit 3
  fi

  if [[ -z "$OTS_CACHE_DIR" ]]; then
    OTS_CACHE_DIR="$OUT_DIR/.ots-cache"
  fi
  mkdir -p "$OTS_CACHE_DIR"
  export XDG_CACHE_HOME="$OTS_CACHE_DIR"

  stamp_target() {
    local target="$1"
    if [[ ! -f "$target" ]]; then
      echo "WARN: OTS target missing, skipped: $target" >&2
      return
    fi
    ots stamp "$target"
    local proof="${target}.ots"
    if [[ -f "$proof" ]]; then
      OTS_PROOF_LIST+=("$(basename "$proof")")
      if [[ "$OTS_UPGRADE" -eq 1 ]]; then
        ots upgrade "$proof" || echo "WARN: ots upgrade failed for $proof" >&2
      fi
    fi
  }

  case "$OTS_STAMP_MODE" in
    pdf)
      stamp_target "${CERT_MD_PATH%.md}.pdf"
      ;;
    archive)
      stamp_target "$ARCHIVE_PATH"
      ;;
    both)
      stamp_target "${CERT_MD_PATH%.md}.pdf"
      stamp_target "$ARCHIVE_PATH"
      ;;
  esac

  if [[ "${#OTS_PROOF_LIST[@]}" -gt 0 ]]; then
    {
      echo
      echo "## OpenTimestamps Proofs Generated"
      for pf in "${OTS_PROOF_LIST[@]}"; do
        echo "- ${pf}"
      done
      if [[ "$OTS_UPGRADE" -eq 1 ]]; then
        echo "- upgrade: requested (`ots upgrade` attempted)"
      fi
    } >> "$CERT_MD_PATH"

    if [[ -f "${CERT_MD_PATH%.md}.pdf" && ( "$OTS_STAMP_MODE" == "archive" ) ]]; then
      # Keep PDF in sync with markdown metadata when only archive stamping is used.
      if command -v pandoc >/dev/null 2>&1; then
        pandoc "$CERT_MD_PATH" -o "${CERT_MD_PATH%.md}.pdf"
      fi
    fi

    {
      echo "ots_stamp_mode=${OTS_STAMP_MODE}"
      echo "ots_upgrade_requested=${OTS_UPGRADE}"
      echo "ots_cache_dir=${OTS_CACHE_DIR}"
      echo "ots_proofs_begin"
      for pf in "${OTS_PROOF_LIST[@]}"; do
        echo "$pf"
      done
      echo "ots_proofs_end"
    } >> "$META_PATH"
  fi
fi

if [[ "$LOCK_READONLY" -eq 1 ]]; then
  find "$OUT_DIR" -type f -exec chmod 0444 {} +
  find "$OUT_DIR" -type d -exec chmod 0555 {} +
fi

if [[ "$LOCK_IMMUTABLE" -eq 1 ]]; then
  if command -v chattr >/dev/null 2>&1; then
    # chattr can fail depending on FS/permissions; do not abort bundle creation.
    chattr +i "$OUT_DIR" "$OUT_DIR"/* 2>/dev/null || {
      echo "WARN: chattr +i failed (filesystem or permission restriction)." >&2
    }
  else
    echo "WARN: chattr not available; immutable flag not applied." >&2
  fi
fi

echo "Evidence bundle created:"
echo "  $OUT_DIR"
echo "Primary files:"
echo "  $ARCHIVE_PATH"
echo "  $CHECKSUM_PATH"
echo "  $CERT_MD_PATH"
echo "  $META_PATH"
