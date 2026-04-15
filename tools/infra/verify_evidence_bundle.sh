#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Verify checksums inside an evidence bundle created by create_evidence_bundle.sh.

Usage:
  tools/infra/verify_evidence_bundle.sh <bundle-dir>

Expected files in bundle-dir:
  *.tgz
  *.checksums.txt
USAGE
}

if [[ $# -ne 1 ]]; then
  usage >&2
  exit 2
fi

BUNDLE_DIR="$1"
if [[ ! -d "$BUNDLE_DIR" ]]; then
  echo "Bundle directory not found: $BUNDLE_DIR" >&2
  exit 2
fi

ARCHIVE_FILE="$(find "$BUNDLE_DIR" -maxdepth 1 -type f -name '*.tgz' | head -n 1)"
CHECKSUM_FILE="$(find "$BUNDLE_DIR" -maxdepth 1 -type f -name '*.checksums.txt' | head -n 1)"

if [[ -z "$ARCHIVE_FILE" || -z "$CHECKSUM_FILE" ]]; then
  echo "Missing archive or checksum manifest in: $BUNDLE_DIR" >&2
  exit 2
fi

get_hash() {
  local alg="$1"
  awk -v a="$alg" '$1 == a { print $2 }' "$CHECKSUM_FILE" | head -n 1
}

expected_sha256="$(get_hash SHA256)"
expected_sha512="$(get_hash SHA512)"
expected_b2="$(get_hash BLAKE2B-512)"
expected_sha3="$(get_hash SHA3-512)"

actual_sha256="$(sha256sum "$ARCHIVE_FILE" | awk '{print $1}')"
actual_sha512="$(sha512sum "$ARCHIVE_FILE" | awk '{print $1}')"

[[ "$expected_sha256" == "$actual_sha256" ]] || {
  echo "SHA256 mismatch" >&2
  exit 1
}
[[ "$expected_sha512" == "$actual_sha512" ]] || {
  echo "SHA512 mismatch" >&2
  exit 1
}

if [[ -n "$expected_b2" ]]; then
  if ! command -v b2sum >/dev/null 2>&1; then
    echo "b2sum unavailable; cannot verify BLAKE2B-512" >&2
    exit 1
  fi
  actual_b2="$(b2sum "$ARCHIVE_FILE" | awk '{print $1}')"
  [[ "$expected_b2" == "$actual_b2" ]] || {
    echo "BLAKE2B-512 mismatch" >&2
    exit 1
  }
fi

if [[ -n "$expected_sha3" ]]; then
  if ! command -v openssl >/dev/null 2>&1; then
    echo "openssl unavailable; cannot verify SHA3-512" >&2
    exit 1
  fi
  actual_sha3="$(openssl dgst -sha3-512 "$ARCHIVE_FILE" | sed -E 's/^SHA3-512\([^)]+\)= //')"
  [[ "$expected_sha3" == "$actual_sha3" ]] || {
    echo "SHA3-512 mismatch" >&2
    exit 1
  }
fi

echo "OK: all available checksums match for $ARCHIVE_FILE"
