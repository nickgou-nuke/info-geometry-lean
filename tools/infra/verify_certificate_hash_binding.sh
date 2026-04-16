#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Verify archive hash binding across:
  - archive file (*.tgz)
  - checksum manifest (*.checksums.txt)
  - certificate markdown (*.certificate.md)

Usage:
  tools/infra/verify_certificate_hash_binding.sh <bundle-dir>
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
CERT_MD_FILE="$(find "$BUNDLE_DIR" -maxdepth 1 -type f -name '*.certificate.md' | head -n 1)"

if [[ -z "$ARCHIVE_FILE" || -z "$CHECKSUM_FILE" || -z "$CERT_MD_FILE" ]]; then
  echo "Missing required files in $BUNDLE_DIR" >&2
  exit 2
fi

sha512_archive="$(sha512sum "$ARCHIVE_FILE" | awk '{print $1}')"
sha512_manifest="$(awk '$1 == "SHA512" {print $2}' "$CHECKSUM_FILE" | head -n 1)"
sha512_cert="$(sed -n 's/^- SHA-512: `\([0-9a-fA-F]\+\)`$/\1/p' "$CERT_MD_FILE" | head -n 1)"

if [[ -z "$sha512_manifest" || -z "$sha512_cert" ]]; then
  echo "Could not parse SHA-512 from manifest/certificate." >&2
  exit 1
fi

[[ "$sha512_archive" == "$sha512_manifest" ]] || {
  echo "Mismatch: archive SHA-512 != manifest SHA-512" >&2
  exit 1
}
[[ "$sha512_archive" == "$sha512_cert" ]] || {
  echo "Mismatch: archive SHA-512 != certificate SHA-512" >&2
  exit 1
}

echo "OK: SHA-512 binding verified across archive, manifest, and certificate markdown."
echo "  archive:   $ARCHIVE_FILE"
echo "  manifest:  $CHECKSUM_FILE"
echo "  cert-md:   $CERT_MD_FILE"
echo "  sha512:    $sha512_archive"
