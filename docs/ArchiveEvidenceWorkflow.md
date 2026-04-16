# Archive, Evidence, and Signature Workflow

This workflow creates a reproducible source archive, binds it to cryptographic hashes,
and prepares a certificate package for timestamping and qualified signatures.

It is a technical procedure, not legal advice.

## 0. Repository legal metadata check (current repo)

Run:

```bash
sed -n '1,80p' LICENSE
sed -n '1,80p' NOTICE
sed -n '1,120p' CITATION.cff
```

Current repository metadata already includes:

- License: `Apache-2.0` (`LICENSE`)
- Copyright holders (`NOTICE`):
  - Nikolay Goutev
  - Dimitar Tonev
- Citation file: `CITATION.cff`
- Repository URLs (in `CITATION.cff`):
  - `https://github.com/nickgou-nuke/info-geometry-lean`

If needed, update `NOTICE` and `CITATION.cff` before creating evidence bundles.

## 1. Create reproducible archive + hashes + certificate draft

Use the bundled script:

```bash
tools/infra/create_evidence_bundle.sh --ref HEAD --with-pdf
```

For PDF-first blockchain proof in one command:

```bash
tools/infra/create_evidence_bundle.sh --ref HEAD --with-pdf --ots-stamp pdf --ots-upgrade
```

If your environment blocks writes to `~/.cache`, pass an explicit cache dir:

```bash
tools/infra/create_evidence_bundle.sh --with-pdf --ots-stamp pdf --ots-cache-dir /tmp/ots-cache
```

Modes:

- `--source-only` (default): archives tracked repository source at a git ref.
- `--full-state`: archives current working tree state (including build artifacts),
  excluding `.git` and `archive/evidence/`.

Output goes to:

```text
archive/evidence/<UTC>_<shortsha>/
```

Generated files:

- `*.tgz` (source snapshot from `git archive`)
- `*.checksums.txt` (SHA-256, SHA-512, and when available BLAKE2b + SHA3-512)
- `*.certificate.md` (certificate draft with signer/timestamp placeholders)
- `*.certificate.pdf` (if `pandoc` is installed and `--with-pdf` is used)
- `*.metadata.txt` (commit/remotes/size/provenance)
- copies of `LICENSE`, `NOTICE`, `CITATION.cff`
- bundle-local verifiers:
  - `verify_evidence_bundle.sh`
  - `verify_certificate_hash_binding.sh`
  - `VERIFY.md`

By default the script applies exclusion policy from:

```text
tools/infra/archive_excludes.txt
```

Current default exclusions:

- `external_refs/` (third-party reference/vendor content)
- `interspec_src/` (external InterSpec source drop)

For each excluded prefix, the bundle writes a local stub file:

```text
<excluded-path>/README.EXCLUDED.md
```

Disable stubs with `--no-exclusion-stubs`.

Verify the bundle:

```bash
tools/infra/verify_evidence_bundle.sh archive/evidence/<bundle-dir>
```

Verify SHA-512 binding between archive, checksum manifest, and certificate text:

```bash
tools/infra/verify_certificate_hash_binding.sh archive/evidence/<bundle-dir>
```

## 2. Write-protect / immutability hardening

Read-only lock at generation time:

```bash
tools/infra/create_evidence_bundle.sh --lock-readonly
```

Optional immutable bit (`chattr +i`, Linux filesystem dependent):

```bash
tools/infra/create_evidence_bundle.sh --lock-immutable
```

Notes:

- `chmod 0444`/`0555` is portable and reversible.
- `chattr +i` is stronger but filesystem/permission dependent and may fail.

## 3. Timestamp evidence (two independent channels recommended)

### A) RFC3161 trusted timestamp authority (TSA)

```bash
openssl ts -query -data CERTIFICATE.pdf -sha512 -cert -out CERTIFICATE.tsq
curl -sS -H 'Content-Type: application/timestamp-query' \
  --data-binary @CERTIFICATE.tsq \
  "https://<your-tsa-endpoint>" \
  -o CERTIFICATE.tsr
```

Keep both `CERTIFICATE.tsq` and `CERTIFICATE.tsr` in the evidence folder.

### B) Public blockchain anchoring

Integrated approach (script-managed) uses OpenTimestamps when `ots` is installed:

```bash
tools/infra/create_evidence_bundle.sh --with-pdf --ots-stamp pdf --ots-upgrade
```

Manual OpenTimestamps commands:

```bash
ots stamp CERTIFICATE.pdf
ots verify CERTIFICATE.pdf.ots
```

Store `CERTIFICATE.pdf.ots` with the bundle.

## 4. Qualified electronic signatures (QES)

Have both listed copyright holders sign the certificate PDF:

- Signer 1: Nikolay Goutev
- Signer 2: Dimitar Tonev

Use a Qualified Trust Service Provider workflow compliant with your jurisdiction.
Attach/export:

- Signed PDF container
- signer certificate chain
- revocation evidence (CRL/OCSP or provider equivalent)

## 5. Evidence package checklist

Final package should include:

- archive `*.tgz`
- checksum manifest `*.checksums.txt`
- certificate `*.certificate.md` and signed PDF
- metadata file `*.metadata.txt`
- RFC3161 files (`*.tsq`, `*.tsr`) if used
- blockchain proof (`*.ots` or transaction proof)
- legal metadata copies (`LICENSE`, `NOTICE`, `CITATION.cff`)

## 6. Citation line (for certificate text)

Suggested canonical repository citation line:

```text
Repository: nickgou-nuke/info-geometry-lean.git
Canonical URL: https://github.com/nickgou-nuke/info-geometry-lean
```

## 7. Public release export (own code lane)

For publication-oriented exports with third-party zones excluded and stubbed:

```bash
python3 tools/infra/export_public_release.py --ref HEAD
```

This generates:

- clean tree: `archive/public-release/<timestamp>_<sha>/info-geometry-lean-public/`
- `THIRD_PARTY_RELEASE_INDEX.md` (auto-generated exclusion audit)
- `PUBLIC_RELEASE_MANIFEST.json`
- deterministic `.tgz` + checksum manifest

## 8. Deep third-party/license scan before release

Run a full repository scan:

```bash
python3 tools/infra/scan_third_party_licenses.py --all-files --out docs/ThirdPartyDeepScanReport.md
```

This report classifies findings into:

- `third_party_or_reference`
- `review_needed`
- `project_owned`

Use it before publishing a public release bundle.
