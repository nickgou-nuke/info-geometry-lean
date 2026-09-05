#!/usr/bin/env bash
set -euo pipefail
command -v lake >/dev/null || { echo 'ERROR: lake is not installed or not on PATH.' >&2; exit 127; }
lake build InfoGeometry.Canonical.BipolarCayleyKleinPristineChain
lake env lean lean/InfoGeometry/Canonical/BipolarCayleyKleinAudit.lean
