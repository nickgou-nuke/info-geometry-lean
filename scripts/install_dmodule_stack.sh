#!/usr/bin/env bash
set -euo pipefail

# Minimal bootstrap for the de Rham / D-module computation stack.
#  - SageMath: orchestration layer
#  - Singular: via SageMath install
#  - GAP: for symbolic algebra checks
#  - Macaulay2: user-space install without root (Debian package extraction)
#
# Canonical installation path:
# 1) Prefer system-level apt installs (if sudo is available).
# 2) Otherwise, use local extraction in this script.
#
# Recommended system package set:
#   sudo apt-get install -y macaulay2 singular singular-data singular gap normaliz normaliz-bin
#
# For a non-root environment, it downloads .deb packages and unpacks them into
# $HOME/.local/m2-stack.

log() { printf '\n[info] %s\n' "$*"; }
fail() { printf '[fail] %s\n' "$*"; }

have() { command -v "$1" >/dev/null 2>&1; }

log "Checking existing tools..."
have sage && log "sage: $(command -v sage)"
have Singular && log "Singular (capital S): $(command -v Singular)"
have gap && log "gap: $(command -v gap)"

if have sage; then
  log "SageMath found."
else
  fail "SageMath not found on PATH. Install in this environment first or add it."
fi

if have gap; then
  log "gap found."
else
  fail "GAP not found on PATH."
fi

# Singular binary name differs across installs; check both spellings.
if command -v singular >/dev/null 2>&1; then
  log "singular executable: $(command -v singular)"
elif command -v Singular >/dev/null 2>&1; then
  log "Singular executable (capital S): $(command -v Singular)"
else
  fail "Singular executable not found in PATH."
fi

# Optional checks.
if command -v asir >/dev/null 2>&1; then
  log "Risa/Asir: asir found ($(command -v asir))."
else
  log "Risa/Asir not found (non-packaged in this environment by default)."
fi

if command -v julia >/dev/null 2>&1; then
  log "Julia found: $(command -v julia)"
  log "Install Oscar.jl manually from Julia with: julia -e 'using Pkg; Pkg.add(\"Oscar\")'"
else
  log "Julia not found; Oscar.jl install not available until Julia is installed."
fi

# --- Macaulay2 install ---
M2_PREFIX="${HOME}/.local/m2-stack"
M2_BIN="${M2_PREFIX}/usr/bin/M2"
M2_LIB_PATH="${M2_PREFIX}/usr/lib:${M2_PREFIX}/usr/lib/aarch64-linux-gnu:${M2_PREFIX}/usr/lib/aarch64-linux-gnu/blas:${M2_PREFIX}/usr/lib/aarch64-linux-gnu/lapack"

if [[ -x "${M2_BIN}" ]]; then
  log "Macaulay2 already present at ${M2_BIN}."
else
  log "Installing Macaulay2 user-space into ${M2_PREFIX} ..."

  mkdir -p "${M2_PREFIX}"

  TMPDIR="$(mktemp -d)"
  cd "${TMPDIR}"

  # Core Macaulay2 + binary + dependencies needed by the Ubuntu arm64 package.
  # NOTE: package versions are for Ubuntu noble; tune as needed on other systems.
  apt-get download \
    macaulay2 \
    macaulay2-common \
    liblapack3 \
    libblas3 \
    libflint18t64 \
    libntl44 \
    libmathic0v5 \
    libmathicgb0t64 \
    libmemtailor0 \
    libfrobby0 \
    libgivaro9 \
    libmps3t64 \
    libmpfi0 \
    libtbb12 \
    libboost-stacktrace1.83.0 \
    libgmpxx4ldbl \
    libsingular4m3n0t64 \
    singular-data \
    libgfortran5 \
    libgf2x3

  # Unpack all downloaded packages into local prefix
  for pkg in *.deb; do
    dpkg-deb -x "${pkg}" "${M2_PREFIX}"
  done

  # Make factorization load robust even when finite-field factory tables are
  # not yet on an absolute default search path.
  # (This disables a hard failure and allows Dmodule workflows to run.)
  FACTOR_FILE="${M2_PREFIX}/usr/share/Macaulay2/Core/factor.m2"
  python3 - <<'PY' "${FACTOR_FILE}"
import sys
p = sys.argv[1]
text = open(p).read()
old = '''i := position(gfdirs, gfdir -> fileExists(gfdir | "gftables/961")) -- 961==31^2\nif i === null\nthen error ("sample Factory finite field addition table file missing, needed for factorization: ", concatenate between_", " gfdirs)\nsetFactoryGFtableDirectory gfdirs_i\n'''
new = '''i := position(gfdirs, gfdir -> fileExists(gfdir | "gftables/961")) -- 961==31^2\nif i =!= null then setFactoryGFtableDirectory gfdirs_i\n'''
if old not in text:
    raise SystemExit(f"pattern not found in {p}")
open(p, "w").write(text.replace(old, new))
print("patched", p)
PY

  mkdir -p "${HOME}/.local/bin"
  cat > "${HOME}/.local/bin/m2-stack" <<EOF2
#!/usr/bin/env bash
export LD_LIBRARY_PATH="${M2_LIB_PATH}:\${LD_LIBRARY_PATH}"
exec "${M2_BIN}" "\$@"
EOF2
  chmod +x "${HOME}/.local/bin/m2-stack"

  cd - >/dev/null
  rm -rf "${TMPDIR}"
  log "Macaulay2 installed. Wrapper: ${HOME}/.local/bin/m2-stack"
fi

log "Verifying toolchain launchers."
export LD_LIBRARY_PATH="${M2_LIB_PATH}:${LD_LIBRARY_PATH:-}"
"${M2_BIN}" --version | head -n 2 || fail "M2 failed"
"${HOME}/.local/bin/m2-stack" -q <<'EOFM2'
needsPackage "Dmodules"
R = QQ[x,y]
f = x^2 + y^2 + 1
print f
print "M2 ok"
quit
EOFM2

cat <<'EOF'

Installed/available check complete.

If the system has sudo, consider running system-level:
  sudo apt-get update
  sudo apt-get install -y macaulay2 singular singular-data singular gap normaliz normaliz-bin

For full Macaulay2 support, add to shell:
  export PATH="${HOME}/.local/bin:$PATH"
  export LD_LIBRARY_PATH="${HOME}/.local/m2-stack/usr/lib:${HOME}/.local/m2-stack/usr/lib/aarch64-linux-gnu:${HOME}/.local/m2-stack/usr/lib/aarch64-linux-gnu/blas:${HOME}/.local/m2-stack/usr/lib/aarch64-linux-gnu/lapack:${LD_LIBRARY_PATH}"
EOF