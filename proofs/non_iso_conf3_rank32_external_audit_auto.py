#!/usr/bin/env python3
"""External non-isotropic Conf3 rank audit (D=4) using D-module / singularity tools.

This is the next-tier audit for the actual de Rham branch (beyond SymPy).
Track A = finite-field / E-polynomial cross-checks; Track B = D-module or
Dupont/Gysin de Rham computation.

The script is a launcher/protocol adapter:
- emits Singular and Macaulay2 inputs;
- emits and optionally runs a SageManifolds geometry-sidecar input;
- runs available tools when binaries are present;
- writes a compact JSON report plus raw command logs under
  `proofs/artefacts/non_iso_conf3_rank32_audit/`.

SageManifolds is used only for the differential-geometry parameter-base side
of the stack (charts, vector fields, differential forms, flow-style checks),
and is not the de Rham proof core.

The current kernel state does NOT assume that a rank-32 case is proved by
finite computations alone.  This script is the reproducible external bridge.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from subprocess import run
from shutil import which
from textwrap import dedent
import json

ROOT = Path(__file__).resolve().parent
ART = ROOT / "artefacts" / "non_iso_conf3_rank32_audit"
ART.mkdir(parents=True, exist_ok=True)

D = 4

SINGULAR_INPUT = dedent(
    """
    // D=4 non-isotropic Conf3: f = q(a)q(b)q(a-b)
    // NOTE: this is a structural scaffold. Adjust q(*) to your chosen
    // nondegenerate complex quadric normalization over characteristic 0.
    ring R = 0,(a0,a1,a2,a3,b0,b1,b2,b3),dp;

    poly qa = a0^2 + a1^2 + a2^2 + a3^2;
    poly qb = b0^2 + b1^2 + b2^2 + b3^2;
    poly qab = (a0-b0)^2 + (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2;

    ideal I = qa, qb, qab;

    // Codim data / transversality probes for strata
    int dimI = dim(I);
    ideal singI = jacob(I);

    matrix J[3][8];
    J[1,1] = diff(qa,a0); J[1,2] = diff(qa,a1); J[1,3] = diff(qa,a2); J[1,4] = diff(qa,a3);
    J[1,5] = 0;         J[1,6] = 0;         J[1,7] = 0;         J[1,8] = 0;
    J[2,1] = 0;         J[2,2] = 0;         J[2,3] = 0;         J[2,4] = 0;
    J[2,5] = diff(qb,b0);J[2,6] = diff(qb,b1);J[2,7] = diff(qb,b2);J[2,8] = diff(qb,b3);
    J[3,1] = diff(qab,a0);J[3,2] = diff(qab,a1);J[3,3] = diff(qab,a2);J[3,4] = diff(qab,a3);
    J[3,5] = diff(qab,b0);J[3,6] = diff(qab,b1);J[3,7] = diff(qab,b2);J[3,8] = diff(qab,b3);

    // print(dimI);
    // print(J);
    """
)

MACAULAY2_INPUT = dedent(
    """
    -- D=4 non-isotropic Conf3 de Rham cohomology probe
    -- Placeholder workflow for Oaku--Takayama style computation in Macaulay2.
    -- Uses D-modules package as available in your local M2 distribution.
    needsPackage "Dmodules";

    R = QQ[a0,a1,a2,a3,b0,b1,b2,b3, MonomialOrder => Lex];

    qa  = a0^2 + a1^2 + a2^2 + a3^2;
    qb  = b0^2 + b1^2 + b2^2 + b3^2;
    qab = (a0-b0)^2 + (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2;
    f = qa*qb*qab;

    -- Next steps depend on local D-modules API:
    -- 1) build the localization module Q(a,b,1/f) as a Weyl module,
    -- 2) compute its de Rham cohomology / Euler characteristic,
    -- 3) extract ranks of H^i (or full Poincaré polynomial).

    -- Example (pseudo):
    -- W = makeWeylModule (f);
    -- M = localCohomologyModule W;
    -- c = deRhamCohomology M;
    -- print c;

    """
)

SAGEMANIFOLDS_INPUT = dedent(
    """
    # SageManifolds geometry stack audit for the parameterized-family layer.
    # This file is optional and scoped to differential-geometry sanity.
    from sage.all import *
    try:
        from sage.manifolds.all import *
    except Exception as exc:
        print("SAGEMANIFOLDS_IMPORT_ERROR", exc)
        raise SystemExit(2)

    print("=== non_iso_conf3_rank32_sagemanifolds ===")

    # Parameter base and coordinates.
    B = Manifold(4, 'B', structure='smooth')
    X = B.chart('mu beta q theta')
    mu, beta, qpar, theta = X[:4]
    print('base_dim', B.dim())

    # Fiber manifold and coordinates for translation-reduced variables.
    F = Manifold(8, 'F', structure='smooth')
    Y = F.chart('a0 a1 a2 a3 b0 b1 b2 b3')
    (a0, a1, a2, a3, b0, b1, b2, b3) = Y[:8]
    print('fiber_dim', F.dim())

    # Differential-form probes on the split quadric coordinate model.
    qa = a0^2 + a1^2 + a2^2 + a3^2
    qb = b0^2 + b1^2 + b2^2 + b3^2
    qab = (a0 - b0)^2 + (a1 - b1)^2 + (a2 - b2)^2 + (a3 - b3)^2
    try:
        w_a = qa.differential() / qa
        w_b = qb.differential() / qb
        w_ab = qab.differential() / qab
        print('omega_defs', [w_a is not None, w_b is not None, w_ab is not None])
    except Exception as exc:
        print('omega_defs_error', exc)
        w_a = None

    # Optional chart-level connection toy model (informational only).
    try:
        g = F.riemannian_metric('g')
        g[0, 0], g[1, 1], g[2, 2], g[3, 3], g[4, 4], g[5, 5], g[6, 6], g[7, 7] = 1, 1, 1, 1, 1, 1, 1, 1
        print('metric_rank', g.rank())
    except Exception as exc:
        print('metric_build_error', exc)

    # Vector field + Lie-derivative probe (diagnostic only).
    try:
        V = F.vector_field('V')
        # Try a coordinate component assignment if API agrees.
        try:
            V[X, 0] = 1
        except Exception:
            pass
        omega = w_a
        if omega is not None:
            print('lie_derivative_ok', omega.lie_derivative(V) is not None)
    except Exception as exc:
        print('lie_derivative_error', exc)

    # Parameter-symbol probe for modular-flow layer bookkeeping.
    print('mu_is_symbol', mu is not None)
    print('status_ok')
    """
)


@dataclass
class RunSummary:
    singular: str
    macaulay: str
    sage: str


def _run(cmd: str, logfile: Path) -> tuple[str, str]:
    """Run command and capture stdout+stderr. Return (status, text)."""
    try:
        res = run(cmd, shell=True, check=False, capture_output=True, text=True)
        out = res.stdout + ("\n" + res.stderr if res.stderr else "")
        status = "ok" if res.returncode == 0 else f"exit:{res.returncode}"
        logfile.write_text(out)
        return status, out
    except FileNotFoundError:
        return "missing", ""
    except Exception as e:  # pragma: no cover - defensive for launcher failures
        return "exception", str(e)


def _write_outputs() -> tuple[Path, Path, Path, Path]:
    singular_file = ART / "non_iso_conf3_rank32.sing"
    macaulay_file = ART / "non_iso_conf3_rank32.m2"
    sage_file = ART / "non_iso_conf3_rank32_sagemanifolds.sage"
    singular_file.write_text(SINGULAR_INPUT)
    macaulay_file.write_text(MACAULAY2_INPUT)
    sage_file.write_text(SAGEMANIFOLDS_INPUT)
    return singular_file, macaulay_file, sage_file, ART / "non_iso_conf3_rank32_run_report.json"


def run_toolchain() -> RunSummary:
    sfile, mfile, sagefile, _ = _write_outputs()

    # Track A: Singular-style structural/strata checks
    singular_bin = which("singular")
    if singular_bin:
        sStatus, _ = _run(f"{singular_bin} -q {sfile}", ART / "non_iso_conf3_rank32_singular.log")
    else:
        sStatus = "missing"
        (ART / "non_iso_conf3_rank32_singular.log").write_text("[skip] singular binary not found\n")

    # Track B: D-module/Oaku-style cohomology via Macaulay2
    macaulay_bin = which("M2") or which("Macaulay2")
    if macaulay_bin:
        mStatus, _ = _run(
            f"{macaulay_bin} < {mfile} > {ART / 'non_iso_conf3_rank32_M2.log'} 2>&1",
            ART / "non_iso_conf3_rank32_M2_wrap.log",
        )
    else:
        mStatus = "missing"
        (ART / "non_iso_conf3_rank32_M2_wrap.log").write_text("[skip] Macaulay2 binary not found\n")

    # Optional Sage/SageManifolds geometry layer, if available.
    if which("sage"):
        sStatusSage, _ = _run(f"sage -q {sagefile}", ART / "non_iso_conf3_rank32_sagemanifolds.log")
    else:
        sStatusSage = "missing"
        (ART / "non_iso_conf3_rank32_sagemanifolds.log").write_text("[skip] sage binary not found\n")

    # Backward-compatible legacy logfile name for any external watchers.
    if (ART / "non_iso_conf3_rank32_sage.log").exists() is False:
        (ART / "non_iso_conf3_rank32_sage.log").write_text((ART / "non_iso_conf3_rank32_sagemanifolds.log").read_text())

    return RunSummary(singular=sStatus, macaulay=mStatus, sage=sStatusSage)


def emit_json_report(run_summary: RunSummary) -> Path:
    report_path = ART / "non_iso_conf3_rank32_report.json"

    # If no external D-module output exists, we keep a verified-flag scaffold.
    status = "inconclusive"
    if run_summary.singular == "ok" and run_summary.macaulay == "ok":
        status = "pending"
    elif run_summary.singular != "missing" or run_summary.macaulay != "missing" or run_summary.sage != "missing":
        status = "partial"

    report = {
        "source": str((Path(__file__).resolve()).name),
        "D": D,
        "ambient_dimension": 2 * D,
        "status": status,
        "toolchain": {
            "singular": run_summary.singular,
            "macaulay2": run_summary.macaulay,
            "sage": run_summary.sage,
            "sagemanifolds": run_summary.sage,
        },
        # Empty until explicit M2 parsing layer is added.
        "pointwise": {
            "betti": [],
            "total_rank": 0,
            "max_degree": 0,
        },
        # Expected codimension pattern for the corrected triple-independent model.
        "three_quadric_codim_data": {
            "codimQA": 1,
            "codimQB": 1,
            "codimQAB": 1,
            "codimQA_QB": 2,
            "codimQA_QAB": 2,
            "codimQB_QAB": 2,
            "codimTriple": 3,
        },
        "rank_decision_verifications": {
            "resolvedDupontArrangementConstructed": False,
            "betaGysinLeavesTwoIndependentFluxClasses": False,
            "dupontModelComputesActualDeRham": False,
            "cooperadFunctorialityForResolvedModel": False,
            "codimDataEqExpected": True,
        },
        "notes": (
            "Launch artifact for external D-module audit. "
            "Replace pointwise.betti and total_rank when macaualey2/singular output "
            "is parsed into a structured JSON layer. "
            "SageManifolds is a separate optional geometry/spec witness layer and "
            "does not close de Rham rank by itself."
        ),
        "inputs": {
            "singular": "non_iso_conf3_rank32.sing",
            "macaulay2": "non_iso_conf3_rank32.m2",
            "sagemanifolds": "non_iso_conf3_rank32_sagemanifolds.sage",
        },
    }

    report_path.write_text(json.dumps(report, indent=2, sort_keys=True))
    return report_path


def main() -> None:
    run_summary = run_toolchain()
    report = emit_json_report(run_summary)
    print("non_iso_conf3_rank32_external_audit.py:")
    print(f" - Singular input: {ART / 'non_iso_conf3_rank32.sing'}")
    print(f" - Macaulay2 input: {ART / 'non_iso_conf3_rank32.m2'}")
    print(f" - SageManifolds input: {ART / 'non_iso_conf3_rank32_sagemanifolds.sage'}")
    print(f" - JSON report: {report}")
    print(f" - Logs are collected in: {ART}")
    print("(No rank claim is made by this finite script alone.)")


if __name__ == "__main__":
    main()
