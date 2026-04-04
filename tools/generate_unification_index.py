#!/usr/bin/env python3
from __future__ import annotations

import datetime as dt
import sys
from dataclasses import dataclass
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


@dataclass(frozen=True)
class ModuleEntry:
    module: str
    status: str
    note: str


@dataclass(frozen=True)
class UnificationEntry:
    theorem: str
    file: str
    line: int
    source_theories: str
    bridge: str
    preserved_structure: str
    transport_type: str
    literature_status: str
    note: str


MODULES = [
    ModuleEntry(
        module="InfoGeometry.Math.Convexity",
        status="mostly_classical",
        note="Direct convexity/Jensen/KL finite-form lemmas aligned with standard convex-analysis literature.",
    ),
    ModuleEntry(
        module="InfoGeometry.Geometry.LegendreDuality",
        status="mostly_classical",
        note="Fenchel-Young, gap, and equality-case layer; classical convex duality core.",
    ),
    ModuleEntry(
        module="InfoGeometry.Geometry.DualFlat",
        status="mostly_classical",
        note="Bregman three-point and Pythagorean identities in a standard dual-flat setting.",
    ),
    ModuleEntry(
        module="InfoGeometry.EntropicInference",
        status="mostly_classical",
        note="Constructive finite KL-Pythagorean decompositions and Jeffrey-style projection identities.",
    ),
    ModuleEntry(
        module="InfoGeometry.Information.MultiLogPotential",
        status="mostly_classical",
        note="Covariance/Fisher symmetry and exponential-family local information geometry.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.RGFlow",
        status="classical_specialization",
        note="Real Banach fixed-point specialization plus constant-flow baseline; mathematically standard but not a nontrivial RG existence theory.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.AnalyticalIndex",
        status="classical_adjacent_model",
        note="Finite-dimensional repo-specific analytical-index model using standard index-theoretic vocabulary.",
    ),
    ModuleEntry(
        module="InfoGeometry.KK.KasparovCycle",
        status="classical_adjacent_model",
        note="Bounded KK-style cycle surface connected to the repo’s analytical-index model rather than full Kasparov theory.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.KMSSinkhornBridge",
        status="repo_specific_unification",
        note="Explicit bridge between Sinkhorn dynamics and KMS-style closure conditions; literature-inspired but repo-specific.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.TomitaTakesaki",
        status="repo_specific_unification",
        note="Header itself describes an atom-level split `Cl(1,1)` modular layer, not a full standard-form Tomita-Takesaki development.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.OperatorAlgebraBridge",
        status="packaging_heavy_bridge_surface",
        note="Contains some real closures, but a noticeable part of the file is API packaging and readiness bundling.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.GrandSynthesis",
        status="mixed_capstone_surface",
        note="Contains exact determinant/Jacobian lemmas and real bridge theorems, but also capstone packaging/orchestration layers.",
    ),
    ModuleEntry(
        module="InfoGeometry.Quantum.RealMajorana",
        status="repo_specific_unification",
        note="Real CAR/BdG transport scaffold with explicit Weyl-sector transport and polarization bridge structure.",
    ),
    ModuleEntry(
        module="InfoGeometry.Quantum.BulkBoundary",
        status="repo_specific_unification",
        note="Finite-dimensional algebraic bulk-boundary mechanism transporting zero-mode witnesses through Bogoliubov structure.",
    ),
    ModuleEntry(
        module="InfoGeometry.Canonical.ArnoldMajoranaNetwork",
        status="repo_specific_unification",
        note="Network layer consuming transported Weyl/zero-mode witnesses; strong local unification but entirely repo-specific.",
    ),
]


ENTRIES = [
    UnificationEntry(
        theorem="convexOn_neg_log",
        file="lean/InfoGeometry/Math/Convexity.lean",
        line=19,
        source_theories="convex analysis",
        bridge="none; direct standard statement",
        preserved_structure="convexity on `(0, ∞)`",
        transport_type="classical reproduction",
        literature_status="classical theorem",
        note="Safe core.",
    ),
    UnificationEntry(
        theorem="neg_log_jensen_sum",
        file="lean/InfoGeometry/Math/Convexity.lean",
        line=28,
        source_theories="convex analysis, information theory",
        bridge="Jensen applied to `-log`",
        preserved_structure="finite convex combination inequality",
        transport_type="classical reproduction",
        literature_status="classical theorem",
        note="Safe core.",
    ),
    UnificationEntry(
        theorem="fenchelYoung_ineq",
        file="lean/InfoGeometry/Geometry/LegendreDuality.lean",
        line=86,
        source_theories="convex duality",
        bridge="primal/dual conjugacy",
        preserved_structure="Fenchel majorization inequality",
        transport_type="classical reproduction",
        literature_status="classical theorem",
        note="Safe core.",
    ),
    UnificationEntry(
        theorem="three_point_identity",
        file="lean/InfoGeometry/Geometry/DualFlat.lean",
        line=355,
        source_theories="information geometry, Bregman geometry",
        bridge="dual-flat gradient/Bregman relation",
        preserved_structure="Bregman three-point law",
        transport_type="classical reproduction",
        literature_status="classical theorem",
        note="Safe core.",
    ),
    UnificationEntry(
        theorem="kl_pythagorean_jeffrey_toReal_strict",
        file="lean/InfoGeometry/EntropicInference.lean",
        line=452,
        source_theories="information geometry, KL projection geometry",
        bridge="strict positivity + Jeffrey reconstruction",
        preserved_structure="KL decomposition",
        transport_type="classical special case",
        literature_status="classical theorem / finite constructive specialization",
        note="Strong standard-core formalization.",
    ),
    UnificationEntry(
        theorem="covariance_symm",
        file="lean/InfoGeometry/Information/MultiLogPotential.lean",
        line=153,
        source_theories="statistics, information geometry",
        bridge="covariance expression for Fisher metric",
        preserved_structure="symmetry of covariance/Fisher bilinear form",
        transport_type="classical reproduction",
        literature_status="classical theorem",
        note="Safe core.",
    ),
    UnificationEntry(
        theorem="existsUnique_fixedPoint_of_contracting",
        file="lean/InfoGeometry/Canonical/RGFlow.lean",
        line=247,
        source_theories="metric fixed-point theory, RG language",
        bridge="Banach contraction recast as RG step map",
        preserved_structure="existence/uniqueness of fixed point",
        transport_type="classical specialization",
        literature_status="classical theorem / repo-specific interpretation",
        note="Mathematically standard; physics reading is interpretive.",
    ),
    UnificationEntry(
        theorem="analyticalIndex",
        file="lean/InfoGeometry/Canonical/AnalyticalIndex.lean",
        line=59,
        source_theories="finite-dimensional linear algebra, index vocabulary",
        bridge="chiral kernel slices -> integer index",
        preserved_structure="dimension difference of chiral slices",
        transport_type="repo-specific model",
        literature_status="repo-specific construction",
        note="Classical-adjacent, not full Atiyah-Singer.",
    ),
    UnificationEntry(
        theorem="indexInvariantAlong_of_conjugacy",
        file="lean/InfoGeometry/Canonical/AnalyticalIndex.lean",
        line=654,
        source_theories="index-like invariance, conjugacy transport",
        bridge="chiral conjugacy along a path",
        preserved_structure="analytical-index invariance",
        transport_type="invariance theorem",
        literature_status="repo-specific unification",
        note="Good example of strong local bridge content.",
    ),
    UnificationEntry(
        theorem="index_bridge_spectral",
        file="lean/InfoGeometry/KK/KasparovCycle.lean",
        line=83,
        source_theories="KK-style cycles, analytical index",
        bridge="spectral involution -> no-zero-eigenvalue crossing",
        preserved_structure="analytical-index invariance of the constant family",
        transport_type="invariance theorem",
        literature_status="repo-specific unification",
        note="Finite-dimensional spectral stability bridge, not just a definitional alias.",
    ),
    UnificationEntry(
        theorem="sinkhorn_step_kmsClosure_of_control",
        file="lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean",
        line=177,
        source_theories="Sinkhorn dynamics, KMS/operator-algebra language",
        bridge="stepwise control hypothesis -> KMS closure",
        preserved_structure="closure of next-step state",
        transport_type="bridge theorem",
        literature_status="repo-specific unification",
        note="Genuinely unifying in local sense; not classical Sinkhorn or full KMS theory.",
    ),
    UnificationEntry(
        theorem="neg_log_relative_volume_change_rn",
        file="lean/InfoGeometry/Canonical/DiracRicciBridge.lean",
        line=37,
        source_theories="RN density, Kähler potential",
        bridge="relative volume change vs. logarithmic Kähler potential",
        preserved_structure="additive potential identity",
        transport_type="local bridge theorem",
        literature_status="repo-specific unification",
        note="Still elementary, but no longer just a named definitional equality.",
    ),
    UnificationEntry(
        theorem="logAbsDetMatrix_mul",
        file="lean/InfoGeometry/Canonical/GrandSynthesis.lean",
        line=158,
        source_theories="matrix analysis, determinant calculus",
        bridge="classical determinant chain rule",
        preserved_structure="multiplicativity under matrix product",
        transport_type="classical reproduction",
        literature_status="classical theorem",
        note="Safe local theorem embedded in synthesis layer.",
    ),
    UnificationEntry(
        theorem="information_wheeler_dewitt_equivalence_of_fullCapstone",
        file="lean/InfoGeometry/Canonical/GrandSynthesis.lean",
        line=1337,
        source_theories="thermodynamic KMS side, geometric-algebraic side",
        bridge="full-capstone equivalence",
        preserved_structure="bi-implication of capstone state bundles",
        transport_type="capstone equivalence",
        literature_status="repo-specific synthesis theorem",
        note="Potentially meaningful local unification; not externally classical by name alone.",
    ),
    UnificationEntry(
        theorem="kk_supercomm_compact_of_even_rep",
        file="lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean",
        line=405,
        source_theories="KK compactness, operator bridge layer",
        bridge="re-export into operator-algebra readiness surface",
        preserved_structure="compactness fact",
        transport_type="direct forwarder",
        literature_status="packaging theorem",
        note="Useful API surface, not a deep new bridge.",
    ),
    UnificationEntry(
        theorem="weylZeroModePair_under_bogoliubov_of_preservesChiralityPolarization",
        file="lean/InfoGeometry/Quantum/BulkBoundary.lean",
        line=485,
        source_theories="real Majorana Weyl sectors, Bogoliubov transport, bulk-boundary zero modes",
        bridge="chirality-polarization-preserving transport",
        preserved_structure="nonzero zero-mode pair in transported Weyl sectors",
        transport_type="transport theorem",
        literature_status="repo-specific unification",
        note="Strong local cross-domain bridge.",
    ),
    UnificationEntry(
        theorem="exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov",
        file="lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean",
        line=596,
        source_theories="Majorana/BulkBoundary zero-mode transport, mixture-of-experts network dynamics",
        bridge="simplified boundary model + Bogoliubov transport -> network fixed zero mode",
        preserved_structure="fixed nonzero transported Weyl-plus kernel witness",
        transport_type="repo-specific constructive unification",
        literature_status="repo-specific construction",
        note="Good candidate for genuinely novel local theorem content.",
    ),
    UnificationEntry(
        theorem="chiralAnomalyIndex",
        file="lean/InfoGeometry/Canonical/TopologicalInvariants.lean",
        line=57,
        source_theories="topological invariants, anomaly/index language",
        bridge="repo-defined anomaly index construction",
        preserved_structure="custom integer-valued invariant",
        transport_type="repo-specific construction",
        literature_status="analogue / repo-specific",
        note="Literature-adjacent naming; not a proof of classical Atiyah-Singer.",
    ),
]


def status_explainer(status: str) -> str:
    return {
        "mostly_classical": "mostly standard mathematics reproduced in Lean",
        "classical_specialization": "standard theorem pattern in a repo-specific specialization",
        "classical_adjacent_model": "built from standard vocabulary but uses a simplified repo-specific model",
        "repo_specific_unification": "genuine bridge or transport theorem inside the repo’s own framework",
        "packaging_heavy_bridge_surface": "contains real theorems but a noticeable fraction is packaging/re-export/readiness surface",
        "mixed_capstone_surface": "mixes real theorem content with high-level capstone packaging",
    }[status]


def render_md() -> str:
    now = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    lines: list[str] = []
    lines.append("# Unification Index")
    lines.append("")
    lines.append(f"Generated: `{now}`")
    lines.append("")
    lines.append(
        "This report tracks where the repository is reproducing standard mathematics, "
        "where it is building repo-specific bridges between known subjects, and where "
        "the surface is mostly packaging rather than deep unification."
    )
    lines.append("")
    lines.append("## Criterion")
    lines.append("")
    lines.append("A surface counts as real unification here only if it gives:")
    lines.append("- two independently meaningful sides,")
    lines.append("- an explicit structure-preserving bridge,")
    lines.append("- a transport/invariance/equivalence theorem across that bridge,")
    lines.append("- something stronger than `rfl`, direct forwarding, or tuple repackaging.")
    lines.append("")
    lines.append("The categories below are local to the repo’s formal framework.")
    lines.append("They do not automatically imply external novelty in the research-literature sense.")
    lines.append("")
    lines.append("## Module Split")
    lines.append("")
    lines.append("| Module | Status | Meaning | Note |")
    lines.append("| --- | --- | --- | --- |")
    for item in MODULES:
        lines.append(
            f"| `{item.module}` | `{item.status}` | {status_explainer(item.status)} | {item.note} |"
        )
    lines.append("")
    lines.append("## Theorem-To-Literature Table")
    lines.append("")
    lines.append("| Theorem | Source theories | Bridge / morphism | Preserved structure | Transport type | Literature status | Note |")
    lines.append("| --- | --- | --- | --- | --- | --- | --- |")
    for item in ENTRIES:
        theorem_ref = f"[`{item.theorem}`](/home/goutev/LEAN4/info-geometry-lean/{item.file}#L{item.line})"
        lines.append(
            f"| {theorem_ref} | {item.source_theories} | {item.bridge} | {item.preserved_structure} | {item.transport_type} | {item.literature_status} | {item.note} |"
        )
    lines.append("")
    lines.append("## Reading Rule")
    lines.append("")
    lines.append("- Treat `classical theorem` and `classical theorem / finite constructive specialization` rows as safe standard-core reading.")
    lines.append("- Treat `repo-specific unification` rows as the strongest local candidates for genuine new formal mathematics inside the repo’s framework.")
    lines.append("- Treat `thin bridge`, `packaging theorem`, and `analogue` rows cautiously; they may be valid Lean mathematics without carrying strong unification weight.")
    lines.append("")
    lines.append("## Policy")
    lines.append("")
    lines.append("- Standard subject names alone do not count as unification.")
    lines.append("- Capstone naming alone does not count as novelty.")
    lines.append("- The real contribution, when present, is the verified bridge that lets mathematics pass between theories.")
    return "\n".join(lines) + "\n"


def main() -> int:
    root = repo_root()
    out = root / "UNIFICATION_INDEX.md"
    out.write_text(render_md(), encoding="utf-8")
    print(f"[generate-unification-index] wrote {out}")
    print(f"[generate-unification-index] modules={len(MODULES)} entries={len(ENTRIES)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
