"""Complete structured registry of all 218 E2E checks (Tiers 1-4) for R1/R2/R3 reconciliation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class CheckSpec:
    check_id: str
    tier: int
    feature: str
    gate: str  # "PHASE-0", "M1", "M2", "M3"
    bucket: str  # "BUCKET 1", "BUCKET 2", "BUCKET 3"
    description: str
    spec: dict[str, Any]


# ---------------------------------------------------------------------------
# Baseline owner file inventories (verified on disk at commit abd5826b36)
# ---------------------------------------------------------------------------

F1_1_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
    "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean",
    "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
)

F1_2_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/OperatorAlgebra/MaurerCartanFrameTransport.lean",
    "lean/InfoGeometry/OperatorAlgebra/DerivationRightLogarithmicForm.lean",
    "lean/InfoGeometry/OperatorAlgebra/DerivationGaugeTransport.lean",
    "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean",
)

F1_3_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Thermo/OnsagerOperatorClosure.lean",
    "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
    "lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean",
)

F1_4_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Optics/OperatorDerivationForms.lean",
    "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
    "lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean",
    "lean/InfoGeometry/Canonical/FrechetCECovariantConnection.lean",
)

F1_5_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
    "lean/InfoGeometry/Algebra/NonAssocDerivation.lean",
    "lean/InfoGeometry/Geometry/AssociativeGaugeConnection.lean",
)

F1_6_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Optics/OperatorDerivationForms.lean",
    "lean/InfoGeometry/Canonical/CEOneFormNOperatorBridge.lean",
    "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
)

F1_7_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
    "lean/InfoGeometry/OperatorAlgebra/DerivationGaugeTransport.lean",
    "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean",
    "lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean",
)

F3_1_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Clifford/Cl11Matrix.lean",
    "lean/InfoGeometry/Clifford/Cl11GradedMorita.lean",
    "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean",
    "lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean",
    "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean",
)

F3_2_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean",
    "lean/InfoGeometry/Clifford/Cl11CliffordMapIsometryBridge.lean",
    "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean",
)

F3_3_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean",
    "lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean",
    "lean/InfoGeometry/Canonical/SplitCliffordMatrixLimitSoldering.lean",
)

F3_4_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Clifford/GradedGraceContraction.lean",
    "lean/InfoGeometry/Clifford/Cl11SupergradedTensorBridge.lean",
    "lean/InfoGeometry/ErlangenCoordinateless.lean",
)

F3_5_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean",
    "lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean",
)

F2_1_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
    "lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean",
    "lean/InfoGeometry/Canonical/ErlangenOperator2.lean",
    "lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean",
    "lean/InfoGeometry/Geometry/PhaseErlanger.lean",
    "lean/InfoGeometry/Canonical/FelixKleinGeometryUnification.lean",
)

F2_2_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/Krein/KreinSpace.lean",
    "lean/InfoGeometry/Krein/DoubledSpace.lean",
    "lean/InfoGeometry/Krein/DoubleRealKreinShearDefect.lean",
    "lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean",
    "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
)

F2_3_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
    "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
    "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean",
    "lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean",
    "lean/InfoGeometry/KK/RealCl55KasparovCycleBridge.lean",
)

F2_4_BASELINE: tuple[str, ...] = (
    "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
    "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
    "lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean",
    "lean/InfoGeometry/OperatorAlgebra/KreinFrechetRiesz.lean",
    "lean/InfoGeometry/Algebra/KreinPeirceTowerIntertwine.lean",
)

F2_5_BASELINE_COMPILED: tuple[str, ...] = (
    "lean/InfoGeometry/Projective/GrassmannAusdehnungslehreRegressiveShadow.lean",
    "lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean",
    "lean/InfoGeometry/Canonical/GrassmannProductQuotientAndMasterAtlas.lean",
    "lean/InfoGeometry/Projective/KleinQuadric.lean",
    "lean/InfoGeometry/Projective/KleinQuadricPlucker.lean",
    "lean/InfoGeometry/Projective/ExteriorPluckerTower.lean",
    "lean/InfoGeometry/Projective/PluckerRayAxisAndDyname.lean",
    "lean/InfoGeometry/Projective/MobiusPluckerKleinCompatibility.lean",
    "lean/InfoGeometry/Canonical/GrassmannPfaffianDarbouxAlgebra.lean",
    "lean/InfoGeometry/Canonical/GrassmannPfaffianSyzygyAndNormalForms.lean",
    "lean/InfoGeometry/Projective/PluckerLinearComplex.lean",
    "lean/InfoGeometry/Projective/PluckerLinearComplexGeometry.lean",
    "lean/InfoGeometry/Projective/PluckerCongruenceCylindroidAndRegulus.lean",
    "lean/InfoGeometry/Projective/PluckerQuadraticComplexAndSurfaces.lean",
)

F2_5_BASELINE_ALL: tuple[str, ...] = F2_5_BASELINE_COMPILED + (
    "lean/InfoGeometry/Projective/PluckerKummerQuarticAndMasterAtlas.lean",
)

F2_5_ERLANGEN_PROGRAM_MODULES: tuple[str, ...] = (
    "lean/InfoGeometry/Erlangen/ErlangenProgramGroupHierarchyAndPrincipal.lean",
    "lean/InfoGeometry/Erlangen/ErlangenProgramTransferHesseAndBodies.lean",
    "lean/InfoGeometry/Erlangen/ErlangenProgramMobiusLieAndContact.lean",
    "lean/InfoGeometry/Erlangen/ErlangenProgramCurvatureBinaryAndMasterAtlas.lean",
    "lean/InfoGeometry/Projective/KleinErlangenProgramGroupsAndProjectiveTransfer.lean",
    "lean/InfoGeometry/Canonical/KleinErlangenSphereContactAndBinaryForms.lean",
)

F2_5_SYNTHESIS_AND_BRIDGE_MODULES: tuple[str, ...] = (
    "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
    "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
)

M3_OWNER_FILES: tuple[str, ...] = tuple(
    dict.fromkeys(
        F2_5_ERLANGEN_PROGRAM_MODULES
        + F2_5_SYNTHESIS_AND_BRIDGE_MODULES
        + (
            "lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean",
            "lean/InfoGeometry/Canonical/GrassmannPfaffianSyzygyAndNormalForms.lean",
            "lean/InfoGeometry/Projective/PluckerKummerQuarticAndMasterAtlas.lean",
            "lean/InfoGeometry/Projective/PluckerRayAxisAndDyname.lean",
            "lean/InfoGeometry/Projective/GrassmannSubspaceShadowsResultantAndHadamard.lean",
            "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
            "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
            "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean",
            "lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean",
            "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
            "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
            "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
            "lean/InfoGeometry/Canonical/ErlangenOperator2.lean",
            "lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean",
            "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
            "lean/InfoGeometry/Krein/KreinSpace.lean",
            "lean/InfoGeometry/Krein/DoubledSpace.lean",
            "lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean",
            "lean/InfoGeometry/Geometry/ConstructiveKasparov.lean",
            "lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean",
            "lean/InfoGeometry/Canonical/SmoothPrincipalCartanBundleClosure.lean",
        )
    )
)

ALL_BASELINE_OWNER_FILES: tuple[str, ...] = tuple(
    dict.fromkeys(
        F1_1_BASELINE
        + F1_2_BASELINE
        + F1_3_BASELINE
        + F1_4_BASELINE
        + F1_5_BASELINE
        + F1_6_BASELINE
        + F1_7_BASELINE
        + F3_1_BASELINE
        + F3_2_BASELINE
        + F3_3_BASELINE
        + F3_4_BASELINE
        + F3_5_BASELINE
        + F2_1_BASELINE
        + F2_2_BASELINE
        + F2_3_BASELINE
        + F2_4_BASELINE
        + (
            "lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean",
            "lean/InfoGeometry/Canonical/OperatorErlangenGaloisConnection.lean",
            "lean/InfoGeometry/Krein/DoubledMatrixSymplectic.lean",
        )
    )
)

M1_OWNER_FILES: tuple[str, ...] = (
    "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
    "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean",
    "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
    "lean/InfoGeometry/Optics/OperatorDerivationForms.lean",
    "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
    "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
    "lean/InfoGeometry/Synthesis/OnsagerOperatorDifferentialCalculus.lean",
)

M2_OWNER_FILES: tuple[str, ...] = (
    "lean/InfoGeometry/Clifford/GradedGraceContraction.lean",
    "lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean",
    "lean/InfoGeometry/ErlangenCoordinateless.lean",
    "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean",
    "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean",
    "lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean",
    "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean",
    "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean",
    "lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean",
    "lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean",
)


def _mod(rel_path: str) -> str:
    assert rel_path.startswith("lean/") and rel_path.endswith(".lean")
    return rel_path[len("lean/") : -len(".lean")].replace("/", ".")


def _mods(paths: tuple[str, ...]) -> list[str]:
    return [_mod(p) for p in paths]


# ---------------------------------------------------------------------------
# Tier 1: Feature Coverage (92 checks across 18 features)
# ---------------------------------------------------------------------------

TIER1_CHECKS: tuple[CheckSpec, ...] = (
    # F1.1 (6)
    CheckSpec(
        "T1-F1.1-1", 1, "F1.1", "PHASE-0", "BUCKET 1",
        "Phase-0 R1 probe & strict quality/Apache header pass on F1.1 baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_1_BASELINE), "probe": "r1_baseline", "strict_headers": True},
    ),
    CheckSpec(
        "T1-F1.1-2", 1, "F1.1", "PHASE-0", "BUCKET 1",
        "Axiom audit on F1.1 baseline modules & oneFormAlternatingEquiv/exteriorDerivativeOne/oneForms_addHom_ext",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_1_BASELINE), "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.1-3", 1, "F1.1", "M1", "BUCKET 1",
        "M1 arbitrary-degree differential forms owner compiles with Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
            ],
            "discover_keywords": ("ExteriorCalculus", "DerivationDifferential"),
            "required_patterns": [r"DerivationOperatorForm", r"\bceWedge\b", r"\bceExteriorDerivative_ceWedge\b"],
        },
    ),
    CheckSpec(
        "T1-F1.1-4", 1, "F1.1", "M1", "BUCKET 1",
        "Type-shape: TwoForm K equiv DerivationOperatorForm K 2 and arbitrary-degree d_n without CommRing A",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
            ],
            "required_patterns": [
                r"twoCochainEquivDerivationOperatorForm|twoFormAlternatingEquiv",
                r"def\s+(?:ceExteriorDerivative|exteriorDerivative)\w*",
            ],
            "forbidden_patterns": [r"\[CommRing\s+A\]"],
            "forbidden_scope": "decl",
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.1-5", 1, "F1.1", "M1", "BUCKET 1",
        "Type-shape: universal factorization OneForms A ->+ DerivationOperatorForm K 1 & uniqueness",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
            ],
            "required_patterns": [r"OneForms\s+A\s*→\+\s*(?:DerivationOperatorForm|OneForm)|oneForms_addHom_ext"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.1-6", 1, "F1.1", "M1", "BUCKET 2",
        "Type-shape: commutative specialization from DerivationOperatorForm to graded-commutative / deRhamComplex",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
            ],
            "required_patterns": [
                r"\bceWedge_comm_of_commRing\b|\bwedge_comm_of_commRing\b",
                r"\bderivationDeRhamComplex\b|\bdeRhamComplex\b",
            ],
            "target_decls": [
                "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.ceWedge_comm_of_commRing",
                "InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.derivationDeRhamComplex",
            ],
            "co_occur": True,
        },
    ),
    # F1.2 (5)
    CheckSpec(
        "T1-F1.2-1", 1, "F1.2", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & Apache header pass on F1.2 Maurer-Cartan baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_2_BASELINE), "probe": "r1_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F1.2-2", 1, "F1.2", "PHASE-0", "BUCKET 1",
        "Axiom audit on F1.2 baseline modules (gaugeForm_flat, rightLogarithmicOneForm_maurerCartan, maurer_cartan_flatness)",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_2_BASELINE), "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.2-3", 1, "F1.2", "M1", "BUCKET 1",
        "M1 MaurerCartanTower owner compiles with byte-0 Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean", "lean/InfoGeometry/OperatorAlgebra/MaurerCartanFrameTransport.lean"],
            "discover_keywords": ("MaurerCartanTower",),
            "required_patterns": [r"structure\s+MaurerCartanTower", r"structure\s+MaurerCartanStage"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.2-4", 1, "F1.2", "M1", "BUCKET 1",
        "Type-shape: canonical sign dictionary theta_L(g) = -g^{-1} theta_R(g) g",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean", "lean/InfoGeometry/OperatorAlgebra/MaurerCartanFrameTransport.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationRightLogarithmicForm.lean"],
            "required_patterns": [r"\bthetaR_eq_neg_thetaL_inv\b|\bthetaR_eq_conj_thetaL\b|\bgaugeOneForm_zero_eq_neg_rightLogarithmicOneForm\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.2-5", 1, "F1.2", "M1", "BUCKET 1",
        "Type-shape: MaurerCartanTower stage transitions preserve MC flatness on Peirce & tensor-tower stages",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean"],
            "required_patterns": [r"\bMaurerCartanTower\b", r"\btensorStageTower_unitThetaL_flat\b|\bderivationLieStage_thetaL_flat\b"],
            "co_occur": True,
        },
    ),
    # F1.3 (5)
    CheckSpec(
        "T1-F1.3-1", 1, "F1.3", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R1 probe pass on F1.3 Onsager baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_3_BASELINE), "probe": "r1_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F1.3-2", 1, "F1.3", "PHASE-0", "BUCKET 2",
        "Axiom audit on F1.3 Onsager baseline modules & finite Gibbs BKM synthesis",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_3_BASELINE) + ["InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral"], "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.3-3", 1, "F1.3", "M1", "BUCKET 1",
        "OnsagerDifferentialFormsBridge & Synthesis/OnsagerOperatorDifferentialCalculus pass strict Apache header & 0 duplicate TransportTensor/TimeReversal",
        {
            "kind": "onsager_consolidation",
            "targets": [
                "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
                "lean/InfoGeometry/Synthesis/OnsagerOperatorDifferentialCalculus.lean",
            ],
        },
    ),
    CheckSpec(
        "T1-F1.3-4", 1, "F1.3", "M1", "BUCKET 1",
        "Type-shape: generalized Onsager pairing on DerivationOperatorForm K 1 / arbitrary-degree OpForm",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean"],
            "discover_keywords": ("OnsagerDifferentialForms",),
            "required_patterns": [r"\bDerivationOperatorForm\b", r"onsager_casimir_.*reciprocity"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.3-5", 1, "F1.3", "M1", "BUCKET 2",
        "Type-shape: CEBKMOnsagerGibbsNOperatorFamily maps explicitly into general OnsagerCasimirSystem <-> DerivationOperatorForm",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean", "lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean"],
            "discover_keywords": ("OnsagerDifferentialForms",),
            "required_patterns": [r"finiteGibbs.*DerivationOperatorForm|OnsagerCasimirSystem.*DerivationOperatorForm"],
            "co_occur": True,
        },
    ),
    # F1.4 (5)
    CheckSpec(
        "T1-F1.4-1", 1, "F1.4", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R1 probe pass on F1.4 Frechet baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_4_BASELINE), "probe": "r1_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F1.4-2", 1, "F1.4", "PHASE-0", "BUCKET 1",
        "Axiom audit on F1.4 Frechet baseline modules",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_4_BASELINE), "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.4-3", 1, "F1.4", "M1", "BUCKET 1",
        "Modified OperatorFrechetForms.lean carries byte-0 Apache header, passes unified_gate, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/Canonical/OperatorFrechetForms.lean"],
            "required_patterns": [r"\bOperatorFrechetForm\b"],
        },
    ),
    CheckSpec(
        "T1-F1.4-4", 1, "F1.4", "M1", "BUCKET 1",
        "Type-shape: d_Fr on OperatorFrechetForm A A M n -> (n+1) and d_Fr^2 = 0 under ContDiff 2",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/OperatorFrechetForms.lean"],
            "required_patterns": [r"\bfrechetExteriorDeriv\b|\bfrechetExtDeriv\b", r"\bContDiff\b|\bIsSymmSndFDerivAt\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.4-5", 1, "F1.4", "M1", "BUCKET 1",
        "Type-shape: d_Fr agrees with CE d_n on linear FrechetOperatorDerivation & extDeriv on charts",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
                "lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
            ],
            "required_patterns": [r"\bFrechetOperatorDerivation\b", r"\bextDeriv\b|\bceExteriorDerivative\b|\bexteriorDerivative\b"],
            "co_occur": False,
        },
    ),
    # F1.5 (5)
    CheckSpec(
        "T1-F1.5-1", 1, "F1.5", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R1 probe pass on F1.5 Leibniz derivation baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_5_BASELINE), "probe": "r1_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F1.5-2", 1, "F1.5", "PHASE-0", "BUCKET 1",
        "Axiom audit on F1.5 baseline modules (LieActionLane, DerivationLieLane)",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_5_BASELINE), "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.5-3", 1, "F1.5", "M1", "BUCKET 1",
        "Unified Leibniz derivation adapter spine compiles with Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
                "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
            ],
            "required_patterns": [r"\bLieActionLane\b", r"\bFormDerivation\b|\bIsLeibnizAction\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F1.5-4", 1, "F1.5", "M1", "BUCKET 1",
        "Type-shape: adapters from FrechetOperatorDerivation, NonAssocDerivation, AlgebraDerivation, NCDerivation, CyclicAlgebraDerivation, OpDerivation, ThermodynamicOperatorDerivation, IsLeibniz into LieActionLane/FormDerivation",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/Optics/OperatorDerivationForms.lean",
                "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
            ],
            "required_patterns": [
                r"\btoDerivationDifferentialLieSystem\b|\bFrechetOperatorDerivation\b",
                r"\balgebraDerivationToDerivations\b",
                r"\bnonAssocDerivationEquivDerivations\b",
            ],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F1.5-5", 1, "F1.5", "M1", "BUCKET 1",
        "Type-shape: NCG.DerivationDifferential.LieSystem maps to LieActionLane WITHOUT Function.Injective",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
            ],
            "required_patterns": [r"\blieSystemToLieActionLane\b|\blieSystemToDerivationLieLane\b"],
            "forbidden_patterns": [r"Function\.Injective"],
            "forbidden_scope": "decl",
            "co_occur": True,
        },
    ),
    # F1.6 (5)
    CheckSpec(
        "T1-F1.6-1", 1, "F1.6", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R1 probe pass on F1.6 n-operator-forms baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_6_BASELINE), "probe": "r1_baseline", "strict_headers": True},
    ),
    CheckSpec(
        "T1-F1.6-2", 1, "F1.6", "PHASE-0", "BUCKET 1",
        "Axiom audit on F1.6 baseline modules (ofCEFamily, component, singleton_exteriorDerivativeZero_eq_firstFrechetJet)",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_6_BASELINE), "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.6-3", 1, "F1.6", "M1", "BUCKET 1",
        "M1 disambiguation aliases (OneFormTuple / AlternatingOperatorForm) compile preserving NOperatorForm backward compatibility",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/Optics/OperatorDerivationForms.lean", "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean"],
            "required_patterns": [r"\bNOperatorForm\b", r"\bOneFormTuple\b|\bAlternatingOperatorForm\b"],
        },
    ),
    CheckSpec(
        "T1-F1.6-4", 1, "F1.6", "M1", "BUCKET 1",
        "Type-shape: canonical map from linear OneFormTuple n to alternating OpForm R V A n",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Optics/OperatorDerivationForms.lean", "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean"],
            "required_patterns": [r"\bopFormOneToOneFormTuple\b|\boneFormLinearToOpFormOne\b|\bopFormWedgeTuple\b", r"\bOpForm\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.6-5", 1, "F1.6", "M1", "BUCKET 1",
        "Type-shape: OpForm / DerivationOperatorForm carries graded wedge and exterior derivative",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean"],
            "required_patterns": [r"\bOpForm\b", r"\bderivN\b|\bopWedge\b"],
            "co_occur": True,
        },
    ),
    # F1.7 (5)
    CheckSpec(
        "T1-F1.7-1", 1, "F1.7", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R1 probe pass on F1.7 NC operator ring differential geometry baseline owners",
        {"kind": "quality_and_probe", "targets": list(F1_7_BASELINE), "probe": "r1_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F1.7-2", 1, "F1.7", "PHASE-0", "BUCKET 1",
        "Axiom audit on F1.7 baseline modules (connectionCurvature_bianchi, covariantDerivative_gauge_equivariant, noncommutativeChernSimonsTransgression)",
        {"kind": "axiom_audit_modules", "modules": _mods(F1_7_BASELINE), "probe": "r1_baseline"},
    ),
    CheckSpec(
        "T1-F1.7-3", 1, "F1.7", "M1", "BUCKET 1",
        "Unified M1 NC geometry owner compiles with Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bconnectionCurvature_bianchi\b", r"\bcovariantDerivative\b"],
        },
    ),
    CheckSpec(
        "T1-F1.7-4", 1, "F1.7", "M1", "BUCKET 1",
        "Type-shape: NCG.AlgebraDerivation curvature & gauge transform reconciled with DerivationDifferentialForms",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean",
            ],
            "required_patterns": [r"\balgDeriv_covariantDerivative_gaugeTransformOneForm\b|\bpureGaugeForm_nc_eq_thetaL_inv\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F1.7-5", 1, "F1.7", "M1", "BUCKET 1",
        "Type-shape: Connes cyclic 1-cocycle factors cleanly from universal OneForms A and DerivationOperatorForm K 1",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean",
                "lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean",
            ],
            "required_patterns": [r"\bcyclicAlgebraDerivationToDerivations\b|\bCyclicAlgebraDerivation\b|\bOneForms\b"],
            "co_occur": False,
        },
    ),
    # F3.1 (5)
    CheckSpec(
        "T1-F3.1-1", 1, "F3.1", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R3 probe pass on F3.1 Cl(1,1) tower baseline owners",
        {"kind": "quality_and_probe", "targets": list(F3_1_BASELINE), "probe": "r3_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F3.1-2", 1, "F3.1", "PHASE-0", "BUCKET 1",
        "Axiom audit on F3.1 baseline modules (cl11EquivMat, cl11StandardEquiv, tensorMatrixEquiv, ClInf)",
        {"kind": "axiom_audit_modules", "modules": _mods(F3_1_BASELINE), "probe": "r3_baseline"},
    ),
    CheckSpec(
        "T1-F3.1-3", 1, "F3.1", "M2", "BUCKET 1",
        "M2 Cl(1,1) tower unification owner compiles with Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean", "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean"],
            "discover_keywords": ("SplitCliffordTower", "Cl11GradedTensorMorita"),
            "required_patterns": [r"\bClTower\b", r"\bClsplit\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.1-4", 1, "F3.1", "M2", "BUCKET 1",
        "Type-shape: inductive AlgEquiv Clsplit n (g)tensor A ~ ClTower A n for arbitrary [Ring A] [Algebra R A]",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean", "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean"],
            "required_patterns": [r"\bclSplitEquivClTowerReal\b|\bclTowerEquivCliffordTensor\b|Clsplit.*≃ₐ\[ℝ\].*ClTower|ClTower.*≃ₐ\[ℝ\].*Clsplit"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.1-5", 1, "F3.1", "M2", "BUCKET 1",
        "Type-shape: compatibility of splitCliffordStep, diagEmbed, bottEmbed & 3-way basis conjugacy",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedMorita.lean", "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean"],
            "required_patterns": [r"\bdiagEmbed\b", r"\bbottEmbed\b", r"\bcl11StandardEquiv\b|\bcl11MatrixAlgEquiv\b"],
            "co_occur": True,
        },
    ),
    # F3.2 (5)
    CheckSpec(
        "T1-F3.2-1", 1, "F3.2", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R3 probe pass on F3.2 Cl(1,1) atom symmetry baseline owners",
        {"kind": "quality_and_probe", "targets": list(F3_2_BASELINE), "probe": "r3_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F3.2-2", 1, "F3.2", "PHASE-0", "BUCKET 1",
        "Axiom audit on F3.2 baseline modules (localCl11Map, cl11EquivMat_splitReflectionCliffordAuto, erlangenDoubleCylinderInvariantSubring_noncommutative)",
        {"kind": "axiom_audit_modules", "modules": _mods(F3_2_BASELINE), "probe": "r3_baseline"},
    ),
    CheckSpec(
        "T1-F3.2-3", 1, "F3.2", "M2", "BUCKET 1",
        "M2 atom-symmetry extension compiles with byte-0 Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean"],
            "required_patterns": [r"\blocalCl11Map\b", r"\bSymmetryAction\b"],
        },
    ),
    CheckSpec(
        "T1-F3.2-4", 1, "F3.2", "M2", "BUCKET 1",
        "Type-shape: SymmetryAction V4 on CliffordAlgebra q11, Clsplit n, and SplitCliffordInfinity",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean",
                "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean",
                "lean/InfoGeometry/Clifford/Cl11CliffordMapIsometryBridge.lean",
            ],
            "required_patterns": [r"\bSymmetryAction\b.*(?:V4|KleinFour)", r"\bClsplit\b|\bSplitCliffordInfinity\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.2-5", 1, "F3.2", "M2", "BUCKET 1",
        "Type-shape: compatibility between SymmetryAction on SplitCliffordInfinity & erlangenDoubleCylinderSymmetryAction",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean",
                "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean",
                "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean",
            ],
            "required_patterns": [r"\bdoubleCylinderColimitV4\w*|\berlangenDoubleCylinderSymmetryAction\b", r"\bSplitCliffordInfinity\b|\blocalCl11AlgebraHom_v4_equivariant\b"],
            "co_occur": True,
        },
    ),
    # F3.3 (5)
    CheckSpec(
        "T1-F3.3-1", 1, "F3.3", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R3 probe pass on F3.3 graded tensor chains & differentials baseline owners",
        {
            "kind": "quality_and_probe",
            "targets": list(F3_3_BASELINE),
            "opengauss_targets": [
                "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean",
            ],
            "probe": "r3_baseline",
            "strict_headers": False,
        },
    ),
    CheckSpec(
        "T1-F3.3-2", 1, "F3.3", "PHASE-0", "BUCKET 1",
        "Axiom audit on F3.3 baseline modules (nativeChain_matrix_suffixParity, jwDifferential_sq, jwDifferential_homotopy)",
        {"kind": "axiom_audit_modules", "modules": _mods(F3_3_BASELINE), "probe": "r3_baseline"},
    ),
    CheckSpec(
        "T1-F3.3-3", 1, "F3.3", "M2", "BUCKET 1",
        "Transported differential/homotopy owner on SplitCliffordInfinity / nativeChain compiles with Apache header & clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean", "lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean"],
            "required_patterns": [r"\bnativeChain\b", r"\bjwDifferential\b"],
        },
    ),
    CheckSpec(
        "T1-F3.3-4", 1, "F3.3", "M2", "BUCKET 1",
        "Type-shape: transported d_native / h_native on SplitCliffordInfinity satisfy d^2=0, dh+hd=1, range=ker, d!=0",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean", "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean"],
            "required_patterns": [r"\bSplitCliffordInfinity\b", r"\bsplitJWDifferential\b|\bnativeChainDifferential\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.3-5", 1, "F3.3", "M2", "BUCKET 1",
        "Type-shape: intertwining of d_native with jwDifferential via canonicalCliffordUHFColimitEquiv & formula on nativeChain",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean", "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean"],
            "required_patterns": [r"\bcanonicalCliffordUHFColimitEquiv\b", r"\bnativeChainDifferential_nativeChain\b|\bnativeChain\b"],
            "co_occur": True,
        },
    ),
    # F3.4 (6)
    CheckSpec(
        "T1-F3.4-1", 1, "F3.4", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R3 probe pass on F3.4 coordinate-less Clifford baseline owners",
        {"kind": "quality_and_probe", "targets": list(F3_4_BASELINE), "probe": "r3_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F3.4-2", 1, "F3.4", "PHASE-0", "BUCKET 1",
        "Axiom audit on F3.4 baseline modules (cliffordGradeProj_idem, clifford_i_injective, cliffordGradeProj_zero_eq_algebraMap_hTrace)",
        {"kind": "axiom_audit_modules", "modules": _mods(F3_4_BASELINE), "probe": "r3_baseline"},
    ),
    CheckSpec(
        "T1-F3.4-3", 1, "F3.4", "M2", "BUCKET 1",
        "Coordinate-less Clifford invariance owner compiles with byte-0 Apache header, 0 placeholders, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean", "lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean"],
            "discover_keywords": ("CoordinateLessClifford", "GradedGraceContraction"),
            "required_patterns": [r"\bcliffordSymmetryAction\b|\bequivOfIsometry\b"],
        },
    ),
    CheckSpec(
        "T1-F3.4-4", 1, "F3.4", "M2", "BUCKET 1",
        "Type-shape: equivOfIsometry f commutes with involute, reverse, evenOdd, cliffordGradeProj, graceOperator & preserves hTrace_cl",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean"],
            "required_patterns": [
                r"\bcliffordSymmetryAction_equivariant_gradeProj\b|equivOfIsometry.*cliffordGradeProj|cliffordGradeProj.*equivOfIsometry",
                r"equivOfIsometry.*reverse|reverse.*equivOfIsometry",
                r"\bhTraceInvariantReadout\b|hTrace_cl.*equivOfIsometry",
            ],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.4-5", 1, "F3.4", "M2", "BUCKET 1",
        "Type-shape: SymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q) & invariant subalgebra theorem",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean", "lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean"],
            "required_patterns": [r"SymmetryAction.*IsometryEquiv.*CliffordAlgebra", r"\binvariantSubring_cliffordSymmetryAction\b|\bisInvariant_cliffordSymmetryAction_iff_mem_range\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.4-6", 1, "F3.4", "M2", "BUCKET 1",
        "ErlangenCoordinateless.lean upgraded or explicitly documented as M_2(C) Pauli realization aligned with abstract CliffordAlgebra Q",
        {
            "kind": "contract_probe",
            "required_files": [
                "lean/InfoGeometry/ErlangenCoordinateless.lean",
                "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean",
            ],
            "required_patterns": [r"\berlangen_coordinateless_capstone\b", r"\bcliffordSymmetryAction\b"],
            "target_decls": [
                "ErlangenCoordinateless.erlangen_coordinateless_capstone",
                "ErlangenCoordinateless.pauli_s1_s2_not_commute",
                "InfoGeometry.Clifford.CoordinateLessCliffordInvariance.cliffordSymmetryAction",
            ],
            "co_occur": False,
        },
    ),
    # F3.5 (5)
    CheckSpec(
        "T1-F3.5-1", 1, "F3.5", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R3 probe pass on F3.5 Zorn/Hodge & Cartan-Hestenes baseline owners",
        {"kind": "quality_and_probe", "targets": list(F3_5_BASELINE), "probe": "r3_baseline", "strict_headers": True},
    ),
    CheckSpec(
        "T1-F3.5-2", 1, "F3.5", "PHASE-0", "BUCKET 1",
        "Axiom audit on F3.5 baseline modules (cliffordMorphism_generator_square, cartan_hestenes_rotor_darboux_spin_connection_identity)",
        {"kind": "axiom_audit_modules", "modules": _mods(F3_5_BASELINE), "probe": "r3_baseline"},
    ),
    CheckSpec(
        "T1-F3.5-3", 1, "F3.5", "M2", "BUCKET 1",
        "M2 R3<->R1 coupling upgrades compile with Apache header, unified_gate exit 0, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": list(F3_5_BASELINE),
            "required_patterns": [r"\bFormHodgeCliffordData\b", r"\brotorDarbouxConnection\b|\brotorFrameVector\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F3.5-4", 1, "F3.5", "M2", "BUCKET 1",
        "Type-shape: coupling FormHodgeCliffordData to CliffordAlgebra.equivExterior D.Q / cliffordGradeProj",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean", "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean"],
            "required_patterns": [r"\bFormHodgeCliffordData\b", r"\bequivExterior\b|\bcliffordGradeProj\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F3.5-5", 1, "F3.5", "M2", "BUCKET 1",
        "Type-shape: abstract CliffordAlgebra Q Darboux spin-connection theorem via CliffordAlgebra.reverse",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean", "lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean"],
            "required_patterns": [r"\bCliffordAlgebra\.reverse\b", r"\bCliffordAlgebra\s+Q\b"],
            "co_occur": True,
        },
    ),
    # F2.1 (5)
    CheckSpec(
        "T1-F2.1-1", 1, "F2.1", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R2 probe pass on F2.1 Erlangen 2.0 baseline owners",
        {"kind": "quality_and_probe", "targets": list(F2_1_BASELINE), "probe": "r2_r1r2_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F2.1-2", 1, "F2.1", "PHASE-0", "BUCKET 1",
        "Axiom audit on F2.1 baseline modules (OperatorIntertwiner, cartanFiberErlangen20Datum, ErlangenOperatorDatum)",
        {"kind": "axiom_audit_modules", "modules": _mods(F2_1_BASELINE), "probe": "r2_r1r2_baseline"},
    ),
    CheckSpec(
        "T1-F2.1-3", 1, "F2.1", "M3", "BUCKET 1",
        "M3 Erlangen 2.0 unification modules compile with Apache header, unified_gate exit 0, clean axioms, and cite 1872 Erlanger Programm (ABN7632.0001.001)",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean"],
            "required_patterns": [r"\bErlangen20Datum\b"],
            "verify_erlangen_1872_docs": True,
        },
    ),
    CheckSpec(
        "T1-F2.1-4", 1, "F2.1", "M3", "BUCKET 1",
        "Type-shape: unified constructors SymmetryAction <-> Erlangen20Datum, PhaseCentralizer -> SymmetryAction, ErlangenOperatorDatum -> Erlangen20Datum",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
                "lean/InfoGeometry/Canonical/ErlangenOperator2.lean",
                "lean/InfoGeometry/Geometry/PhaseErlanger.lean",
                "lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean",
            ],
            "discover_keywords": ("Erlangen20OperatorGeometry", "FelixKleinGeometryUnification"),
            "required_patterns": [r"\bphaseCentralizerSymmetryAction\b|PhaseCentralizer.*SymmetryAction", r"\btoErlangen20Datum\b|ErlangenOperatorDatum.*Erlangen20Datum"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F2.1-5", 1, "F2.1", "M3", "BUCKET 1",
        "cartanFiberErlangen20Datum & cantorDoubleCylinderErlangen20Datum unified in Erlangen20 hierarchy",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean",
                "lean/InfoGeometry/Canonical/CantorDoubleCylinderColimitAlgebra.lean",
                "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
            ],
            "required_patterns": [r"\bcartanFiberErlangen20Datum\b", r"\bcantorDoubleCylinderErlangen20Datum\b"],
            "co_occur": False,
        },
    ),
    # F2.2 (5)
    CheckSpec(
        "T1-F2.2-1", 1, "F2.2", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R2 probe pass on F2.2 double-real Krein baseline owners",
        {"kind": "quality_and_probe", "targets": list(F2_2_BASELINE), "probe": "r2_r1r2_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F2.2-2", 1, "F2.2", "PHASE-0", "BUCKET 1",
        "Axiom audit on F2.2 baseline modules (componentNReal_not_krein_isometry, kreinMetric88_properties, firstStep_leftGenerator_eq_cl11Rep)",
        {"kind": "axiom_audit_modules", "modules": _mods(F2_2_BASELINE), "probe": "r2_r1r2_baseline"},
    ),
    CheckSpec(
        "T1-F2.2-3", 1, "F2.2", "M3", "BUCKET 1",
        "M3 Krein unification files compile with byte-0 Apache header, unified_gate exit 0, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/Krein/KreinSpace.lean", "lean/InfoGeometry/Krein/DoubledSpace.lean", "lean/InfoGeometry/KK/ClNNFredholmBridge.lean"],
            "required_patterns": [r"\bKreinSpace\b", r"\bDoubledSpace\b"],
        },
    ),
    CheckSpec(
        "T1-F2.2-4", 1, "F2.2", "M3", "BUCKET 1",
        "Type-shape: KreinSpace (EuclideanSpace R Krein16Idx) from kreinMetric88, KreinGradedModule from gamma44, functor RealKreinSpace => RealKVect",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean",
                "lean/InfoGeometry/Krein/Category.lean",
                "lean/InfoGeometry/Quantum/RealKCategory.lean",
            ],
            "required_patterns": [r"KreinSpace.*Krein16Idx|Krein16Idx.*KreinSpace", r"\bRealKreinSpace\b.*\bRealKVect\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F2.2-5", 1, "F2.2", "M3", "BUCKET 2",
        "Type-shape: ClNNFredholmBridge extended to arbitrary Clsplit n & carrier-isometry transport",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/ClNNFredholmBridge.lean", "lean/InfoGeometry/Krein/DoubledSpace.lean"],
            "required_patterns": [r"\bClsplit\b", r"kreinAdjoint.*≃ₗᵢ|eH.*kreinInner"],
            "co_occur": True,
        },
    ),
    # F2.3 (5)
    CheckSpec(
        "T1-F2.3-1", 1, "F2.3", "PHASE-0", "BUCKET 2",
        "Phase-0 quality & R2 probe pass on F2.3 Kasparov & spectral triple baseline owners",
        {"kind": "quality_and_probe", "targets": list(F2_3_BASELINE), "probe": "r2_r1r2_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F2.3-2", 1, "F2.3", "PHASE-0", "BUCKET 2",
        "Axiom audit on F2.3 baseline modules (superComm_pi_compact, RealSplitKreinUnboundedCycle.regular)",
        {"kind": "axiom_audit_modules", "modules": _mods(F2_3_BASELINE), "probe": "r2_r1r2_baseline"},
    ),
    CheckSpec(
        "T1-F2.3-3", 1, "F2.3", "M3", "BUCKET 2",
        "Updated SpectralTriple.lean & M3 Kasparov bridge compile with byte-0 Apache header, unified_gate exit 0, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean", "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean"],
            "required_patterns": [r"\bRealStructureKreinCompatible\b"],
        },
    ),
    CheckSpec(
        "T1-F2.3-4", 1, "F2.3", "M3", "BUCKET 2",
        "Type-shape: RealStructureKreinCompatible uses kreinInner & bridge PhaseRealSpectralTriple -> RealSplitKreinUnboundedCycle -> RealSplitKreinKasparovCycle",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
                "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean",
                "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
            ],
            "required_patterns": [r"def\s+RealStructureKreinCompatible|RealStructureKreinCompatible.*kreinInner", r"\btoUnboundedCycle\b|PhaseRealSpectralTriple.*RealSplitKreinUnboundedCycle"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F2.3-5", 1, "F2.3", "M3", "BUCKET 2",
        "Type-shape: nontrivial finite-dim RealSplitKreinKasparovCycle witness with F != 0 & F^2 = 1",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/KK/Examples.lean",
                "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
                "lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean",
            ],
            "required_patterns": [r"\bRealSplitKreinKasparovCycle\b", r"\.F\s*≠\s*0|F\s*\*\s*F\s*=\s*1"],
            "co_occur": True,
        },
    ),
    # F2.4 (5)
    CheckSpec(
        "T1-F2.4-1", 1, "F2.4", "PHASE-0", "BUCKET 1",
        "Phase-0 quality & R1<->R2 probe pass on F2.4 cross-pillar baseline owners",
        {"kind": "quality_and_probe", "targets": list(F2_4_BASELINE), "probe": "r2_r1r2_baseline", "strict_headers": False},
    ),
    CheckSpec(
        "T1-F2.4-2", 1, "F2.4", "PHASE-0", "BUCKET 1",
        "Axiom audit on F2.4 baseline modules (action_preserves_compact_phase_defects, ncDeriv_leibniz, kreinToDual)",
        {"kind": "axiom_audit_modules", "modules": _mods(F2_4_BASELINE), "probe": "r2_r1r2_baseline"},
    ),
    CheckSpec(
        "T1-F2.4-3", 1, "F2.4", "M3", "BUCKET 1",
        "M3 cross-pillar bridge modules compile with Apache header, unified_gate exit 0, clean axioms",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": ["lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean", "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean"],
            "required_patterns": [r"\bEquivariantDatum\b", r"\bncDeriv\b"],
        },
    ),
    CheckSpec(
        "T1-F2.4-4", 1, "F2.4", "M3", "BUCKET 1",
        "Type-shape: all 4 cross-pillar morphisms (EquivariantDatum->Erlangen20, Omega^1->Omega^1_D, Onsager->HasJReciprocity, MC<->1-F^2)",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
                "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
                "lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean",
                "lean/InfoGeometry/Geometry/ConstructiveKasparov.lean",
            ],
            "required_patterns": [
                r"\bEquivariantErlangenKasparov\b|EquivariantDatum.*Erlangen20Datum",
                r"\bHasJReciprocity\b",
                r"\bD_A\b|fluctuat",
            ],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F2.4-5", 1, "F2.4", "M3", "BUCKET 1",
        "Zero scalar/diagonal surrogate check: cross-pillar bridges retain non-commuting [Ring A] / EndH H",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
                "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
            ],
            "required_patterns": [r"\[(?:Normed)?Ring\s+A\]", r"\bncDeriv\b|\bEquivariantDatum\b", r"Matrix\s*\(Fin\s*2\)|\*.*≠.*\*"],
            "forbidden_patterns": [r"\[CommRing\s+A\]"],
            "forbidden_scope": "decl",
            "co_occur": True,
        },
    ),
    # F2.5 (5)
    CheckSpec(
        "T1-F2.5-1", 1, "F2.5", "PHASE-0", "BUCKET 1",
        "Phase-0 shared-checkout disk, Apache-header, placeholder & axiom_audit hygiene on Grassmann*/Plucker*/KleinQuadric* modules",
        {"kind": "f25_baseline_hygiene", "targets": list(F2_5_BASELINE_ALL), "compiled_targets": list(F2_5_BASELINE_COMPILED)},
    ),
    CheckSpec(
        "T1-F2.5-2", 1, "F2.5", "M3", "BUCKET 1",
        "F2.5 Klein 1872 <-> Grassmann [6,7,8] & Plucker Bridges A/B/C, GrassmannPluckerKleinFunctorialBridges & 11 Erlangen/Grassmann/Plucker modules compile cleanly",
        {
            "kind": "milestone_quality_and_probe",
            "required_files": list(F2_5_ERLANGEN_PROGRAM_MODULES) + list(F2_5_SYNTHESIS_AND_BRIDGE_MODULES),
            "discover_keywords": ("GrassmannPluckerKlein", "PluckerGrassmannKlein", "ErlangenProgram", "KleinErlangen"),
            "required_patterns": [
                r"\bKleinQuadric\b|\bPlucker6\b",
                r"\bGrassmann\b|\bPfaffian\b|\bIsSyncyclic4\b",
                r"\bklein_erlangen_1872_master_synthesis\b",
                r"\bgrassmann_plucker_klein_trilogy_synthesis\b",
                r"\blieMobiusToCircleHom\b",
                r"\bfinrank_ker_complexForm_complexCongr\b",
                r"\bplucker_grassmann_klein_grand_synthesis\b",
            ],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F2.5-3", 1, "F2.5", "M3", "BUCKET 1",
        "Bridge A type-shape & kernel check: Grassmann exterior/regressive products <-> Plucker ray coordinates & Klein quadric",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Projective/GrassmannAusdehnungslehreRegressiveShadow.lean",
                "lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean",
                "lean/InfoGeometry/Projective/KleinQuadricPlucker.lean",
            ],
            "required_patterns": [
                r"\bpluckerToExterior2\b|\bgrassmannBladeToPlucker\b|\bKleinQuadric\b|\bPlucker6\b",
                r"\bregressive\b|\bplucker_span_eq_iff_proportional\b|\bhodge_pluckerToExterior2_eq_kleinHodgeDual\b",
            ],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T1-F2.5-4", 1, "F2.5", "M3", "BUCKET 1",
        "Bridge B type-shape & kernel check: Grassmann syncyclic circle space <-> Klein §§6-7 Mobius 4-var lightcone & Lie sphere 5-var Korper (incl. lieMobiusToCircleHom)",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean",
                "lean/InfoGeometry/Projective/MobiusPluckerKleinCompatibility.lean",
            ],
            "required_patterns": [r"\bIsSyncyclic4\b|\bIsCircleTangent\b|\bcircleBilin\b", r"\blieMobiusToCircleHom\b|\blieQuadricBilin\b|\bmoebiusQuadricBilin\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T1-F2.5-5", 1, "F2.5", "M3", "BUCKET 1",
        "Bridge C type-shape & kernel check: Grassmann Pfaffian normal forms & Darboux rank <-> Plucker linear/special complexes, GL4 contravariant functor, Kummer surfaces & §9 contact 1-forms",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Erlangen/ErlangenProgramCurvatureBinaryAndMasterAtlas.lean",
                "lean/InfoGeometry/Canonical/GrassmannPfaffianSyzygyAndNormalForms.lean",
                "lean/InfoGeometry/Projective/PluckerLinearComplexGeometry.lean",
                "lean/InfoGeometry/Projective/PluckerKummerQuarticAndMasterAtlas.lean",
            ],
            "required_patterns": [r"\bcomplexForm\b|\bpfaffJet\w*|\bDarboux\b", r"\bcomplexCongr\b|\bPlucker6\b|\bkummerSingularQuartic\b"],
            "co_occur": True,
        },
    ),
    # F4.1 (5)
    CheckSpec(
        "T1-F4.1-1", 1, "F4.1", "PHASE-0", "BUCKET 1",
        "Phase-0 placeholder_audit --strict & axiom_audit --fail-on-gaps across all 60 baseline R1/R2/R3 owner files",
        {"kind": "baseline_wide_hygiene", "targets": list(ALL_BASELINE_OWNER_FILES)},
    ),
    CheckSpec(
        "T1-F4.1-2", 1, "F4.1", "M3", "BUCKET 1",
        "Existence & BUCKET 1/2/3 tagging of R1, R3, and Master Reconciliation specification docs (including Klein 1872 Erlanger Programm ABN7632.0001.001)",
        {"kind": "rubric_spec_docs_present"},
    ),
    CheckSpec(
        "T1-F4.1-3", 1, "F4.1", "M3", "BUCKET 1",
        "Barrel & mirror sync: M1-M3 owners imported in lean/InfoGeometry.lean and src/ NCG parity resolved",
        {"kind": "barrel_and_src_sync"},
    ),
    CheckSpec(
        "T1-F4.1-4", 1, "F4.1", "M3", "BUCKET 1",
        "Scoped axiom_check & axiom_index pass across complete M1-M3 compiled .olean closure",
        {"kind": "m1_m2_m3_axiom_closure"},
    ),
    CheckSpec(
        "T1-F4.1-5", 1, "F4.1", "M3", "BUCKET 1",
        "Scoped unified_gate, semantic_content_audit, native_decide, Prop-wrapper & strict byte-0 Apache header gate across M1-M3",
        {"kind": "m1_m2_m3_strict_quality"},
    ),
)


# ---------------------------------------------------------------------------
# Tier 2: Boundary & Corner Cases (92 checks across 18 features)
# ---------------------------------------------------------------------------

TIER2_CHECKS: tuple[CheckSpec, ...] = (
    # F1.1 (6)
    CheckSpec(
        "T2-F1.1-1", 2, "F1.1", "M1", "BUCKET 1",
        "Degree spectrum n = 0,1,2,3,4: d_{n+1}(d_n w) = 0 verified explicitly at n=0,1,2,3",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bceExteriorDerivative_succ_comp\b|\bactionExteriorDerivative_succ_comp\b|\bd_succ_comp_d_eq_zero\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.1-2", 2, "F1.1", "M1", "BUCKET 1",
        "Non-vacuity & noncommutativity: M_2(R) inner derivation lane witness with w ^ eta != -(eta ^ w)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"Matrix\s*\(Fin\s*2\)\s*\(Fin\s*2\)\s*ℝ", r"\bceWedge\b|\bactionWedge\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.1-3", 2, "F1.1", "M1", "BUCKET 1",
        "Graded associativity & unit of wedge at degrees (1,1,2) and (0,2,1)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bceWedge_assoc\b|\bactionWedge_assoc\b", r"\bceWedge_zero_left\b|\bactionWedge_zero_left\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.1-4", 2, "F1.1", "M1", "BUCKET 1",
        "Graded Leibniz boundary at odd degree p=1 (-1 sign) and even degree p=2 (+1 sign)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bceExteriorDerivative_ceWedge\b|\bactionExteriorDerivative_actionWedge\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.1-5", 2, "F1.1", "M1", "BUCKET 1",
        "Commutative [CommRing A] graded-commutativity vs noncommutative M_2(R) separation",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bceWedge_comm_of_commRing\b|\bactionWedge_comm_of_commRing\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.1-6", 2, "F1.1", "PHASE-0", "BUCKET 1",
        "Universal 1-form Leibniz boundary on non-commuting M_2(R) (a * b != b * a & tensor order preserved)",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean", "symbol": "differential_mul"},
    ),
    # F1.2 (5)
    CheckSpec(
        "T2-F1.2-1", 2, "F1.2", "M1", "BUCKET 1",
        "Non-commuting unit sign test on GL_2(R): theta_L != theta_R and theta_L != -theta_R without Ad_{g^-1}",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean", "lean/InfoGeometry/OperatorAlgebra/MaurerCartanFrameTransport.lean"],
            "required_patterns": [r"\bthetaR_eq_conj_thetaL\b|\bactionThetaR_eq_conj_actionThetaL\b", r"\bthetaR_eq_neg_thetaL_inv\b|\bactionThetaR_eq_neg_actionThetaL_inv\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.2-2", 2, "F1.2", "PHASE-0", "BUCKET 1",
        "Product cocycle non-abelian order: gaugeForm_product theta_L(gh) = h^{-1} theta_L(g) h + theta_L(h)",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/OperatorAlgebra/MaurerCartanFrameTransport.lean", "symbol": "gaugeForm_product"},
    ),
    CheckSpec(
        "T2-F1.2-3", 2, "F1.2", "M1", "BUCKET 1",
        "Flat gaugeForm (F=0) vs non-flat connection Gamma in M_2(R) with F(Gamma) != 0",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean"],
            "required_patterns": [r"\bthetaL_flat\b|\bactionThetaL_flat\b", r"\bceCurvature\b|\bactionCurvature\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.2-4", 2, "F1.2", "M1", "BUCKET 1",
        "5-graded Peirce nilpotent MC boundary instantiated in MaurerCartanTower",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean"],
            "required_patterns": [r"\bMaurerCartanTower\b", r"\bpeirceFiveGradedStage\b|\bpeirce_five_graded_mc_stage\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.2-5", 2, "F1.2", "PHASE-0", "BUCKET 1",
        "src/ vs lean/ parity check on NCG/NoncommutativeConnectionCurvature.lean (detects Phase-0 lag honestly)",
        {"kind": "src_parity_ncg", "expect_synced": False},
    ),
    # F1.3 (5)
    CheckSpec(
        "T2-F1.3-1", 2, "F1.3", "PHASE-0", "BUCKET 1",
        "Diagonal reversible vanishing (reversible1Form_diag_zero) & 2nd Law nonneg (totalGenerator1Form_nonneg)",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean", "symbol": "reversible1Form_diag_zero"},
    ),
    CheckSpec(
        "T2-F1.3-2", 2, "F1.3", "M1", "BUCKET 1",
        "Non-Gibbs / non-matrix [Ring A] [Algebra R A] witness for OnsagerCasimirSystem + DerivationOperatorForm",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean"],
            "required_patterns": [r"\bOnsagerCasimirSystem\b", r"\bDerivationOperatorForm\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.3-3", 2, "F1.3", "M1", "BUCKET 1",
        "Time-reversal parity sign flip (+1 vs -1) gives exact Casimir antisymmetric coupling",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean", "lean/InfoGeometry/Thermo/OnsagerOperatorClosure.lean"],
            "required_patterns": [r"\bParityOnsagerSystem\b", r"onsager_casimir_.*reciprocity"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.3-4", 2, "F1.3", "M1", "BUCKET 1",
        "Duplicate-type unification test: single TransportTensor & TimeReversal type across OperatorExteriorAlgebraGeneral, OnsagerOperatorClosure, Synthesis",
        {"kind": "onsager_no_duplicates"},
    ),
    CheckSpec(
        "T2-F1.3-5", 2, "F1.3", "PHASE-0", "BUCKET 2",
        "Scope boundary check: finiteGibbsCEFamilyNOperatorForm carries explicit FiniteOperatorAlgebra n / GibbsOperator n",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean", "symbol": "finiteGibbsCEFamilyNOperatorForm"},
    ),
    # F1.4 (5)
    CheckSpec(
        "T2-F1.4-1", 2, "F1.4", "M1", "BUCKET 1",
        "Degree n=0,1,2 Frechet exterior derivative d_Fr(d_Fr f) = 0 on C^2 nonlinear matrix maps",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/OperatorFrechetForms.lean"],
            "required_patterns": [r"\bfrechetExteriorDeriv\b|\bfrechetExtDeriv\b", r"=\s*0"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.4-2", 2, "F1.4", "M1", "BUCKET 1",
        "Linear FrechetOperatorDerivation vs nonlinear powerFrechetDerivation (x^3 noncommutative order preserved)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/OperatorFrechetForms.lean", "lean/InfoGeometry/Optics/OperatorDerivationForms.lean"],
            "required_patterns": [r"\bpowerFrechetDerivation\b", r"\bFrechetOperatorDerivation\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.4-3", 2, "F1.4", "PHASE-0", "BUCKET 2",
        "frechetOperatorDerivationOfThermodynamic requires [FiniteDimensional R Value] vs arbitrary [NormedRing A]",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/Optics/OperatorDerivationForms.lean", "symbol": "frechetOperatorDerivationOfThermodynamic"},
    ),
    CheckSpec(
        "T2-F1.4-4", 2, "F1.4", "M1", "BUCKET 1",
        "Non-differentiable corner case: d_Fr^2 = 0 explicitly requires ContDiff 2 / second-derivative symmetry",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/OperatorFrechetForms.lean"],
            "required_patterns": [r"\bfrechetExteriorDeriv\b|\bfrechetExtDeriv\b", r"\bContDiff\b|\bIsSymmSndFDerivAt\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.4-5", 2, "F1.4", "PHASE-0", "BUCKET 1",
        "ExchangeInvolution.even_odd & odd_even orthogonality on nontrivial M_2(R) (exchange != +-id)",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean", "symbol": "ExchangeInvolution"},
    ),
    # F1.5 (5)
    CheckSpec(
        "T2-F1.5-1", 2, "F1.5", "M1", "BUCKET 1",
        "Non-faithful inner derivation counterexample ad : M_2(R) -> End(M_2(R)) (ad(I_2) = 0) adapted without false Injective",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/Algebra/DerivationLieLane.lean"],
            "required_patterns": [r"\binnerLieActionLane\b", r"\blieSystemToLieActionLane\b"],
            "forbidden_patterns": [r"Function\.Injective"],
            "forbidden_scope": "decl",
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.5-2", 2, "F1.5", "M1", "BUCKET 1",
        "Non-associative IsDerivation ([NonUnitalNonAssocRing A]) adapts without [Associative]",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/Algebra/DerivationLieLane.lean", "lean/InfoGeometry/Algebra/NonAssocDerivation.lean"],
            "required_patterns": [r"\bfullDerivationLieLane\b", r"\bnonAssocDerivationEquivDerivations\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.5-3", 2, "F1.5", "M1", "BUCKET 1",
        "Ring base Z vs R vs CommRing R: NCDerivation A -> LieActionLane Z A & Frechet -> LieActionLane R A",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/Algebra/DerivationLieLane.lean"],
            "required_patterns": [r"\bncDerivationEquivDerivations\b|\binnerLieActionLane\b", r"\bLieActionLane\s+ℤ\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.5-4", 2, "F1.5", "M1", "BUCKET 1",
        "CyclicAlgebraDerivation trace-vanishing tau(D a) = 0 preserved by adaptation",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean"],
            "required_patterns": [r"\bcyclicAlgebraDerivationToDerivations\b|\bcyclicAlgebraDerivationToNCDerivation\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.5-5", 2, "F1.5", "PHASE-0", "BUCKET 1",
        "Zero-kernel faithfulness separation: DerivationLieLane K.act x = 0 -> x = 0",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/Algebra/DerivationLieLane.lean", "symbol": "DerivationLieLane"},
    ),
    # F1.6 (5)
    CheckSpec(
        "T2-F1.6-1", 2, "F1.6", "PHASE-0", "BUCKET 1",
        "Non-linear / non-alternating NOperatorForm 2 witness (fun _ _ x => x^2)",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/Optics/OperatorDerivationForms.lean", "symbol": "NOperatorForm"},
    ),
    CheckSpec(
        "T2-F1.6-2", 2, "F1.6", "M1", "BUCKET 1",
        "Degree n=0 (Subsingleton NOperatorForm 0 vs nontrivial OpForm 0 ~ A) & n=1 disambiguation",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Optics/OperatorDerivationForms.lean", "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean"],
            "required_patterns": [r"\bNOperatorForm\b", r"\bOpForm\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.6-3", 2, "F1.6", "M1", "BUCKET 1",
        "Antisymmetry vs tuple order at n=2: (a ^ b)(v, v) = 0 vs tuple (a, b)(v, v) != 0",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Optics/OperatorDerivationForms.lean", "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean"],
            "required_patterns": [r"\bopForm_two_diag_zero\b|\bAlternatingMap\b", r"\bnOperatorForm_two_linear_diag_nonzero_witness\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.6-4", 2, "F1.6", "M1", "BUCKET 1",
        "Noncommutative wedge failure of graded-commutativity on M_2(R)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean"],
            "required_patterns": [r"\bceWedge_one_one_apply\b|\bop2FormEquivOpForm_wedge\b", r"\bceWedge\b|\bopWedge\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.6-5", 2, "F1.6", "M1", "BUCKET 1",
        "High-degree n >= 3 alternating property verified on DerivationOperatorForm K 3",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bthreeFormToThreeCochain\b", r"\bthreeFormToThreeCochain_injective\b"],
            "co_occur": True,
        },
    ),
    # F1.7 (5)
    CheckSpec(
        "T2-F1.7-1", 2, "F1.7", "PHASE-0", "BUCKET 1",
        "Non-abelian curvature Gamma ^ Gamma != 0 when [X, Y] != 0 on M_2(R)",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean", "symbol": "connectionWedgeSquare"},
    ),
    CheckSpec(
        "T2-F1.7-2", 2, "F1.7", "M1", "BUCKET 1",
        "Abelian reduction under [CommRing A] & left-module (D+Gamma) vs adjoint (D+[Gamma,.]) covariant derivative",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean"],
            "required_patterns": [r"\bceCurvature_eq_exteriorDerivative_of_commRing\b", r"\bcovariantExteriorDerivativeN_eq_ceExteriorDerivative_of_commRing\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F1.7-3", 2, "F1.7", "PHASE-0", "BUCKET 1",
        "Gauge covariance of curvature: connectionCurvature_gaugeOneForm & covariantDerivative_gauge_equivariant",
        {"kind": "baseline_probe", "probe": "r1_baseline", "verify_file": "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean", "symbol": "covariantDerivative_gauge_equivariant"},
    ),
    CheckSpec(
        "T2-F1.7-4", 2, "F1.7", "M1", "BUCKET 1",
        "Higher-degree Bianchi d_Gamma F = 0 in DerivationOperatorForm K 3 & Chern-Simons cubic transgression",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
                "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean",
            ],
            "required_patterns": [r"\bceCurvature_bianchi\b|\bconnectionCurvature_bianchi\b", r"\bnoncommutativeChernSimonsTransgression\b|\bactionCurvature_bianchi\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T2-F1.7-5", 2, "F1.7", "M1", "BUCKET 1",
        "Cyclic cocycle Hochschild boundary b phi = 0 on noncommutative M_2(R)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean", "lean/InfoGeometry/Physics/ConnesCyclicCohomology.lean"],
            "required_patterns": [r"\bCyclicAlgebraDerivation\b|\bconnesCyclic\b", r"\bhochschild\b|\bcyclic\b"],
            "co_occur": True,
        },
    ),
    # F3.1 (5)
    CheckSpec(
        "T2-F3.1-1", 2, "F3.1", "M2", "BUCKET 1",
        "Stage n=0,1,2 equivalence Clsplit n (g)tensor A ~ ClTower A n",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean"],
            "required_patterns": [r"\bClsplit\b", r"\bClTower\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.1-2", 2, "F3.1", "PHASE-0", "BUCKET 1",
        "Unital diagEmbed 1 = 1 vs non-unital bottEmbed 1 != 1 on ClTower R 0",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean", "symbol": "bottEmbed"},
    ),
    CheckSpec(
        "T2-F3.1-3", 2, "F3.1", "M2", "BUCKET 1",
        "3-basis Cl(1,1) ~ M_2(R) sign/generator reconciliation without conflating Eplus and -Eplus",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedMorita.lean"],
            "required_patterns": [r"\bcl11EquivMat\b", r"\bcl11StandardEquiv\b", r"\bcl11MatrixAlgEquiv\b|\bthreeBasis_generator_table\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.1-4", 2, "F3.1", "M2", "BUCKET 1",
        "Noncommutative seed [Ring A] [Nontrivial A] (M_2(R)) transported across Clsplit n (g)tensor A ~ ClTower A n",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean"],
            "required_patterns": [r"\bmat2_noncomm_witness\b|\bNontrivial\b", r"\bClTower\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.1-5", 2, "F3.1", "PHASE-0", "BUCKET 1",
        "Obstruction & split-signature guardrails: gradedTensorSuccessor_not_algHom respected",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Canonical/SplitCliffordMatrixLimitSoldering.lean", "symbol": "gradedTensorSuccessor_not_algHom"},
    ),
    # F3.2 (5)
    CheckSpec(
        "T2-F3.2-1", 2, "F3.2", "M2", "BUCKET 1",
        "V_4 group laws (W1^2=1, W2^2=1, W1*W2=W12) & nontrivial action on CliffordAlgebra q11",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean", "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean"],
            "required_patterns": [r"\bV4\b|\bv4ToQ11IsometryHom\b", r"\bcl11V4_invariant_iff_scalar\b|\bv4ToQ11IsometryHom_W12\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.2-2", 2, "F3.2", "M2", "BUCKET 1",
        "Invariant subring noncommutativity at tower stages & SplitCliffordInfinity for [Nontrivial B]",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean",
                "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean",
                "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean",
            ],
            "required_patterns": [r"\berlangenDoubleCylinderInvariantSubring_noncommutative\b|\bdoubleCylinderColimitV4SymmetryAction\b|\bmat2_noncomm_witness\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.2-3", 2, "F3.2", "M2", "BUCKET 1",
        "Scalar-level fixed subalgebra of Cl(1,1) under full V_4 is center R * 1",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean", "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean"],
            "required_patterns": [r"\bcl11V4_invariant_iff_scalar\b|\bv4_invariant_cl11_iff_scalar\b", r"\bmat2V4_invariant_iff_scalar\b|\bisInvariant_cliffordSymmetryAction_iff_mem_range\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.2-4", 2, "F3.2", "M2", "BUCKET 1",
        "Stage-level V_4 action intertwines splitCliffordStep n : Clsplit n -> Clsplit (n+1)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean", "lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean"],
            "required_patterns": [r"\bdiagV4ClsplitAuto_bond\b|\bsplitCliffordStep\b", r"\bSymmetryAction\b|\bV4\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.2-5", 2, "F3.2", "PHASE-0", "BUCKET 1",
        "Central inversion readout: localCl11Switch_centralInversion preserves q11(-v) = q11(v)",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean", "symbol": "localCl11Map"},
    ),
    # F3.3 (5)
    CheckSpec(
        "T2-F3.3-1", 2, "F3.3", "PHASE-0", "BUCKET 1",
        "Empty chain (n=0: nativeChain 0 = 1) and zero-head chain (nativeChain 1 (cons 0) = 0)",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean", "symbol": "nativeChain"},
    ),
    CheckSpec(
        "T2-F3.3-2", 2, "F3.3", "M2", "BUCKET 1",
        "Suffix parity Koszul sign (-1)^{suffix_parity} on 2-site & 3-site nativeChain under transported d_native",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean", "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean"],
            "required_patterns": [r"\bnativeChainDifferential_nativeChain\b|\bsuffixParity\b", r"\bSplitCliffordInfinity\b|\bnativeChain\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.3-3", 2, "F3.3", "M2", "BUCKET 1",
        "Non-vacuous d_native != 0 witness on SplitCliffordInfinity mapping annihilation generator to 1",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean"],
            "required_patterns": [r"\bsplitJWDifferential_ne_zero\b|\bnativeChainDifferential_ne_zero\b", r"\bSplitCliffordInfinity\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.3-4", 2, "F3.3", "PHASE-0", "BUCKET 1",
        "Noncommutative terminal coefficient preservation (coefficientChain_matrix_suffixParity without CommRing B)",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean", "symbol": "coefficientChain_matrix_suffixParity"},
    ),
    CheckSpec(
        "T2-F3.3-5", 2, "F3.3", "M2", "BUCKET 1",
        "Transport respects gradedTensorSuccessor_not_algHom guardrail (uses canonicalCliffordUHFColimitEquiv / parity-twisted bond)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean", "lean/InfoGeometry/Canonical/SplitCliffordMatrixLimitSoldering.lean"],
            "required_patterns": [r"\bcanonicalCliffordUHFColimitEquiv\b", r"\bsplitJWDifferential_intertwines\b|\bgradedTensorSuccessor_not_algHom\b"],
            "co_occur": True,
        },
    ),
    # F3.4 (6)
    CheckSpec(
        "T2-F3.4-1", 2, "F3.4", "M2", "BUCKET 1",
        "Arbitrary [Module R M] without FiniteDimensional / finrank for equivOfIsometry commutation",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean"],
            "required_patterns": [r"\bcliffordSymmetryAction_equivariant_gradeProj\b|equivOfIsometry.*cliffordGradeProj|cliffordGradeProj.*equivOfIsometry"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.4-2", 2, "F3.4", "M2", "BUCKET 1",
        "Non-commuting CliffordAlgebra witness: iota e_0 * iota e_1 != iota e_1 * iota e_0 & grade-2 invariance",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean"],
            "required_patterns": [r"\bcl11_noncommutative_witness\b|CliffordAlgebra\.ι.*≠", r"\bcliffordGradeProj\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.4-3", 2, "F3.4", "M2", "BUCKET 1",
        "Degenerate Q = 0 (ExteriorAlgebra) corner case: equivOfIsometry reduces to ExteriorAlgebra.map",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean"],
            "required_patterns": [r"\bExteriorAlgebra\b|\bequivExterior\b", r"\bequivOfIsometry\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.4-4", 2, "F3.4", "M2", "BUCKET 1",
        "Parity reflection -id invariant subalgebra equals even subalgebra evenOdd Q 0",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean"],
            "required_patterns": [r"\bequivOfIsometry_neg_fixed_iff_mem_even\b|\bevenOdd\s+Q\s+0\b", r"\binvolute\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.4-5", 2, "F3.4", "M2", "BUCKET 2",
        "Grade k > finrank vanishes under explicit [Module.Finite R M] & top pseudoscalar det f law",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Clifford/GradedGraceContraction.lean"],
            "required_patterns": [r"\bequivOfIsometry_top_grade_eq_det_smul\b|\bcliffordGradeProj_eq_zero_of_gt_finrank\b", r"\bfinrank\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.4-6", 2, "F3.4", "PHASE-0", "BUCKET 1",
        "Cl(3,1) Krein indefiniteness guardrail: not_nonneg_cliffordKreinPairing_Q31 preserved",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Clifford/GradedGraceContraction.lean", "symbol": "not_nonneg_cliffordKreinPairing_Q31"},
    ),
    # F3.5 (5)
    CheckSpec(
        "T2-F3.5-1", 2, "F3.5", "M2", "BUCKET 1",
        "Non-vacuity of CliffordMobiusDeRhamMonodromy: zero (clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧ ... tautologies",
        {"kind": "monodromy_non_vacuous"},
    ),
    CheckSpec(
        "T2-F3.5-2", 2, "F3.5", "M2", "BUCKET 1",
        "Abstract CliffordAlgebra Q rotor Darboux theorem specializes via cl11EquivMat to M_2(R) hyperbolic rotor",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean"],
            "required_patterns": [r"\bcl11BoostBivector\b", r"\bCliffordAlgebra\.reverse\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.5-3", 2, "F3.5", "M2", "BUCKET 1",
        "Grade-2 bivector closure: reverse Omega = -Omega for Omega = (dR) * reverse R with R * reverse R = 1",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean"],
            "required_patterns": [r"\breverse\b.*=\s*-", r"\bCliffordAlgebra\.reverse\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.5-4", 2, "F3.5", "M2", "BUCKET 1",
        "Exterior-Clifford Dirac square / Chevalley coupling via equivExterior Q on FormHodgeCliffordData",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean", "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean"],
            "required_patterns": [r"\bFormHodgeCliffordData\b", r"\bequivExterior\b|\bcliffordGradeProj\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F3.5-5", 2, "F3.5", "PHASE-0", "BUCKET 1",
        "Noncommutative Clifford generator check: ZornDifferentialFormsCliffordBridge.clifford_noncomm_witness",
        {"kind": "baseline_probe", "probe": "r3_baseline", "verify_file": "lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean", "symbol": "clifford_noncomm_witness"},
    ),
    # F2.1 (5)
    CheckSpec(
        "T2-F2.1-1", 2, "F2.1", "M3", "BUCKET 1",
        "Non-vacuous Erlangen20Datum witness with non-commuting sl_2(R) on R^2",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean", "lean/InfoGeometry/Canonical/FelixKleinGeometryUnification.lean"],
            "required_patterns": [r"\bErlangen20Datum\b", r"Matrix\s*\(Fin\s*2\)|\*.*≠.*\*"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.1-2", 2, "F2.1", "M3", "BUCKET 1",
        "PhaseErlanger.MetricPreserving cleanly separated from KreinSpace.IsKreinIsometry",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Geometry/PhaseErlanger.lean", "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean"],
            "required_patterns": [r"\bMetricPreserving\b", r"\bIsKreinIsometry\b|\bkreinInner\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.1-3", 2, "F2.1", "PHASE-0", "BUCKET 2",
        "Smooth Cartan honest boundary: homothetyCartanGeometry_curvature_formula & conditional principal_atlas_action_transitive_unique",
        {"kind": "baseline_probe", "probe": "r2_r1r2_baseline", "verify_file": "lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean", "symbol": "homothetyCartanGeometry_curvature_formula"},
    ),
    CheckSpec(
        "T2-F2.1-4", 2, "F2.1", "PHASE-0", "BUCKET 3",
        "Klein A_5 honest boundary recorded (kleinVertexF_not_invariant_under_icosianGenA)",
        {"kind": "doc_symbol_exists", "file": "docs/ERLANGEN_2_THEOREM_HONEST_MANIFEST.md", "symbol": "kleinVertexF_not_invariant_under_icosianGenA"},
    ),
    CheckSpec(
        "T2-F2.1-5", 2, "F2.1", "PHASE-0", "BUCKET 1",
        "OperatorErlangenGaloisConnection remains a Galois connection (no false universal anti-equivalence)",
        {"kind": "file_symbol_exists", "file": "lean/InfoGeometry/Canonical/OperatorErlangenGaloisConnection.lean", "symbol": "subgroup_le_fixingSubgroup_iff"},
    ),
    # F2.2 (5)
    CheckSpec(
        "T2-F2.2-1", 2, "F2.2", "PHASE-0", "BUCKET 1",
        "shear != krein_isometry boundary: componentNReal_not_krein_isometry vs matrixAction_preserves_symplectic_iff",
        {"kind": "baseline_probe", "probe": "r2_r1r2_baseline", "verify_file": "lean/InfoGeometry/Krein/DoubleRealKreinShearDefect.lean", "symbol": "componentNReal_not_krein_isometry"},
    ),
    CheckSpec(
        "T2-F2.2-2", 2, "F2.2", "M3", "BUCKET 1",
        "Five doubled-space operators kept distinct (KreinSpace.jCLM != DoubledSpace.modular_j, spectral_epsilon, gradeCLM, cl11.{J,eps})",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Krein/DoubledSpace.lean", "lean/InfoGeometry/Krein/KreinSpace.lean"],
            "required_patterns": [r"\bmodular_j\b", r"\bspectral_epsilon\b", r"\bjCLM\s*≠\s*modular_j\b|\bmodular_j\s*≠"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.2-3", 2, "F2.2", "M3", "BUCKET 1",
        "Indefiniteness of Krein16Idx -> R (kreinMetric88): positive v_+ and negative v_- vectors",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean"],
            "required_patterns": [r"\bKrein16Idx\b", r"\bkreinInner\b.*<\s*0|0\s*<\s*\bkreinInner\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.2-4", 2, "F2.2", "M3", "BUCKET 2",
        "Krein adjoint transport proved via Hilbert-adjoint conjugation (not assumed as structure field)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Krein/KreinSpace.lean", "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean"],
            "required_patterns": [r"\bkreinAdjoint\b", r"\badjoint\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.2-5", 2, "F2.2", "M3", "BUCKET 1",
        "Stage n=0,1,2 Clsplit n Krein cycle in ClNNFredholmBridge (n=1 matches firstStep_*, n=2 non-commuting)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/ClNNFredholmBridge.lean"],
            "required_patterns": [r"\bClsplit\b", r"\bfirstStep_leftGenerator_eq_cl11Rep\b"],
            "co_occur": True,
        },
    ),
    # F2.3 (5)
    CheckSpec(
        "T2-F2.3-1", 2, "F2.3", "M3", "BUCKET 1",
        "Hilbert vs Krein RealStructure separation: RealStructureKreinCompatible distinguished from RealStructureMetricCompatible",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean"],
            "required_patterns": [r"\bRealStructureKreinCompatible\b", r"\bRealStructureMetricCompatible\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.3-2", 2, "F2.3", "M3", "BUCKET 2",
        "Non-zero F witness (F != 0, F^2 = 1, [F, pi(a)] != 0) contrasting with trivialKasparovCycle (F = 0)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/Examples.lean", "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean"],
            "required_patterns": [r"\bRealSplitKreinKasparovCycle\b", r"\.F\s*≠\s*0|F\s*\*\s*F\s*=\s*1"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.3-3", 2, "F2.3", "M3", "BUCKET 2",
        "Finite-dim CFC.sqrt (BUCKET 2) vs infinite-dim [CompleteSpace H] X.resolvent (BUCKET 3) boundary",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean"],
            "required_patterns": [r"\bCFC\.sqrt\b|\bFiniteDimensional\b", r"\bresolvent\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.3-4", 2, "F2.3", "M3", "BUCKET 3",
        "Right-B-module & Kasparov product BUCKET 3 honesty in KK/Product.lean & RealSplitKreinKasparovCycle",
        {"kind": "bucket3_honesty", "files": ["lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean", "lean/InfoGeometry/KK/Product.lean"]},
    ),
    CheckSpec(
        "T2-F2.3-5", 2, "F2.3", "PHASE-0", "BUCKET 2",
        "Cl55MasterKasparovDatum trivial algebraic index boundary (ker D_H = 0, index = 0 in Mat32)",
        {"kind": "doc_symbol_exists", "file": "docs/ERLANGEN_2_THEOREM_HONEST_MANIFEST.md", "symbol": "RealCl55KasparovCycleBridge"},
    ),
    # F2.4 (5)
    CheckSpec(
        "T2-F2.4-1", 2, "F2.4", "M3", "BUCKET 1",
        "Non-commuting Connes 1-form [D, pi(a)] != 0 on M_2(R) with Leibniz rule",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean"],
            "required_patterns": [r"\bncDeriv_leibniz\b|\bcommutator\b", r"Matrix\s*\(Fin\s*2\)|\*.*≠.*\*"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.4-2", 2, "F2.4", "M3", "BUCKET 1",
        "Equivariant chiral kernel slice preservation (chiralKernelSlicePlus / Minus) under EquivariantDatum -> Erlangen20Datum",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean", "lean/InfoGeometry/KK/ChiralFredholmSurface.lean"],
            "required_patterns": [r"\bchiralKernelSlice\w*", r"\bErlangen20Datum\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.4-3", 2, "F2.4", "M3", "BUCKET 1",
        "Onsager Krein-J reciprocity (HasJReciprocity) holds for Krein J and fails for parabolic shear componentNReal",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ErlangenOperator2.lean", "lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean", "lean/InfoGeometry/Krein/DoubleRealKreinShearDefect.lean"],
            "required_patterns": [r"\bHasJReciprocity\b", r"\bcomponentNReal\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.4-4", 2, "F2.4", "M3", "BUCKET 2",
        "Gauge-fluctuated D_A = D + A + J A J^-1: pure gauge u D u^-1 vs non-flat A defect shift",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Geometry/ConstructiveKasparov.lean", "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean"],
            "required_patterns": [r"\bD_A\b|fluctuat", r"1\s*-\s*F|F\s*\*\s*F\s*-\s*1"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.4-5", 2, "F2.4", "M3", "BUCKET 3",
        "Unbounded domain guardrail: (pi a) x in domain required explicitly for D_A on RealSplitKreinUnboundedCycle",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean"],
            "required_patterns": [r"\bdomain\b", r"\bRealSplitKreinUnboundedCycle\b"],
            "co_occur": True,
        },
    ),
    # F2.5 (5)
    CheckSpec(
        "T2-F2.5-1", 2, "F2.5", "M3", "BUCKET 1",
        "Klein 1872 Grassmann [6,7,8] citations (1844, 1862 p.278, 1852 Crelle 44) & Plucker decomposable vs non-decomposable bivector boundary",
        {"kind": "rubric_f25_grassmann_citations"},
    ),
    CheckSpec(
        "T2-F2.5-2", 2, "F2.5", "M3", "BUCKET 1",
        "Bridge B boundary: 4-variable Mobius lightcone (u_1^2+..+u_4^2) embeds strictly into 5-variable Lie sphere contact extension (u_1^2+..+u_5^2)",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/KleinErlangenSphereContactAndBinaryForms.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Erlangen/ErlangenProgramMobiusLieAndContact.lean",
            ],
            "required_patterns": [
                r"\bmoebiusQuadricBilin\b|\bcircleBilin\b|\blieToGrassmannCircleProj\b",
                r"\blieQuadricBilin\b|\blieBilin\b|\blieMobiusToCircleHom\b",
            ],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.5-3", 2, "F2.5", "M3", "BUCKET 1",
        "Bridge C boundary: Darboux rank & general linear complex (Note VI nonzero curvature) vs special linear complex (zero curvature / line axis)",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Erlangen/ErlangenProgramCurvatureBinaryAndMasterAtlas.lean",
                "lean/InfoGeometry/Canonical/GrassmannPfaffianSyzygyAndNormalForms.lean",
            ],
            "required_patterns": [
                r"\bfinrank_ker_complexForm_complexCongr\b|\bcomplexCongr_general_iff\b|\bpgk3_pfaffian_plucker_klein_contact_bridge\b",
                r"\bNondegenerate\b|\bkleinQ\b",
            ],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T2-F2.5-4", 2, "F2.5", "M3", "BUCKET 1",
        "Concurrent Grassmann*/Plucker*, GrassmannPluckerKleinFunctorialBridges & all 11 Erlangen/Grassmann/Plucker .olean compilation, axiom_check & OpenGauss boundary",
        {"kind": "f25_all_oleans_compiled", "targets": list(F2_5_BASELINE_ALL) + list(F2_5_ERLANGEN_PROGRAM_MODULES) + list(F2_5_SYNTHESIS_AND_BRIDGE_MODULES)},
    ),
    CheckSpec(
        "T2-F2.5-5", 2, "F2.5", "PHASE-0", "BUCKET 1",
        "Phase-0 Grassmann 1862 epistemic compilation doc & KleinQuadric/GrassmannAusdehnungslehre/Darboux .olean hygiene boundary",
        {"kind": "f25_grassmann_1862_baseline"},
    ),
    # F4.1 (5)
    CheckSpec(
        "T2-F4.1-1", 2, "F4.1", "M3", "BUCKET 1",
        "Doc-vs-code symbol fidelity: 100% of backtick-quoted Lean paths & symbols in M1/M2/M3 spec docs exist in lean/InfoGeometry/",
        {"kind": "rubric_doc_symbol_fidelity"},
    ),
    CheckSpec(
        "T2-F4.1-2", 2, "F4.1", "M3", "BUCKET 3",
        "Bucket-overclaim anti-smuggling check across all spec docs & reconciled Lean owners",
        {"kind": "rubric_no_bucket3_overclaims"},
    ),
    CheckSpec(
        "T2-F4.1-3", 2, "F4.1", "M3", "BUCKET 1",
        "No redundant *Bridge.lean sprawl or duplicate TransportTensor/TimeReversal/Clifford/Krein wrappers",
        {"kind": "onsager_no_duplicates"},
    ),
    CheckSpec(
        "T2-F4.1-4", 2, "F4.1", "PHASE-0", "BUCKET 1",
        "Unrelated dirty-worktree preservation & baseline test_default_lean_sources.py clean",
        {"kind": "default_lean_sources_clean"},
    ),
    CheckSpec(
        "T2-F4.1-5", 2, "F4.1", "M3", "BUCKET 1",
        "Dual-lane Lake target check: lakefile.lean & src/InfoGeometry/ resolve M1-M3 reconciled modules",
        {"kind": "dual_lake_targets"},
    ),
)


# ---------------------------------------------------------------------------
# Tier 3: Cross-Feature Pairwise Combination Checks (23 checks)
# ---------------------------------------------------------------------------

TIER3_CHECKS: tuple[CheckSpec, ...] = (
    CheckSpec(
        "T3-01", 3, "F1.1,F1.6,F2.3,F2.4", "M3", "BUCKET 2",
        "DerivationOperatorForm / CEOneForm / NOperatorForm <-> Connes [D, pi(a)] & compactness vs X.resolvent",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean", "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean"],
            "discover_keywords": ("ConnesNCG", "RealSplitKreinUnboundedCycle", "SpectralTriple"),
            "required_patterns": [r"\bDerivationOperatorForm\b|\bOneForms\b", r"\bRealSplitKreinUnboundedCycle\b|\bPhaseRealSpectralTriple\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-02", 3, "F1.3,F2.1,F2.2,F2.4", "M3", "BUCKET 1",
        "OnsagerCasimirSystem / Op1Form -> ErlangenOperatorDatum (HasJReciprocity with Krein J vs shear) & kreinToDual",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean", "lean/InfoGeometry/Canonical/ErlangenOperator2.lean"],
            "discover_keywords": ("ErlangenOperator2", "Onsager"),
            "required_patterns": [r"\bOnsagerCasimirSystem\b", r"\bHasJReciprocity\b", r"\bkreinToDual\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-03", 3, "F3.1,F3.2,F2.2,F2.3", "M3", "BUCKET 2",
        "Cl(1,1) / Clsplit n -> RealSplitKreinKasparovCycle (ClNNFredholmBridge extension keeping 5 doubled operators distinct)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/ClNNFredholmBridge.lean"],
            "discover_keywords": ("ClNNFredholm",),
            "required_patterns": [r"\bClsplit\b", r"\bRealSplitKreinKasparovCycle\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-04", 3, "F1.1,F1.7,F3.4,F3.5", "M2", "BUCKET 1",
        "ZornDifferentialFormsCliffordBridge (FormHodgeCliffordData) <-> cliffordGradeProj / equivExterior (Chevalley action)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean", "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean"],
            "required_patterns": [r"\bFormHodgeCliffordData\b", r"\bcliffordGradeProj\b|\bequivExterior\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-05", 3, "F3.4,F2.1,F2.2", "M3", "BUCKET 1",
        "CliffordAlgebra.equivOfIsometry <-> SymmetryAction <-> Erlangen20Datum (cliffordGradeProj & hTrace_cl as IsInvariantReadout)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean"],
            "discover_keywords": ("CoordinateLessClifford", "Erlangen20"),
            "required_patterns": [r"\bequivOfIsometry\b", r"\bErlangen20Datum\b", r"\bIsInvariantReadout\b|\bInvariantReadout\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-06", 3, "F3.1", "M2", "BUCKET 1",
        "ClTower A n <-> Clsplit n (g)tensor A via iterated tensorMatrixEquiv; diagEmbed vs non-unital bottEmbed on M_2(R)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean", "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean", "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean"],
            "required_patterns": [r"\bClTower\b", r"\bClsplit\b", r"\bdiagEmbed\b|\bbottEmbed\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-07", 3, "F3.3,F3.1,F1.1", "M2", "BUCKET 1",
        "jwDifferential / jwHomotopy transported onto nativeChain / SplitCliffordInfinity (d^2=0, dh+hd=1, suffixParity)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean", "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean"],
            "required_patterns": [r"\bjwDifferential\b", r"\bnativeChain\b", r"\bSplitCliffordInfinity\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-08", 3, "F1.2,F1.7,F2.3,F2.4", "M3", "BUCKET 2",
        "R1 MC curvature / gauge fluctuation D_A = D + A + J A J^-1 <-> ConstructiveKasparovDatum.defect (1 - F^2)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Geometry/ConstructiveKasparov.lean", "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean"],
            "discover_keywords": ("ConstructiveKasparov", "KasparovGauge"),
            "required_patterns": [r"\bConstructiveKasparovDatum\b", r"\bconnectionCurvature\b|\bMaurerCartan\b|fluctuat"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-09", 3, "F1.2,F1.7,F3.5", "M2", "BUCKET 1",
        "Abstract CliffordAlgebra Q Darboux MC Omega = (dR) * reverse R <-> R1 MC tower & M_2(R) specialization",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean"],
            "required_patterns": [r"\bCliffordAlgebra\.reverse\b", r"\bcl11EquivMat\b|\bgaugeForm\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-10", 3, "F1.1,F1.4,F1.5", "M1", "BUCKET 1",
        "OperatorFrechetForm d_Fr <-> CE d_n on FrechetOperatorDerivation <-> extDeriv (DeRhamBridge)",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
                "lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean",
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
            ],
            "required_patterns": [r"\bOperatorFrechetForm\b", r"\bFrechetOperatorDerivation\b", r"\bextDeriv\b|\bceExteriorDerivative\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-11", 3, "F1.1,F1.5,F1.2", "M1", "BUCKET 1",
        "Non-faithful LieActionLane (ad : M_2(R) -> End(M_2(R))) -> DerivationOperatorForm -> MC flatness",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean", "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean"],
            "required_patterns": [r"\bLieActionLane\b", r"\bactionThetaL_flat\b|\bthetaL_flat\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-12", 3, "F1.3,F1.4,F1.6", "PHASE-0", "BUCKET 2",
        "CEBKMOnsagerGibbsNOperatorFamily <-> OperatorFrechetJet (Phase 0) & general DerivationOperatorForm Onsager pairing (M1)",
        {
            "kind": "dual_mode_probe",
            "phase0_probe": "r1_baseline",
            "full_gate": "M1",
            "candidate_files": ["lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean", "lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean"],
            "required_patterns": [r"\bOnsagerCasimirSystem\b", r"\bDerivationOperatorForm\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-13", 3, "F2.1,F2.3,F2.4", "M3", "BUCKET 1",
        "EquivariantDatum X <-> Erlangen20Datum <-> SymmetryAction (chiral kernel slices & analyticalIndex invariant)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean", "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean"],
            "discover_keywords": ("EquivarianceBridge", "EquivariantErlangen"),
            "required_patterns": [r"\bEquivariantDatum\b", r"\bErlangen20Datum\b", r"\banalyticalIndex\b|\bchiralKernelSlice\w*"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-14", 3, "F2.2,F2.3", "M3", "BUCKET 2",
        "PhaseRealSpectralTriple (RealStructureKreinCompatible) <-> RealSplitKreinUnboundedCycle <-> RealSplitKreinKasparovCycle",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean", "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean", "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean"],
            "discover_keywords": ("SpectralTriple", "RealSplitKrein"),
            "required_patterns": [r"\bRealStructureKreinCompatible\b", r"\bRealSplitKreinUnboundedCycle\b", r"\bRealSplitKreinKasparovCycle\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-15", 3, "F2.1,F2.2,F3.2", "M3", "BUCKET 1",
        "CantorDoubleCylinderColimitAlgebra (G_swap, H_lp, J_lp_clm, chiral anomaly = 0) <-> V_4 / SplitCliffordInfinity",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Canonical/CantorDoubleCylinderColimitAlgebra.lean", "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean"],
            "required_patterns": [r"\bcantorDoubleCylinder\w*", r"\bSplitCliffordInfinity\b|\bV4\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-16", 3, "F2.2,F2.1,F2.4", "M3", "BUCKET 1",
        "Krein16Idx -> R (Cl(4,4) kreinMetric88, gamma44) KreinSpace/KreinGradedModule <-> g2LieSubalgebra Erlangen20Datum",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean"],
            "required_patterns": [r"\bKrein16Idx\b", r"\bKreinSpace\b", r"\bg2LieSubalgebra\b|\bErlangen20Datum\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-17", 3, "F1.2,F2.1", "M3", "BUCKET 2",
        "R1 MaurerCartanTower <-> SmoothCartanGeometry (gl2R_maurerCartan_flat vs homothetyCartanGeometry kappa)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean", "lean/InfoGeometry/Canonical/SmoothPrincipalCartanBundleClosure.lean", "lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean"],
            "required_patterns": [r"\bSmoothCartanGeometry\b|\bhomothetyCartanGeometry\b", r"\bMaurerCartanTower\b|\bthetaL\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-18", 3, "F1.7,F2.2", "PHASE-0", "BUCKET 1",
        "ClTower B n peirce11 MC curvature & RingDeriv Berry-Chern <-> StarOrderedRing Krein positivity (KreinPeirceTowerIntertwine)",
        {
            "kind": "dual_mode_probe",
            "phase0_probe": "r2_r1r2_baseline",
            "full_gate": "M3",
            "candidate_files": ["lean/InfoGeometry/Algebra/KreinPeirceTowerIntertwine.lean", "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean"],
            "required_patterns": [r"\bpeirce11_positive_sector_krein_positivity_and_bianchi\b", r"\bClsplit\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-19", 3, "F1.1,F3.2,F3.4", "M3", "BUCKET 1",
        "CliffordAlgebra.equivOfIsometry naturality on universal 1-forms OneForms (CliffordAlgebra Q)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean", "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean"],
            "discover_keywords": ("CliffordOneForms", "CoordinateLessClifford"),
            "required_patterns": [r"\bequivOfIsometry\b", r"\bOneForms\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-20", 3, "F1.1,F1.2,F2.1,F2.2,F2.3,F3.1,F3.4", "M3", "BUCKET 2",
        "Full 3-pillar triangle on DoubledSpace R (Cl(1,1) -> Krein -> RealSplitKreinKasparovCycle F!=0 -> Erlangen20Datum -> Omega^1_D & MC fluctuation)",
        {
            "kind": "contract_probe",
            "candidate_files": ["lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean", "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean"],
            "discover_keywords": ("ThreePillar", "MasterReconciliation"),
            "required_patterns": [r"\bRealSplitKreinKasparovCycle\b", r"\bErlangen20Datum\b", r"\bDoubledSpace\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-21", 3, "F2.1,F2.5,F3.4", "M3", "BUCKET 1",
        "Bridge A (R2 <-> R3): Grassmann exterior/regressive products <-> Plucker ray coordinates & Klein quadric coordinated with SymmetryAction / Erlangen20Datum",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Projective/KleinQuadricPlucker.lean",
            ],
            "discover_keywords": ("GrassmannPluckerKlein", "PluckerGrassmannKlein"),
            "required_patterns": [r"\bKleinQuadric\b|\bPlucker6\b|\bpluckerToExterior2\b", r"\bSymmetryAction\b|\bErlangen20Datum\b|\bequivOfIsometry\b"],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-22", 3, "F2.1,F2.5", "M3", "BUCKET 1",
        "Bridge B (R2 <-> R2): Grassmann syncyclic circle space <-> Klein §§6-7 Mobius lightcone (u_1^2+..+u_4^2) & Lie sphere Korper (u_1^2+..+u_5^2)",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Erlangen/ErlangenProgramMobiusLieAndContact.lean",
            ],
            "required_patterns": [
                r"\bIsSyncyclic4\b|\bsyncyclic\b",
                r"\bIsLieMobius\b|\blieMobiusToCircleHom\b|\blieQuadricBilin\b|\bmoebiusQuadricBilin\b",
            ],
            "co_occur": True,
        },
    ),
    CheckSpec(
        "T3-23", 3, "F1.1,F1.2,F2.1,F2.5", "M3", "BUCKET 1",
        "Bridge C (R1 <-> R2): Grassmann Pfaffian normal forms & Darboux rank <-> Plucker linear/special complexes, Kummer surfaces, Note VI & §9 contact 1-forms",
        {
            "kind": "contract_probe",
            "candidate_files": [
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
                "lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean",
                "lean/InfoGeometry/Erlangen/ErlangenProgramCurvatureBinaryAndMasterAtlas.lean",
            ],
            "required_patterns": [
                r"\bcomplexForm\b|\bpfaffJet\w*|\bDarboux\b",
                r"\bcomplexCongr\b|\bPlucker6\b|\bkummerSingularQuartic\b",
                r"\bcontactOneForm\b|\blegendreContact\b",
            ],
            "co_occur": True,
        },
    ),
)


# ---------------------------------------------------------------------------
# Tier 4: Real-World / End-to-End Acceptance Scenarios (11 scenarios)
# ---------------------------------------------------------------------------

TIER4_CHECKS: tuple[CheckSpec, ...] = (
    CheckSpec(
        "T4-01", 4, "F1.1-F4.1", "M3", "BUCKET 1",
        "Item-by-item ORIGINAL_REQUEST.md rubric audit (verified Lean owners + hypotheses + BUCKET 1/2/3 + zero contradiction)",
        {"kind": "full_rubric_audit"},
    ),
    CheckSpec(
        "T4-02", 4, "F1.1,F1.2,F1.3,F1.4,F1.5,F1.6,F1.7", "M1", "BUCKET 1",
        "M1 E2E Noncommutative Gauge (M_2(R) curvature, Bianchi, MC sign dictionary), Frechet d_Fr & Onsager workflow",
        {
            "kind": "e2e_scenario",
            "scenario": "m1_nc_gauge_frechet_onsager",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/DerivationExteriorCalculus.lean",
                "lean/InfoGeometry/OperatorAlgebra/MaurerCartanTower.lean",
                "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
                "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
            ],
            "required_patterns": [r"\bDerivationOperatorForm\b", r"\bMaurerCartanTower\b", r"\bOnsagerCasimirSystem\b", r"\bfrechetExteriorDeriv\b|\bfrechetExtDeriv\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T4-03", 4, "F3.1,F3.2,F3.3,F3.4", "M2", "BUCKET 1",
        "M2 E2E Coordinate-Less Clifford (equivOfIsometry, cliffordGradeProj, O(Q) invariants) & Cl(1,1) tower + jwDifferential on nativeChain",
        {
            "kind": "e2e_scenario",
            "scenario": "m2_coordless_clifford_tower",
            "candidate_files": [
                "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean",
                "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean",
                "lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean",
                "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean",
            ],
            "required_patterns": [r"\bcliffordSymmetryAction\b", r"\bcliffordGradeProj\b", r"\bClTower\b", r"\bClsplit\b", r"\bsplitJWDifferential\b", r"\bnativeChainDifferential\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T4-04", 4, "F1.2,F3.4,F3.5", "M2", "BUCKET 1",
        "M2/M1 E2E Rotor Spin-Connection (CliffordAlgebra Q reverse Darboux MC) & Hodge-Dirac (FormHodgeCliffordData <-> equivExterior)",
        {
            "kind": "e2e_scenario",
            "scenario": "m2_rotor_hodge_coupling",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean",
                "lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean",
                "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean",
            ],
            "required_patterns": [r"\bFormHodgeCliffordData\b", r"\bequivExterior\b|\bcliffordGradeProj\b", r"\bCliffordAlgebra\.reverse\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T4-05", 4, "F2.1,F2.2,F2.3,F2.4", "M3", "BUCKET 2",
        "M3 E2E Double-Real Krein (DoubledSpace R vs shear) -> PhaseRealSpectralTriple -> RealSplitKreinKasparovCycle (F!=0) -> EquivariantDatum -> Erlangen20Datum",
        {
            "kind": "e2e_scenario",
            "scenario": "m3_krein_kasparov_erlangen_pipeline",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
                "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean",
                "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
                "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
                "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
            ],
            "required_patterns": [r"\bRealStructureKreinCompatible\b", r"\bRealSplitKreinUnboundedCycle\b", r"\bRealSplitKreinKasparovCycle\b", r"\bEquivariantDatum\b", r"\bErlangen20Datum\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T4-06", 4, "F2.1,F2.2,F3.2,F2.4", "M3", "BUCKET 1",
        "M3 E2E Cantor Double-Cylinder Cl(1,1) Erlangen-Krein-NCG Synthesis (DoubleCylinderColimit, H_lp, chiral anomaly = 0, SplitCliffordInfinity V_4)",
        {
            "kind": "e2e_scenario",
            "scenario": "m3_cantor_double_cylinder",
            "candidate_files": [
                "lean/InfoGeometry/Canonical/CantorDoubleCylinderColimitAlgebra.lean",
                "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean",
                "lean/InfoGeometry/Canonical/SplitCliffordTowerUnification.lean",
            ],
            "required_patterns": [r"\bcantorDoubleCylinderErlangen20Datum\b", r"\berlangenDoubleCylinderInvariantSubring_noncommutative\b"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T4-07", 4, "F1.1,F1.2,F1.7,F2.3,F2.4", "M3", "BUCKET 2",
        "M3 E2E Noncommutative Gauge Fluctuation (Omega^1_univ -> Omega^1_D(A), D_A = D + A + J A J^-1, pure gauge vs curved 1 - F^2 defect)",
        {
            "kind": "e2e_scenario",
            "scenario": "m3_nc_gauge_fluctuation",
            "candidate_files": [
                "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean",
                "lean/InfoGeometry/Geometry/ConstructiveKasparov.lean",
                "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
                "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
            ],
            "required_patterns": [r"\bOneForms\b", r"\bConstructiveKasparovDatum\b|\bRealSplitKreinKasparovCycle\b", r"\bD_A\b|fluctuat"],
            "co_occur": False,
        },
    ),
    CheckSpec(
        "T4-08", 4, "F4.1,F4.2", "PHASE-0", "BUCKET 1",
        "Dual-mode regression & build-lock certification (baseline probes + test_default_lean_sources.py in baseline; full M4 build-lock certification in full)",
        {"kind": "dual_mode_certification"},
    ),
    CheckSpec(
        "T4-09", 4, "F4.1,F4.2", "M3", "BUCKET 1",
        "Full hygiene, axiom, vacuity, native_decide & byte-0 Apache header gate across complete M1-M3 closure",
        {"kind": "m1_m2_m3_strict_quality"},
    ),
    CheckSpec(
        "T4-10", 4, "F4.1,F4.2", "M3", "BUCKET 3",
        "Epistemic honesty & BUCKET 1/2/3 non-overclaim audit across docs/ and reconciled Lean docstrings",
        {"kind": "rubric_no_bucket3_overclaims"},
    ),
    CheckSpec(
        "T4-11", 4, "F2.1,F2.5,F4.1", "M3", "BUCKET 1",
        "End-to-End Klein 1872 - Grassmann [6,7,8] - Plucker Bridges A, B, C, GrassmannPluckerKleinFunctorialBridges & 11 Erlangen/Grassmann/Plucker modules workflow",
        {
            "kind": "e2e_scenario",
            "scenario": "m3_klein_grassmann_plucker_bridges",
            "required_files": [
                "lean/InfoGeometry/Erlangen/ErlangenProgramCurvatureBinaryAndMasterAtlas.lean",
                "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinFunctorialBridges.lean",
            ],
            "candidate_files": list(F2_5_ERLANGEN_PROGRAM_MODULES) + list(F2_5_SYNTHESIS_AND_BRIDGE_MODULES) + list(F2_5_BASELINE_ALL),
            "discover_keywords": ("GrassmannPluckerKlein", "PluckerGrassmannKlein", "ErlangenProgram", "KleinErlangen"),
            "required_patterns": [
                r"\bKleinQuadric\b|\bPlucker6\b",
                r"\bGrassmann\b|\bPfaffian\b|\bDarboux\b",
                r"\bIsSyncyclic4\b|\bmoebiusQuadricBilin\b",
                r"\bklein_erlangen_1872_master_synthesis\b",
                r"\bgrassmann_plucker_klein_trilogy_synthesis\b",
                r"\blieMobiusToCircleHom\b",
                r"\bfinrank_ker_complexForm_complexCongr\b",
                r"\bErlangen20Datum\b|\bSymmetryAction\b|\bequivOfIsometry\b|\bDerivationOperatorForm\b|\bOneForms\b",
            ],
            "co_occur": False,
        },
    ),
)


CHECKS: tuple[CheckSpec, ...] = TIER1_CHECKS + TIER2_CHECKS + TIER3_CHECKS + TIER4_CHECKS


def checks_by_id() -> dict[str, CheckSpec]:
    return {c.check_id: c for c in CHECKS}


def is_active_for_mode(check: CheckSpec, mode: str) -> bool:
    if mode == "baseline":
        return check.gate == "PHASE-0"
    if mode == "m1":
        return check.gate in ("PHASE-0", "M1")
    if mode == "m2":
        return check.gate in ("PHASE-0", "M2")
    if mode == "m3":
        return check.gate in ("PHASE-0", "M3")
    if mode == "full":
        return True
    raise ValueError(f"Unsupported E2E mode: {mode!r}")


def get_summary_counts() -> dict[str, int]:
    t1 = sum(1 for c in CHECKS if c.tier == 1)
    t2 = sum(1 for c in CHECKS if c.tier == 2)
    t3 = sum(1 for c in CHECKS if c.tier == 3)
    t4 = sum(1 for c in CHECKS if c.tier == 4)
    return {
        "tier1": t1,
        "tier2": t2,
        "tier3": t3,
        "tier4": t4,
        "total": len(CHECKS),
        "phase0": sum(1 for c in CHECKS if c.gate == "PHASE-0"),
        "m1": sum(1 for c in CHECKS if c.gate == "M1"),
        "m2": sum(1 for c in CHECKS if c.gate == "M2"),
        "m3": sum(1 for c in CHECKS if c.gate == "M3"),
    }
