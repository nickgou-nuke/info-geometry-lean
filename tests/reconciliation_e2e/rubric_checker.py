"""Item-by-item ORIGINAL_REQUEST.md rubric and BUCKET 1/2/3 honesty checker."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from tests.reconciliation_e2e import REPO_ROOT
from tests.reconciliation_e2e.lean_probes import (
    _LEAN_IDENT_SEG,
    _LEAN_NAME,
    parse_declarations_from_text,
)
from tools.infra.opengauss_screener import _strip_lean_comments_and_strings


@dataclass(frozen=True)
class RubricItem:
    item_id: str
    pillar: str
    concept: str
    bucket_scope: str
    baseline_owners: tuple[str, ...]
    baseline_symbols: tuple[str, ...]
    milestone: str
    milestone_requirements: tuple[str, ...]


RUBRIC_ITEMS: tuple[RubricItem, ...] = (
    RubricItem(
        item_id="R1-forms",
        pillar="R1",
        concept="Differential forms (arbitrary-degree CE d_n, graded wedge, universal Omega^1, de Rham)",
        bucket_scope="BUCKET 1 (algebraic DGA & Omega^1); BUCKET 2 (smooth deRhamComplex)",
        baseline_owners=(
            "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
            "lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean",
            "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
        ),
        baseline_symbols=(
            "DerivationOperatorForm",
            "oneFormAlternatingEquiv",
            "exteriorDerivativeZero",
            "exteriorDerivativeOne",
            "exteriorDerivativeTwo",
            "OneForms",
            "differential_mul",
            "oneForms_addHom_ext",
            "OpForm",
        ),
        milestone="M1",
        milestone_requirements=(
            "TwoForm linear equivalence with DerivationOperatorForm K 2",
            "arbitrary-degree differential d_n with d_{n+1} o d_n = 0",
            "associative graded wedge with graded Leibniz rule",
            "universal OneForms -> DerivationOperatorForm K 1 factorization",
        ),
    ),
    RubricItem(
        item_id="R1-mc-tower",
        pillar="R1",
        concept="Maurer-Cartan tower and left/right logarithmic sign dictionary",
        bucket_scope="BUCKET 1 (algebraic MC & finite/DirectLimit stages); BUCKET 2 (analytic limit)",
        baseline_owners=(
            "lean/InfoGeometry/OperatorAlgebra/MaurerCartanFrameTransport.lean",
            "lean/InfoGeometry/OperatorAlgebra/DerivationRightLogarithmicForm.lean",
            "lean/InfoGeometry/OperatorAlgebra/DerivationGaugeTransport.lean",
            "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean",
        ),
        baseline_symbols=(
            "gaugeForm",
            "gaugeForm_product",
            "gaugeForm_flat",
            "rightLogarithmicOneForm",
            "gaugeOneForm_zero_eq_neg_rightLogarithmicOneForm",
            "rightLogarithmicOneForm_maurerCartan",
            "pureGaugeForm_eq_neg",
            "maurer_cartan_flatness",
        ),
        milestone="M1",
        milestone_requirements=(
            "canonical theta_L = -g^{-1} theta_R g sign dictionary",
            "MaurerCartanTower stage transitions preserving flatness",
        ),
    ),
    RubricItem(
        item_id="R1-onsager",
        pillar="R1",
        concept="Onsager operator theory and generalized Onsager-Casimir 1-form reciprocity",
        bucket_scope="BUCKET 1/2 (general OnsagerCasimirSystem); BUCKET 2 (FiniteOperatorAlgebra BKM)",
        baseline_owners=(
            "lean/InfoGeometry/Thermo/OnsagerOperatorClosure.lean",
            "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
            "lean/InfoGeometry/Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean",
            "lean/InfoGeometry/Synthesis/OnsagerOperatorDifferentialCalculus.lean",
        ),
        baseline_symbols=(
            "OnsagerCasimirSystem",
            "ParityOnsagerSystem",
            "onsager_casimir_1Form_master_reciprocity",
            "reversible1Form_diag_zero",
            "totalGenerator1Form_nonneg",
            "finiteGibbsCEFamilyNOperatorForm",
            "finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian",
        ),
        milestone="M1",
        milestone_requirements=(
            "single canonical TransportTensor and TimeReversal (no duplicate defs)",
            "general OnsagerCasimirSystem pairing with DerivationOperatorForm / OpForm",
        ),
    ),
    RubricItem(
        item_id="R1-frechet",
        pillar="R1",
        concept="Frechet derivations and Frechet n-forms (d_Fr matching CE d_n and extDeriv)",
        bucket_scope="BUCKET 1 (linear jet & ContDiff identities); BUCKET 2 (finite Gibbs BKM)",
        baseline_owners=(
            "lean/InfoGeometry/Optics/OperatorDerivationForms.lean",
            "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
            "lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean",
            "lean/InfoGeometry/Canonical/FrechetCECovariantConnection.lean",
        ),
        baseline_symbols=(
            "FrechetOperatorDerivation",
            "OperatorFrechetJet",
            "OperatorFrechetForm",
            "ExchangeInvolution",
            "operatorFrechetJet_one_apply_eq_exteriorDerivativeZero",
            "covariantFrechet_eq_ce",
        ),
        milestone="M1",
        milestone_requirements=(
            "Frechet exterior derivative d_Fr on OperatorFrechetForm",
            "d_Fr^2 = 0 under explicit ContDiff 2 hypothesis",
            "d_Fr agreement with CE d_n and Mathlib extDeriv",
        ),
    ),
    RubricItem(
        item_id="R1-leibniz",
        pillar="R1",
        concept="Leibniz derivations unification without forced faithfulness",
        bucket_scope="BUCKET 1 (algebraic adapter spine)",
        baseline_owners=(
            "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
            "lean/InfoGeometry/Algebra/NonAssocDerivation.lean",
            "lean/InfoGeometry/Geometry/AssociativeGaugeConnection.lean",
        ),
        baseline_symbols=(
            "LieActionLane",
            "DerivationLieLane",
            "NonAssocDerivation",
            "IsLeibniz",
        ),
        milestone="M1",
        milestone_requirements=(
            "adapters from derivation wrappers into LieActionLane / FormDerivation",
            "non-faithful inner/adjoint LieSystem adapted without Function.Injective",
        ),
    ),
    RubricItem(
        item_id="R1-n-op-forms",
        pillar="R1",
        concept="n-operator-forms disambiguation (OneFormTuple vs alternating OpForm / DerivationOperatorForm)",
        bucket_scope="BUCKET 1 (type-level disambiguation and alternating calculus)",
        baseline_owners=(
            "lean/InfoGeometry/Optics/OperatorDerivationForms.lean",
            "lean/InfoGeometry/Canonical/CEOneFormNOperatorBridge.lean",
            "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
        ),
        baseline_symbols=(
            "NOperatorForm",
            "ofCEFamily",
            "component",
            "OpForm",
        ),
        milestone="M1",
        milestone_requirements=(
            "explicit OneFormTuple vs AlternatingOperatorForm disambiguation",
            "antisymmetrization / wedge embedding into alternating n-forms",
        ),
    ),
    RubricItem(
        item_id="R1-nc-diff-geom",
        pillar="R1",
        concept="NC operator ring differential geometry (covariant derivative, curvature, Bianchi, gauge equivariance, cyclic)",
        bucket_scope="BUCKET 1 (algebraic noncommutative gauge & cyclic geometry)",
        baseline_owners=(
            "lean/InfoGeometry/OperatorAlgebra/DerivationDifferentialForms.lean",
            "lean/InfoGeometry/OperatorAlgebra/DerivationGaugeTransport.lean",
            "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean",
            "lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean",
        ),
        baseline_symbols=(
            "connectionCurvature",
            "covariantDerivative",
            "connectionCurvature_bianchi",
            "fundamentalCovariantDerivative_gauge_intertwine",
            "covariantDerivative_gauge_equivariant",
            "noncommutativeChernSimonsTransgression",
        ),
        milestone="M1",
        milestone_requirements=(
            "arbitrary-degree covariant derivative & Bianchi identity",
            "NCG vs DerivationDifferentialForms gauge/curvature reconciliation",
        ),
    ),
    RubricItem(
        item_id="R3-cl11-towers",
        pillar="R3",
        concept="Cl(1,1)-tensored graded towers unification (ClTower / ClInf <-> Clsplit n gtensor A / SplitCliffordInfinity)",
        bucket_scope="BUCKET 1 (AlgEquiv & DirectLimit colimit maps; split signature only, NOT 8-fold Bott)",
        baseline_owners=(
            "lean/InfoGeometry/Clifford/Cl11Matrix.lean",
            "lean/InfoGeometry/Clifford/Cl11GradedMorita.lean",
            "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean",
            "lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean",
            "lean/InfoGeometry/Algebra/NoncommutativeCliffordColimitMassGapSynthesis.lean",
        ),
        baseline_symbols=(
            "cl11EquivMat",
            "cl11StandardEquiv",
            "tensorMatrixEquiv",
            "ClTower",
            "diagEmbed",
            "bottEmbed",
            "ClInf",
        ),
        milestone="M2",
        milestone_requirements=(
            "inductive equivalence Clsplit n (g)tensor A ~ ClTower A n",
            "reconciliation of diagEmbed vs bottEmbed and 3 Cl(1,1) ~ M_2(R) bases",
        ),
    ),
    RubricItem(
        item_id="R3-cl11-atom-sym",
        pillar="R3",
        concept="Cl(1,1) atom symmetry of operator algebra geometry (V4 & splitReflection -> SymmetryAction)",
        bucket_scope="BUCKET 1 (exact group actions and noncommutative fixed subrings)",
        baseline_owners=(
            "lean/InfoGeometry/Canonical/Cl11KleinFourAdjointRepresentation.lean",
            "lean/InfoGeometry/Clifford/Cl11CliffordMapIsometryBridge.lean",
            "lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean",
            "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean",
        ),
        baseline_symbols=(
            "localCl11Map",
            "cl11EquivMat_splitReflectionCliffordAuto",
            "SymmetryAction",
            "erlangenDoubleCylinderSymmetryAction",
            "erlangenDoubleCylinderInvariantSubring_noncommutative",
        ),
        milestone="M2",
        milestone_requirements=(
            "SymmetryAction V4 on CliffordAlgebra q11, Clsplit n, and SplitCliffordInfinity",
            "compatibility with erlangenDoubleCylinderSymmetryAction",
        ),
    ),
    RubricItem(
        item_id="R3-graded-chains",
        pillar="R3",
        concept="Graded tensor chains and differentials (jwDifferential / jwHomotopy on nativeChain / SplitCliffordInfinity)",
        bucket_scope="BUCKET 1 (algebraic direct-limit endomorphisms; no Hilbert norm/gap overclaim)",
        baseline_owners=(
            "lean/InfoGeometry/Clifford/Cl11HomogeneousChains.lean",
            "lean/InfoGeometry/Clifford/Cl11GradedDifferential.lean",
            "lean/InfoGeometry/Canonical/SplitCliffordMatrixLimitSoldering.lean",
        ),
        baseline_symbols=(
            "nativeChain",
            "coefficientChain_matrix_suffixParity",
            "jwDifferential_sq",
            "jwDifferential_homotopy",
            "jwDifferential_ne_zero",
            "jwDifferential_range_eq_ker",
            "gradedTensorSuccessor_not_algHom",
        ),
        milestone="M2",
        milestone_requirements=(
            "transported jwDifferential and jwHomotopy on SplitCliffordInfinity / nativeChain",
            "respects gradedTensorSuccessor_not_algHom obstruction",
        ),
    ),
    RubricItem(
        item_id="R3-coordless-clifford",
        pillar="R3",
        concept="Coordinate-less invariant Clifford algebra representation (equivOfIsometry invariance & O(Q) subalgebra)",
        bucket_scope="BUCKET 1 (arbitrary Module R M); BUCKET 2 (FiniteDimensional / finrank cutoff)",
        baseline_owners=(
            "lean/InfoGeometry/Clifford/GradedGraceContraction.lean",
            "lean/InfoGeometry/Clifford/Cl11SupergradedTensorBridge.lean",
            "lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean",
            "lean/InfoGeometry/ErlangenCoordinateless.lean",
        ),
        baseline_symbols=(
            "cliffordGradeProj",
            "cliffordGradeProj_idem",
            "clifford_ι_injective",
            "cliffordGradeProj_zero_eq_algebraMap_hTrace",
            "not_nonneg_cliffordKreinPairing_Q31",
        ),
        milestone="M2",
        milestone_requirements=(
            "equivOfIsometry commutation with involute, reverse, evenOdd, cliffordGradeProj, hTrace_cl",
            "SymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q) and invariant subalgebra",
            "ErlangenCoordinateless M_2(C) vs abstract CliffordAlgebra Q alignment",
        ),
    ),
    RubricItem(
        item_id="R3-R1-coupling",
        pillar="R3",
        concept="R3 <-> R1 coupling (FormHodgeCliffordData <-> cliffordGradeProj/equivExterior; abstract Clifford rotor MC)",
        bucket_scope="BUCKET 1 (algebraic exterior-Clifford & rotor Darboux); BUCKET 2 (smooth trajectories)",
        baseline_owners=(
            "lean/InfoGeometry/Canonical/ZornDifferentialFormsCliffordBridge.lean",
            "lean/InfoGeometry/Synthesis/CartanHestenesRotorSpinConnectionMaurerCartanSynthesis.lean",
            "lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean",
        ),
        baseline_symbols=(
            "FormHodgeCliffordData",
            "hodgeDirac",
            "clifford_noncomm_witness",
        ),
        milestone="M2",
        milestone_requirements=(
            "FormHodgeCliffordData coupled to equivExterior / cliffordGradeProj",
            "abstract CliffordAlgebra Q Darboux spin-connection via reverse",
            "CliffordMobiusDeRhamMonodromy vacuous rfl conjunctions eliminated",
        ),
    ),
    RubricItem(
        item_id="R2-erlangen20",
        pillar="R2",
        concept="Felix Klein Erlangen 2.0 unification",
        bucket_scope="BUCKET 1 (algebraic/Lie/Cartan-fiber); BUCKET 2/3 (smooth principal atlas, W_4,4, A_5)",
        baseline_owners=(
            "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
            "lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean",
            "lean/InfoGeometry/Canonical/ErlangenOperator2.lean",
            "lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean",
            "lean/InfoGeometry/Geometry/PhaseErlanger.lean",
            "lean/InfoGeometry/Canonical/FelixKleinGeometryUnification.lean",
        ),
        baseline_symbols=(
            "Erlangen20Datum",
            "OperatorIntertwiner",
            "ErlangenOperatorDatum",
            "gl2R_maurerCartan_flat",
            "homothetyCartanGeometry_curvature_formula",
            "cartanFiberErlangen20Datum",
        ),
        milestone="M3",
        milestone_requirements=(
            "unified hierarchy linking Erlangen20Datum, SymmetryAction, ErlangenOperatorDatum, PhaseErlanger, SmoothCartanGeometry",
            "explicit citation and alignment with Felix Klein's 1872 Erlanger Programm (ABN7632.0001.001 & arXiv:0807.3161v1: §§1-5 groups/stabilizers/Abbildung/orbits, §§8-9 contact 1-forms/infinitesimal symmetries, §10/Concluding Remarks coordinate-less invariants)",
            "honest manifest boundaries preserved",
        ),
    ),
    RubricItem(
        item_id="R2-double-real-krein",
        pillar="R2",
        concept="Double-real Krein spaces unification (DoubledSpace, Krein16Idx, RealKreinSpace/RealKVect, Clsplit n)",
        bucket_scope="BUCKET 1 (finite-dim Krein16Idx & Clsplit n); BUCKET 2 (CompleteSpace DoubledSpace E)",
        baseline_owners=(
            "lean/InfoGeometry/Krein/KreinSpace.lean",
            "lean/InfoGeometry/Krein/DoubledSpace.lean",
            "lean/InfoGeometry/Krein/DoubleRealKreinShearDefect.lean",
            "lean/InfoGeometry/Krein/DoubledMatrixSymplectic.lean",
            "lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean",
        ),
        baseline_symbols=(
            "KreinSpace",
            "DoubledSpace",
            "modular_j",
            "spectral_epsilon",
            "componentNReal_not_krein_isometry",
            "matrixAction_preserves_symplectic_iff",
            "Krein16Idx",
            "gamma44",
            "kreinMetric88_properties",
        ),
        milestone="M3",
        milestone_requirements=(
            "KreinSpace & KreinGradedModule on Krein16Idx -> R (kreinMetric88, gamma44)",
            "5 doubled-space operators kept distinct; shear != krein_isometry preserved",
            "ClNNFredholmBridge extended from Cl(1,1) to Clsplit n",
        ),
    ),
    RubricItem(
        item_id="R2-kasparov",
        pillar="R2",
        concept="Kasparov cycles and spectral triples (RealStructureKreinCompatible, unbounded -> bounded cycle)",
        bucket_scope="BUCKET 2 (finite-dim CFC.sqrt & B=R); BUCKET 3 (unbounded functional calc, right B-mod, Kasparov product)",
        baseline_owners=(
            "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
            "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
            "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean",
            "lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean",
            "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
            "lean/InfoGeometry/KK/RealCl55KasparovCycleBridge.lean",
        ),
        baseline_symbols=(
            "PhaseRealSpectralTriple",
            "RealStructureMetricCompatible",
            "RealSplitKreinKasparovCycle",
            "superComm_pi_compact",
            "RealSplitKreinUnboundedCycle",
            "firstStep_leftGenerator_eq_cl11Rep",
        ),
        milestone="M3",
        milestone_requirements=(
            "RealStructureKreinCompatible using kreinInner",
            "bridge PhaseRealSpectralTriple -> RealSplitKreinUnboundedCycle -> RealSplitKreinKasparovCycle",
            "nontrivial F != 0 witness and honest BUCKET 2/3 tags",
        ),
    ),
    RubricItem(
        item_id="X-R1-R2-R3",
        pillar="Cross-Pillar",
        concept="Cross-pillar R1 <-> R2 <-> R3 alignment (EquivariantDatum->Erlangen20, Connes 1-forms, Onsager->J-reciprocity, MC<->1-F^2)",
        bucket_scope="BUCKET 1/2 (algebraic & finite-dim); BUCKET 3 (infinite-dim domain stability of D_A)",
        baseline_owners=(
            "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
            "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
            "lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean",
            "lean/InfoGeometry/OperatorAlgebra/KreinFrechetRiesz.lean",
            "lean/InfoGeometry/Algebra/KreinPeirceTowerIntertwine.lean",
        ),
        baseline_symbols=(
            "EquivariantDatum",
            "action_preserves_compact_phase_defects",
            "ncDeriv_leibniz",
            "kreinToDual",
            "peirce11_positive_sector_krein_positivity_and_bianchi",
            "clTower_and_colimit_peirce_transport",
        ),
        milestone="M3",
        milestone_requirements=(
            "EquivariantDatum -> Erlangen20Datum preserving chiral kernels",
            "R1 1-forms -> Connes [D, pi(a)] with Leibniz",
            "R1 Onsager/Frechet -> HasJReciprocity / kreinToDual",
            "R1 MC curvature <-> 1 - F^2 / gauge-fluctuated D_A",
        ),
    ),
    RubricItem(
        item_id="R2-klein-grassmann-plucker",
        pillar="R2",
        concept="Klein 1872 <-> Grassmann [6,7,8] & Plucker Bridges A, B, C",
        bucket_scope="BUCKET 1 (algebraic Bridges A, B, C & Grassmann/Plucker identities); BUCKET 2 (Kummer/quartic singular locus)",
        baseline_owners=(
            "lean/InfoGeometry/Projective/GrassmannAusdehnungslehreRegressiveShadow.lean",
            "lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean",
            "lean/InfoGeometry/Canonical/GrassmannProductQuotientAndMasterAtlas.lean",
            "lean/InfoGeometry/Projective/KleinQuadric.lean",
            "lean/InfoGeometry/Projective/KleinQuadricPlucker.lean",
            "lean/InfoGeometry/Projective/ExteriorPluckerTower.lean",
            "lean/InfoGeometry/Projective/MobiusPluckerKleinCompatibility.lean",
            "lean/InfoGeometry/Canonical/GrassmannPfaffianDarbouxAlgebra.lean",
            "lean/InfoGeometry/Projective/PluckerLinearComplex.lean",
            "lean/InfoGeometry/Projective/PluckerLinearComplexGeometry.lean",
        ),
        baseline_symbols=(
            "KleinQuadric",
            "PluckerLinearComplex",
        ),
        milestone="M3",
        milestone_requirements=(
            "cites Grassmann [6] (1844), [7] (1862 p.278), [8] (1852 Crelle 44)",
            "Bridge A: Grassmann exterior/regressive products <-> Plucker ray coordinates & Klein quadric",
            "Bridge B: Grassmann syncyclic circle space <-> Mobius 4-var lightcone & Lie sphere 5-var Korper",
            "Bridge C: Grassmann Pfaffian normal forms & Darboux rank <-> Plucker linear/special complexes, Kummer surfaces, Note VI curvature & §9 contact 1-forms",
        ),
    ),
)

_BUCKET3_CLAIM_SPECS: tuple[tuple[str, str], ...] = (
    (
        "continuum_4d_yang_mills_bucket1",
        r"(?:continuum\s+4D\s+Yang[-–]Mills|4D\s+continuum\s+Yang[-–]Mills|4D\s+YM\s+mass\s+gap\s+proved)",
    ),
    (
        "cstar_correspondence_proved_bucket1",
        r"C\*-correspondence\s+proved",
    ),
    (
        "internal_kasparov_product_bucket1",
        r"(?:internal\s+Kasparov\s+product|KK\(A,\s*B\)\s*[×x]\s*KK\(B,\s*C\)\s*(?:->|→)\s*KK\(A,\s*C\)\s+proved)",
    ),
    (
        "infinite_dim_functional_calc_bucket1",
        r"D\s*\(1\s*\+\s*D\s*(?:\^2|²)\)\s*\^\s*\(?-1/2\)?",
    ),
    (
        "w44_tm_cotangent_bucket1",
        r"W_?\{?4,4\}?\s*(?:≅|\\cong|≃)\s*TM\s*⊕\s*T\*M",
    ),
    (
        "eightfold_bott_m16_bucket1",
        r"(?:8-fold\s+real\s+Bott|eightfold\s+Bott|M_?\{?16\}?\(ℝ\)\s+periodicity\s+proved)",
    ),
    (
        "full_g2_integration_bucket1",
        r"(?:full\s+G_?2\(2\)\s+(?:group\s+)?integration|concrete\s+G_?\{?2\(2\)\}?\s+Haar)",
    ),
)

FORBIDDEN_OVERCLAIM_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = tuple(
    (
        name,
        re.compile(
            rf"(?:BUCKET\s*1\b[^\n]{{0,160}}(?:{claim})|(?:{claim})[^\n]{{0,160}}\[?\s*`?BUCKET\s*1\b`?\s*\]?)",
            re.I,
        ),
    )
    for name, claim in _BUCKET3_CLAIM_SPECS
)

_COMPILED_BUCKET3_CLAIMS: tuple[tuple[str, re.Pattern[str]], ...] = tuple(
    (name, re.compile(claim, re.I)) for name, claim in _BUCKET3_CLAIM_SPECS
)

_DOC_SYMBOL_ALLOWLIST: frozenset[str] = frozenset(
    {
        # Lean 4 / Mathlib types, classes, tactics, and standard symbols
        "AddEquiv",
        "RingEquiv",
        "AlgEquiv",
        "LinearEquiv",
        "ContinuousLinearEquiv",
        "LinearMap",
        "ContinuousLinearMap",
        "AlternatingMap",
        "ExteriorAlgebra",
        "CliffordAlgebra",
        "QuadraticForm",
        "QuadraticMap",
        "Submodule",
        "Submonoid",
        "Subgroup",
        "Subalgebra",
        "Subring",
        "FiniteDimensional",
        "CompleteSpace",
        "CommRing",
        "NormedRing",
        "NormedAlgebra",
        "InnerProductSpace",
        "PartialOrder",
        "IsCoprime",
        "ContDiff",
        "DifferentiableAt",
        "HasFDerivAt",
        "HasStrictDerivAt",
        "AddCommGroup",
        "AddCommMonoid",
        "IsScalarTower",
        "SMulCommClass",
        "StarOrderedRing",
        "GaloisConnection",
        "LieSubalgebra",
        "LieIdeal",
        "LieHom",
        "MulAction",
        "deRhamComplex",
        "extDeriv",
        "fderiv",
        "iteratedFDeriv",
        "native_decide",
        "Classical.choice",
        "Quot.sound",
        "propext",
        "sorryAx",
        "DirectLimit",
        "DirectedSystem",
        "DiscreteTopology",
        "evenOdd",
        "equivExterior",
        "IsometryEquiv",
        "equivOfIsometry",
        "HasDerivAt",
        "MonoidHom",
        "NormedAddCommGroup",
        "LinearIsometryEquiv",
        "IsManifold",
        "UniformSpace",
        "Matrix",
        "Module",
        "Algebra",
        "Function",
        # Spec-doc status / epistemic / QMS SOP §3.6 envelope labels
        "bucket_3_open_debt",
        "countermodel_found",
        "pending_audit",
        "non_theorem_claims",
        "concept_id",
        "source_text",
        "intake_classification",
        "mathematical_domain",
        "target_status",
        "risk_level",
        "allowed_imports",
        "formal_objects",
        "acceptance_theorems",
        "theorem_backed",
        "conjectural_scaffold",
        "qms_document_draft",
    }
)

_MATHLIB_QUAL_PREFIXES: frozenset[str] = frozenset(
    {
        "AddEquiv",
        "AlgEquiv",
        "Algebra",
        "CliffordAlgebra",
        "ContinuousLinearEquiv",
        "ContinuousLinearMap",
        "DirectLimit",
        "DirectedSystem",
        "ExteriorAlgebra",
        "Fin",
        "Function",
        "LinearEquiv",
        "LinearIsometryEquiv",
        "LinearMap",
        "Matrix",
        "Module",
        "MonoidHom",
        "Nat",
        "QuadraticForm",
        "QuadraticMap",
        "Real",
        "RingEquiv",
        "Subalgebra",
        "Subgroup",
        "Submodule",
        "Submonoid",
        "Subring",
        "UniformSpace",
    }
)

_CORPUS_INDEX_CACHE: tuple[set[str], set[str], set[str], set[str]] | None = None
_CORPUS_SECTIONS_CACHE: set[str] | None = None
_CORPUS_STEM_DECLS_CACHE: dict[str, set[str]] | None = None
_CORPUS_PRIV_STEM_DECLS_CACHE: dict[str, set[str]] | None = None
_NS_DIRECTIVE_RX = re.compile(rf"^[ \t]{{0,4}}namespace\s+({_LEAN_NAME})\s*$", re.M)
_END_DIRECTIVE_RX = re.compile(rf"^[ \t]{{0,4}}end(?:\s+({_LEAN_NAME}))?\s*$", re.M)
_SEC_DIRECTIVE_RX = re.compile(
    rf"^[ \t]{{0,4}}(?:noncomputable\s+|private\s+|protected\s+)?section(?:\s+({_LEAN_NAME}))?\s*$",
    re.M,
)
_STRUCT_FIELD_RX = re.compile(rf"^[ \t]+({_LEAN_IDENT_SEG})\s*(?:[:({{\[])")


def _all_lean_corpus_index() -> tuple[set[str], set[str], set[str], set[str]]:
    """Build (all_short_decls, all_fqns, all_namespaces, all_module_stems) from comment/string-stripped Lean sources."""
    global _CORPUS_INDEX_CACHE, _CORPUS_SECTIONS_CACHE, _CORPUS_STEM_DECLS_CACHE, _CORPUS_PRIV_STEM_DECLS_CACHE
    if _CORPUS_INDEX_CACHE is not None:
        return _CORPUS_INDEX_CACHE

    lean_root = REPO_ROOT / "lean" / "InfoGeometry"
    all_decls: set[str] = set()
    all_fqns: set[str] = set()
    all_namespaces: set[str] = {"InfoGeometry"}
    all_module_stems: set[str] = set()
    all_sections: set[str] = set()
    stem_decls: dict[str, set[str]] = {}
    priv_stem_decls: dict[str, set[str]] = {}

    if (REPO_ROOT / "lean" / "InfoGeometry.lean").is_file():
        all_module_stems.add("InfoGeometry")

    for path in lean_root.rglob("*.lean"):
        rel = path.relative_to(REPO_ROOT).as_posix()
        if any(seg in rel for seg in ("/Unstable/", "/Archive/", "/tmp/")):
            continue
        stem = path.stem
        all_module_stems.add(stem)
        stem_bucket = stem_decls.setdefault(stem, set())
        priv_bucket = priv_stem_decls.setdefault(stem, set())
        txt = path.read_text(encoding="utf-8", errors="replace")
        stripped = _strip_lean_comments_and_strings(txt)
        for d in parse_declarations_from_text(stripped, already_stripped=True):
            if d.is_private:
                priv_bucket.add(d.short_name)
                if "." in d.short_name:
                    priv_bucket.add(d.short_name.split(".")[-1])
                continue
            all_decls.add(d.short_name)
            stem_bucket.add(d.short_name)
            all_fqns.add(d.fqn)
            if "." in d.short_name:
                last = d.short_name.split(".")[-1]
                all_decls.add(last)
                stem_bucket.add(last)
            if "." in d.fqn:
                ns = d.fqn.rsplit(".", 1)[0]
                all_namespaces.add(ns)
                parts = ns.split(".")
                for i in range(len(parts)):
                    all_namespaces.add(".".join(parts[: i + 1]))
                    if parts[i]:
                        all_namespaces.add(parts[i])
            if d.kind in ("structure", "class"):
                for line in d.block_text.splitlines()[1:]:
                    fm = _STRUCT_FIELD_RX.match(line)
                    if fm:
                        fld = fm.group(1)
                        all_decls.add(fld)
                        stem_bucket.add(fld)
                        all_fqns.add(f"{d.fqn}.{fld}")
        for m_ns in _NS_DIRECTIVE_RX.finditer(stripped):
            ns = m_ns.group(1)
            all_namespaces.add(ns)
            parts = ns.split(".")
            for i in range(len(parts)):
                all_namespaces.add(".".join(parts[: i + 1]))
                if parts[i]:
                    all_namespaces.add(parts[i])
        for m_sec in _SEC_DIRECTIVE_RX.finditer(stripped):
            sec_name = m_sec.group(1)
            if sec_name:
                all_sections.add(sec_name)

    _CORPUS_INDEX_CACHE = (all_decls, all_fqns, all_namespaces, all_module_stems)
    _CORPUS_SECTIONS_CACHE = all_sections
    _CORPUS_STEM_DECLS_CACHE = stem_decls
    _CORPUS_PRIV_STEM_DECLS_CACHE = priv_stem_decls
    return _CORPUS_INDEX_CACHE


def verify_baseline_rubric_coverage() -> dict[str, Any]:
    """Verify every rubric item has existing baseline owners and symbols on disk."""
    missing_files: list[str] = []
    missing_symbols: list[str] = []
    checked_items = 0
    for item in RUBRIC_ITEMS:
        checked_items += 1
        combined_text = ""
        for rel in item.baseline_owners:
            full = REPO_ROOT / rel
            if not full.is_file():
                missing_files.append(f"{item.item_id}: missing file {rel}")
            else:
                combined_text += "\n" + full.read_text(encoding="utf-8", errors="replace")
        for sym in item.baseline_symbols:
            if not re.search(rf"\b{re.escape(sym)}\b", combined_text):
                missing_symbols.append(f"{item.item_id}: missing symbol {sym!r}")
    return {
        "passed": not missing_files and not missing_symbols,
        "checked_items": checked_items,
        "missing_files": missing_files,
        "missing_symbols": missing_symbols,
    }


def find_master_spec_docs() -> list[str]:
    """Locate M1, M2, and M3 reconciliation specification docs under docs/."""
    docs_dir = REPO_ROOT / "docs"
    found: list[str] = []
    for name in (
        "R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md",
        "R3_CLIFFORD_TOWERS_AND_INVARIANCE_SPEC.md",
    ):
        p = docs_dir / name
        if p.is_file():
            found.append(f"docs/{name}")
    for p in sorted(docs_dir.glob("*RECONCILIATION*SPEC*.md")):
        rel = f"docs/{p.name}"
        if rel not in found:
            found.append(rel)
    for p in sorted(docs_dir.glob("*MASTER*SPEC*.md")):
        rel = f"docs/{p.name}"
        if rel not in found:
            found.append(rel)
    return found


def verify_spec_docs_present(require_m1: bool = True, require_m2: bool = True, require_m3: bool = True) -> dict[str, Any]:
    missing: list[str] = []
    docs_dir = REPO_ROOT / "docs"
    if require_m1 and not (docs_dir / "R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md").is_file():
        missing.append("docs/R1_NONCOMMUTATIVE_DIFFERENTIAL_GEOMETRY_SPEC.md")
    if require_m2 and not (docs_dir / "R3_CLIFFORD_TOWERS_AND_INVARIANCE_SPEC.md").is_file():
        missing.append("docs/R3_CLIFFORD_TOWERS_AND_INVARIANCE_SPEC.md")
    master_candidates = [
        p
        for p in list(docs_dir.glob("*RECONCILIATION*SPEC*.md")) + list(docs_dir.glob("*MASTER*SPEC*.md"))
        if p.is_file()
    ]
    if require_m3 and not master_candidates:
        missing.append("docs/*RECONCILIATION*SPEC*.md (M3 Master Specification)")

    present = find_master_spec_docs()
    untagged: list[str] = []
    for rel in present:
        txt = (REPO_ROOT / rel).read_text(encoding="utf-8", errors="replace")
        if not re.search(r"\bBUCKET\s*[123]\b", txt):
            untagged.append(rel)
    return {
        "passed": not missing and not untagged,
        "present": present,
        "missing": missing,
        "untagged_bucket_docs": untagged,
    }


def _is_lean_ident_token(tok: str) -> bool:
    if not re.match(r"^[^\W\d_][\w']*$", tok):
        return False
    if "_" in tok:
        return True
    if re.match(r"^[a-z]", tok) and re.search(r"[A-Z]", tok):
        return True
    if re.match(r"^[A-Z]", tok) and re.search(r"[a-z]", tok) and len(re.findall(r"[A-Z]", tok)) >= 2:
        return True
    return False


def _resolve_qualified_symbol(
    q: str,
    all_fqns: set[str],
    all_namespaces: set[str],
    stem_decls: dict[str, set[str]],
) -> bool:
    if q in all_fqns or q in all_namespaces:
        return True
    if not q.startswith("InfoGeometry."):
        if f"InfoGeometry.{q}" in all_fqns or f"InfoGeometry.{q}" in all_namespaces:
            return True
        suffix = f".{q}"
        if any(fqn.endswith(suffix) for fqn in all_fqns) or any(
            ns.endswith(suffix) for ns in all_namespaces
        ):
            return True
        if "." in q:
            stem, decl = q.split(".", 1)
            if decl in stem_decls.get(stem, ()):
                return True
        ig_mod_path = REPO_ROOT / "lean" / "InfoGeometry" / Path(*q.split(".")).with_suffix(".lean")
        if ig_mod_path.is_file():
            return True
        prefix = q.split(".", 1)[0]
        if prefix in _MATHLIB_QUAL_PREFIXES:
            return True
    mod_path = REPO_ROOT / "lean" / Path(*q.split(".")).with_suffix(".lean")
    return mod_path.is_file()


def verify_doc_symbols(doc_paths: Iterable[str]) -> dict[str, Any]:
    """Verify backtick-quoted Lean paths, FQNs, and unqualified Lean identifiers in spec docs."""
    all_decls, all_fqns, all_namespaces, all_module_stems = _all_lean_corpus_index()
    all_sections = _CORPUS_SECTIONS_CACHE or set()
    stem_decls = _CORPUS_STEM_DECLS_CACHE or {}
    priv_stem_decls = _CORPUS_PRIV_STEM_DECLS_CACHE or {}
    missing_paths: list[str] = []
    missing_symbols: list[str] = []
    checked_docs: list[str] = []

    path_re = re.compile(r"`((?:lean/)?InfoGeometry/[A-Za-z0-9_/]+\.lean)`")
    qual_re = re.compile(r"`([^\W\d_][\w']+(?:\.[^\W\d_][\w']*)+)`")
    backtick_re = re.compile(r"`([^`\n]+)`")
    heading_rx = re.compile(r"^\s*#{1,6}\s+(.*)$")
    errata_heading_rx = re.compile(r"\b(?:Verified\s+Errata|Citation\s+Corrections|Errata)\b", re.I)
    errata_line_rx = re.compile(
        r"\b(?:Actual\s+names?|renamed\s+to|instead\s+of|absent\s+on\s+disk|does\s+not\s+exist)\b"
    )
    internal_note_rx = re.compile(r"\b(?:private|structural|internal|helper|auxiliary|recursion)\b", re.I)
    skip_exts = (".lean", ".olean", ".md", ".py", ".json", ".sh", ".pdf", ".txt")

    for rel in doc_paths:
        full = REPO_ROOT / rel
        if not full.is_file():
            missing_paths.append(f"{rel}: doc file does not exist")
            continue
        checked_docs.append(rel)
        txt = full.read_text(encoding="utf-8", errors="replace")
        for m in path_re.finditer(txt):
            cand = m.group(1)
            norm = cand if cand.startswith("lean/") else f"lean/{cand}"
            if not (REPO_ROOT / norm).is_file():
                missing_paths.append(f"{rel}: referenced path `{cand}` not found")

        seen_qual: set[str] = set()
        seen_unqual: set[str] = set()
        in_errata_section = False

        for line in txt.splitlines():
            hm = heading_rx.match(line)
            if hm:
                in_errata_section = bool(errata_heading_rx.search(hm.group(1)))
                continue

            is_errata_line = in_errata_section and bool(errata_line_rx.search(line))

            for m in qual_re.finditer(line):
                q = m.group(1)
                if q.endswith(skip_exts) or q in seen_qual or q in _DOC_SYMBOL_ALLOWLIST:
                    continue
                seen_qual.add(q)
                if is_errata_line:
                    continue
                if not _resolve_qualified_symbol(q, all_fqns, all_namespaces, stem_decls):
                    missing_symbols.append(
                        f"{rel}: `{q}` not found as Lean module, namespace, or declaration FQN"
                    )

            cited_stems = [
                Path(m_st).stem for m_st in re.findall(r"`([A-Za-z0-9_/]+\.lean)`", line)
            ]
            is_internal_note = bool(cited_stems) and bool(internal_note_rx.search(line))

            for m in backtick_re.finditer(line):
                tok = m.group(1).strip()
                if tok in seen_unqual or tok in _DOC_SYMBOL_ALLOWLIST:
                    continue
                if not _is_lean_ident_token(tok):
                    continue
                seen_unqual.add(tok)
                if (
                    tok in all_decls
                    or tok in all_module_stems
                    or tok in all_namespaces
                    or tok in all_sections
                ):
                    continue
                # Slash-paired abbreviated suffix (e.g., `thermodynamicFamilyRangeLane`/`QuotientLane`)
                before = line[: m.start()]
                m_prev = re.search(r"`([^`\n]+)`\s*/\s*$", before)
                if m_prev:
                    prev_tok = m_prev.group(1).strip()
                    if prev_tok in all_decls and any(
                        (prev_tok[:k] + tok) in all_decls for k in range(1, len(prev_tok))
                    ):
                        continue
                # Explicitly cited internal/structural private helper in a named module on the same line
                if is_internal_note and any(
                    tok in priv_stem_decls.get(st, ()) for st in cited_stems
                ):
                    continue
                if is_errata_line:
                    continue
                missing_symbols.append(
                    f"{rel}: unqualified symbol `{tok}` not found in comment-stripped Lean declarations"
                )

    return {
        "passed": not missing_paths and not missing_symbols,
        "checked_docs": checked_docs,
        "missing_paths": missing_paths,
        "missing_symbols": missing_symbols,
    }


def detect_bucket3_overclaims_in_text(rel: str, txt: str) -> list[str]:
    """Detect prefix, suffix, and heading/section-scoped BUCKET 1 overclaims of BUCKET 3 open items."""
    findings: list[str] = []
    heading_rx = re.compile(r"^\s*(#{1,6})\s+(.*)$")
    standalone_bucket_rx = re.compile(
        r"^\s*(?:[-*]\s+)?(?:\*{1,2})?`?BUCKET\s*([123])`?(?:\*{1,2})?\s*[:\-—]?\s*(?:\*{1,2})?\s*$",
        re.I,
    )
    bucket_tag_rx = re.compile(r"\bBUCKET\s*([123])\b", re.I)
    heading_stack: list[tuple[int, str | None]] = []
    paragraph_bucket: str | None = None

    for lineno, line in enumerate(txt.splitlines(), start=1):
        # 1. Line-level prefix or suffix BUCKET 1 overclaim
        line_hit = False
        for name, pat in FORBIDDEN_OVERCLAIM_PATTERNS:
            if pat.search(line):
                findings.append(f"{rel}:{lineno}: potential BUCKET 3 overclaim matched `{name}`")
                line_hit = True

        # 2. Markdown heading stack tracking
        hm = heading_rx.match(line)
        if hm:
            lvl = len(hm.group(1))
            htext = hm.group(2)
            while heading_stack and heading_stack[-1][0] >= lvl:
                heading_stack.pop()
            b_nums = set(bucket_tag_rx.findall(htext))
            h_bucket = next(iter(b_nums)) if len(b_nums) == 1 else None
            heading_stack.append((lvl, h_bucket))
            paragraph_bucket = None
            continue

        # 3. Standalone paragraph bucket header (e.g. "BUCKET 1:" followed by bullets)
        if not line.strip():
            paragraph_bucket = None
            continue
        sm = standalone_bucket_rx.match(line)
        if sm:
            paragraph_bucket = sm.group(1)
            continue

        # 4. Active multiline BUCKET 1 section/paragraph check
        active_heading_bucket = next((b for _, b in reversed(heading_stack) if b is not None), None)
        active_bucket = paragraph_bucket or active_heading_bucket
        if active_bucket == "1" and not line_hit:
            # Skip only if the line itself explicitly tags the item as BUCKET 2 or BUCKET 3
            line_buckets = set(bucket_tag_rx.findall(line))
            if not (line_buckets & {"2", "3"}):
                for name, claim_rx in _COMPILED_BUCKET3_CLAIMS:
                    if claim_rx.search(line):
                        findings.append(
                            f"{rel}:{lineno}: multiline BUCKET 1 section overclaim matched `{name}`"
                        )
    return findings


def verify_no_bucket3_overclaims(doc_paths: Iterable[str], lean_paths: Iterable[str] = ()) -> dict[str, Any]:
    """Ensure BUCKET 3 open debt boundaries are never misrepresented as BUCKET 1 proved."""
    findings: list[str] = []
    for rel in list(doc_paths) + list(lean_paths):
        full = REPO_ROOT / rel
        if not full.is_file():
            continue
        txt = full.read_text(encoding="utf-8", errors="replace")
        findings.extend(detect_bucket3_overclaims_in_text(rel, txt))
    return {"passed": not findings, "findings": findings}


def check_monodromy_vacuity() -> dict[str, Any]:
    """Detect `(clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧ ...` vacuity in CliffordMobiusDeRhamMonodromy.lean."""
    rel = "lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean"
    full = REPO_ROOT / rel
    if not full.is_file():
        return {"passed": False, "vacuous_matches": [f"{rel}: missing"]}
    txt = full.read_text(encoding="utf-8", errors="replace")
    vac_pat = re.compile(r"\(clsplit_succ_equiv\s+n\)\s*=\s*\(clsplit_succ_equiv\s+n\)\s*∧")
    matches = [
        f"{rel}:{idx}: {line.strip()}"
        for idx, line in enumerate(txt.splitlines(), start=1)
        if vac_pat.search(line)
    ]
    return {"passed": not matches, "vacuous_matches": matches}


def check_src_parity_ncg() -> dict[str, Any]:
    """Compare lean/ vs src/ NoncommutativeConnectionCurvature.lean parity."""
    lean_p = REPO_ROOT / "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean"
    src_p = REPO_ROOT / "src/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean"
    if not lean_p.is_file():
        return {"in_sync": False, "reason": "lean/ owner missing", "missing_in_src": []}
    if not src_p.is_file():
        return {"in_sync": False, "reason": "src/ mirror missing", "missing_in_src": ["entire file"]}
    lean_txt = lean_p.read_text(encoding="utf-8", errors="replace")
    src_txt = src_p.read_text(encoding="utf-8", errors="replace")
    watched = (
        "AlgebraDerivation.zero",
        "noncommutativeChernSimonsCubic",
        "noncommutativeChernSimonsTransgression",
    )
    missing_in_src = [s for s in watched if s in lean_txt and s not in src_txt]
    return {
        "in_sync": not missing_in_src,
        "missing_in_src": missing_in_src,
        "lean_lines": len(lean_txt.splitlines()),
        "src_lines": len(src_txt.splitlines()),
    }


def check_duplicate_onsager_types() -> dict[str, Any]:
    """Check whether TransportTensor / TimeReversal have duplicate primary definitions."""
    files = (
        "lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean",
        "lean/InfoGeometry/Thermo/OnsagerOperatorClosure.lean",
        "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
        "lean/InfoGeometry/Synthesis/OnsagerOperatorDifferentialCalculus.lean",
    )
    def_re = re.compile(r"^\s*(?:structure|def)\s+(TransportTensor|TimeReversal)\b", re.M)
    owners: dict[str, list[str]] = {"TransportTensor": [], "TimeReversal": []}
    for rel in files:
        full = REPO_ROOT / rel
        if not full.is_file():
            continue
        txt = full.read_text(encoding="utf-8", errors="replace")
        for m in def_re.finditer(txt):
            owners[m.group(1)].append(rel)
    duplicates = {k: v for k, v in owners.items() if len(v) > 1}
    return {"passed": not duplicates, "owners": owners, "duplicates": duplicates}


def check_infogeometry_barrel_imports(modules: Iterable[str]) -> dict[str, Any]:
    """Check that reconciled M1-M3 modules are imported in lean/InfoGeometry.lean."""
    barrel = REPO_ROOT / "lean" / "InfoGeometry.lean"
    if not barrel.is_file():
        return {"passed": False, "missing": list(modules), "error": "lean/InfoGeometry.lean missing"}
    txt = barrel.read_text(encoding="utf-8", errors="replace")
    imported = set(re.findall(r"^\s*import\s+([A-Za-z0-9_.]+)", txt, re.M))
    missing = [m for m in modules if m not in imported]
    return {"passed": not missing, "missing": missing, "imported_count": len(imported)}


def verify_erlangen_1872_primary_source(doc_paths: Iterable[str]) -> dict[str, Any]:
    """Verify M3 Erlangen 2.0 / Master spec docs incorporate Klein's 1872 Erlanger Programm (ABN7632.0001.001 & arXiv:0807.3161v1 §§1-10)."""
    combined = ""
    checked: list[str] = []
    for rel in doc_paths:
        full = REPO_ROOT / rel
        if full.is_file():
            checked.append(rel)
            combined += "\n" + full.read_text(encoding="utf-8", errors="replace")

    if not checked:
        return {
            "passed": False,
            "checked_docs": [],
            "missing": ["No M3 Erlangen/Master spec doc found"],
        }

    requirements: list[tuple[str, re.Pattern[str]]] = [
        ("primary_source_id_or_title", re.compile(r"ABN7632\.0001\.001|0807\.3161v1|Vergleichende Betrachtungen|Erlanger Programm|Erlangen Programm", re.I)),
        ("year_1872_klein", re.compile(r"1872.*Klein|Klein.*1872|Felix Klein", re.I)),
        ("manifold_or_carrier", re.compile(r"\b(?:manifold|manifoldness|Mannigfaltigkeit|carrier)\b", re.I)),
        ("transformation_group_hauptgruppe", re.compile(r"\b(?:Hauptgruppe|transformation group|principal group)\b", re.I)),
        ("invariant_theory", re.compile(r"\binvariant", re.I)),
        ("subgroup_stabilizer_abbildung_orbit_faithful_sec1_5", re.compile(r"(?:stabilizer|adjoin|Abbildung|orbit|faithful|self-conjugate|normal subgroup|subgroup|transfer)", re.I)),
        ("sec1_5_space_element_and_transfer", re.compile(r"(?:Abbildung|transfer by representation|space[- ]element|Plücker|Cayley[-–]Klein)", re.I)),
        ("sec8_9_contact_1form_infinitesimal_r1_r2", re.compile(r"(?:contact transformation|Pfaffian|1-form|one-form|infinitesimal)", re.I)),
        ("sec10_coordinateless_analytic_r2_r3", re.compile(r"(?:coordinate[- ]?(?:less|independent|system[- ]independent)|Ausdehnungslehre|Grassmann)", re.I)),
    ]
    missing = [name for name, pat in requirements if not pat.search(combined)]
    return {
        "passed": not missing,
        "checked_docs": checked,
        "missing": missing,
    }


def verify_klein_grassmann_plucker_docs(doc_paths: Iterable[str]) -> dict[str, Any]:
    """Verify M3 / Master spec docs cover Klein 1872 <-> Grassmann [6,7,8] & Plucker Bridges A, B, C."""
    combined = ""
    checked: list[str] = []
    for rel in doc_paths:
        full = REPO_ROOT / rel
        if full.is_file():
            checked.append(rel)
            combined += "\n" + full.read_text(encoding="utf-8", errors="replace")

    if not checked:
        return {"passed": False, "checked_docs": [], "missing": ["No M3 spec docs found"]}

    requirements: list[tuple[str, re.Pattern[str]]] = [
        ("grassmann_1844", re.compile(r"\b1844\b|Ausdehnungslehre", re.I)),
        ("grassmann_1862_p278", re.compile(r"\b1862\b|\bp\.?\s*278\b", re.I)),
        ("grassmann_1852_crelle", re.compile(r"\b1852\b|Crelle", re.I)),
        ("bridge_a_klein_quadric_plucker", re.compile(r"regressive.*Pl[üu]cker|Klein\s+quadric", re.I)),
        ("bridge_b_syncyclic_mobius_lie_sphere", re.compile(r"syncyclic.*(?:M[öo]bius|Lie\s+sphere)", re.I | re.S)),
        ("bridge_c_pfaffian_darboux_linear_complex_note_vi", re.compile(r"Darboux.*(?:linear\s+complex|Kummer|Note\s+VI)", re.I | re.S)),
    ]
    missing = [name for name, pat in requirements if not pat.search(combined)]
    return {"passed": not missing, "checked_docs": checked, "missing": missing}


def check_dual_lake_targets(modules: Iterable[str]) -> dict[str, Any]:
    """Check that InfoGeometry modules are covered by lakefile.lean and check src/ presence for lakefile.src.lean."""
    lakefile = (REPO_ROOT / "lakefile.lean").read_text(encoding="utf-8", errors="replace")
    has_ig_submodules = ".andSubmodules `InfoGeometry" in lakefile
    missing_lean: list[str] = []
    missing_src: list[str] = []
    for mod in modules:
        rel_sub = Path(*mod.split(".")[1:]).with_suffix(".lean") if mod.startswith("InfoGeometry.") else Path(*mod.split(".")).with_suffix(".lean")
        if not (REPO_ROOT / "lean" / "InfoGeometry" / rel_sub).is_file():
            missing_lean.append(mod)
        if not (REPO_ROOT / "src" / "InfoGeometry" / rel_sub).is_file():
            missing_src.append(mod)
    return {
        "passed": has_ig_submodules and not missing_lean and not missing_src,
        "has_ig_submodules": has_ig_submodules,
        "missing_lean": missing_lean,
        "missing_src": missing_src,
    }
