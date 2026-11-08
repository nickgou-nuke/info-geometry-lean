import InfoGeometry.Clifford.SolderingIsomorphism
import InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Twistor.Incidence

/-!
# Soldering CAR roots in the filtered GNS operator representation

The real split-soldering roots determine null vectors in `Vec22`.  Coefficient
extension sends those same matrices into the first complex matrix stage of the
Bernoulli/UHF tower.  The first-stage state GNS representation then sends the
roots to bounded operators on its GNS Hilbert space.  This file proves the root
identification and the CAR relations after both maps.

The statement is about this finite-stage embedding and its represented
operators. The concrete root spinors also define twistor incidences through
the finite soldering action; this does not identify twistor space with the GNS
Hilbert space or with a parabolic quotient.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

namespace InfoGeometry.Clifford.SolderingGNSCARBridge

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Clifford.SolderingIsomorphism
open InfoGeometry.Twistor.Incidence
open InfoGeometry.Projective.SplitQuaternionRankOneProjective
open InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open scoped ComplexOrder InnerProductSpace NNReal

abbrev RealMatrix2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev ComplexMatrix2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Entrywise extension of the real matrix coefficients to complex scalars. -/
def realMatrixToComplex : RealMatrix2 →+* ComplexMatrix2 :=
  Complex.ofRealHom.mapMatrix

/-- The complex first-stage image of the real raising CAR root. -/
def rootPlusGaugeStage : gaugeStage 1 :=
  CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootPlus)

/-- The complex first-stage image of the real lowering CAR root. -/
def rootMinusGaugeStage : gaugeStage 1 :=
  CStarMatrix.ofMatrixStarAlgEquiv (realMatrixToComplex rootMinus)

/-- The soldered null vector maps to the same complex matrix as the raising
CAR root. -/
theorem complexified_soldering_vecRootPlus :
    realMatrixToComplex (soldering vecRootPlus) =
      realMatrixToComplex rootPlus := by
  change realMatrixToComplex (soldering (solderingInv rootPlus)) = _
  exact congrArg realMatrixToComplex (soldering_solderingInv rootPlus)

/-- The soldered null vector maps to the same complex matrix as the lowering
CAR root. -/
theorem complexified_soldering_vecRootMinus :
    realMatrixToComplex (soldering vecRootMinus) =
      realMatrixToComplex rootMinus := by
  change realMatrixToComplex (soldering (solderingInv rootMinus)) = _
  exact congrArg realMatrixToComplex (soldering_solderingInv rootMinus)

/-- The raising CAR null vector and its nonzero spinor define an incident
twistor in the finite soldering model. -/
theorem vecRootPlus_incident_twistor :
    Incident (0, spinorPlus) vecRootPlus := by
  have hmatrix : soldering vecRootPlus = rootPlus := by
    change soldering (solderingInv rootPlus) = rootPlus
    exact soldering_solderingInv rootPlus
  have hact : InfoGeometry.Twistor.Incidence.pointAction
      vecRootPlus spinorPlus = 0 := by
    apply Prod.ext
    · change (soldering vecRootPlus) 0 0 * spinorPlus.1 +
        (soldering vecRootPlus) 0 1 * spinorPlus.2 = 0
      rw [hmatrix]
      exact rootPlus_spinor_annihilation.1
    · change (soldering vecRootPlus) 1 0 * spinorPlus.1 +
        (soldering vecRootPlus) 1 1 * spinorPlus.2 = 0
      rw [hmatrix]
      exact rootPlus_spinor_annihilation.2
  change (0 : ℝ × ℝ) =
    InfoGeometry.Twistor.Incidence.pointAction vecRootPlus spinorPlus
  exact hact.symm

/-- The lowering CAR null vector and its nonzero spinor define an incident
twistor in the finite soldering model. -/
theorem vecRootMinus_incident_twistor :
    Incident (0, spinorMinus) vecRootMinus := by
  have hmatrix : soldering vecRootMinus = rootMinus := by
    change soldering (solderingInv rootMinus) = rootMinus
    exact soldering_solderingInv rootMinus
  have hact : InfoGeometry.Twistor.Incidence.pointAction
      vecRootMinus spinorMinus = 0 := by
    apply Prod.ext
    · change (soldering vecRootMinus) 0 0 * spinorMinus.1 +
        (soldering vecRootMinus) 0 1 * spinorMinus.2 = 0
      rw [hmatrix]
      exact rootMinus_spinor_annihilation.1
    · change (soldering vecRootMinus) 1 0 * spinorMinus.1 +
        (soldering vecRootMinus) 1 1 * spinorMinus.2 = 0
      rw [hmatrix]
      exact rootMinus_spinor_annihilation.2
  change (0 : ℝ × ℝ) =
    InfoGeometry.Twistor.Incidence.pointAction vecRootMinus spinorMinus
  exact hact.symm

theorem realMatrixToComplex_rootPlus_sq :
    realMatrixToComplex rootPlus * realMatrixToComplex rootPlus = 0 := by
  rw [← realMatrixToComplex.map_mul, rootPlus_sq_zero]
  exact map_zero _

theorem realMatrixToComplex_rootMinus_sq :
    realMatrixToComplex rootMinus * realMatrixToComplex rootMinus = 0 := by
  rw [← realMatrixToComplex.map_mul, rootMinus_sq_zero]
  exact map_zero _

theorem realMatrixToComplex_root_anticommutator :
    realMatrixToComplex rootPlus * realMatrixToComplex rootMinus +
      realMatrixToComplex rootMinus * realMatrixToComplex rootPlus = 1 := by
  calc
    _ = realMatrixToComplex (rootPlus * rootMinus) +
        realMatrixToComplex (rootMinus * rootPlus) := by
          rw [← realMatrixToComplex.map_mul, ← realMatrixToComplex.map_mul]
    _ = realMatrixToComplex
        (rootPlus * rootMinus + rootMinus * rootPlus) := by
          rw [← realMatrixToComplex.map_add]
    _ = 1 := by rw [root_anticommutator]; exact map_one _

theorem rootPlusGaugeStage_sq :
    rootPlusGaugeStage * rootPlusGaugeStage = 0 := by
  simpa only [rootPlusGaugeStage, map_mul, map_zero] using
    congrArg CStarMatrix.ofMatrixStarAlgEquiv
      realMatrixToComplex_rootPlus_sq

theorem rootMinusGaugeStage_sq :
    rootMinusGaugeStage * rootMinusGaugeStage = 0 := by
  simpa only [rootMinusGaugeStage, map_mul, map_zero] using
    congrArg CStarMatrix.ofMatrixStarAlgEquiv
      realMatrixToComplex_rootMinus_sq

theorem rootGaugeStage_anticommutator :
    rootPlusGaugeStage * rootMinusGaugeStage +
      rootMinusGaugeStage * rootPlusGaugeStage = 1 := by
  simpa only [rootPlusGaugeStage, rootMinusGaugeStage,
    map_mul, map_add, map_one] using
    congrArg CStarMatrix.ofMatrixStarAlgEquiv
      realMatrixToComplex_root_anticommutator

/-- The native finite-stage GNS representation of the first gauge matrix
algebra as bounded operators on its GNS Hilbert space. -/
def gaugeStageGNSRepresentation :
    gaugeStage 1 →⋆ₐ[ℂ]
      (gaugeGNSStage 1 →L[ℂ] gaugeGNSStage 1) :=
  (gaugeStateFamily.state 1).functional.gnsStarAlgHom

/-- Represent the raising root on the native first-stage GNS Hilbert space. -/
def rootPlusGNSOperator : gaugeGNSStage 1 →L[ℂ] gaugeGNSStage 1 :=
  gaugeStageGNSRepresentation rootPlusGaugeStage

/-- Represent the lowering root on the native first-stage GNS Hilbert space. -/
def rootMinusGNSOperator : gaugeGNSStage 1 →L[ℂ] gaugeGNSStage 1 :=
  gaugeStageGNSRepresentation rootMinusGaugeStage

/-- The represented raising root remains square-zero. -/
theorem rootPlusGNSOperator_sq :
    rootPlusGNSOperator * rootPlusGNSOperator = 0 := by
  change (gaugeStateFamily.state 1).functional.gnsStarAlgHom
      rootPlusGaugeStage *
        (gaugeStateFamily.state 1).functional.gnsStarAlgHom
          rootPlusGaugeStage = 0
  rw [← map_mul, rootPlusGaugeStage_sq]
  exact map_zero _

/-- The represented lowering root remains square-zero. -/
theorem rootMinusGNSOperator_sq :
    rootMinusGNSOperator * rootMinusGNSOperator = 0 := by
  change (gaugeStateFamily.state 1).functional.gnsStarAlgHom
      rootMinusGaugeStage *
        (gaugeStateFamily.state 1).functional.gnsStarAlgHom
          rootMinusGaugeStage = 0
  rw [← map_mul, rootMinusGaugeStage_sq]
  exact map_zero _

/-- The soldered null roots satisfy CAR in the noncommutative bounded-operator
representation on the native first-stage GNS Hilbert space. -/
theorem rootGNSOperator_anticommutator :
    rootPlusGNSOperator * rootMinusGNSOperator +
      rootMinusGNSOperator * rootPlusGNSOperator = 1 := by
  change
    (gaugeStateFamily.state 1).functional.gnsStarAlgHom rootPlusGaugeStage *
        (gaugeStateFamily.state 1).functional.gnsStarAlgHom rootMinusGaugeStage +
      (gaugeStateFamily.state 1).functional.gnsStarAlgHom rootMinusGaugeStage *
        (gaugeStateFamily.state 1).functional.gnsStarAlgHom rootPlusGaugeStage = 1
  calc
    _ = (gaugeStateFamily.state 1).functional.gnsStarAlgHom
        (rootPlusGaugeStage * rootMinusGaugeStage +
          rootMinusGaugeStage * rootPlusGaugeStage) := by
          rw [map_add, map_mul, map_mul]
    _ = 1 := by rw [rootGaugeStage_anticommutator, map_one]

/-- First Peirce projector in the represented CAR algebra, built from the
raising and lowering operators on the finite-stage GNS Hilbert space. -/
def rootPlusGNSPeirceProjector : gaugeGNSStage 1 →L[ℂ] gaugeGNSStage 1 :=
  rootPlusGNSOperator * rootMinusGNSOperator

/-- Complementary Peirce projector in the represented CAR algebra. -/
def rootMinusGNSPeirceProjector : gaugeGNSStage 1 →L[ℂ] gaugeGNSStage 1 :=
  rootMinusGNSOperator * rootPlusGNSOperator

/-- The represented raising-lowering product is idempotent. -/
theorem rootPlusGNSPeirceProjector_idempotent :
    rootPlusGNSPeirceProjector * rootPlusGNSPeirceProjector =
      rootPlusGNSPeirceProjector := by
  have hpn : rootMinusGNSOperator * rootPlusGNSOperator =
      1 - rootPlusGNSOperator * rootMinusGNSOperator := by
    calc
      rootMinusGNSOperator * rootPlusGNSOperator =
          (rootPlusGNSOperator * rootMinusGNSOperator +
            rootMinusGNSOperator * rootPlusGNSOperator) -
              rootPlusGNSOperator * rootMinusGNSOperator := by noncomm_ring
      _ = 1 - rootPlusGNSOperator * rootMinusGNSOperator := by
        rw [rootGNSOperator_anticommutator]
  change (rootPlusGNSOperator * rootMinusGNSOperator) *
      (rootPlusGNSOperator * rootMinusGNSOperator) = _
  calc
    _ = rootPlusGNSOperator *
        (rootMinusGNSOperator * rootPlusGNSOperator) *
          rootMinusGNSOperator := by noncomm_ring
    _ = rootPlusGNSOperator *
        (1 - rootPlusGNSOperator * rootMinusGNSOperator) *
          rootMinusGNSOperator := by rw [hpn]
    _ = rootPlusGNSOperator * rootMinusGNSOperator := by
      noncomm_ring [rootPlusGNSOperator_sq, rootMinusGNSOperator_sq]

/-- The complementary represented product is idempotent. -/
theorem rootMinusGNSPeirceProjector_idempotent :
    rootMinusGNSPeirceProjector * rootMinusGNSPeirceProjector =
      rootMinusGNSPeirceProjector := by
  have hnp : rootPlusGNSOperator * rootMinusGNSOperator =
      1 - rootMinusGNSOperator * rootPlusGNSOperator := by
    calc
      rootPlusGNSOperator * rootMinusGNSOperator =
          (rootMinusGNSOperator * rootPlusGNSOperator +
            rootPlusGNSOperator * rootMinusGNSOperator) -
              rootMinusGNSOperator * rootPlusGNSOperator := by noncomm_ring
      _ = 1 - rootMinusGNSOperator * rootPlusGNSOperator := by
        rw [add_comm, rootGNSOperator_anticommutator]
  change (rootMinusGNSOperator * rootPlusGNSOperator) *
      (rootMinusGNSOperator * rootPlusGNSOperator) = _
  calc
    _ = rootMinusGNSOperator *
        (rootPlusGNSOperator * rootMinusGNSOperator) *
          rootPlusGNSOperator := by noncomm_ring
    _ = rootMinusGNSOperator *
        (1 - rootMinusGNSOperator * rootPlusGNSOperator) *
          rootPlusGNSOperator := by rw [hnp]
    _ = rootMinusGNSOperator * rootPlusGNSOperator := by
      noncomm_ring [rootPlusGNSOperator_sq, rootMinusGNSOperator_sq]

/-- The two represented Peirce projectors annihilate in either order. -/
theorem rootGNSPeirceProjectors_orthogonal :
    rootPlusGNSPeirceProjector * rootMinusGNSPeirceProjector = 0 ∧
    rootMinusGNSPeirceProjector * rootPlusGNSPeirceProjector = 0 := by
  constructor
  · change (rootPlusGNSOperator * rootMinusGNSOperator) *
      (rootMinusGNSOperator * rootPlusGNSOperator) = 0
    calc
      _ = rootPlusGNSOperator *
          (rootMinusGNSOperator * rootMinusGNSOperator) *
            rootPlusGNSOperator := by noncomm_ring
      _ = 0 := by rw [rootMinusGNSOperator_sq]; noncomm_ring
  · change (rootMinusGNSOperator * rootPlusGNSOperator) *
      (rootPlusGNSOperator * rootMinusGNSOperator) = 0
    calc
      _ = rootMinusGNSOperator *
          (rootPlusGNSOperator * rootPlusGNSOperator) *
            rootMinusGNSOperator := by noncomm_ring
      _ = 0 := by rw [rootPlusGNSOperator_sq]; noncomm_ring

/-- The two represented Peirce projectors resolve the identity on the
finite-stage GNS Hilbert space. -/
theorem rootGNSPeirceProjectors_resolve_identity :
    rootPlusGNSPeirceProjector + rootMinusGNSPeirceProjector = 1 :=
  rootGNSOperator_anticommutator

/-- The first represented Peirce projector is exactly the GNS image of the
corresponding product in the finite gauge matrix stage. -/
theorem rootPlusGNSPeirceProjector_eq_gns_image :
    rootPlusGNSPeirceProjector =
      gaugeStageGNSRepresentation
        (rootPlusGaugeStage * rootMinusGaugeStage) := by
  change gaugeStageGNSRepresentation rootPlusGaugeStage *
      gaugeStageGNSRepresentation rootMinusGaugeStage = _
  rw [map_mul]

/-- The complementary represented Peirce projector is exactly the GNS image
of the reversed product in the finite gauge matrix stage. -/
theorem rootMinusGNSPeirceProjector_eq_gns_image :
    rootMinusGNSPeirceProjector =
      gaugeStageGNSRepresentation
        (rootMinusGaugeStage * rootPlusGaugeStage) := by
  change gaugeStageGNSRepresentation rootMinusGaugeStage *
      gaugeStageGNSRepresentation rootPlusGaugeStage = _
  rw [map_mul]

/-- The global raising-root representation acts on the canonical inclusion
by the native first-stage GNS action. -/
theorem rootPlus_globalStage_action
    (x : gaugeGNSStage 1) :
    globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily 1 rootPlusGaugeStage
        (gaugeGNSStageToColimit 1 x) =
      gaugeGNSStageToColimit 1 (rootPlusGNSOperator x) := by
  change globalStageRepresentationStarAlgHom
      gaugeStage gaugeSystem gaugeStateFamily 1 rootPlusGaugeStage
      (gnsStageToHilbertColimit gaugeStage gaugeSystem gaugeStateFamily 1 x) =
    gnsStageToHilbertColimit gaugeStage gaugeSystem gaugeStateFamily 1
      ((gaugeStateFamily.state 1).functional.gnsStarAlgHom
        rootPlusGaugeStage x)
  rw [globalStageRepresentation_stage
    gaugeStage gaugeSystem gaugeStateFamily rootPlusGaugeStage
    ⟨1, le_rfl⟩ x]
  have hmap : gaugeSystem.map (le_refl 1) rootPlusGaugeStage =
      rootPlusGaugeStage := by
    exact congrArg (fun f => f rootPlusGaugeStage)
      (gaugeSystem.map_id 1)
  dsimp [CStarStateColimit.Native.FilteredGNSTailRepresentation.tailGNSOperator,
    CStarStateColimit.Native.FilteredGNSTailRepresentation.tailObservable]
  rw [hmap]
  rfl

/-- The global lowering-root representation acts on the canonical inclusion
by the native first-stage GNS action. -/
theorem rootMinus_globalStage_action
    (x : gaugeGNSStage 1) :
    globalStageRepresentationStarAlgHom
        gaugeStage gaugeSystem gaugeStateFamily 1 rootMinusGaugeStage
        (gaugeGNSStageToColimit 1 x) =
      gaugeGNSStageToColimit 1 (rootMinusGNSOperator x) := by
  change globalStageRepresentationStarAlgHom
      gaugeStage gaugeSystem gaugeStateFamily 1 rootMinusGaugeStage
      (gnsStageToHilbertColimit gaugeStage gaugeSystem gaugeStateFamily 1 x) =
    gnsStageToHilbertColimit gaugeStage gaugeSystem gaugeStateFamily 1
      ((gaugeStateFamily.state 1).functional.gnsStarAlgHom
        rootMinusGaugeStage x)
  rw [globalStageRepresentation_stage
    gaugeStage gaugeSystem gaugeStateFamily rootMinusGaugeStage
    ⟨1, le_rfl⟩ x]
  have hmap : gaugeSystem.map (le_refl 1) rootMinusGaugeStage =
      rootMinusGaugeStage := by
    exact congrArg (fun f => f rootMinusGaugeStage)
      (gaugeSystem.map_id 1)
  dsimp [CStarStateColimit.Native.FilteredGNSTailRepresentation.tailGNSOperator,
    CStarStateColimit.Native.FilteredGNSTailRepresentation.tailObservable]
  rw [hmap]
  rfl

end InfoGeometry.Clifford.SolderingGNSCARBridge
