/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import InfoGeometry.Canonical.CuntzGNSFilteredSystem
import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
import InfoGeometry.OperatorAlgebra.Candidates.RectangularHomotopyCoercivity
import Mathlib.Analysis.InnerProductSpace.StandardSubspace

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 5000000

/-!
# A two-term CAR complex on the global trace-GNS Hilbert space

The stage-five CAR Majorana mass is an involution in the finite real matrix
algebra. Coherent complexification, the C⋆ matrix realization, and the native
global GNS stage representation carry it to a bounded involution on the
completed trace-GNS Hilbert colimit. Thus it supplies an actual bounded
rectangular left-inverse pair there.

The total differential is the off-diagonal block of this represented
involution, so it is square-zero and the two-term complex is contractible.
This proves vanishing algebraic cohomology for this specific complex; it does
not identify a physical vacuum sector or prove a vacuum mass gap.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open ClosedSubmodule

namespace InfoGeometry.Canonical.Cl11CARMassHilbertHomotopy

open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Clifford.Cl11TensorTower
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.OperatorAlgebra.Candidates.RectangularHomotopyCoercivity

local instance cstarMatrixStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance cstarMatrixStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The completed global Hilbert carrier of the concrete normalized-trace
matrix tower. This is the same carrier used by the existing finite-stage
trace-GNS bridge, constructed directly from its defining tower and state
family. -/
abbrev CuntzMatrixTraceHilbertColimit : Type :=
  GNSHilbertColimit CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily

/-- The finite CAR mass represented in the native complex C⋆ matrix algebra
at tower stage five. -/
def carMassStageFiveCStarMatrixHom : MatStage 5 →+* CStarMatrixStage 5 :=
  (CStarMatrix.ofMatrixStarAlgEquiv.toRingEquiv.toRingHom).comp
    (coherentComplexifyClStage 5).toRingHom

def carMassStageFiveCStarMatrix : CStarMatrixStage 5 :=
  carMassStageFiveCStarMatrixHom carMassOperator

/-- The C⋆ matrix realization preserves the CAR mass involution identity. -/
theorem carMassStageFiveCStarMatrix_square :
    carMassStageFiveCStarMatrix * carMassStageFiveCStarMatrix = 1 := by
  change carMassStageFiveCStarMatrixHom carMassOperator *
      carMassStageFiveCStarMatrixHom carMassOperator = 1
  calc
    _ = carMassStageFiveCStarMatrixHom
        (carMassOperator * carMassOperator) :=
          (map_mul carMassStageFiveCStarMatrixHom carMassOperator
            carMassOperator).symm
    _ = carMassStageFiveCStarMatrixHom 1 := by
      rw [carMassOperator_square_eq_one]
    _ = 1 := map_one carMassStageFiveCStarMatrixHom

/-- The concrete CAR mass acts as a bounded operator on the completed global
trace-GNS Hilbert colimit. -/
def carMassStageFiveGNSRepresentation :
    CStarMatrixStage 5 →⋆ₐ[ℂ]
    CuntzMatrixTraceHilbertColimit →L[ℂ]
      CuntzMatrixTraceHilbertColimit :=
  globalStageRepresentationStarAlgHom CStarMatrixStage
    cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 5

def carMassGNSOperator :
    CuntzMatrixTraceHilbertColimit →L[ℂ]
      CuntzMatrixTraceHilbertColimit :=
  carMassStageFiveGNSRepresentation carMassStageFiveCStarMatrix

/-- Realification of the represented CAR operator. -/
def carMassGNSOperatorReal :
    CuntzMatrixTraceHilbertColimit →L[ℝ]
      CuntzMatrixTraceHilbertColimit :=
  carMassGNSOperator.restrictScalars ℝ

/-- The genuine two-degree Hilbert carrier on which the CAR operator is an
off-diagonal differential. -/
abbrev CARMassBRSTPair := Pair
  (H₀ := CuntzMatrixTraceHilbertColimit)
  (H₁ := CuntzMatrixTraceHilbertColimit)

/-- Degree-raising block of the two-term complex. -/
def carMassHilbertDifferential : CARMassBRSTPair →L[ℝ] CARMassBRSTPair :=
  differential carMassGNSOperatorReal

/-- Degree-lowering block on the two-term complex. -/
def carMassHilbertHomotopy : CARMassBRSTPair →L[ℝ] CARMassBRSTPair :=
  homotopy carMassGNSOperatorReal

/-- The represented CAR mass remains an involution on each vector of the
completed GNS Hilbert space. -/
theorem carMassGNSOperator_apply_square
    (ψ : CuntzMatrixTraceHilbertColimit) :
    carMassGNSOperator (carMassGNSOperator ψ) = ψ := by
  change globalStageRepresentationStarAlgHom CStarMatrixStage
      cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 5
      carMassStageFiveCStarMatrix
      (globalStageRepresentationStarAlgHom CStarMatrixStage
        cstarMatrixInductiveSystem cstarMatrixTraceStateFamily 5
        carMassStageFiveCStarMatrix ψ) = ψ
  rw [← globalStageRepresentation_mul_apply]
  rw [carMassStageFiveCStarMatrix_square]
  exact globalStageRepresentation_one_apply CStarMatrixStage
    cstarMatrixInductiveSystem cstarMatrixTraceStateFamily ψ

/-- Realification preserves the involution relation. -/
theorem carMassGNSOperatorReal_square :
    carMassGNSOperatorReal.comp carMassGNSOperatorReal = 1 := by
  ext ψ
  exact carMassGNSOperator_apply_square ψ

/-- The total differential is square-zero because it is an off-diagonal
degree-raising block. -/
theorem carMassHilbertDifferential_sq_zero :
    carMassHilbertDifferential.comp carMassHilbertDifferential = 0 :=
  differential_sq_zero carMassGNSOperatorReal

/-- The degree-lowering block is square-zero for the same block reason. -/
theorem carMassHilbertHomotopy_sq_zero :
    carMassHilbertHomotopy.comp carMassHilbertHomotopy = 0 :=
  homotopy_sq_zero carMassGNSOperatorReal

/-- The two-term complex is contractible: the differential and lowering
homotopy have identity anticommutator. -/
theorem carMassHilbert_contracting_identity :
    carMassHilbertDifferential * carMassHilbertHomotopy +
      carMassHilbertHomotopy * carMassHilbertDifferential = 1 := by
  have hcontract := contracting_identity
    carMassGNSOperatorReal carMassGNSOperatorReal 0 (by
      simpa using carMassGNSOperatorReal_square)
  have hprojection := totalProjection_eq_zero_of_right_inverse
    carMassGNSOperatorReal carMassGNSOperatorReal
    (by simpa using carMassGNSOperatorReal_square)
  rw [hprojection, sub_zero] at hcontract
  simpa [carMassHilbertDifferential, carMassHilbertHomotopy] using hcontract

/-- Every closed vector in this two-term complex is exact. The witness is the
lowering homotopy applied to the closed vector. -/
theorem carMassHilbert_exact (x : CARMassBRSTPair)
    (hx : carMassHilbertDifferential x = 0) :
    ∃ y, carMassHilbertDifferential y = x := by
  refine ⟨carMassHilbertHomotopy x, ?_⟩
  have h := congrArg (fun T : CARMassBRSTPair →L[ℝ] CARMassBRSTPair => T x)
    carMassHilbert_contracting_identity
  simpa [add_apply, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hx]
    using h

/-- Algebraic cohomology of the represented two-term CAR complex. -/
def carMassBRSTCohomology :=
  LinearMap.ker carMassHilbertDifferential.toLinearMap ⧸
    (LinearMap.range carMassHilbertDifferential.toLinearMap).comap
      (LinearMap.ker carMassHilbertDifferential.toLinearMap).subtype

/-- The cohomology quotient vanishes: every closed representative is in the
range, by the explicit contracting homotopy. -/
theorem carMassBRSTCohomology_class_eq_zero
    (x : LinearMap.ker carMassHilbertDifferential.toLinearMap) :
    (Submodule.Quotient.mk x : carMassBRSTCohomology) =
      Submodule.Quotient.mk 0 := by
  rw [Submodule.Quotient.eq, sub_zero, Submodule.mem_comap,
    LinearMap.mem_range]
  obtain ⟨y, hy⟩ := carMassHilbert_exact x.1 x.2
  exact ⟨y, hy⟩

/-- The represented two-term CAR complex has zero algebraic cohomology. -/
theorem carMassBRSTCohomology_subsingleton :
    Subsingleton carMassBRSTCohomology := by
  refine ⟨?_⟩
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  calc
    (Submodule.Quotient.mk a : carMassBRSTCohomology) =
        Submodule.Quotient.mk 0 := carMassBRSTCohomology_class_eq_zero a
    _ = Submodule.Quotient.mk b :=
      (carMassBRSTCohomology_class_eq_zero b).symm

/-- Every vector in the real Hilbert space underlying the complex GNS colimit
obeys the lower estimate for the represented CAR involution. The constant is
explicit in its operator norm. -/
theorem carMassHilbert_left_inverse_coercivity
    (ψ : CuntzMatrixTraceHilbertColimit) :
    (1 / (‖carMassGNSOperatorReal‖ + 1) ^ 2) * ‖ψ‖ ^ 2 ≤
      ‖carMassGNSOperatorReal ψ‖ ^ 2 := by
  let C : ℝ := ‖carMassGNSOperatorReal‖ + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hbound : ‖carMassGNSOperatorReal‖ ≤ C := by
    change ‖carMassGNSOperatorReal‖ ≤ ‖carMassGNSOperatorReal‖ + 1
    exact le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 from zero_le_one)
  have hhd : carMassGNSOperatorReal.comp carMassGNSOperatorReal =
        1 - (0 : CuntzMatrixTraceHilbertColimit →L[ℝ]
          CuntzMatrixTraceHilbertColimit) := by
    simpa using carMassGNSOperatorReal_square
  have hP : (0 : CuntzMatrixTraceHilbertColimit →L[ℝ]
      CuntzMatrixTraceHilbertColimit) ψ = 0 := by simp
  simpa [C] using
    (rectangular_left_inverse_coercivity
      (d₀ := carMassGNSOperatorReal)
      (h₁ := carMassGNSOperatorReal)
      (P := 0) hhd hC hbound ψ hP)

end InfoGeometry.Canonical.Cl11CARMassHilbertHomotopy

end
