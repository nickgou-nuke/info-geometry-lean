/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCCRAndreevCancellation
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Real restriction of the finite CCR–CAR common carrier

The cutoff CCR defect and CAR mass act on one finite complex tensor carrier.
Restricting scalars gives a real operator representation of the same algebra.
This is the real-linear carrier bridge; it does not identify the complex-linear
image with the whole real endomorphism algebra.
-/

namespace InfoGeometry.Canonical.FiniteCCRRealRestrictionBridge

noncomputable section

open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Canonical.FARAndreevCancellation
open InfoGeometry.Physics
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

/-- Opposite matrix units in the exact real `Fin 32` carrier of the finite
CCR–CAR restriction. -/
def realStageFiveE01 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.single 0 1 1

def realStageFiveE10 : Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.single 1 0 1

/-- The represented real stage-five operator carrier is genuinely
noncommutative. -/
theorem realStageFive_noncommutative_witness :
    realStageFiveE01 * realStageFiveE10 ≠
      realStageFiveE10 * realStageFiveE01 := by
  intro h
  simp only [realStageFiveE01, realStageFiveE10] at h
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have h00 := congrArg (fun M : Matrix (Fin 32) (Fin 32) ℝ => M 0 0) h
  have hOne : (1 : ℝ) = 0 := by simpa [Matrix.single] using h00
  exact one_ne_zero hOne

/-- A complex-linear endomorphism of the finite common carrier, regarded as a
real-linear endomorphism of that same state space. -/
def restrictToReal : CutoffCAROperator →+* Module.End ℝ CutoffCARState where
  toFun T := T.restrictScalars ℝ
  map_one' := by
    ext x
    rfl
  map_mul' T S := by
    ext x
    rfl
  map_zero' := by
    ext x
    rfl
  map_add' T S := by
    ext x
    rfl

/-- The real restriction is faithful: equality of its real-linear actions is
already equality of the original complex-linear operators. -/
theorem restrictToReal_injective : Function.Injective restrictToReal := by
  intro T S h
  apply LinearMap.ext
  intro x
  exact congrFun (congrArg DFunLike.coe h) x

/-- The cutoff–CAR tensor state has 16 complex coordinates. -/
theorem cutoffCARState_complex_finrank : Module.finrank ℂ CutoffCARState = 16 := by
  rw [Module.finrank_tensorProduct]
  simp [CutoffState,
    InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.Fock4,
    InfoGeometry.Algebra.FiniteSpin.Vec4C]

/-- As a real carrier, the same state space has dimension 32. -/
theorem cutoffCARState_real_finrank : Module.finrank ℝ CutoffCARState = 32 := by
  calc
    Module.finrank ℝ CutoffCARState =
        2 * Module.finrank ℂ CutoffCARState := finrank_real_of_complex CutoffCARState
    _ = 32 := by rw [cutoffCARState_complex_finrank]

/-- Matrix coordinates for all real-linear operators on the actual
cutoff–CAR state carrier, using the repository's finite-basis convention. -/
noncomputable def cutoffCARStageFiveMatrixEquiv :
    Module.End ℝ CutoffCARState ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ := by
  letI : FiniteDimensional ℂ CutoffCARState := inferInstance
  letI : FiniteDimensional ℝ CutoffCARState := FiniteDimensional.trans ℝ ℂ CutoffCARState
  exact LinearMap.toMatrixAlgEquiv
    (Module.finBasisOfFinrankEq ℝ CutoffCARState cutoffCARState_real_finrank)

/-- Faithful finite matrix representation of the complex common-carrier
operators on the real 32-state carrier. -/
def cutoffCARStageFiveRepresentation :
    CutoffCAROperator →+* Matrix (Fin 32) (Fin 32) ℝ :=
  (cutoffCARStageFiveMatrixEquiv.toRingHom).comp restrictToReal

/-- The finite complex operator algebra embeds faithfully into the real
32-by-32 matrix algebra. -/
theorem cutoffCARStageFiveRepresentation_injective :
    Function.Injective cutoffCARStageFiveRepresentation := by
  intro T S h
  apply restrictToReal_injective
  apply cutoffCARStageFiveMatrixEquiv.injective
  exact h

/-- The finite CCR boundary defect remains a nonzero 32-by-32 real matrix. -/
theorem cutoffCARStageFiveBoundary_ne_zero :
    cutoffCARStageFiveRepresentation finiteCCRBoundary ≠ 0 := by
  intro h
  apply finiteCCRBoundary_ne_zero
  exact cutoffCARStageFiveRepresentation_injective (by simpa using h)

/-- Entrywise transport of the two-sector BdG algebra to real 32-by-32
matrices. -/
def cutoffCARBdGStageFiveRepresentation :
    BdGBlock CutoffCAROperator →+*
      BdGBlock (Matrix (Fin 32) (Fin 32) ℝ) where
  toFun H := H.map cutoffCARStageFiveRepresentation
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' H K := by
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' H K := by
    ext i j
    simp

/-- The nonzero CCR boundary survives as a nonzero Andreev-odd block matrix
in the real stage-five representation. -/
theorem cutoffCARStageFiveBoundaryHoleLift_ne_zero :
    cutoffCARBdGStageFiveRepresentation finiteCCRBoundaryHoleLift ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun H : BdGBlock (Matrix (Fin 32) (Fin 32) ℝ) => H 0 0) h
  have hentry : cutoffCARStageFiveRepresentation finiteCCRBoundary = 0 := by
    simpa [cutoffCARBdGStageFiveRepresentation,
      finiteCCRBoundaryHoleLift_eq_signed_blocks] using h00
  exact cutoffCARStageFiveBoundary_ne_zero hentry

/-- The complex-carrier Andreev cancellation transports to the actual
32-by-32 real matrix block representation. -/
theorem cutoffCARStageFive_andreev_cancellation :
    cutoffCARBdGStageFiveRepresentation
        (andreevSwap * finiteCCRBoundaryHoleLift * andreevSwap +
          finiteCCRBoundaryHoleLift) = 0 := by
  rw [andreev_hole_cancels_CCR_boundary_anomaly]
  exact map_zero cutoffCARBdGStageFiveRepresentation

/-- Apply scalar restriction entrywise to a BdG block over the complex
common-carrier operators. -/
def restrictBdGToReal :
    BdGBlock CutoffCAROperator →+* BdGBlock (Module.End ℝ CutoffCARState) where
  toFun H := H.map restrictToReal
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' H K := by
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' H K := by
    ext i j
    simp

/-- Entrywise restriction preserves block multiplication. -/
theorem restrictBdGToReal_mul (H K : BdGBlock CutoffCAROperator) :
    restrictBdGToReal (H * K) = restrictBdGToReal H * restrictBdGToReal K :=
  map_mul restrictBdGToReal H K

/-- The finite CCR boundary defect remains nonzero after real restriction. -/
theorem realCCRBoundary_ne_zero :
    restrictToReal finiteCCRBoundary ≠ 0 := by
  intro h
  apply finiteCCRBoundary_ne_zero
  apply restrictToReal_injective
  exact h

/-- The Andreev-odd boundary operator remains nonzero over the real carrier. -/
theorem realCCRBoundaryHoleLift_ne_zero :
    (!![restrictToReal finiteCCRBoundary, 0;
       0, -restrictToReal finiteCCRBoundary] :
        BdGBlock (Module.End ℝ CutoffCARState)) ≠ 0 := by
  intro h
  have h00 := congrArg (fun X : BdGBlock (Module.End ℝ CutoffCARState) => X 0 0) h
  exact realCCRBoundary_ne_zero (by simpa using h00)

/-- Andreev conjugation still cancels the real-restricted CCR boundary
contribution exactly. -/
theorem real_andreev_hole_cancels_CCR_boundary_anomaly :
    andreevSwap *
        (!![restrictToReal finiteCCRBoundary, 0;
           0, -restrictToReal finiteCCRBoundary] :
          BdGBlock (Module.End ℝ CutoffCARState)) * andreevSwap +
      !![restrictToReal finiteCCRBoundary, 0;
         0, -restrictToReal finiteCCRBoundary] = 0 := by
  rw [andreevSwap_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The same cancellation is the image of the already-proved complex
finite-carrier cancellation under the faithful real restriction. -/
theorem restrictBdGToReal_andreev_cancellation :
    restrictBdGToReal
        (andreevSwap * finiteCCRBoundaryHoleLift * andreevSwap +
          finiteCCRBoundaryHoleLift) = 0 := by
  rw [andreev_hole_cancels_CCR_boundary_anomaly]
  exact map_zero restrictBdGToReal

/-- The mass commutator generated by the real-restricted boundary term is the
restriction of the finite CAR mass interaction. -/
theorem realCCRBoundary_mass_commutator :
    (!![restrictToReal finiteCCRBoundary, 0;
       0, -restrictToReal finiteCCRBoundary] :
        BdGBlock (Module.End ℝ CutoffCARState)) *
        massiveBdGHamiltonian
          (restrictToReal finiteCARKinetic) (restrictToReal finiteCARMass) -
      massiveBdGHamiltonian
        (restrictToReal finiteCARKinetic) (restrictToReal finiteCARMass) *
        !![restrictToReal finiteCCRBoundary, 0;
           0, -restrictToReal finiteCCRBoundary] =
    (2 : ℤ) • !![0, restrictToReal (finiteCCRBoundary * finiteCARMass);
      -restrictToReal (finiteCCRBoundary * finiteCARMass), 0] := by
  have hK : restrictToReal finiteCCRBoundary * restrictToReal finiteCARKinetic =
      restrictToReal finiteCARKinetic * restrictToReal finiteCCRBoundary :=
    congrArg restrictToReal finiteCCRBoundary_commutes_with_CAR_mass_pair.1
  have hM : restrictToReal finiteCCRBoundary * restrictToReal finiteCARMass =
      restrictToReal finiteCARMass * restrictToReal finiteCCRBoundary :=
    congrArg restrictToReal finiteCCRBoundary_commutes_with_CAR_mass_pair.2
  have hBlock :
      (!![restrictToReal finiteCCRBoundary, 0;
         0, -restrictToReal finiteCCRBoundary] :
          BdGBlock (Module.End ℝ CutoffCARState)) =
        chiralGrading *
          (!![restrictToReal finiteCCRBoundary, 0;
             0, restrictToReal finiteCCRBoundary] :
            BdGBlock (Module.End ℝ CutoffCARState)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]
  have h := chiral_grading_twisted_mass_interaction
    (restrictToReal finiteCCRBoundary)
    (restrictToReal finiteCARKinetic)
    (restrictToReal finiteCARMass) hK hM
  rw [hBlock]
  simpa only [map_mul] using h

/-- Identify the real operator matrices from the finite CAR carrier with the
repository's established fifth matrix stage. -/
noncomputable def cutoffCARStageFiveStageEquiv :
    Module.End ℝ CutoffCARState ≃ₐ[ℝ] Stage 5 :=
  cutoffCARStageFiveMatrixEquiv.trans
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm

/-- The finite complex CAR operators act faithfully in the existing
stage-five matrix algebra. -/
def cutoffCARToStageFive : CutoffCAROperator →+* Stage 5 :=
  (cutoffCARStageFiveStageEquiv.toRingHom).comp restrictToReal

theorem cutoffCARToStageFive_injective : Function.Injective cutoffCARToStageFive := by
  intro T S h
  apply restrictToReal_injective
  apply cutoffCARStageFiveStageEquiv.injective
  exact h

/-- Entrywise transport of the finite BdG operators to the existing stage-five
algebra. -/
def cutoffCARBdGToStageFive :
    BdGBlock CutoffCAROperator →+* BdGBlock (Stage 5) where
  toFun H := H.map cutoffCARToStageFive
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' H K := by
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' H K := by
    ext i j
    simp

/-- The Andreev cancellation holds inside the repository's finite tower stage. -/
theorem stageFive_andreev_cancellation :
    cutoffCARBdGToStageFive
        (andreevSwap * finiteCCRBoundaryHoleLift * andreevSwap +
          finiteCCRBoundaryHoleLift) = 0 := by
  rw [andreev_hole_cancels_CCR_boundary_anomaly]
  exact map_zero cutoffCARBdGToStageFive

/-- Andreev cancellation commutes with the canonical stage-five embedding into
the existing inductive colimit. -/
def cutoffCARBdGToColimit :
    BdGBlock CutoffCAROperator →+* BdGBlock Limit where
  toFun H := (cutoffCARBdGToStageFive H).map (ofStage 5)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' H K := by
    ext i j
    simp [Matrix.mul_apply]
  map_zero' := by
    ext i j
    simp
  map_add' H K := by
    ext i j
    simp

theorem colimit_stageFive_andreev_cancellation :
    cutoffCARBdGToColimit
        (andreevSwap * finiteCCRBoundaryHoleLift * andreevSwap +
          finiteCCRBoundaryHoleLift) = 0 := by
  rw [andreev_hole_cancels_CCR_boundary_anomaly]
  exact map_zero cutoffCARBdGToColimit

/-- The finite CAR mass interaction remains an exact commutator identity after
transport through stage five and into the existing inductive colimit. -/
theorem colimit_stageFive_mass_commutator :
    cutoffCARBdGToColimit
        (finiteCCRBoundaryHoleLift *
          massiveBdGHamiltonian finiteCARKinetic finiteCARMass -
        massiveBdGHamiltonian finiteCARKinetic finiteCARMass *
          finiteCCRBoundaryHoleLift) =
      (2 : ℤ) • cutoffCARBdGToColimit
        (!![0, finiteCCRBoundary * finiteCARMass;
           -(finiteCCRBoundary * finiteCARMass), 0] :
          BdGBlock CutoffCAROperator) := by
  simpa only [map_sub, map_mul, map_zsmul, finiteCCRBoundaryHoleLift] using
    congrArg cutoffCARBdGToColimit finiteCCRBoundaryHoleLift_mass_commutator

end

end InfoGeometry.Canonical.FiniteCCRRealRestrictionBridge
