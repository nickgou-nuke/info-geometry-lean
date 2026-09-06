import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.CuntzFractalHoppingAnyons
import InfoGeometry.Physics.Algebra.TripotentInvariantCarrierBridge

/-!
# Concrete finite braid/zero-mode audit

The four-state hopping braid has a distinguished fourth basis vector.  We use
the tripotent diagonal operator with eigenvalues `(1,1,1,0)` to make this
zero-mode carrier explicit.  Both adjacent transpositions preserve it and act
as the identity on it.  Thus this concrete carrier is braid-invariant but
cannot support a noncommutative restricted braid action; a larger carrier is
required for that capstone.
-/

noncomputable section

namespace InfoGeometry.Physics.TripotentFractalHorizonBridge

open InfoGeometry.Physics
open InfoGeometry.Physics.Algebra

abbrev Carrier := Fin 4 → ℝ
abbrev Op := Module.End ℝ Carrier

def horizonTripotentMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 0]

def horizonTripotent : Op := Matrix.mulVecLin horizonTripotentMatrix

def braid01 : Op := Matrix.mulVecLin braidSigma01
def braid12 : Op := Matrix.mulVecLin braidSigma12

theorem horizonTripotent_matrix_cube :
    horizonTripotentMatrix * horizonTripotentMatrix * horizonTripotentMatrix =
      horizonTripotentMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [horizonTripotentMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem horizonTripotent_tripotent : horizonTripotent ^ 3 = horizonTripotent := by
  apply LinearMap.ext
  intro x
  change Matrix.mulVec horizonTripotentMatrix
      (Matrix.mulVec horizonTripotentMatrix
        (Matrix.mulVec horizonTripotentMatrix x)) =
    Matrix.mulVec horizonTripotentMatrix x
  simpa [Matrix.mulVec_mulVec, mul_assoc] using
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => Matrix.mulVec M x)
      horizonTripotent_matrix_cube

theorem braid01_braid12_braid01 :
    braid01 * braid12 * braid01 = braid12 * braid01 * braid12 := by
  apply LinearMap.ext
  intro x
  change Matrix.mulVec braidSigma01
      (Matrix.mulVec braidSigma12 (Matrix.mulVec braidSigma01 x)) =
    Matrix.mulVec braidSigma12
      (Matrix.mulVec braidSigma01 (Matrix.mulVec braidSigma12 x))
  simpa [Matrix.mulVec_mulVec, mul_assoc] using
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => Matrix.mulVec M x)
      braidSigma01_braidSigma12_braidSigma01

theorem braid01_preserves_horizon :
    ∀ x, x ∈ zeroModeCarrier horizonTripotent →
      braid01 x ∈ zeroModeCarrier horizonTripotent := by
  intro x hx
  change horizonTripotent (braid01 x) = 0
  have hx0 : x 0 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 0
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx1 : x 1 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 1
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx2 : x 2 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 2
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  funext i
  fin_cases i <;>
    simp [braid01, braidSigma01, horizonTripotent, horizonTripotentMatrix,
      Matrix.mulVecLin, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hx0, hx1, hx2]

theorem braid12_preserves_horizon :
    ∀ x, x ∈ zeroModeCarrier horizonTripotent →
      braid12 x ∈ zeroModeCarrier horizonTripotent := by
  intro x hx
  change horizonTripotent (braid12 x) = 0
  have hx0 : x 0 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 0
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx1 : x 1 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 1
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx2 : x 2 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 2
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  funext i
  fin_cases i <;>
    simp [braid12, braidSigma12, horizonTripotent, horizonTripotentMatrix,
      Matrix.mulVecLin, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hx0, hx1, hx2]

theorem braid01_is_identity_on_horizon
    (x : Carrier) (hx : x ∈ zeroModeCarrier horizonTripotent) :
    braid01 x = x := by
  have hx0 : x 0 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 0
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx1 : x 1 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 1
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx2 : x 2 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 2
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  funext i
  fin_cases i <;>
    simp [braid01, braidSigma01, Matrix.mulVecLin, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, hx0, hx1, hx2]

theorem braid12_is_identity_on_horizon
    (x : Carrier) (hx : x ∈ zeroModeCarrier horizonTripotent) :
    braid12 x = x := by
  have hx0 : x 0 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 0
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx1 : x 1 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 1
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  have hx2 : x 2 = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp hx) 2
    simpa [horizonTripotent, Matrix.mulVecLin, horizonTripotentMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
  funext i
  fin_cases i <;>
    simp [braid12, braidSigma12, Matrix.mulVecLin, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, hx0, hx1, hx2]

/-- The concrete one-dimensional zero-mode carrier has no noncommutative
restricted braid action: both generators act as the identity there. -/
theorem braid_generators_commute_on_horizon
    (x : Carrier) (hx : x ∈ zeroModeCarrier horizonTripotent) :
    braid01 (braid12 x) = braid12 (braid01 x) := by
  calc
    braid01 (braid12 x) = braid01 x :=
      congrArg braid01 (braid12_is_identity_on_horizon x hx)
    _ = x := braid01_is_identity_on_horizon x hx
    _ = braid12 x := (braid12_is_identity_on_horizon x hx).symm
    _ = braid12 (braid01 x) :=
      congrArg braid12 (braid01_is_identity_on_horizon x hx).symm

end InfoGeometry.Physics.TripotentFractalHorizonBridge
