import Mathlib
import proofs.OperatorQGTSoldering
import InfoGeometry.Canonical.SplitOctonionChiralSoldering
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv

noncomputable section

namespace InfoGeometry.Unified

open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Canonical

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Module ℚ W]

/-- A chiral QGT state together with the explicit projection compatibility that
defines the intended split-octonion reduction. -/
structure UnifiedChiralGeometricState where
  chiralSolderingOperator : Module.End ℚ StandardRationalSplitOctonion
  qgtConnection : QGTFourVector W
  chiralProjection : (Fin 2 → W) →ₗ[ℚ] StandardRationalSplitOctonion
  intertwining : ∀ ψ : Fin 2 → W,
    chiralProjection (QGTSoldering qgtConnection ψ) =
      chiralSolderingOperator (chiralProjection ψ)

/-- Constructs the geometric tensor connection for a scalar action. -/
def qgtFromScalar (q : ℚ) : QGTFourVector W where
  symmetricBKM
  | 0 => algebraMap ℚ (Module.End ℂ W) q
  | 1 => 0
  | 2 => 0
  | 3 => 0
  antisymmetricBerry := 0

/-- A genuine constructive realization of the chiral QGT state for the scalar sector.
Given any structural chiral projection, the scaled left-multiplication action of the
split-octonion skeleton exactly matches the scaled QGT connection. -/
def genuineChiralGeometricState (q : ℚ)
    (proj : (Fin 2 → W) →ₗ[ℚ] StandardRationalSplitOctonion) :
    UnifiedChiralGeometricState (W := W) where
  chiralSolderingOperator := chiralSoldering (q • rationalBasis .one)
  qgtConnection := qgtFromScalar (W := W) q
  chiralProjection := proj
  intertwining := by
    intro ψ
    dsimp [QGTSoldering, operatorSolderingAction, qgtFromScalar]
    simp only [add_zero, sub_zero, smul_zero]
    have h : Optics.OperatorLiftCarrier.matrixAction
      !![algebraMap ℚ (Module.End ℂ W) q, 0;
         0, algebraMap ℚ (Module.End ℂ W) q] ψ = q • ψ := by
      ext i
      fin_cases i <;>
      · dsimp [Optics.OperatorLiftCarrier.matrixAction, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply, add_zero, zero_add, Module.algebraMap_end_apply]
    rw [h]
    rw [LinearMap.map_smul]
    have h2 : chiralSoldering (q • rationalBasis .one) (proj ψ) = q • proj ψ := by
      simp [chiralSoldering, splitOctonionMulQ, chiralLeftSoldering]
      ext idx
      fin_cases idx <;>
      · simp [splitOctonionOfQuaternionPairQ, splitQuaternionAddQ, splitQuaternionMulQ, splitQuaternionConjQ, splitQuaternionOfQ, splitQuaternionLPartQ, rationalBasis, Pi.smul_apply, smul_eq_mul]
        try ring
    rw [h2]
theorem split_octonion_qgt_intertwining
    (state : UnifiedChiralGeometricState (W := W))
    (ψ : Fin 2 → W) :
    state.chiralProjection (QGTSoldering state.qgtConnection ψ) =
      state.chiralSolderingOperator (state.chiralProjection ψ) :=
  state.intertwining ψ

end InfoGeometry.Unified
