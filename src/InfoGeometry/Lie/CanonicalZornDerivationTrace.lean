import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Cocycle.MatrixDetExpTrace

/-!
# Trace-zero canonical split-octonion derivations

The parameter owner gives an explicit eight-coordinate formula for every
canonical derivation.  This file transports that formula to the standard
function-space basis and computes its trace directly.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationTrace

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivationDimension

abbrev VZ := ZornVectorMatrix ℝ
abbrev Coord8 := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev VDer8 := ZornVectorMatrix.Derivation (R := ℝ)

noncomputable def canonicalVectorLinearEquiv :
    InfoGeometry.Lie.CanonicalZornDerivation.CZ ≃ₗ[ℝ] VZ where
  toEquiv := canonicalVectorEquiv
  map_add' X Y := by
    exact canonicalVectorEquiv_add X Y
  map_smul' r X := by
    exact canonicalVectorEquiv_smul r X

def coordinateEquiv : VZ ≃ₗ[ℝ] Coord8 where
  toFun X := ![X.a, X.b, X.v 0, X.v 1, X.v 2, X.w 0, X.w 1, X.w 2]
  invFun f :=
    { a := f 0, b := f 1,
      v := ![f 2, f 3, f 4],
      w := ![f 5, f 6, f 7] }
  left_inv X := by
    cases X with
    | mk a v w b =>
      apply ZornVectorMatrix.ext
      · rfl
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i <;> rfl
      · rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl
  map_add' X Y := by
    funext i
    fin_cases i <;> rfl
  map_smul' r X := by
    funext i
    fin_cases i <;> rfl

def derivationToLinearMap (D : VDer8) : Module.End ℝ VZ where
  toFun := D
  map_add' := D.map_add
  map_smul' := D.map_smul

private def coordinateAction (p : Params) : Module.End ℝ Coord8 :=
  (coordinateEquiv : VZ ≃ₗ[ℝ] Coord8).conj
    (derivationToLinearMap (parameterDerivation p))

theorem parameterDerivation_trace_zero (p : Params) :
    LinearMap.trace ℝ VZ (derivationToLinearMap (parameterDerivation p)) = 0 := by
  rw [← LinearMap.trace_conj' (derivationToLinearMap (parameterDerivation p))
    coordinateEquiv]
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 8))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Pi.basisFun_repr,
    coordinateAction, derivationToLinearMap, parameterDerivation, parameterAction,
    coordinateEquiv, ZornVectorMatrix.add, ZornVectorMatrix.smul,
    Fin.sum_univ_succ]
  ring

theorem canonicalZornDerivation_trace_zero
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) :
    LinearMap.trace ℝ (InfoGeometry.Lie.CanonicalZornDerivation.CZ) D.1 = 0 := by
  let Dv := InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation D
  have hconj :
      (canonicalVectorLinearEquiv.conj D.1) =
        derivationToLinearMap Dv := by
    apply LinearMap.ext
    intro X
    rfl
  rw [← LinearMap.trace_conj' D.1 canonicalVectorLinearEquiv]
  rw [hconj]
  have hp := parameterDerivation_trace_zero
    (InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters Dv)
  have hparam :
      parameterDerivation (derivationParameters Dv) = Dv := by
    change parameterLinearEquiv (parameterLinearEquiv.symm Dv) = Dv
    exact parameterLinearEquiv.right_inv Dv
  have hparam' := congrArg derivationToLinearMap hparam
  rw [hparam'] at hp
  exact hp

def canonicalDerivationMatrix
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (coordinateEquiv.conj (canonicalVectorLinearEquiv.conj D.1))

theorem canonicalDerivationMatrix_trace_zero
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) :
    Matrix.trace (canonicalDerivationMatrix D) = 0 := by
  unfold canonicalDerivationMatrix
  rw [← LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 8))]
  rw [LinearMap.trace_conj'
    (canonicalVectorLinearEquiv.conj D.1) coordinateEquiv]
  rw [LinearMap.trace_conj' D.1 canonicalVectorLinearEquiv]
  exact canonicalZornDerivation_trace_zero D

theorem canonicalDerivationMatrix_exponential_det_one
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations)
    (t : ℝ) :
    Matrix.det (NormedSpace.exp (t • canonicalDerivationMatrix D)) = 1 := by
  rw [InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace_real]
  rw [Matrix.trace_smul, canonicalDerivationMatrix_trace_zero, _root_.smul_zero]
  simp

end InfoGeometry.Lie.CanonicalZornDerivationTrace
