import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Prequantum.AlgebraicGNSState
import InfoGeometry.Meta.MarkovJonesInduction

/-!
# Real algebraic GNS input for the matrix trace tower

The complex normalized trace is converted to its real part on the underlying
real *-algebra.  Positivity is inherited from the matrix `Tr(A* A)` identity;
no order on the complex matrix carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Meta.MarkovJonesInduction

def matrixTraceRealLinearMap (n : ℕ) : MatrixStage n →ₗ[ℝ] ℝ where
  toFun A := (matrixTraceFunctional n A).re
  map_add' A B := by
    simp only [map_add, Complex.add_re]

  map_smul' c A := by
    change ((matrixTraceFunctional n ((c : ℂ) • A)).re) = _
    rw [map_smul]
    simp [Complex.mul_re]

@[simp] theorem matrixTraceRealLinearMap_apply (n : ℕ) (A : MatrixStage n) :
    matrixTraceRealLinearMap n A = (matrixTraceFunctional n A).re :=
  rfl

def matrixTraceRealAlgebraicState (n : ℕ) :
    RealAlgebraicState (MatrixStage n) where
  toLinearMap := matrixTraceRealLinearMap n
  normalized := by
    rw [matrixTraceRealLinearMap_apply]
    have h := congrArg Complex.re (matrixTraceState_one n)
    simpa only [matrixTraceState] using h
  positive := by
    intro A
    rw [matrixTraceRealLinearMap_apply]
    exact matrixTraceState_nonneg n A
  symmetric := by
    intro A B
    rw [matrixTraceRealLinearMap_apply, matrixTraceRealLinearMap_apply]
    rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
    have htrace : Matrix.trace (star B * A) =
        star (Matrix.trace (star A * B)) := by
      rw [← Matrix.trace_conjTranspose]
      congr 1
      simp [star]
    rw [htrace]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hcoef : (1 / (2 ^ n : ℂ)).im = 0 := by
      have hcast : (1 / (2 ^ n : ℂ)) =
          ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast, Complex.ofReal_im]
    rw [hcoef]
    ring

@[simp] theorem matrixTraceRealAlgebraicState_eval (n : ℕ) (A : MatrixStage n) :
    (matrixTraceRealAlgebraicState n).eval A =
      (matrixTraceFunctional n A).re :=
  rfl

theorem matrixTraceRealAlgebraicState_positive (n : ℕ) (A : MatrixStage n) :
    0 ≤ (matrixTraceRealAlgebraicState n).eval (star A * A) :=
  (matrixTraceRealAlgebraicState n).positive A

def realInductiveNet (T : Data) :
    InductiveAlgebraNet (𝕜 := ℝ) (A := MatrixStage) :=
  fun n => (T n).toAlgHom.restrictScalars ℝ

def realTraceNet (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A) :
    MarkovTraceNet (realInductiveNet T) where
  trace := matrixTraceRealLinearMap
  trace_one := by
    intro n
    exact (matrixTraceRealAlgebraicState n).normalized
  trace_stable := by
    intro n A
    rw [matrixTraceRealLinearMap_apply, matrixTraceRealLinearMap_apply]
    have h := congrArg Complex.re (hT n A)
    simpa [matrixTraceState] using h

def compatibleRealStateNet (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A) :
    CompatibleAlgebraicStateNet (realInductiveNet T) :=
  CompatibleAlgebraicStateNet.ofMarkovTraceNet
    (realTraceNet T hT) (by
      intro n A
      exact matrixTraceState_nonneg n A)

theorem compatibleRealStateNet_state (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ) (A : MatrixStage n) :
    (compatibleRealStateNet T hT).state n A =
      (matrixTraceRealAlgebraicState n).toLinearMap A :=
  rfl

end InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
