import Mathlib.Tactic

import InfoGeometry.Canonical.Cl11LeftRightDoubleBridge
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Native bipartite Cl(1,1) composite Dirac operator

This module ports the finite algebraic content of the bipartite composite
operator

  D_tot = D_L ⊗ β_R + I_L ⊗ D_R

onto the repository-owned Cl(1,1) matrix atom and stage-two tensor carrier.

Proved here:

* exact square expansion;
* decoupling when β_R² = I and {β_R,D_R}=0;
* the standard off-diagonal Dirac anticommutes with β = diag(1,-1);
* finite Krein-adjoint compatibility under β_L ⊗ β_R;
* tensor-factor swap sends A ⊗ B to B ⊗ A and therefore reflects D_tot.

These are finite matrix identities.  They are not, by themselves, a
formalization of the analytic Baaj--Julg theorem, Tomita--Takesaki theory, or
an unbounded Kasparov product.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11BipartiteDiracBridge

open scoped Matrix Kronecker
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.Cl11LeftRightDoubleBridge

abbrev Atom := Mat2
abbrev StageTwo := MatStage 2

/-- Composite bipartite Dirac operator on the native two-site carrier. -/
def compositeDirac (DL betaR DR : Atom) : StageTwo :=
  DL ⊗ₖ betaR + (1 : Atom) ⊗ₖ DR

/-- Exact algebraic square expansion of the bipartite composite operator. -/
theorem compositeDirac_sq_expansion (DL betaR DR : Atom) :
    compositeDirac DL betaR DR * compositeDirac DL betaR DR =
      (DL * DL) ⊗ₖ (betaR * betaR) +
      DL ⊗ₖ (betaR * DR + DR * betaR) +
      (1 : Atom) ⊗ₖ (DR * DR) := by
  unfold compositeDirac
  rw [add_mul, mul_add, mul_add]
  simp only [Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.kronecker_add]
  abel

/-- If the right grading is involutive and the right Dirac operator is odd,
the mixed term vanishes. -/
theorem compositeDirac_sq_decoupled
    (DL betaR DR : Atom)
    (hbeta : betaR * betaR = 1)
    (hodd : betaR * DR + DR * betaR = 0) :
    compositeDirac DL betaR DR * compositeDirac DL betaR DR =
      (DL * DL) ⊗ₖ (1 : Atom) +
      (1 : Atom) ⊗ₖ (DR * DR) := by
  rw [compositeDirac_sq_expansion, hbeta, hodd]
  simp

/-- Standard split fundamental symmetry β = diag(1,-1). -/
def kreinBeta : Atom :=
  Eplus

/-- Generic off-diagonal 2×2 Dirac matrix. -/
def offDiagonalDirac (v w : ℝ) : Atom :=
  !![(0 : ℝ), v; w, 0]

@[simp] theorem kreinBeta_sq :
    kreinBeta * kreinBeta = (1 : Atom) := by
  simpa [kreinBeta] using Eplus_sq

@[simp] theorem kreinBeta_transpose :
    kreinBetaᵀ = kreinBeta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinBeta, Eplus, Matrix.transpose_apply]

/-- Every off-diagonal Dirac matrix anticommutes with the split grading. -/
theorem offDiagonalDirac_anticomm_kreinBeta (v w : ℝ) :
    kreinBeta * offDiagonalDirac v w +
      offDiagonalDirac v w * kreinBeta = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinBeta, Eplus, offDiagonalDirac,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete decoupling for the native off-diagonal right Dirac sector. -/
theorem compositeDirac_chiral_decoupled
    (DL : Atom) (v w : ℝ) :
    compositeDirac DL kreinBeta (offDiagonalDirac v w) *
        compositeDirac DL kreinBeta (offDiagonalDirac v w) =
      (DL * DL) ⊗ₖ (1 : Atom) +
      (1 : Atom) ⊗ₖ
        (offDiagonalDirac v w * offDiagonalDirac v w) := by
  apply compositeDirac_sq_decoupled
  · exact kreinBeta_sq
  · exact offDiagonalDirac_anticomm_kreinBeta v w

/-- Total fundamental symmetry β_L ⊗ β_R. -/
def totalBeta (betaL betaR : Atom) : StageTwo :=
  betaL ⊗ₖ betaR

/-- Transpose of the native composite operator. -/
theorem compositeDirac_transpose (DL betaR DR : Atom) :
    (compositeDirac DL betaR DR)ᵀ =
      DLᵀ ⊗ₖ betaRᵀ + (1 : Atom) ⊗ₖ DRᵀ := by
  simp [compositeDirac, TowerMatrix.transpose_kronecker]

/-- Finite Krein-adjoint compatibility of the composite operator. -/
theorem compositeDirac_krein_self_adjoint
    (DL betaL DR betaR : Atom)
    (hSymmR : betaRᵀ = betaR)
    (hSqR : betaR * betaR = 1)
    (hAdjL : betaL * DLᵀ = DL * betaL)
    (hAdjR : betaR * DRᵀ = DR * betaR) :
    totalBeta betaL betaR * (compositeDirac DL betaR DR)ᵀ =
      compositeDirac DL betaR DR * totalBeta betaL betaR := by
  rw [compositeDirac_transpose]
  unfold totalBeta compositeDirac
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hSymmR, hAdjL, hAdjR, hSqR]
  simp

/-! ## Tensor-factor reflection -/

/-- Swap the two binary tensor coordinates in the native stage-two index. -/
def swapStageTwoIndex :
    InfoGeometry.Clifford.TowerMatrix.Idx 2 →
      InfoGeometry.Clifford.TowerMatrix.Idx 2
  | ((u, i), j) => ((u, j), i)

/-- Tensor-factor swap on stage-two matrices. -/
def tensorSwap (M : StageTwo) : StageTwo :=
  M.submatrix swapStageTwoIndex swapStageTwoIndex

@[simp] theorem swapStageTwoIndex_involutive (x : InfoGeometry.Clifford.TowerMatrix.Idx 2) :
    swapStageTwoIndex (swapStageTwoIndex x) = x := by
  rcases x with ⟨⟨u, i⟩, j⟩
  rfl

/-- Tensor swap exchanges elementary Kronecker tensors. -/
theorem tensorSwap_kronecker (A B : Atom) :
    tensorSwap (A ⊗ₖ B) = B ⊗ₖ A := by
  ext x y
  rcases x with ⟨⟨ux, ix⟩, jx⟩
  rcases y with ⟨⟨uy, iy⟩, jy⟩
  have hux : ux = uy := Subsingleton.elim _ _
  subst uy
  rfl

/-- Tensor swap is involutive. -/
theorem tensorSwap_involutive :
    Function.Involutive tensorSwap := by
  intro M
  ext x y
  simp [tensorSwap, swapStageTwoIndex_involutive]

/-- Tensor swap reflects the composite operator into the opposite ordering. -/
theorem tensorSwap_compositeDirac (DL betaR DR : Atom) :
    tensorSwap (compositeDirac DL betaR DR) =
      betaR ⊗ₖ DL + DR ⊗ₖ (1 : Atom) := by
  unfold compositeDirac tensorSwap
  ext x y
  rcases x with ⟨⟨ux, ix⟩, jx⟩
  rcases y with ⟨⟨uy, iy⟩, jy⟩
  have hux : ux = uy := Subsingleton.elim _ _
  subst uy
  simp [swapStageTwoIndex, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  ring

end InfoGeometry.Canonical.Cl11BipartiteDiracBridge
