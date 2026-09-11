import InfoGeometry.Clifford.OperatorValuedJonesProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite operator-valued polarization equivalence

For a finite internal index `W`, this is the explicit Kronecker realization of
the general causal-coordinate equivalence.  It upgrades an entrywise
reconstruction identity to a genuine equivalence and an explicit uniqueness
theorem.
-/

noncomputable section

namespace InfoGeometry.Optics.FiniteOperatorValuedPolarization

open InfoGeometry.Clifford

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Operators on the sheet-indexed finite carrier. -/
abbrev OperatorValuedMatrix (W : Type*) :=
  Matrix (Fin 2 × W) (Fin 2 × W) ℂ

/-- Regard a large sheet-indexed matrix as a `2 × 2` matrix of internal blocks. -/
def blockMatrixEquiv (W : Type*) :
    OperatorValuedMatrix W ≃ Matrix (Fin 2) (Fin 2) (Matrix W W ℂ) where
  toFun M i j a b := M (i, a) (j, b)
  invFun A ia jb := A ia.1 jb.1 ia.2 jb.2
  left_inv M := by
    ext ia jb
    rfl
  right_inv A := by
    ext i j a b
    rfl

/-- Four internal operator blocks are exactly one sheet-indexed operator. -/
def finiteOperatorPolarizationEquiv :
    CausalOperatorCoordinates (Matrix W W ℂ) ≃ OperatorValuedMatrix W :=
  (causalOperatorCoordinatesEquiv (B := Matrix W W ℂ)).trans
    (blockMatrixEquiv W).symm

/-- Extract the unique four operator-valued causal coordinates. -/
def operatorCoordinates (M : OperatorValuedMatrix W) :
    CausalOperatorCoordinates (Matrix W W ℂ) :=
  causalCoordinates (blockMatrixEquiv W M)

@[simp] theorem finiteOperatorPolarizationEquiv_symm_apply
    (M : OperatorValuedMatrix W) :
    (finiteOperatorPolarizationEquiv (W := W)).symm M =
      operatorCoordinates M :=
  rfl

/-- Exact reconstruction of every operator on the sheet-indexed carrier. -/
@[simp] theorem operator_valued_polarization
    (M : OperatorValuedMatrix W) :
    finiteOperatorPolarizationEquiv (operatorCoordinates M) = M :=
  (finiteOperatorPolarizationEquiv (W := W)).apply_symm_apply M

/-- The four internal blocks in the reconstruction are unique. -/
theorem operator_valued_polarization_unique
    (M : OperatorValuedMatrix W)
    (A : CausalOperatorCoordinates (Matrix W W ℂ))
    (hA : finiteOperatorPolarizationEquiv A = M) :
    A = operatorCoordinates M := by
  apply (finiteOperatorPolarizationEquiv (W := W)).injective
  rw [hA, operator_valued_polarization]

/-- Kronecker product with an internal operator block. -/
def kronecker
    (S : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix W W ℂ) :
    OperatorValuedMatrix W :=
  fun ia jb => S ia.1 jb.1 * A ia.2 jb.2

@[simp] theorem kronecker_apply
    (S : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix W W ℂ)
    (i j : Fin 2) (a b : W) :
    kronecker S A (i, a) (j, b) = S i j * A a b :=
  rfl

theorem kronecker_add_left
    (S T : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix W W ℂ) :
    kronecker (S + T) A = kronecker S A + kronecker T A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [kronecker, add_mul]

theorem kronecker_add_right
    (S : Matrix (Fin 2) (Fin 2) ℂ) (A B : Matrix W W ℂ) :
    kronecker S (A + B) = kronecker S A + kronecker S B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [kronecker, mul_add]

theorem kronecker_sheet_mul
    (S T : Matrix (Fin 2) (Fin 2) ℂ) :
    kronecker S (1 : Matrix W W ℂ) * kronecker T (1 : Matrix W W ℂ) =
      kronecker (S * T) (1 : Matrix W W ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [kronecker, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_ite_eq']

@[simp] theorem kronecker_identity :
    kronecker I_mat (1 : Matrix W W ℂ) = (1 : OperatorValuedMatrix W) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [kronecker, I_mat, Matrix.one_apply]

theorem kronecker_neg_left
    (S : Matrix (Fin 2) (Fin 2) ℂ) (A : Matrix W W ℂ) :
    kronecker (-S) A = -kronecker S A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [kronecker]

theorem kronecker_Gamma_sq :
    kronecker (Gamma_mat (B := ℂ)) (1 : Matrix W W ℂ) *
        kronecker (Gamma_mat (B := ℂ)) (1 : Matrix W W ℂ) =
      (1 : OperatorValuedMatrix W) := by
  rw [kronecker_sheet_mul, Gamma_sq, kronecker_identity]

theorem kronecker_J_sq :
    kronecker (J_mat (B := ℂ)) (1 : Matrix W W ℂ) *
        kronecker (J_mat (B := ℂ)) (1 : Matrix W W ℂ) =
      (1 : OperatorValuedMatrix W) := by
  rw [kronecker_sheet_mul, J_sq, kronecker_identity]

theorem kronecker_K_sq :
    kronecker (K_mat (B := ℂ)) (1 : Matrix W W ℂ) *
        kronecker (K_mat (B := ℂ)) (1 : Matrix W W ℂ) =
      -(1 : OperatorValuedMatrix W) := by
  rw [kronecker_sheet_mul, K_sq, kronecker_neg_left, kronecker_identity]

theorem kronecker_J_Gamma_anticomm :
    kronecker (J_mat (B := ℂ)) (1 : Matrix W W ℂ) *
        kronecker (Gamma_mat (B := ℂ)) (1 : Matrix W W ℂ) =
      -(kronecker (Gamma_mat (B := ℂ)) (1 : Matrix W W ℂ) *
        kronecker (J_mat (B := ℂ)) (1 : Matrix W W ℂ)) := by
  rw [kronecker_sheet_mul, kronecker_sheet_mul, J_Gamma]
  rw [kronecker_neg_left]

@[simp] theorem kronecker_identity_mul (M : OperatorValuedMatrix W) :
    kronecker I_mat (1 : Matrix W W ℂ) * M = M := by
  rw [kronecker_identity]
  exact one_mul M

@[simp] theorem kronecker_mul_identity (M : OperatorValuedMatrix W) :
    M * kronecker I_mat (1 : Matrix W W ℂ) = M := by
  rw [kronecker_identity]
  exact mul_one M

/-- The complex circular axis `-i ΓJ` used by `reconstruct_causal`. -/
def circularMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I) • K_mat

/-- The equivalence is the operator-valued Pauli/Dirac Kronecker expansion. -/
theorem finiteOperatorPolarizationEquiv_eq_kronecker
    (A : CausalOperatorCoordinates (Matrix W W ℂ)) :
    finiteOperatorPolarizationEquiv A =
      kronecker I_mat A.scalar +
      kronecker Gamma_mat A.chiral +
      kronecker J_mat A.exchange +
      kronecker circularMatrix A.circular := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [finiteOperatorPolarizationEquiv, blockMatrixEquiv,
      causalOperatorCoordinatesEquiv, reconstruct_causal, kronecker,
      I_mat, Gamma_mat, J_mat, circularMatrix, K_mat, Matrix.smul_apply,
      sub_eq_add_neg]

/-- Every sheet-indexed operator has the unique four-term Kronecker expansion. -/
theorem operator_valued_polarization_kronecker
    (M : OperatorValuedMatrix W) :
    M =
      kronecker I_mat (operatorCoordinates M).scalar +
      kronecker Gamma_mat (operatorCoordinates M).chiral +
      kronecker J_mat (operatorCoordinates M).exchange +
      kronecker circularMatrix (operatorCoordinates M).circular := by
  rw [← finiteOperatorPolarizationEquiv_eq_kronecker]
  exact (operator_valued_polarization M).symm

end InfoGeometry.Optics.FiniteOperatorValuedPolarization
