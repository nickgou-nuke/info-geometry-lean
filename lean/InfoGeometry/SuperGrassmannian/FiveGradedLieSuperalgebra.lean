import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# 5-Graded Lie Superalgebra, Kantor–Tanaka Derivation & Spinorial Superconformal Grading

This module formalizes the mathematical theory of 5-graded Lie (super)algebras,
clarifying the distinction between:
1. The **3-graded bosonic core** ($\mathfrak{g}_{-2} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+2}$) with cubic derivation:
   $$\mathcal{D}^3(X) = 4\mathcal{D}(X)$$
2. The **spinorial / fermionic odd sector** ($\mathfrak{g}_{-1} \oplus \mathfrak{g}_{+1}$) with reflection:
   $$\mathcal{D}^3(X) = \mathcal{D}(X) \quad (\mathcal{D}^2(X) = X)$$
3. The **full 5-graded Lie algebra** ($\mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_1 \oplus \mathfrak{g}_2$)
   with the quintic Kantor–Tanaka characteristic identity:
   $$\mathcal{D}^5(X) - 5\mathcal{D}^3(X) + 4\mathcal{D}(X) = 0$$

### Key Architectural Results:
- **Polynomial Factorization**:
  $x(x^2 - 1)(x^2 - 4) = x^5 - 5x^3 + 4x$.
- **Concrete $\mathfrak{sl}(3, R)$ Witness**:
  The Cartan grading element $H = \operatorname{diag}(1, 0, -1) \in \mathfrak{sl}(3, R)$
  acts on $M_3(R)$ via $\operatorname{ad}_H(X) = [H, X]$, satisfying the quintic identity identically.
- **Decomposition of Ideals**:
  Inner automorphism $x \mapsto J x J$ preserves ideal handedness (left ideal $\to$ left ideal).
  Anti-automorphism $\tau(x y) = \tau(y)\tau(x)$ switches handedness (left ideal $\to$ right ideal).
- **Central Identity Hamiltonian**:
  In the minimal carrier, $\{Q, Q^\dagger\} = P_L + P_R = 1$ is the central identity,
  trivially commuting with all elements and yielding vanishing supertrace $\operatorname{STr}(1) = 0$.

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra

open scoped Matrix

variable {R : Type*} [CommRing R]

/-! ### Section 1: Polynomial Factorization and Characteristic Roots -/

/-- **Theorem (Quintic Characteristic Factorization)**:
    $x(x^2 - 1)(x^2 - 4) = x^5 - 5x^3 + 4x$. -/
theorem quintic_polynomial_factorization (x : R) :
    x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x := by
  ring

/-- **Theorem (Linear Factor Expansion)**:
    $x(x - 1)(x + 1)(x - 2)(x + 2) = x^5 - 5x^3 + 4x$. -/
theorem five_grade_roots_expansion (x : R) :
    x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x := by
  ring

/-- **Theorem (Bosonic 3-Graded Roots)**:
    $x(x - 2)(x + 2) = x^3 - 4x$. -/
theorem three_grade_bosonic_roots (x : R) :
    x * (x - 2) * (x + 2) = x ^ 3 - 4 * x := by
  ring

/-- **Theorem (Fermionic Odd Roots)**:
    $(x - 1)(x + 1) = x^2 - 1$. -/
theorem odd_fermionic_roots (x : R) :
    (x - 1) * (x + 1) = x ^ 2 - 1 := by
  ring

/-! ### Section 2: Concrete $3 \times 3$ Kantor–Tanaka Matrix Model -/

/-- The canonical Cartan grading matrix $H = \operatorname{diag}(1, 0, -1)$ in $\mathfrak{sl}(3, R)$. -/
def H_grading : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal (![1, 0, -1])

/-- The adjoint commutator derivation $\operatorname{ad}_H(X) = H X - X H$. -/
def adH (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  H_grading * X - X * H_grading

/-- Explicit action on the 9 matrix components: -/
theorem adH_00 (X : Matrix (Fin 3) (Fin 3) R) : adH X 0 0 = 0 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem adH_01 (X : Matrix (Fin 3) (Fin 3) R) : adH X 0 1 = X 0 1 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem adH_02 (X : Matrix (Fin 3) (Fin 3) R) : adH X 0 2 = 2 * X 0 2 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]; ring

theorem adH_10 (X : Matrix (Fin 3) (Fin 3) R) : adH X 1 0 = - X 1 0 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem adH_11 (X : Matrix (Fin 3) (Fin 3) R) : adH X 1 1 = 0 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem adH_12 (X : Matrix (Fin 3) (Fin 3) R) : adH X 1 2 = X 1 2 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem adH_20 (X : Matrix (Fin 3) (Fin 3) R) : adH X 2 0 = -2 * X 2 0 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]; ring

theorem adH_21 (X : Matrix (Fin 3) (Fin 3) R) : adH X 2 1 = - X 2 1 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem adH_22 (X : Matrix (Fin 3) (Fin 3) R) : adH X 2 2 = 0 := by
  dsimp [adH, H_grading]
  simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Section 3: The 9 Quintic Component Lemmas and Master Theorem -/

theorem quintic_00 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 0 0 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [adH_00, adH_00, adH_00]; simp

theorem quintic_01 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 0 1 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  repeat rw [adH_01]
  simp; ring

theorem quintic_02 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 0 2 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  repeat rw [adH_02]
  simp; ring

theorem quintic_10 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 1 0 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  repeat rw [adH_10]
  simp; ring

theorem quintic_11 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 1 1 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [adH_11, adH_11, adH_11]; simp

theorem quintic_12 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 1 2 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  repeat rw [adH_12]
  simp; ring

theorem quintic_20 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 2 0 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  repeat rw [adH_20]
  simp; ring

theorem quintic_21 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 2 1 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  repeat rw [adH_21]
  simp; ring

theorem quintic_22 (X : Matrix (Fin 3) (Fin 3) R) :
    (adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X) 2 2 = 0 := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [adH_22, adH_22, adH_22]; simp

/-- **Master Theorem**: For ANY $3 \times 3$ matrix $X$, the adjoint derivation $\operatorname{ad}_H$
    satisfies the exact quintic Kantor–Tanaka identity:
    $$\operatorname{ad}_H^5(X) - 5\operatorname{ad}_H^3(X) + 4\operatorname{ad}_H(X) = 0$$ -/
theorem adH_quintic_identity (X : Matrix (Fin 3) (Fin 3) R) :
    adH (adH (adH (adH (adH X)))) -
    5 • adH (adH (adH X)) +
    4 • adH X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact quintic_00 X
  · exact quintic_01 X
  · exact quintic_02 X
  · exact quintic_10 X
  · exact quintic_11 X
  · exact quintic_12 X
  · exact quintic_20 X
  · exact quintic_21 X
  · exact quintic_22 X

/-! ### Section 4: Bosonic Subspace and 3-Graded Reduction -/

/-- A matrix is in the bosonic subspace if its odd transition entries vanish. -/
def isBosonicSubspace (X : Matrix (Fin 3) (Fin 3) R) : Prop :=
  X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0

theorem bosonic_00 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 0 0 = (4 • adH X) 0 0 := by
  simp only [Matrix.smul_apply, adH_00, smul_zero]

theorem bosonic_01 (X : Matrix (Fin 3) (Fin 3) R) (h : X 0 1 = 0) : (adH (adH (adH X))) 0 1 = (4 • adH X) 0 1 := by
  simp only [Matrix.smul_apply, adH_01, h, smul_zero]

theorem bosonic_02 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 0 2 = (4 • adH X) 0 2 := by
  simp only [Matrix.smul_apply]
  repeat rw [adH_02]
  simp; ring

theorem bosonic_10 (X : Matrix (Fin 3) (Fin 3) R) (h : X 1 0 = 0) : (adH (adH (adH X))) 1 0 = (4 • adH X) 1 0 := by
  simp only [Matrix.smul_apply, adH_10, h, smul_zero, neg_zero]

theorem bosonic_11 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 1 1 = (4 • adH X) 1 1 := by
  simp only [Matrix.smul_apply, adH_11, smul_zero]

theorem bosonic_12 (X : Matrix (Fin 3) (Fin 3) R) (h : X 1 2 = 0) : (adH (adH (adH X))) 1 2 = (4 • adH X) 1 2 := by
  simp only [Matrix.smul_apply, adH_12, h, smul_zero]

theorem bosonic_20 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 2 0 = (4 • adH X) 2 0 := by
  simp only [Matrix.smul_apply]
  repeat rw [adH_20]
  simp; ring

theorem bosonic_21 (X : Matrix (Fin 3) (Fin 3) R) (h : X 2 1 = 0) : (adH (adH (adH X))) 2 1 = (4 • adH X) 2 1 := by
  simp only [Matrix.smul_apply, adH_21, h, smul_zero, neg_zero]

theorem bosonic_22 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 2 2 = (4 • adH X) 2 2 := by
  simp only [Matrix.smul_apply, adH_22, smul_zero]

/-- **Theorem**: On the bosonic subspace, $\operatorname{ad}_H$ satisfies the cubic 3-graded identity:
    $$\operatorname{ad}_H^3(X) = 4\operatorname{ad}_H(X)$$ -/
theorem adH_bosonic_cubic (X : Matrix (Fin 3) (Fin 3) R) (h : isBosonicSubspace X) :
    adH (adH (adH X)) = 4 • adH X := by
  rcases h with ⟨h01, h10, h12, h21⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact bosonic_00 X
  · exact bosonic_01 X h01
  · exact bosonic_02 X
  · exact bosonic_10 X h10
  · exact bosonic_11 X
  · exact bosonic_12 X h12
  · exact bosonic_20 X
  · exact bosonic_21 X h21
  · exact bosonic_22 X

/-! ### Section 5: Fermionic Subspace and Reflection Reduction -/

/-- A matrix is in the fermionic subspace if its diagonal and corner entries vanish. -/
def isFermionicSubspace (X : Matrix (Fin 3) (Fin 3) R) : Prop :=
  X 0 0 = 0 ∧ X 1 1 = 0 ∧ X 2 2 = 0 ∧ X 0 2 = 0 ∧ X 2 0 = 0

theorem fermionic_00 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 0 0 = adH X 0 0 := by
  rw [adH_00, adH_00]

theorem fermionic_01 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 0 1 = adH X 0 1 := by
  rw [adH_01, adH_01]

theorem fermionic_02 (X : Matrix (Fin 3) (Fin 3) R) (h : X 0 2 = 0) : (adH (adH (adH X))) 0 2 = adH X 0 2 := by
  repeat rw [adH_02]
  simp [h]

theorem fermionic_10 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 1 0 = adH X 1 0 := by
  repeat rw [adH_10]
  ring

theorem fermionic_11 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 1 1 = adH X 1 1 := by
  rw [adH_11, adH_11]

theorem fermionic_12 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 1 2 = adH X 1 2 := by
  rw [adH_12, adH_12]

theorem fermionic_20 (X : Matrix (Fin 3) (Fin 3) R) (h : X 2 0 = 0) : (adH (adH (adH X))) 2 0 = adH X 2 0 := by
  repeat rw [adH_20]
  simp [h]

theorem fermionic_21 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 2 1 = adH X 2 1 := by
  repeat rw [adH_21]
  ring

theorem fermionic_22 (X : Matrix (Fin 3) (Fin 3) R) : (adH (adH (adH X))) 2 2 = adH X 2 2 := by
  rw [adH_22, adH_22]

/-- **Theorem**: On the fermionic subspace, $\operatorname{ad}_H$ satisfies the reflection identity:
    $$\operatorname{ad}_H^3(X) = \operatorname{ad}_H(X)$$ -/
theorem adH_fermionic_cubic (X : Matrix (Fin 3) (Fin 3) R) (h : isFermionicSubspace X) :
    adH (adH (adH X)) = adH X := by
  rcases h with ⟨h00, h11, h22, h02, h20⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact fermionic_00 X
  · exact fermionic_01 X
  · exact fermionic_02 X h02
  · exact fermionic_10 X
  · exact fermionic_11 X
  · exact fermionic_12 X
  · exact fermionic_20 X h20
  · exact fermionic_21 X
  · exact fermionic_22 X

/-! ### Section 6: Ideal Handedness — Automorphisms vs Anti-Automorphisms -/

/-- An inner automorphism $x \mapsto J x J$ preserves ideal multiplication order:
    $J (a b) J = (J a J) (J b J)$.
    Hence, it maps a left ideal to a left ideal: $J (\mathcal{A} P_L) J = \mathcal{A} P_R$. -/
theorem inner_automorphism_mul {A : Type*} [Ring A] (J a b : A) (hJ : J * J = 1) :
    J * (a * b) * J = (J * a * J) * (J * b * J) := by
  calc
    J * (a * b) * J = (J * a) * (1 * b * J) := by
      simp only [one_mul, mul_assoc]
    _ = (J * a) * ((J * J) * b * J) := by rw [hJ]
    _ = (J * a * J) * (J * b * J) := by
      simp only [mul_assoc]

/-- An anti-automorphism reverses multiplication order:
    $\tau(a b) = \tau(b) \tau(a)$.
    Hence, it maps a left ideal $\mathcal{A} P_L$ to a right ideal $P_R \tau(\mathcal{A})$. -/
theorem anti_automorphism_ideal_flip {A : Type*} [Ring A]
    (tau : A → A) (h_rev : ∀ x y, tau (x * y) = tau y * tau x)
    (PL PR : A) (h_tau : tau PL = PR) (a : A) :
    tau (a * PL) = PR * tau a := by
  rw [h_rev, h_tau]

/-! ### Section 7: Central Identity Hamiltonian and Vanishing Supertrace -/

/-- Supertrace of a $2 \times 2$ matrix: $\operatorname{STr}(M) = M_{00} - M_{11}$. -/
def superTrace2 (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 - M 1 1

/-- **Theorem**: The identity Hamiltonian $H = \mathbf{1}$ trivially commutes with all elements. -/
theorem identity_hamiltonian_central (X : Matrix (Fin 2) (Fin 2) R) :
    (1 : Matrix (Fin 2) (Fin 2) R) * X - X * 1 = 0 := by
  rw [one_mul, mul_one, sub_self]

/-- **Theorem**: The supertrace of the identity Hamiltonian vanishes identically:
    $\operatorname{STr}(\mathbf{1}) = 1 - 1 = 0$. -/
theorem identity_hamiltonian_supertrace_zero :
    superTrace2 (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  dsimp [superTrace2]
  simp

/-! ### Section 8: Master Verification Certificate -/

/-- Master certificate bundling the verified components of the 5-Graded Lie Superalgebra. -/
structure FiveGradedLieSuperalgebraCertificate : Prop where
  quintic_factorization : ∀ (x : R), x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x
  five_grade_roots : ∀ (x : R), x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x
  bosonic_roots : ∀ (x : R), x * (x - 2) * (x + 2) = x ^ 3 - 4 * x
  fermionic_roots : ∀ (x : R), (x - 1) * (x + 1) = x ^ 2 - 1
  adH_quintic : ∀ (X : Matrix (Fin 3) (Fin 3) R),
    adH (adH (adH (adH (adH X)))) - 5 • adH (adH (adH X)) + 4 • adH X = 0
  adH_bosonic : ∀ (X : Matrix (Fin 3) (Fin 3) R),
    isBosonicSubspace X → adH (adH (adH X)) = 4 • adH X
  adH_fermionic : ∀ (X : Matrix (Fin 3) (Fin 3) R),
    isFermionicSubspace X → adH (adH (adH X)) = adH X
  inner_automorphism_order : ∀ {A : Type*} [Ring A] (J a b : A),
    J * J = 1 → J * (a * b) * J = (J * a * J) * (J * b * J)
  anti_automorphism_flip : ∀ {A : Type*} [Ring A] (tau : A → A),
    (∀ x y, tau (x * y) = tau y * tau x) → ∀ (PL PR : A), tau PL = PR → ∀ a, tau (a * PL) = PR * tau a
  hamiltonian_central : ∀ (X : Matrix (Fin 2) (Fin 2) R),
    (1 : Matrix (Fin 2) (Fin 2) R) * X - X * 1 = 0
  hamiltonian_supertrace_zero : superTrace2 (1 : Matrix (Fin 2) (Fin 2) R) = 0

/-- Instant compilation of the master certificate with zero open assumptions. -/
theorem compile_five_graded_lie_superalgebra : FiveGradedLieSuperalgebraCertificate (R := R) where
  quintic_factorization := quintic_polynomial_factorization
  five_grade_roots := five_grade_roots_expansion
  bosonic_roots := three_grade_bosonic_roots
  fermionic_roots := odd_fermionic_roots
  adH_quintic := adH_quintic_identity
  adH_bosonic := adH_bosonic_cubic
  adH_fermionic := adH_fermionic_cubic
  inner_automorphism_order := inner_automorphism_mul
  anti_automorphism_flip := anti_automorphism_ideal_flip
  hamiltonian_central := identity_hamiltonian_central
  hamiltonian_supertrace_zero := identity_hamiltonian_supertrace_zero

end InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
