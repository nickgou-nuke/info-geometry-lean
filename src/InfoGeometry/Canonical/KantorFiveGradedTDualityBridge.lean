import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Associative commutator and involution-projector identities

This file proves general ring identities: the commutator derivation law,
conditional additivity of commutator eigenweights, Peirce projector formulas
for an involution in a real algebra, and the off-diagonal decomposition of an
element anticommuting with that involution. It also records algebraic facts
about an algebra equivalence that negates the involution and about a diagonal
sign matrix.

These statements do not construct a Kantor triple system, a five-graded Lie
algebra, a T-duality action, a D-brane representation, or a quadratic-form
signature. Those require separate concrete carriers and proofs.
-/

noncomputable section

namespace InfoGeometry.Canonical.KantorFiveGradedTDuality

open Matrix

/-! ### Commutator identities -/

/-- Ring commutator bracket: $[A, B] = A B - B A$. -/
def comm {R : Type*} [Ring R] (A B : R) : R := A * B - B * A

/-- 
Jacobi Derivation Identity:
The adjoint action $\operatorname{ad}_h$ acts as a derivation on the commutator bracket:
$[h, [x, y]] = [[h, x], y] + [x, [h, y]]$.
-/
theorem comm_derivation {R : Type*} [Ring R] (h x y : R) :
    comm h (comm x y) = comm (comm h x) y + comm x (comm h y) := by
  dsimp [comm]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- Scalar linearity on the left of the commutator bracket. -/
theorem comm_smul_left {R : Type*} [Ring R] [Algebra ℝ R] (c : ℝ) (x y : R) :
    comm (c • x) y = c • comm x y := by
  dsimp [comm]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]

/-- Scalar linearity on the right of the commutator bracket. -/
theorem comm_smul_right {R : Type*} [Ring R] [Algebra ℝ R] (c : ℝ) (x y : R) :
    comm x (c • y) = c • comm x y := by
  dsimp [comm]
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]

/-- 
Grade Additivity Theorem:
If $x$ is an eigenvector of weight $i$ ($[h, x] = i x$) and $y$ is an eigenvector of weight $j$
($[h, y] = j y$), then their commutator $[x, y]$ is an eigenvector of weight $i + j$:
$[h, [x, y]] = (i + j) [x, y]$.
This is a conditional identity about commutator eigenvectors; it does not by
itself construct a graded Lie algebra.
-/
theorem grade_additivity_scalar {R : Type*} [Ring R] [Algebra ℝ R]
    (h x y : R) (i j : ℝ)
    (hx : comm h x = i • x)
    (hy : comm h y = j • y) :
    comm h (comm x y) = (i + j) • (comm x y) := by
  rw [comm_derivation, hx, hy]
  rw [comm_smul_left, comm_smul_right, ← add_smul]

/-! ### Square-zero elements -/

/-- If an element squares to zero, its third power is zero. -/
theorem nilpotent_cube_zero {A : Type*} [Ring A]
    (N : A) (hN_sq : N * N = 0) :
    N * N * N = 0 := by
  rw [hN_sq, zero_mul]

/-! ### Peirce projectors of an involution -/

/-- Positive Peirce projector: $P_+ = \frac{1}{2}(1 + \Gamma)$. -/
def peircePlus {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) : A :=
  (1/2 : ℝ) • (1 + Γ)

/-- Negative Peirce projector: $P_- = \frac{1}{2}(1 - \Gamma)$. -/
def peirceMinus {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) : A :=
  (1/2 : ℝ) • (1 - Γ)

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peircePlus_sq {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) (hΓ : Γ * Γ = 1) :
    peircePlus Γ * peircePlus Γ = peircePlus Γ := by
  simp [peircePlus, smul_mul_assoc, mul_smul_comm, smul_smul, hΓ,
    smul_add, add_mul, mul_add]
  module

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceMinus_sq {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) (hΓ : Γ * Γ = 1) :
    peirceMinus Γ * peirceMinus Γ = peirceMinus Γ := by
  simp [peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul, hΓ,
    smul_sub, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_+ \cdot P_- = 0$. -/
theorem peircePlus_mul_minus {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) (hΓ : Γ * Γ = 1) :
    peircePlus Γ * peirceMinus Γ = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hΓ, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_- \cdot P_+ = 0$. -/
theorem peirceMinus_mul_plus {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) (hΓ : Γ * Γ = 1) :
    peirceMinus Γ * peircePlus Γ = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hΓ, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]

/-- Resolution of identity: $P_+ + P_- = 1$. -/
theorem peircePlus_add_minus {A : Type*} [Ring A] [Algebra ℝ A] (Γ : A) :
    peircePlus Γ + peirceMinus Γ = 1 := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

/-! ### Off-diagonal decomposition -/

/-- Intertwining: $P_+ X = X P_-$ for chiral anticommuting $X$. -/
theorem peircePlus_mul_odd {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ X : A) (h_anticomm : X * Γ + Γ * X = 0) :
    peircePlus Γ * X = X * peirceMinus Γ := by
  dsimp [peircePlus, peirceMinus]
  have h_anti : Γ * X = - (X * Γ) := by
    calc Γ * X = (X * Γ + Γ * X) - X * Γ := by abel
    _ = 0 - X * Γ := by rw [h_anticomm]
    _ = - (X * Γ) := by simp
  calc
    peircePlus Γ * X = ((1/2 : ℝ) • (1 + Γ)) * X := rfl
    _ = (1/2 : ℝ) • ((1 + Γ) * X) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (X + Γ * X) := by rw [add_mul, one_mul]
    _ = (1/2 : ℝ) • (X - X * Γ) := by rw [h_anti, sub_eq_add_neg]
    _ = (1/2 : ℝ) • (X * (1 - Γ)) := by rw [mul_sub, mul_one]
    _ = X * ((1/2 : ℝ) • (1 - Γ)) := by rw [mul_smul_comm]
    _ = X * peirceMinus Γ := rfl

/-- Intertwining: $P_- X = X P_+$ for chiral anticommuting $X$. -/
theorem peirceMinus_mul_odd {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ X : A) (h_anticomm : X * Γ + Γ * X = 0) :
    peirceMinus Γ * X = X * peircePlus Γ := by
  dsimp [peircePlus, peirceMinus]
  have h_anti : Γ * X = - (X * Γ) := by
    calc Γ * X = (X * Γ + Γ * X) - X * Γ := by abel
    _ = 0 - X * Γ := by rw [h_anticomm]
    _ = - (X * Γ) := by simp
  calc
    peirceMinus Γ * X = ((1/2 : ℝ) • (1 - Γ)) * X := rfl
    _ = (1/2 : ℝ) • ((1 - Γ) * X) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (X - Γ * X) := by rw [sub_mul, one_mul]
    _ = (1/2 : ℝ) • (X - - (X * Γ)) := by rw [h_anti]
    _ = (1/2 : ℝ) • (X + X * Γ) := by rw [sub_neg_eq_add]
    _ = (1/2 : ℝ) • (X * (1 + Γ)) := by rw [mul_add, mul_one]
    _ = X * ((1/2 : ℝ) • (1 + Γ)) := by rw [mul_smul_comm]
    _ = X * peircePlus Γ := rfl

/-- Positive diagonal vanishing: $P_+ X P_+ = 0$. -/
theorem peircePlus_odd_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ X : A) (hΓ : Γ * Γ = 1) (h_anticomm : X * Γ + Γ * X = 0) :
    peircePlus Γ * X * peircePlus Γ = 0 := by
  have h := peircePlus_mul_odd Γ X h_anticomm
  rw [h, mul_assoc, peirceMinus_mul_plus Γ hΓ, mul_zero]

/-- Negative diagonal vanishing: $P_- X P_- = 0$. -/
theorem peirceMinus_odd_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ X : A) (hΓ : Γ * Γ = 1) (h_anticomm : X * Γ + Γ * X = 0) :
    peirceMinus Γ * X * peirceMinus Γ = 0 := by
  have h := peirceMinus_mul_odd Γ X h_anticomm
  rw [h, mul_assoc, peircePlus_mul_minus Γ hΓ, mul_zero]

/-- 
Any element $X$ anticommuting with $\Gamma$ decomposes into off-diagonal
blocks relative to the two Peirce projectors:
$X = P_+ X P_- + P_- X P_+$.
-/
theorem odd_off_diagonal_split {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ X : A) (hΓ : Γ * Γ = 1) (h_anticomm : X * Γ + Γ * X = 0) :
    X = peircePlus Γ * X * peirceMinus Γ + peirceMinus Γ * X * peircePlus Γ := by
  calc X = 1 * X * 1 := by rw [one_mul, mul_one]
  _ = (peircePlus Γ + peirceMinus Γ) * X * (peircePlus Γ + peirceMinus Γ) := by
      rw [peircePlus_add_minus Γ]
  _ = (peircePlus Γ * X + peirceMinus Γ * X) * (peircePlus Γ + peirceMinus Γ) := by
      rw [add_mul]
  _ = peircePlus Γ * X * peircePlus Γ + peircePlus Γ * X * peirceMinus Γ +
      (peirceMinus Γ * X * peircePlus Γ + peirceMinus Γ * X * peirceMinus Γ) := by
      rw [add_mul, mul_add, mul_add]
  _ = 0 + peircePlus Γ * X * peirceMinus Γ + (peirceMinus Γ * X * peircePlus Γ + 0) := by
      rw [peircePlus_odd_peircePlus Γ X hΓ h_anticomm,
          peirceMinus_odd_peirceMinus Γ X hΓ h_anticomm]
  _ = peircePlus Γ * X * peirceMinus Γ + peirceMinus Γ * X * peircePlus Γ := by
      abel

/-! ### Algebra equivalences that negate the involution -/

/- A real algebra equivalence sending `Γ` to `-Γ` swaps the Peirce projectors. -/
theorem algebraEquiv_swap_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ : A) (σ : A ≃ₐ[ℝ] A) (h_Γ : σ Γ = -Γ) :
    σ (peircePlus Γ) = peirceMinus Γ := by
  dsimp [peircePlus, peirceMinus]
  rw [map_smul, map_add, map_one, h_Γ, ← sub_eq_add_neg]

/- A real algebra equivalence sending `Γ` to `-Γ` swaps the Peirce projectors. -/
theorem algebraEquiv_swap_peirceMinus {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ : A) (σ : A ≃ₐ[ℝ] A) (h_Γ : σ Γ = -Γ) :
    σ (peirceMinus Γ) = peircePlus Γ := by
  dsimp [peircePlus, peirceMinus]
  rw [map_smul, map_sub, map_one, h_Γ, sub_neg_eq_add]

/- Two successive swaps restore the positive Peirce projector. -/
theorem algebraEquiv_double_swap_peircePlus {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ : A) (σ : A ≃ₐ[ℝ] A) (h_Γ : σ Γ = -Γ) :
    σ (σ (peircePlus Γ)) = peircePlus Γ := by
  rw [algebraEquiv_swap_peircePlus Γ σ h_Γ, algebraEquiv_swap_peirceMinus Γ σ h_Γ]

/-- 
An algebra equivalence that negates the involution swaps the two Peirce
projector factors in an off-diagonal product.
-/
theorem algebraEquiv_swap_offDiagonalTransition {A : Type*} [Ring A] [Algebra ℝ A]
    (Γ X : A) (σ : A ≃ₐ[ℝ] A) (h_Γ : σ Γ = -Γ) :
    σ (peircePlus Γ * X * peirceMinus Γ) =
      peirceMinus Γ * σ X * peircePlus Γ := by
  simp only [map_mul, algebraEquiv_swap_peircePlus Γ σ h_Γ,
    algebraEquiv_swap_peirceMinus Γ σ h_Γ]

/-! ### Diagonal sign matrix -/

variable {R : Type*} [CommRing R]

/-- 
The diagonal matrix with five `1` entries followed by five `-1` entries.
Symmetry and square-to-identity alone do not assert a signature classification.
-/
def eta55 : Matrix (Fin 10) (Fin 10) R :=
  Matrix.diagonal (fun i => if (i : ℕ) < 5 then 1 else -1)

/-- The diagonal sign matrix is symmetric. -/
theorem eta55_transpose :
    (eta55 (R := R))ᵀ = eta55 :=
  Matrix.diagonal_transpose _

/-- The diagonal sign matrix squares to the identity matrix. -/
theorem eta55_sq :
    (eta55 (R := R)) * eta55 = 1 := by
  dsimp [eta55]
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin 10 => (if (i : ℕ) < 5 then (1 : R) else -1) * (if (i : ℕ) < 5 then 1 else -1)) = fun _ => 1 := by
    ext i
    split_ifs <;> ring
  rw [h]
  exact Matrix.diagonal_one

end InfoGeometry.Canonical.KantorFiveGradedTDuality
