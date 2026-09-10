import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace FiniteGNSConstruction

open Matrix
open scoped BigOperators

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev V2C := Fin 2 → ℂ

/-- Matrix-vector action. -/
def matVec (A : M2C) (v : V2C) : V2C :=
  fun i => ∑ j : Fin 2, A i j * v j

/-- Reference cyclic vector `Ω=e₀`. -/
def Omega : V2C
  | 0 => 1
  | 1 => 0

/-- Algebraic Hermitian inner product convention: conjugate-linear in the first slot. -/
def inner (u v : V2C) : ℂ :=
  ∑ i : Fin 2, star (u i) * v i

/-- Vector state `ω(A)=⟨Ω,AΩ⟩`; for `Ω=e₀` this is the `(0,0)` entry. -/
def omegaState (A : M2C) : ℂ := inner Omega (matVec A Omega)

/-- The vector state is exactly the top-left matrix coefficient. -/
theorem omegaState_apply (A : M2C) : omegaState A = A 0 0 := by
  simp [omegaState, inner, matVec, Omega, Fin.sum_univ_two]

/-- Normalization: `ω(1)=1`. -/
theorem omegaState_one : omegaState (1 : M2C) = 1 := by
  simp [omegaState_apply]

/-- Finite positivity: `ω(A⋆A)` is the squared norm of the first column. -/
theorem omegaState_star_mul_self (A : M2C) :
    omegaState (star A * A) =
      ((Complex.normSq (A 0 0) + Complex.normSq (A 1 0) : ℝ) : ℂ) := by
  simp [omegaState_apply, Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_eq_conj_mul_self]

/-- Finite state positivity, stated as non-negativity of the real part. -/
theorem omegaState_positive (A : M2C) :
    0 ≤ (omegaState (star A * A)).re := by
  rw [omegaState_star_mul_self]
  simp [add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]

/-- The vector-state Cauchy--Schwarz estimate specialized to the unit vector `Ω`. -/
theorem omegaState_normSq_le_inner (A : M2C) :
    Complex.normSq (omegaState A) ≤ (omegaState (star A * A)).re := by
  rw [omegaState_star_mul_self]
  simp [omegaState_apply]
  exact Complex.normSq_nonneg (A 1 0)

/-- Linearity of the finite vector state. -/
theorem omegaState_add (A B : M2C) :
    omegaState (A + B) = omegaState A + omegaState B := by
  simp [omegaState_apply]

/-- Homogeneity of the finite vector state. -/
theorem omegaState_smul (c : ℂ) (A : M2C) :
    omegaState (c • A) = c * omegaState A := by
  simp [omegaState_apply]

/-- The concrete GNS representation is left multiplication on `ℂ²`. -/
def pi (A : M2C) (v : V2C) : V2C := matVec A v

/-- GNS expectation identity `ω(A)=⟨Ω,π(A)Ω⟩`. -/
theorem gns_expectation (A : M2C) :
    omegaState A = inner Omega (pi A Omega) := rfl

/-- Matrix multiplication is represented by composition on the finite GNS space. -/
theorem pi_mul (A B : M2C) (v : V2C) :
    pi (A * B) v = pi A (pi B v) := by
  funext i
  fin_cases i <;> simp [pi, matVec, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The finite GNS action is a star representation: `π(A⋆)` is the adjoint of `π(A)`. -/
theorem pi_star_adjoint (A : M2C) (u v : V2C) :
    inner (pi A u) v = inner u (pi (star A) v) := by
  simp [inner, pi, matVec, Matrix.star_apply, Fin.sum_univ_two]
  ring_nf

/-- Equivalent adjoint identity with `A⋆` on the left. -/
theorem pi_star_adjoint' (A : M2C) (u v : V2C) :
    inner (pi (star A) u) v = inner u (pi A v) := by
  simpa using pi_star_adjoint (star A) u v

/-- Matrix with prescribed first column and zero second column. -/
def firstColumnMatrix (v : V2C) : M2C :=
  fun i j => if j = 0 then v i else 0

/-- The reference vector is cyclic for the full `M₂(ℂ)` representation. -/
theorem Omega_cyclic (v : V2C) : ∃ A : M2C, pi A Omega = v := by
  refine ⟨firstColumnMatrix v, ?_⟩
  funext i
  fin_cases i <;> simp [pi, matVec, firstColumnMatrix, Omega]

/-- The GNS null space for this vector state consists exactly of matrices killing `Ω`. -/
def gnsNull (A : M2C) : Prop := pi A Omega = 0

/-- The GNS null space is a left ideal: if `AΩ=0`, then `(BA)Ω=0`. -/
theorem gnsNull_left_ideal (A B : M2C) (hA : gnsNull A) :
    gnsNull (B * A) := by
  unfold gnsNull at hA ⊢
  rw [pi_mul]
  rw [hA]
  funext i
  fin_cases i <;> simp [pi, matVec]

/-- A matrix is null iff its first column is zero. -/
theorem gnsNull_iff_first_column_zero (A : M2C) :
    gnsNull A ↔ A 0 0 = 0 ∧ A 1 0 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [pi, matVec, Omega, Fin.sum_univ_two] at h0 h1
    exact ⟨h0, h1⟩
  · intro h
    funext i
    fin_cases i <;> simp [pi, matVec, Omega, Fin.sum_univ_two, h.1, h.2]

#check omegaState_apply
#check omegaState_one
#check omegaState_star_mul_self
#check omegaState_positive
#check omegaState_normSq_le_inner
#check gns_expectation
#check pi_mul
#check pi_star_adjoint
#check pi_star_adjoint'
#check Omega_cyclic
#check gnsNull_left_ideal
#check gnsNull_iff_first_column_zero

end FiniteGNSConstruction
