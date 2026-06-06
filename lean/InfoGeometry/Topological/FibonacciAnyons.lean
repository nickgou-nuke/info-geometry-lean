import Mathlib.Tactic

/-!
# InfoGeometry.Topological.FibonacciAnyons

Finite algebraic Fibonacci-anyon braiding surface.

The finite matrix theorems are stated with explicit scalar parameters and
explicit hypotheses.  The inductive-colimit Fibonacci owner is separate: it
must construct the staged tensor system and instantiate these parameters
directly.
-/

set_option autoImplicit false

namespace InfoGeometry.Topological.FibonacciAnyons

open Matrix

variable {K : Type*} [CommRing K]

/-- Raw Fibonacci fusion matrix `F = [[τ, √τ], [√τ, -τ]]`. -/
def F_matrixOf (τ sqrtτ : K) : Matrix (Fin 2) (Fin 2) K :=
  !![τ, sqrtτ; sqrtτ, -τ]

/-- Raw diagonal Fibonacci `R` matrix with entries `q_inv^4` and `q^3`. -/
def R_matrixOf (q qInv : K) : Matrix (Fin 2) (Fin 2) K :=
  !![qInv ^ 4, 0; 0, q ^ 3]

/-- Raw diagonal inverse candidate for `R_matrixOf`. -/
def R_dual_matrixOf (q qInv : K) : Matrix (Fin 2) (Fin 2) K :=
  !![q ^ 4, 0; 0, qInv ^ 3]

/-- The raw diagonal `R` matrix is cancelled by its dual when `qInv` is `q`'s inverse. -/
theorem R_matrixOf_mul_R_dual_matrixOf
    (q qInv : K) (hLeft : qInv * q = 1) (hRight : q * qInv = 1) :
    R_matrixOf q qInv * R_dual_matrixOf q qInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two,
      ← mul_pow, hLeft]
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two,
      ← mul_pow, hRight]

/-- The dual diagonal matrix also cancels `R_matrixOf` on the left. -/
theorem R_dual_matrixOf_mul_R_matrixOf
    (q qInv : K) (hLeft : q * qInv = 1) (hRight : qInv * q = 1) :
    R_dual_matrixOf q qInv * R_matrixOf q qInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two,
      ← mul_pow, hLeft]
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [R_matrixOf, R_dual_matrixOf, Matrix.mul_apply, Fin.sum_univ_two,
      ← mul_pow, hRight]

/-- Raw non-diagonal middle braid matrix `B = F R F`. -/
def B_matrixOf (q qInv τ sqrtτ : K) : Matrix (Fin 2) (Fin 2) K :=
  F_matrixOf τ sqrtτ * R_matrixOf q qInv * F_matrixOf τ sqrtτ

/--
The Fibonacci fusion matrix is involutive from the finite golden-ratio
relations `τ^2 + τ = 1` and `sqrtτ^2 = τ`.
-/
theorem F_involution (τ sqrtτ : K)
    (hτ : τ ^ 2 + τ = 1) (hsqrtτ : sqrtτ ^ 2 = τ) :
    F_matrixOf τ sqrtτ * F_matrixOf τ sqrtτ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F_matrixOf, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← hτ, ← hsqrtτ]
    ring
  · ring
  · ring
  · rw [← hτ, ← hsqrtτ]
    ring

/-- The finite middle braid generator is definitionally `F R F`. -/
theorem B_matrix_eq_FRF (q qInv τ sqrtτ : K) :
    B_matrixOf q qInv τ sqrtτ =
      F_matrixOf τ sqrtτ * R_matrixOf q qInv * F_matrixOf τ sqrtτ := by
  rfl

/--
The finite adjacent Artin relation for the Fibonacci `R` and `B` matrices,
closed only from the explicit raw matrix equality supplied as a hypothesis.
-/
theorem fibonacci_artin_relation (q qInv τ sqrtτ : K)
    (hArtin :
      R_matrixOf q qInv * B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv =
        B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv *
          B_matrixOf q qInv τ sqrtτ) :
    R_matrixOf q qInv * B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv =
      B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv *
        B_matrixOf q qInv τ sqrtτ := by
  exact hArtin

/-! ## Functorial transport of the raw matrix target -/

/-- Coordinatewise application of a ring homomorphism to a matrix. -/
def mapMatrix {m n K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (M : Matrix m n K) : Matrix m n L :=
  fun i j => f (M i j)

/-- Matrix multiplication commutes with coordinatewise ring-hom transport. -/
theorem mapMatrix_mul {m n p K L : Type*} [Fintype n] [CommRing K] [CommRing L]
    (f : K →+* L) (A : Matrix m n K) (B : Matrix n p K) :
    mapMatrix f (A * B) = mapMatrix f A * mapMatrix f B := by
  ext i j
  simp [mapMatrix, Matrix.mul_apply]

/-- Coordinatewise ring-hom transport preserves the identity matrix. -/
theorem mapMatrix_one {n K L : Type*} [DecidableEq n] [CommRing K] [CommRing L]
    (f : K →+* L) :
    mapMatrix f (1 : Matrix n n K) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [mapMatrix]
  · simp [mapMatrix, h]

/-- The raw `F` matrix commutes with coordinatewise ring-hom transport. -/
theorem mapMatrix_F {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (τ sqrtτ : K) :
    mapMatrix f (F_matrixOf τ sqrtτ) = F_matrixOf (f τ) (f sqrtτ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mapMatrix, F_matrixOf]

/-- The raw `R` matrix commutes with coordinatewise ring-hom transport. -/
theorem mapMatrix_R {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (q qInv : K) :
    mapMatrix f (R_matrixOf q qInv) = R_matrixOf (f q) (f qInv) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mapMatrix, R_matrixOf]

/-- The raw `B = F R F` matrix commutes with coordinatewise ring-hom transport. -/
theorem mapMatrix_B {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (q qInv τ sqrtτ : K) :
    mapMatrix f (B_matrixOf q qInv τ sqrtτ) =
      B_matrixOf (f q) (f qInv) (f τ) (f sqrtτ) := by
  unfold B_matrixOf
  rw [mapMatrix_mul, mapMatrix_mul, mapMatrix_F, mapMatrix_R]

/--
The raw Fibonacci Artin equality is preserved by any commutative-ring
homomorphism.
-/
theorem fibonacci_artin_relation_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (q qInv τ sqrtτ : K)
    (hArtin :
      R_matrixOf q qInv * B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv =
        B_matrixOf q qInv τ sqrtτ * R_matrixOf q qInv *
          B_matrixOf q qInv τ sqrtτ) :
    R_matrixOf (f q) (f qInv) * B_matrixOf (f q) (f qInv) (f τ) (f sqrtτ) *
        R_matrixOf (f q) (f qInv) =
      B_matrixOf (f q) (f qInv) (f τ) (f sqrtτ) *
        R_matrixOf (f q) (f qInv) *
          B_matrixOf (f q) (f qInv) (f τ) (f sqrtτ) := by
  have hMap := congrArg (mapMatrix f) hArtin
  simpa [mapMatrix_mul, mapMatrix_R, mapMatrix_B] using hMap

end InfoGeometry.Topological.FibonacciAnyons
