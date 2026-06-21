import Mathlib
import InfoGeometry.Algebra.QCCRProved

/-!
# q-CCR finite theorem layer

This file keeps only kernel-checked finite algebra from the q-CCR/Cuntz--Toeplitz
boundary.  The CMP-level C*-algebra isomorphisms are not asserted here.
-/

namespace InfoGeometry.Algebra.QCCR.Kuzmin

open Matrix
open InfoGeometry.Algebra.QCCR.Proved

/-- The finite `k=2,n=2` q-Gram form is positive for `|q| < 1`. -/
theorem finite_q_gram_positive
    (q : ℝ) (hq : |q| < 1) (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((gram_matrix_k2_n2 q).mulVec x) :=
  gram_positive_definite q hq x hx

/-- At `q=0` the finite q-Gram matrix is the identity. -/
theorem finite_q_gram_at_zero :
    gram_matrix_k2_n2 (0 : ℝ) = 1 :=
  gram_at_q_zero

/-- The finite q-Gram matrix is symmetric. -/
theorem finite_q_gram_symmetric (q : ℝ) :
    (gram_matrix_k2_n2 q)ᵀ = gram_matrix_k2_n2 q :=
  gram_symmetric q

/-- The finite flip matrix squares to the identity. -/
theorem finite_flip_square_eq_identity :
    P_matrix_n2 * P_matrix_n2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  P_square_eq_I

/-- The finite q-operator is `q` times the flip. -/
theorem finite_T_eq_q_mul_flip (q : ℝ) :
    T_matrix_n2 q = q • P_matrix_n2 :=
  T_eq_q_mul_P q

/-- The finite q-operator satisfies `T²=q² I`. -/
theorem finite_T_square_eq_q_sq_identity (q : ℝ) :
    T_matrix_n2 q * T_matrix_n2 q = q^2 • (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  T_square_eq_q_sq_I_n2 q

/-- CAR at `q=-1` in the algebraic q-relation. -/
theorem finite_car_anticommutation {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (-1 : R) * (a j * astar i))
    (i j : Fin 2) :
    astar i * a j + a j * astar i = (if i = j then 1 else 0) :=
  car_anticommutation a astar hstar hrel i j

/-- CCR at `q=1` in the algebraic q-relation. -/
theorem finite_ccr_commutation {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (1 : R) * (a j * astar i))
    (i j : Fin 2) :
    astar i * a j - a j * astar i = (if i = j then 1 else 0) :=
  ccr_commutation a astar hstar hrel i j

/-- Toeplitz/Cuntz boundary at `q=0` in the algebraic q-relation. -/
theorem finite_cuntz_toeplitz_limit {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (0 : R) * (a j * astar i))
    (i j : Fin 2) :
    astar i * a j = (if i = j then 1 else 0) :=
  cuntz_toeplitz_limit a astar hstar hrel i j

end InfoGeometry.Algebra.QCCR.Kuzmin
