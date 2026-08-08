import Mathlib
import proofs.FiniteMatrixKnillLaflamme
import proofs.CuntzMatrixCorner
import proofs.KnillLaflammeQEC

noncomputable section

open Matrix Complex FiniteMatrixKnillLaflamme CuntzMatrixCorner

namespace CuntzCornerQEC

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

/-- 
The abstract Knill-Laflamme condition formulated for any C*-algebra,
allowing the formulation of QEC conditions independent of matrix representations.
-/
def SatisfiesKnillLaflammeAlgebra {ι : Type*} [Fintype ι] 
    (P : A) (E : ι → A) : Prop :=
  ∃ λ : ι → ι → ℂ, ∀ a b, P * star (E a) * E b * P = (λ a b) • P

/-- 
If a set of errors and a projector satisfy the Knill-Laflamme conditions 
in the matrix algebra, their transport across the Cuntz corner homomorphism 
perfectly preserves the QEC conditions in the Cuntz algebra.
-/
theorem cuntzCorner_transports_KL {ι : Type*} [Fintype ι]
    (P : Matrix (Fin 2) (Fin 2) ℂ) (E : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (h_KL : SatisfiesKnillLaflamme P E) :
    SatisfiesKnillLaflammeAlgebra S (cuntzCornerMap S P) (fun a => cuntzCornerMap S (E a)) := by
  rcases h_KL with ⟨lambda, h_eq⟩
  use lambda
  intro a b
  have h_eq_ab := h_eq a b
  have h_map := congrArg (cuntzCornerMap S) h_eq_ab
  rw [cuntzCornerMap_mul S (P * (E a)ᴴ * E b) P] at h_map
  rw [cuntzCornerMap_mul S (P * (E a)ᴴ) (E b)] at h_map
  rw [cuntzCornerMap_mul S P ((E a)ᴴ)] at h_map
  rw [cuntzCornerMap_star S (E a)] at h_map
  rw [show cuntzCornerMap S ((lambda a b) • P) = (lambda a b) • cuntzCornerMap S P from ?_] at h_map
  exact h_map
  dsimp [cuntzCornerMap]
  simp [smul_add, mul_smul]

/-- 
Cuntz corner representation of the Fibonacci Code Projector.
This projects onto the dominant Fibonacci ray locally within O_2.
-/
def CuntzFibonacciCodeProjector : A :=
  cuntzCornerMap S KnillLaflammeQEC.P_C_Fibonacci

/-- 
Cuntz corner representation of the tangential error operators.
-/
def CuntzFibonacciErrors (a : Fin 2) : A :=
  cuntzCornerMap S (KnillLaflammeQEC.fibonacciErrors a)

/-- 
The culmination of the 1D rank-one QEC transport:
The abstract Cuntz algebra elements strictly obey the KL condition 
for the tangentially-filtered Fibonacci errors.
-/
theorem CuntzFibonacciCode_SatisfiesKL :
    SatisfiesKnillLaflammeAlgebra S CuntzFibonacciCodeProjector CuntzFibonacciErrors := by
  dsimp [CuntzFibonacciCodeProjector, CuntzFibonacciErrors]
  apply cuntzCorner_transports_KL S KnillLaflammeQEC.P_C_Fibonacci KnillLaflammeQEC.fibonacciErrors
  -- Use the verified 1D KL result
  exact KnillLaflammeQEC.fibonacci_satisfies_KL

end CuntzCornerQEC
