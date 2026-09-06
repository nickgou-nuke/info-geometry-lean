import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBosonFermionGas

open scoped BigOperators
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState

variable {PrimeLabel : Type*} [DecidableEq PrimeLabel]
variable {R : Type*} [CommRing R]

/--
The signed Witten character evaluated on a finite prime label set.
This is the evaluation of the partition function over the exterior algebra.
-/
def signedWittenCharacter (S : Finset PrimeLabel) (x : PrimeLabel → R) : R :=
  ∑ T ∈ S.powerset, (fermionParitySign T : R) * (∏ p ∈ T, x p)

/--
The finite supertrace factorization theorem.
This asserts the algebraic identity underlying the Euler product,
valid for any finite subset of primes, avoiding analytic limits.

∑_{T ⊆ S} (-1)^{|T|} ∏_{p ∈ T} x_p = ∏_{p ∈ S} (1 - x_p)
-/
theorem signedWittenCharacter_eq_prod (S : Finset PrimeLabel) (x : PrimeLabel → R) :
    signedWittenCharacter S x = ∏ p ∈ S, (1 - x p) := by
  unfold signedWittenCharacter fermionParitySign
  have h_prod : ∏ p ∈ S, (1 - x p) = ∑ T ∈ S.powerset, (-1 : R) ^ T.card * (∏ p ∈ S \ T, 1) * ∏ p ∈ T, x p := by
    exact Finset.prod_sub (fun _ => 1) x S
  
  have h_simpl : ∀ T ∈ S.powerset, (-1 : R) ^ T.card * (∏ p ∈ S \ T, 1) * ∏ p ∈ T, x p = 
      (-1 : R) ^ T.card * (∏ p ∈ T, x p) := by
    intro T _
    simp

  
  rw [h_prod]
  apply Finset.sum_congr rfl
  intro T hT
  rw [h_simpl T hT]
  simp

end InfoGeometry.Arithmetic.PrimeBosonFermionGas
