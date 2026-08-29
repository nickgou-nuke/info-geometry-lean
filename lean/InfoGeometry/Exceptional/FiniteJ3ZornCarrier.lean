import Mathlib
import InfoGeometry.Exceptional.SplitOctonionZornReal

/-!
# Finite `J₃` carrier over the existing real Zorn model

This file introduces only the finite carrier and its hermitian predicate.
The entry multiplication is deliberately not promoted to an associative
matrix algebra: the Zorn multiplication is non-associative.  Consequently,
the Jordan product and its identity must be proved on a separately specified
hermitian subcarrier.
-/

namespace InfoGeometry.Exceptional.FiniteJ3Zorn

open InfoGeometry.Exceptional.RealZorn

abbrev J3 := Fin 3 → Fin 3 → ZornMatrixReal

def hermitian (X : J3) : Prop :=
  ∀ i j, X i j = X j i

@[ext] theorem J3_ext {X Y : J3} (h : ∀ i j, X i j = Y i j) : X = Y := by
  funext i j
  exact h i j

def zero : J3 := fun _ _ => 0

@[simp] theorem zero_apply (i j : Fin 3) : zero i j = 0 := rfl

theorem zero_hermitian : hermitian zero := by
  intro i j
  rfl

def identity : J3 := fun i j => if i = j then 1 else 0

theorem identity_hermitian : hermitian identity := by
  intro i j
  by_cases h : i = j <;> simp [identity, h, Ne.symm h]

theorem hermitian_transpose (X : J3) (hX : hermitian X) :
    ∀ i j, X j i = X i j := by
  intro i j
  exact (hX j i).symm

end InfoGeometry.Exceptional.FiniteJ3Zorn
