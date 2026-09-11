import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CyclotomicOperatorProjectors

/-!
# Polynomial classes for operators

These predicates deliberately live in the ambient endomorphism ring.  They
distinguish idempotents, roots of unity, and nilpotents without identifying
any of them merely because their equations use `1` or `0`.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorPolynomialTaxonomy

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

abbrev End (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V] :=
  Module.End R V

abbrev IsIdempotent (T : End R V) : Prop :=
  InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsIdempotent T

abbrev IsRootOfUnity (T : End R V) (m : ℕ) : Prop :=
  InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsRootOfUnity T m

abbrev IsNilpotent (T : End R V) (k : ℕ) : Prop :=
  InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsNilpotent T k

abbrev IsNPotent (T : End R V) (n : ℕ) : Prop :=
  InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsNPotent T n

theorem isIdempotent_iff_isTwoPotent (T : End R V) :
    IsIdempotent T ↔ IsNPotent T 2 := by
  rfl

theorem isRootOfUnity_one (T : End R V) : IsRootOfUnity T 0 := by
  change T ^ 0 = 1
  exact pow_zero T

theorem isIdempotent_isTwoPotent (T : End R V) (hT : IsIdempotent T) :
    IsNPotent T 2 := by
  exact hT

def nonzeroProjectorOfTwoPotent (T : End R V) : End R V := T

def zeroProjectorOfTwoPotent (T : End R V) : End R V := 1 - T

theorem nonzeroProjectorOfTwoPotent_idempotent
    (T : End R V) (hT : IsNPotent T 2) :
    IsIdempotent (nonzeroProjectorOfTwoPotent T) := by
  simpa [IsIdempotent, nonzeroProjectorOfTwoPotent] using hT

theorem zeroProjectorOfTwoPotent_idempotent
    (T : End R V) (hT : IsNPotent T 2) :
    IsIdempotent (zeroProjectorOfTwoPotent T) := by
  unfold IsIdempotent zeroProjectorOfTwoPotent
  change (1 - T) * (1 - T) = 1 - T
  change T * T = T at hT
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  rw [hT]
  simp

theorem twoPotent_projectors_add (T : End R V) :
    zeroProjectorOfTwoPotent T + nonzeroProjectorOfTwoPotent T = 1 := by
  simp [zeroProjectorOfTwoPotent, nonzeroProjectorOfTwoPotent]

theorem twoPotent_projectors_orthogonal (T : End R V) (hT : IsNPotent T 2) :
    zeroProjectorOfTwoPotent T * nonzeroProjectorOfTwoPotent T = 0 := by
  unfold zeroProjectorOfTwoPotent nonzeroProjectorOfTwoPotent
  change T * T = T at hT
  simp only [sub_mul, one_mul]
  rw [hT]
  simp

theorem twoPotent_projectors_orthogonal_rev (T : End R V) (hT : IsNPotent T 2) :
    nonzeroProjectorOfTwoPotent T * zeroProjectorOfTwoPotent T = 0 := by
  unfold zeroProjectorOfTwoPotent nonzeroProjectorOfTwoPotent
  change T * T = T at hT
  simp only [mul_sub, mul_one]
  rw [hT]
  simp

theorem twoPotent_mul_zeroProjector (T : End R V) (hT : IsNPotent T 2) :
    T * zeroProjectorOfTwoPotent T = 0 := by
  unfold zeroProjectorOfTwoPotent
  simp only [mul_sub, mul_one]
  have hT' : T * T = T := by
    change T * T = T at hT
    exact hT
  rw [hT']
  simp

theorem twoPotent_mul_nonzeroProjector (T : End R V) (hT : IsNPotent T 2) :
    T * nonzeroProjectorOfTwoPotent T = T := by
  simpa [nonzeroProjectorOfTwoPotent] using hT

end InfoGeometry.OperatorAlgebra.OperatorPolynomialTaxonomy
