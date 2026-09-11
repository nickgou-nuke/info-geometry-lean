import InfoGeometry.Clifford.Cl55ModularDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittProjectors

/-!
# Finite hyperbolic weights in `Cl(5,5)`

The weights below are elements of the noncommutative Clifford algebra.  Their
coefficients are real scalars, but the two channels are the genuine CAR-derived
hyperbolic projectors.  This is the finite algebraic loxodromic packet; no
diagonal representation and no analytic exponential is introduced.
-/

namespace InfoGeometry.Clifford.Clifford55

noncomputable def hyperbolicWeight55 (i : Fin 5) (a b : ℝ) : Cl55 :=
  a • hyperbolicProjector55Plus i + b • hyperbolicProjector55Minus i

theorem hyperbolicWeight55_mul
    (i : Fin 5) (a b c d : ℝ) :
    hyperbolicWeight55 i a b * hyperbolicWeight55 i c d =
      (a * c) • hyperbolicProjector55Plus i +
        (b * d) • hyperbolicProjector55Minus i := by
  unfold hyperbolicWeight55
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hyperbolicProjector55Plus_idem, hyperbolicProjector55Minus_idem,
    hyperbolicProjector55Plus_mul_minus,
    hyperbolicProjector55Minus_mul_plus, smul_zero]
  module

theorem hyperbolicWeight55_one (i : Fin 5) :
    hyperbolicWeight55 i 1 1 = (1 : Cl55) := by
  rw [hyperbolicWeight55, one_smul, one_smul,
    ← hyperbolicProjector55_complement]

theorem hyperbolicWeight55_mul_axis
    (i : Fin 5) (a b : ℝ) :
    hyperbolicWeight55 i a b * hyperbolicAxis55 i =
      a • hyperbolicProjector55Plus i -
        b • hyperbolicProjector55Minus i := by
  rw [hyperbolicWeight55, ← hyperbolicProjector55_difference]
  simp only [add_mul, smul_mul_assoc, mul_sub,
    hyperbolicProjector55Plus_idem,
    hyperbolicProjector55Plus_mul_minus,
    hyperbolicProjector55Minus_mul_plus,
    hyperbolicProjector55Minus_idem, smul_zero]
  module

theorem hyperbolicWeight55_commutes_axis
    (i : Fin 5) (a b : ℝ) :
    hyperbolicWeight55 i a b * hyperbolicAxis55 i =
      hyperbolicAxis55 i * hyperbolicWeight55 i a b := by
  rw [hyperbolicWeight55_mul_axis]
  rw [hyperbolicWeight55, ← hyperbolicProjector55_difference]
  simp only [sub_mul, mul_add, mul_smul_comm,
    hyperbolicProjector55Plus_idem,
    hyperbolicProjector55Plus_mul_minus,
    hyperbolicProjector55Minus_mul_plus,
    hyperbolicProjector55Minus_idem, sub_zero, zero_sub]
  module

theorem hyperbolicWeight55_modularDerivation_axis_zero
    (i : Fin 5) (a b : ℝ) :
    cl55ModularDerivation (hyperbolicWeight55 i a b)
        (hyperbolicAxis55 i) = 0 := by
  exact cl55Commutator_of_commute _ _
    (hyperbolicWeight55_commutes_axis i a b)

end InfoGeometry.Clifford.Clifford55
