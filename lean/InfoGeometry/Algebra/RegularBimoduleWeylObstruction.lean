import InfoGeometry.Physics.RegularBimoduleCommutant

/-!
# Regular bimodules, phase relations, and conjugate-linear reflection

The imported owner proves the regular commutant equality and commutation of
left and right multiplication. An invertible phase pair is incompatible with
commutation unless its phase is one. Matrix adjunction provides the separate
conjugate-linear left/right exchange. No modular flow or Riemann-zero spectrum
is inferred from a finite Weyl pair.
-/

noncomputable section

namespace InfoGeometry.Algebra.RegularBimoduleWeylObstruction

section Phase

variable {R A : Type*} [Field R] [Ring A] [Algebra R A] [Nontrivial A]

theorem commuting_units_force_phase_one (x z : Aˣ) (q : R)
    (hcomm : Commute (x : A) (z : A))
    (hphase : (z : A) * (x : A) = algebraMap R A q * ((x : A) * (z : A))) :
    q = 1 := by
  have hprod : (↑(x * z) : A) = algebraMap R A q * (↑(x * z) : A) :=
    hcomm.eq.trans hphase
  have hc := congrArg (fun a : A => a * (↑((x * z)⁻¹) : A)) hprod
  have hscalar : (1 : A) = algebraMap R A q := by
    simpa only [mul_assoc, Units.mul_inv, mul_one] using hc
  apply (algebraMap R A).injective
  simpa only [map_one] using hscalar.symm

theorem nontrivial_phase_excludes_commutation (x z : Aˣ) (q : R)
    (hq : q ≠ 1)
    (hphase : (z : A) * (x : A) = algebraMap R A q * ((x : A) * (z : A))) :
    ¬ Commute (x : A) (z : A) := by
  intro hcomm
  exact hq (commuting_units_force_phase_one x z q hcomm hphase)

theorem phase_commutator (x z : A) (q : R)
    (hphase : z * x = q • (x * z)) :
    x * z - z * x = (1 - q) • (x * z) := by
  rw [hphase, sub_smul, one_smul]

theorem phase_anticommutator (x z : A) (q : R)
    (hphase : z * x = q • (x * z)) :
    x * z + z * x = (1 + q) • (x * z) := by
  rw [hphase, add_smul, one_smul]

end Phase

section Conjugation

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℂ

/-- Standard matrix adjunction on the regular complex matrix bimodule. -/
def matrixConjugation (T : Matrix3) : Matrix3 := star T

theorem matrixConjugation_involutive (T : Matrix3) :
    matrixConjugation (matrixConjugation T) = T := star_star T

/-- Scalars are conjugated; the exchange is not asserted to be complex linear. -/
theorem matrixConjugation_smul (c : ℂ) (T : Matrix3) :
    matrixConjugation (c • T) = star c • matrixConjugation T := by
  exact star_smul c T

theorem matrixConjugation_left_exchange (a T : Matrix3) :
    matrixConjugation (a * matrixConjugation T) = T * star a := by
  simp [matrixConjugation, star_mul]

theorem matrixConjugation_right_exchange (b T : Matrix3) :
    matrixConjugation (matrixConjugation T * b) = star b * T := by
  simp [matrixConjugation, star_mul]

end Conjugation

end InfoGeometry.Algebra.RegularBimoduleWeylObstruction
