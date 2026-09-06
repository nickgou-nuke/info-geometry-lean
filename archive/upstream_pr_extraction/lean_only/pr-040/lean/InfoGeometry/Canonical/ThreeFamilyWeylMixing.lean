import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
# Fourier intertwining for the three-family Weyl carrier

This file records the finite algebraic change from the clock basis to the
cyclic-family basis.  It does not introduce a dynamical Hamiltonian or a
phenomenological mixing claim.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.ThreeFamilyWeylMixing

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev Mat3C := Matrix (Fin 3) (Fin 3) ℂ

def fourier3 (ω : ℂ) : Mat3C :=
  !![(1 : ℂ), 1, 1;
     1, ω, ω ^ 2;
     1, ω ^ 2, ω]

theorem fourier3_intertwines_shift (ω : ℂ) (hω : ω ^ 3 = 1) :
    fourier3 ω * colorShift = colorClock ω * fourier3 ω := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [fourier3, colorShift, colorClock, Matrix.mul_apply,
      Fin.sum_univ_three, hω, pow_two] <;>
    try ring
  all_goals
    first
    | exact hω.symm
    | calc
        ω = ω * 1 := by simp
        _ = ω * ω ^ 3 := by rw [hω]
        _ = ω ^ 4 := by ring

end InfoGeometry.Canonical.ThreeFamilyWeylMixing
