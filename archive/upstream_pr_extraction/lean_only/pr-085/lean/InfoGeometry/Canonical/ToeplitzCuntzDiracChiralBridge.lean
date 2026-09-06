import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

/-!
# Native chiral Dirac operators on the ternary Toeplitz--Cuntz algebra

The cyclic supercharge owned by
`ToeplitzCuntzThreeCyclicSuperchargeBridge` is the native three-colour
operator. Its star is the corresponding opposite leg. This file only
packages their sum, difference, and commutator; it does not introduce a
coordinate representation on octonions or identify the defect with a
particular geometric axis.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzDiracChiralBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- The native three-colour differential leg. -/
def diracPlus : A :=
  cyclicSupercharge g + star (cyclicSupercharge g)

/-- The native three-colour chiral difference leg. -/
def diracMinus : A :=
  cyclicSupercharge g - star (cyclicSupercharge g)

/-- The commutator defect of the two native differential legs. -/
def thermalTimeDefect : A :=
  star (cyclicSupercharge g) * cyclicSupercharge g -
    cyclicSupercharge g * star (cyclicSupercharge g)

theorem diracPlus_add_diracMinus :
    diracPlus g + diracMinus g = 2 * cyclicSupercharge g := by
  dsimp [diracPlus, diracMinus]
  noncomm_ring

theorem diracPlus_sub_diracMinus :
    diracPlus g - diracMinus g =
      2 * star (cyclicSupercharge g) := by
  dsimp [diracPlus, diracMinus]
  noncomm_ring

theorem diracPlus_star :
    star (diracPlus g) = diracPlus g := by
  dsimp [diracPlus]
  simp [star_add, star_star, add_comm]

theorem diracMinus_star :
    star (diracMinus g) = -diracMinus g := by
  dsimp [diracMinus]
  simp [star_sub, star_star]

/-- The commutator of the chiral sum and difference is twice the native
left/right defect. -/
theorem diracPlus_diracMinus_commutator :
    diracPlus g * diracMinus g - diracMinus g * diracPlus g =
      2 * thermalTimeDefect g := by
  dsimp [diracPlus, diracMinus, thermalTimeDefect]
  noncomm_ring

theorem diracPlus_diracMinus_anticommutator :
    diracPlus g * diracMinus g + diracMinus g * diracPlus g =
      2 * (cyclicSupercharge g * cyclicSupercharge g -
        star (cyclicSupercharge g) * star (cyclicSupercharge g)) := by
  dsimp [diracPlus, diracMinus]
  noncomm_ring

/-- The native Toeplitz defect is the cubic-SUSY vacuum defect. -/
theorem thermalTimeDefect_eq_cyclicSupercharge_defect :
    thermalTimeDefect g = 0 := by
  dsimp [thermalTimeDefect]
  rw [cyclicSupercharge_star_mul_self g,
    cyclicSupercharge_mul_star g]
  exact sub_self _

theorem diracPlus_diracMinus_anticommute
    (hQsq : cyclicSupercharge g * cyclicSupercharge g =
      star (cyclicSupercharge g) * star (cyclicSupercharge g)) :
    diracPlus g * diracMinus g + diracMinus g * diracPlus g = 0 := by
  rw [diracPlus_diracMinus_anticommutator g, hQsq, sub_self, mul_zero]

theorem diracPlus_diracMinus_commute :
    diracPlus g * diracMinus g = diracMinus g * diracPlus g := by
  have h := diracPlus_diracMinus_commutator g
  rw [thermalTimeDefect_eq_cyclicSupercharge_defect g] at h
  have hzero :
      diracPlus g * diracMinus g - diracMinus g * diracPlus g = 0 := by
    simpa using h
  exact sub_eq_zero.mp hzero

theorem diracPlus_mul_P0 :
    diracPlus g * g.P0 = 0 := by
  dsimp [diracPlus]
  rw [add_mul, cyclicSupercharge_defect_annihilation_right g]
  rw [cyclicSupercharge_star_eq_sq g]
  rw [mul_assoc, cyclicSupercharge_defect_annihilation_right g]
  simp

theorem diracMinus_mul_P0 :
    diracMinus g * g.P0 = 0 := by
  dsimp [diracMinus]
  rw [sub_mul, cyclicSupercharge_defect_annihilation_right g]
  rw [cyclicSupercharge_star_eq_sq g]
  rw [mul_assoc, cyclicSupercharge_defect_annihilation_right g]
  simp

theorem P0_mul_diracPlus :
    g.P0 * diracPlus g = 0 := by
  dsimp [diracPlus]
  rw [mul_add, cyclicSupercharge_defect_annihilation_left g]
  rw [cyclicSupercharge_star_eq_sq g]
  rw [← mul_assoc, cyclicSupercharge_defect_annihilation_left g]
  simp

theorem P0_mul_diracMinus :
    g.P0 * diracMinus g = 0 := by
  dsimp [diracMinus]
  rw [mul_sub, cyclicSupercharge_defect_annihilation_left g]
  rw [cyclicSupercharge_star_eq_sq g]
  rw [← mul_assoc, cyclicSupercharge_defect_annihilation_left g]
  simp

theorem toeplitz_cuntz_dirac_chiral_synthesis :
    diracPlus g + diracMinus g = 2 * cyclicSupercharge g ∧
      diracPlus g * diracMinus g - diracMinus g * diracPlus g =
        2 * thermalTimeDefect g ∧
      thermalTimeDefect g = 0 :=
  ⟨diracPlus_add_diracMinus g,
    diracPlus_diracMinus_commutator g,
    thermalTimeDefect_eq_cyclicSupercharge_defect g⟩

end InfoGeometry.Canonical.ToeplitzCuntzDiracChiralBridge
