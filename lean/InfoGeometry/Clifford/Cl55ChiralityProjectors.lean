import InfoGeometry.Clifford.Cl55OperatorZ2Grading
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Chiral projectors from the native Clifford volume element.

The chirality element is kept separate from any Krein fundamental symmetry.
This owner proves only the algebraic projector identities.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

def chirality55 : Cl55 := cl55WittVolume

def chiralityProjectorPlus55 : Cl55 :=
  (1 / 2 : ℝ) • ((1 : Cl55) + chirality55)

def chiralityProjectorMinus55 : Cl55 :=
  (1 / 2 : ℝ) • ((1 : Cl55) - chirality55)

theorem chirality55_sq : chirality55 * chirality55 = (1 : Cl55) := by
  exact cl55WittVolume_sq

theorem chiralityProjectorPlus55_idem :
    chiralityProjectorPlus55 * chiralityProjectorPlus55 =
      chiralityProjectorPlus55 := by
  unfold chiralityProjectorPlus55
  calc
    ((1 / 2 : ℝ) • (1 + chirality55)) *
        ((1 / 2 : ℝ) • (1 + chirality55)) =
        (1 / 4 : ℝ) • ((1 + chirality55) * (1 + chirality55)) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          norm_num
    _ = (1 / 4 : ℝ) • (2 • (1 : Cl55) + 2 • chirality55) := by
          rw [(show (1 + chirality55) * (1 + chirality55) =
            1 + 2 • chirality55 + chirality55 * chirality55 by
              noncomm_ring)]
          rw [chirality55_sq]
          module
    _ = (1 / 2 : ℝ) • (1 + chirality55) := by
          module

theorem chiralityProjectorMinus55_idem :
    chiralityProjectorMinus55 * chiralityProjectorMinus55 =
      chiralityProjectorMinus55 := by
  unfold chiralityProjectorMinus55
  calc
    ((1 / 2 : ℝ) • (1 - chirality55)) *
        ((1 / 2 : ℝ) • (1 - chirality55)) =
        (1 / 4 : ℝ) • ((1 - chirality55) * (1 - chirality55)) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          norm_num
    _ = (1 / 4 : ℝ) • (2 • (1 : Cl55) - 2 • chirality55) := by
          rw [(show (1 - chirality55) * (1 - chirality55) =
            1 - 2 • chirality55 + chirality55 * chirality55 by
              noncomm_ring)]
          rw [chirality55_sq]
          module
    _ = (1 / 2 : ℝ) • (1 - chirality55) := by
          module

theorem chiralityProjectors55_orthogonal :
    chiralityProjectorPlus55 * chiralityProjectorMinus55 = 0 := by
  unfold chiralityProjectorPlus55 chiralityProjectorMinus55
  calc
    ((1 / 2 : ℝ) • (1 + chirality55)) *
        ((1 / 2 : ℝ) • (1 - chirality55)) =
        (1 / 4 : ℝ) • ((1 + chirality55) * (1 - chirality55)) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          norm_num
    _ = (1 / 4 : ℝ) • (1 - chirality55 * chirality55) := by
          congr 1
          noncomm_ring
    _ = 0 := by rw [chirality55_sq]; simp

theorem chiralityProjectors55_orthogonal_reverse :
    chiralityProjectorMinus55 * chiralityProjectorPlus55 = 0 := by
  unfold chiralityProjectorPlus55 chiralityProjectorMinus55
  calc
    ((1 / 2 : ℝ) • (1 - chirality55)) *
        ((1 / 2 : ℝ) • (1 + chirality55)) =
        (1 / 4 : ℝ) • ((1 - chirality55) * (1 + chirality55)) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          norm_num
    _ = (1 / 4 : ℝ) • (1 - chirality55 * chirality55) := by
          congr 1
          noncomm_ring
    _ = 0 := by rw [chirality55_sq]; simp

theorem chiralityProjectors55_complement :
    chiralityProjectorPlus55 + chiralityProjectorMinus55 = (1 : Cl55) := by
  unfold chiralityProjectorPlus55 chiralityProjectorMinus55
  module

theorem chiralityProjectorPlus55_mul_axis_eq_axis_mul_minus
    (i : Fin 5) :
    chiralityProjectorPlus55 * hyperbolicAxis55 i =
      hyperbolicAxis55 i * chiralityProjectorMinus55 := by
  unfold chiralityProjectorPlus55 chiralityProjectorMinus55
  have hanti := cl55WittVolume_anticommutes_hyperbolicAxis i
  have hanti' : chirality55 * hyperbolicAxis55 i =
      -(hyperbolicAxis55 i * chirality55) := by
    unfold chirality55
    calc
      cl55WittVolume * hyperbolicAxis55 i =
          -(-(cl55WittVolume * hyperbolicAxis55 i)) := by simp
      _ = -(hyperbolicAxis55 i * cl55WittVolume) := by rw [hanti]
  calc
    (1 / 2 : ℝ) • (1 + chirality55) * hyperbolicAxis55 i =
        (1 / 2 : ℝ) •
          (hyperbolicAxis55 i + chirality55 * hyperbolicAxis55 i) := by
            simp [add_mul, smul_add]
    _ = (1 / 2 : ℝ) •
          (hyperbolicAxis55 i - hyperbolicAxis55 i * chirality55) := by
            rw [hanti']
            simp only [sub_eq_add_neg]
    _ = hyperbolicAxis55 i * ((1 / 2 : ℝ) • (1 - chirality55)) := by
            simp [smul_add, sub_eq_add_neg, mul_add, mul_neg]

theorem chiralityProjectorMinus55_mul_axis_eq_axis_mul_plus
    (i : Fin 5) :
    chiralityProjectorMinus55 * hyperbolicAxis55 i =
      hyperbolicAxis55 i * chiralityProjectorPlus55 := by
  unfold chiralityProjectorPlus55 chiralityProjectorMinus55
  have hanti := cl55WittVolume_anticommutes_hyperbolicAxis i
  have hanti' : chirality55 * hyperbolicAxis55 i =
      -(hyperbolicAxis55 i * chirality55) := by
    unfold chirality55
    calc
      cl55WittVolume * hyperbolicAxis55 i =
          -(-(cl55WittVolume * hyperbolicAxis55 i)) := by simp
      _ = -(hyperbolicAxis55 i * cl55WittVolume) := by rw [hanti]
  calc
    (1 / 2 : ℝ) • (1 - chirality55) * hyperbolicAxis55 i =
        (1 / 2 : ℝ) •
          (hyperbolicAxis55 i - chirality55 * hyperbolicAxis55 i) := by
            simp [sub_mul, smul_sub]
    _ = (1 / 2 : ℝ) •
          (hyperbolicAxis55 i + hyperbolicAxis55 i * chirality55) := by
            rw [hanti']
            simp only [sub_neg_eq_add]
    _ = hyperbolicAxis55 i * ((1 / 2 : ℝ) • (1 + chirality55)) := by
            simp [smul_add, mul_add]

theorem chiralityProjectorPlus55_axis_plus_zero (i : Fin 5) :
    chiralityProjectorPlus55 * hyperbolicAxis55 i *
        chiralityProjectorPlus55 = 0 := by
  rw [chiralityProjectorPlus55_mul_axis_eq_axis_mul_minus]
  rw [mul_assoc, chiralityProjectors55_orthogonal_reverse]
  simp

theorem chiralityProjectorMinus55_axis_minus_zero (i : Fin 5) :
    chiralityProjectorMinus55 * hyperbolicAxis55 i *
        chiralityProjectorMinus55 = 0 := by
  rw [chiralityProjectorMinus55_mul_axis_eq_axis_mul_plus]
  rw [mul_assoc, chiralityProjectors55_orthogonal]
  simp

end InfoGeometry.Clifford.Clifford55
