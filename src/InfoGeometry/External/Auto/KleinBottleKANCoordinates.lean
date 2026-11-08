import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.DeterminantSupergrading
import InfoGeometry.External.Auto.IwasawaKUnification
import InfoGeometry.External.Auto.KleinBottleSymmetry
import InfoGeometry.External.Auto.KleinFourAnomalyCancellation

noncomputable section

namespace InfoGeometry.Canonical.KleinBottleKANCoordinates

open Matrix

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- The `J`-axis: modular sheet swap. -/
def JAxis : M2R := modular_j

/-- The `ε`-axis: chiral determinant parity. -/
def epsilonAxis : M2R := chiralParity

/-- The `N`-axis: nilpotent cross-cap shear. -/
def NAxis (x : ℝ) : M2R :=
  InfoGeometry.Quantum.IwasawaKUnification.generatorN x

@[simp] theorem JAxis_sq : JAxis * JAxis = (1 : M2R) := by
  exact modular_j_sq

@[simp] theorem epsilonAxis_sq : epsilonAxis * epsilonAxis = (1 : M2R) := by
  exact chiralParity_sq

@[simp] theorem NAxis_sq (x : ℝ) : NAxis x * NAxis x = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NAxis, InfoGeometry.Quantum.IwasawaKUnification.generatorN,
      Matrix.mul_apply, Fin.sum_univ_two]

/--
The concrete cross-cap sign flip:
conjugating the nilpotent shear by the chiral parity reverses its sign.
-/
theorem epsilon_conj_NAxis (x : ℝ) :
    epsilonAxis * NAxis x * epsilonAxis = -NAxis x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [epsilonAxis, NAxis, chiralParity,
      InfoGeometry.Quantum.IwasawaKUnification.generatorN,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The nilpotent cross-cap axis has determinant zero. -/
theorem det_NAxis (x : ℝ) : (NAxis x).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [NAxis, InfoGeometry.Quantum.IwasawaKUnification.generatorN]

/--
Concrete compatibility collapse:
if the nilpotent cross-cap axis is also chiral-commuting, then over `ℝ`
the cross-cap axis must vanish.
-/
theorem NAxis_vanishes_of_chiral_commute (x : ℝ)
    (hcomm : epsilonAxis * NAxis x = NAxis x * epsilonAxis) :
    NAxis x = 0 := by
  have h_auto : epsilonAxis * NAxis x * epsilonAxis = NAxis x := by
    calc
      epsilonAxis * NAxis x * epsilonAxis
          = (NAxis x * epsilonAxis) * epsilonAxis := by rw [hcomm]
      _ = NAxis x * (epsilonAxis * epsilonAxis) := by rw [mul_assoc]
      _ = NAxis x * 1 := by rw [epsilonAxis_sq]
      _ = NAxis x := by simp
  have hneg : NAxis x = -NAxis x := by
    calc
      NAxis x = epsilonAxis * NAxis x * epsilonAxis := h_auto.symm
      _ = -NAxis x := epsilon_conj_NAxis x
  ext i j
  have hentry : NAxis x i j = (-NAxis x) i j := by
    exact congrFun (congrFun hneg i) j
  have hzero : NAxis x i j + NAxis x i j = 0 :=
    (eq_neg_iff_add_eq_zero.mp hentry)
  have htwo : (2 : ℝ) * NAxis x i j = 0 := by
    linarith
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp htwo).resolve_left h2

/--
Symmetry-adapted Klein bottle coordinate package:
`J`, `ε`, and `N` give the mirror, chiral, and cross-cap axes.  The theorem
records exactly the involution/nilpotence/sign-flip facts used by the local
KAN anomaly cancellation bridge.
-/
theorem klein_bottle_kan_coordinate_axes (x : ℝ) :
    JAxis * JAxis = (1 : M2R) ∧
      epsilonAxis * epsilonAxis = (1 : M2R) ∧
      NAxis x * NAxis x = 0 ∧
      epsilonAxis * NAxis x * epsilonAxis = -NAxis x ∧
      (NAxis x).det = 0 := by
  exact ⟨JAxis_sq, epsilonAxis_sq, NAxis_sq x, epsilon_conj_NAxis x,
    det_NAxis x⟩

end InfoGeometry.Canonical.KleinBottleKANCoordinates
