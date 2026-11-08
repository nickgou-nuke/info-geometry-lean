import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionRegularOperators
import InfoGeometry.Canonical.HestenesPhaseBoostRotors

noncomputable section

namespace SplitOctonion

open scoped Quaternion

lemma H_mul_star_self (g : H) : g * star g = (Quaternion.normSq g : ℝ) • (1 : H) := by
  ext <;> simp [Quaternion.normSq] <;> ring

def hyperbolicAxisOperator (g : H) : Module.End ℝ SplitOctonion :=
  leftRegular (J_g g)

theorem hyperbolicAxisOperator_apply (g : H) (z : SplitOctonion) :
    hyperbolicAxisOperator g z = J_g g * z := by
  rfl

theorem hyperbolicAxisOperator_sq (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicAxisOperator g).comp (hyperbolicAxisOperator g) =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  change J_g g * (J_g g * ⟨a, b⟩) = ⟨a, b⟩
  apply SplitOctonion.ext
  · change 0 * (0 * a + star b * g) +
      star (b * 0 + g * star a) * g = a
    simp only [zero_mul, mul_zero, zero_add]
    simp only [star_mul, star_star]
    rw [mul_assoc, H_star_mul_self, hg, one_smul, mul_one]
  · change (b * 0 + g * star a) * 0 +
      g * star (0 * a + star b * g) = b
    simp only [zero_mul, mul_zero, zero_add]
    simp only [star_mul, star_star]
    rw [← mul_assoc, H_mul_star_self, hg, one_smul, one_mul]

def hyperbolicProjectorPlus (g : H) : Module.End ℝ SplitOctonion :=
  (1 / 2 : ℝ) • (1 + hyperbolicAxisOperator g)

def hyperbolicProjectorMinus (g : H) : Module.End ℝ SplitOctonion :=
  (1 / 2 : ℝ) • (1 - hyperbolicAxisOperator g)

def hyperbolicOperatorFlow (g : H) (eta : ℝ) : Module.End ℝ SplitOctonion :=
  (Real.cosh eta) • (LinearMap.id : Module.End ℝ SplitOctonion) +
    (Real.sinh eta) • hyperbolicAxisOperator g

theorem hyperbolicOperatorFlow_zero (g : H) :
    hyperbolicOperatorFlow g 0 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp [hyperbolicOperatorFlow]

theorem hyperbolicOperatorFlow_add (g : H)
    (hg : Quaternion.normSq g = 1) (s t : ℝ) :
    (hyperbolicOperatorFlow g s).comp (hyperbolicOperatorFlow g t) =
      hyperbolicOperatorFlow g (s + t) := by
  apply LinearMap.ext
  intro z
  have hK : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  change Real.cosh s •
      (Real.cosh t • z + Real.sinh t • hyperbolicAxisOperator g z) +
      Real.sinh s • hyperbolicAxisOperator g
        (Real.cosh t • z + Real.sinh t • hyperbolicAxisOperator g z) =
    Real.cosh (s + t) • z +
      Real.sinh (s + t) • hyperbolicAxisOperator g z
  simp only [map_add, map_smul]
  rw [hK]
  rw [Real.cosh_add, Real.sinh_add]
  module

theorem hyperbolicOperatorFlow_inverse (g : H)
    (hg : Quaternion.normSq g = 1) (eta : ℝ) :
    (hyperbolicOperatorFlow g (-eta)).comp (hyperbolicOperatorFlow g eta) =
        LinearMap.id ∧
      (hyperbolicOperatorFlow g eta).comp (hyperbolicOperatorFlow g (-eta)) =
        LinearMap.id := by
  constructor
  · rw [hyperbolicOperatorFlow_add g hg, neg_add_cancel,
      hyperbolicOperatorFlow_zero]
  · rw [hyperbolicOperatorFlow_add g hg, add_neg_cancel,
      hyperbolicOperatorFlow_zero]

theorem hyperbolicProjectorPlus_sq (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicProjectorPlus g).comp (hyperbolicProjectorPlus g) =
      hyperbolicProjectorPlus g := by
  apply LinearMap.ext
  intro z
  have hk := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  have hzz : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa using hk
  change (1 / 2 : ℝ) •
      ((1 / 2 : ℝ) • (z + hyperbolicAxisOperator g z) +
        hyperbolicAxisOperator g ((1 / 2 : ℝ) •
          (z + hyperbolicAxisOperator g z))) =
    (1 / 2 : ℝ) • (z + hyperbolicAxisOperator g z)
  simp only [map_smul, map_add]
  rw [hzz]
  module

theorem hyperbolicProjectorMinus_sq (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicProjectorMinus g).comp (hyperbolicProjectorMinus g) =
      hyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  have hk := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  have hzz : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa using hk
  change (1 / 2 : ℝ) •
      ((1 / 2 : ℝ) • (z - hyperbolicAxisOperator g z) -
        hyperbolicAxisOperator g ((1 / 2 : ℝ) •
          (z - hyperbolicAxisOperator g z))) =
    (1 / 2 : ℝ) • (z - hyperbolicAxisOperator g z)
  simp only [map_smul, map_sub]
  rw [hzz]
  module

theorem hyperbolicProjectorPlus_comp_minus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicProjectorPlus g).comp (hyperbolicProjectorMinus g) = 0 := by
  apply LinearMap.ext
  intro z
  have hk := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  have hzz : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa using hk
  change (1 / 2 : ℝ) •
      ((1 / 2 : ℝ) • (z - hyperbolicAxisOperator g z) +
        hyperbolicAxisOperator g ((1 / 2 : ℝ) •
          (z - hyperbolicAxisOperator g z))) = 0
  rw [map_smul, map_sub, hzz]
  module

theorem hyperbolicProjectorMinus_comp_plus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicProjectorMinus g).comp (hyperbolicProjectorPlus g) = 0 := by
  apply LinearMap.ext
  intro z
  have hk := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  have hzz : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa using hk
  change (1 / 2 : ℝ) •
      ((1 / 2 : ℝ) • (z + hyperbolicAxisOperator g z) -
        hyperbolicAxisOperator g ((1 / 2 : ℝ) •
          (z + hyperbolicAxisOperator g z))) = 0
  rw [map_smul, map_add, hzz]
  module

theorem hyperbolicProjectorPlus_add_minus (g : H) :
    hyperbolicProjectorPlus g + hyperbolicProjectorMinus g =
      (1 : Module.End ℝ SplitOctonion) := by
  apply LinearMap.ext
  intro z
  change (1 / 2 : ℝ) • (z + hyperbolicAxisOperator g z) +
      (1 / 2 : ℝ) • (z - hyperbolicAxisOperator g z) = z
  module

theorem hyperbolicAxisOperator_comp_projectorPlus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicAxisOperator g).comp (hyperbolicProjectorPlus g) =
      hyperbolicProjectorPlus g := by
  apply LinearMap.ext
  intro z
  have hk := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  have hzz : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa using hk
  change hyperbolicAxisOperator g ((1 / 2 : ℝ) •
      (z + hyperbolicAxisOperator g z)) =
    (1 / 2 : ℝ) • (z + hyperbolicAxisOperator g z)
  rw [map_smul, map_add, hzz]
  module

theorem hyperbolicAxisOperator_comp_projectorMinus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (hyperbolicAxisOperator g).comp (hyperbolicProjectorMinus g) =
      -hyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  have hk := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) z
  have hzz : hyperbolicAxisOperator g (hyperbolicAxisOperator g z) = z := by
    simpa using hk
  change hyperbolicAxisOperator g ((1 / 2 : ℝ) •
      (z - hyperbolicAxisOperator g z)) =
    -((1 / 2 : ℝ) • (z - hyperbolicAxisOperator g z))
  rw [map_smul, map_sub, hzz]
  module

theorem hyperbolicAxisOperator_twin_wave
    (g : H) (eta : ℝ)
    (z : SplitOctonion) :
    InfoGeometry.Canonical.realBoostAction (hyperbolicAxisOperator g) eta z =
      (Real.exp eta) • hyperbolicProjectorPlus g z +
        (Real.exp (-eta)) • hyperbolicProjectorMinus g z := by
  unfold InfoGeometry.Canonical.realBoostAction
    hyperbolicProjectorPlus hyperbolicProjectorMinus
  change Real.cosh eta • z + Real.sinh eta • hyperbolicAxisOperator g z =
    Real.exp eta • ((1 / 2 : ℝ) •
      (z + hyperbolicAxisOperator g z)) +
      Real.exp (-eta) • ((1 / 2 : ℝ) •
        (z - hyperbolicAxisOperator g z))
  rw [Real.cosh_eq, Real.sinh_eq]
  module

theorem hyperbolicOperatorFlow_projector_decomposition
    (g : H) (eta : ℝ) :
    hyperbolicOperatorFlow g eta =
      (Real.exp eta) • hyperbolicProjectorPlus g +
        (Real.exp (-eta)) • hyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  change Real.cosh eta • z + Real.sinh eta • hyperbolicAxisOperator g z =
    Real.exp eta • ((1 / 2 : ℝ) •
      (z + hyperbolicAxisOperator g z)) +
      Real.exp (-eta) • ((1 / 2 : ℝ) •
        (z - hyperbolicAxisOperator g z))
  rw [Real.cosh_eq, Real.sinh_eq]
  module

end SplitOctonion
