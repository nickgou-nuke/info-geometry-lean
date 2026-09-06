import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionLoxodromicCircularBridge
import InfoGeometry.Canonical.SplitOctonionRegularOperators

noncomputable section

namespace SplitOctonion

def ellipticAxisOperator (g : H) : Module.End ℝ SplitOctonion :=
  leftRegular (I_gen g)

theorem ellipticAxisOperator_apply (g : H) (z : SplitOctonion) :
    ellipticAxisOperator g z = I_gen g * z := by
  rfl

theorem ellipticAxisOperator_comp_self (g : H)
    (hg : star g = -g) (hn : Quaternion.normSq g = 1) :
    (ellipticAxisOperator g).comp (ellipticAxisOperator g) =
      -(LinearMap.id : Module.End ℝ SplitOctonion) := by
  have hsq : g * g = -(1 : H) := by
    have h := congrArg SplitOctonion.a (I_gen_sq g hg hn)
    simpa [I_gen, mul_a, mul_b] using h
  apply LinearMap.ext
  intro z
  rcases z with ⟨a, b⟩
  change I_gen g * (I_gen g * ⟨a, b⟩) = -⟨a, b⟩
  apply SplitOctonion.ext
  · simp only [mul_a, mul_b, I_gen, zero_mul, mul_zero, zero_add, add_zero]
    change g * (g * a) = -a
    rw [← mul_assoc, hsq]
    exact neg_one_mul a
  · simp only [mul_a, mul_b, I_gen, zero_mul, mul_zero, zero_add, add_zero]
    change (b * g) * g = -b
    rw [mul_assoc, hsq]
    exact mul_neg_one b

def ellipticOperatorFlow (g : H) (theta : ℝ) : Module.End ℝ SplitOctonion :=
  (Real.cos theta) • (LinearMap.id : Module.End ℝ SplitOctonion) +
    (Real.sin theta) • ellipticAxisOperator g

theorem ellipticOperatorFlow_zero (g : H) :
    ellipticOperatorFlow g 0 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp [ellipticOperatorFlow]

theorem ellipticOperatorFlow_add (g : H)
    (hg : star g = -g) (hn : Quaternion.normSq g = 1) (s t : ℝ) :
    (ellipticOperatorFlow g s).comp (ellipticOperatorFlow g t) =
      ellipticOperatorFlow g (s + t) := by
  apply LinearMap.ext
  intro z
  have hK : ellipticAxisOperator g (ellipticAxisOperator g z) = -z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (ellipticAxisOperator_comp_self g hg hn) z
  change Real.cos s •
      (Real.cos t • z + Real.sin t • ellipticAxisOperator g z) +
      Real.sin s • ellipticAxisOperator g
        (Real.cos t • z + Real.sin t • ellipticAxisOperator g z) =
    Real.cos (s + t) • z +
      Real.sin (s + t) • ellipticAxisOperator g z
  simp only [map_add, map_smul]
  rw [hK]
  rw [Real.cos_add, Real.sin_add]
  module

theorem ellipticOperatorFlow_inverse (g : H)
    (hg : star g = -g) (hn : Quaternion.normSq g = 1) (theta : ℝ) :
    (ellipticOperatorFlow g (-theta)).comp (ellipticOperatorFlow g theta) =
        LinearMap.id ∧
      (ellipticOperatorFlow g theta).comp (ellipticOperatorFlow g (-theta)) =
        LinearMap.id := by
  constructor
  · rw [ellipticOperatorFlow_add g hg hn, neg_add_cancel,
      ellipticOperatorFlow_zero]
  · rw [ellipticOperatorFlow_add g hg hn, add_neg_cancel,
      ellipticOperatorFlow_zero]

end SplitOctonion
