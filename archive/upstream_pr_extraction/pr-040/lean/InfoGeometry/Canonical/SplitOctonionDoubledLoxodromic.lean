import Mathlib.Tactic
import InfoGeometry.Canonical.HestenesLoxodromicRotor
import InfoGeometry.Canonical.SplitOctonionRegularProjectors

noncomputable section

namespace SplitOctonion

open InfoGeometry.Canonical

abbrev DoubledSplitOctonion := SplitOctonion × SplitOctonion

def doubledHyperbolicOperator (g : H) :
    Module.End ℝ DoubledSplitOctonion :=
  { toFun z :=
      (hyperbolicAxisOperator g z.1, hyperbolicAxisOperator g z.2)
    map_add' z w := by
      apply Prod.ext
      · exact (hyperbolicAxisOperator g).map_add z.1 w.1
      · exact (hyperbolicAxisOperator g).map_add z.2 w.2
    map_smul' r z := by
      apply Prod.ext
      · exact (hyperbolicAxisOperator g).map_smul r z.1
      · exact (hyperbolicAxisOperator g).map_smul r z.2 }

def doubledComplexOperator : Module.End ℝ DoubledSplitOctonion :=
  { toFun z := (-z.2, z.1)
    map_add' z w := by
      apply Prod.ext <;> simp [add_comm]
    map_smul' r z := by
      apply Prod.ext <;> simp }

theorem doubledHyperbolicOperator_sq (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicOperator g).comp (doubledHyperbolicOperator g) =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hx := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) x
  have hy := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) y
  exact Prod.ext (by simpa [doubledHyperbolicOperator, LinearMap.comp_apply] using hx)
    (by simpa [doubledHyperbolicOperator, LinearMap.comp_apply] using hy)

theorem doubledComplexOperator_sq :
    doubledComplexOperator.comp doubledComplexOperator =
      -(LinearMap.id : Module.End ℝ DoubledSplitOctonion) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [doubledComplexOperator, LinearMap.comp_apply]

theorem doubledOperators_commute (g : H) :
    (doubledHyperbolicOperator g).comp doubledComplexOperator =
      doubledComplexOperator.comp (doubledHyperbolicOperator g) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [doubledHyperbolicOperator, doubledComplexOperator,
    LinearMap.comp_apply]

theorem doubledLoxodromicAction_add (g : H)
    (hg : Quaternion.normSq g = 1)
    (t₁ θ₁ t₂ θ₂ : ℝ) (z : DoubledSplitOctonion) :
    realLoxodromicAction (doubledHyperbolicOperator g)
        doubledComplexOperator t₁ θ₁
        (realLoxodromicAction (doubledHyperbolicOperator g)
          doubledComplexOperator t₂ θ₂ z) =
      realLoxodromicAction (doubledHyperbolicOperator g)
        doubledComplexOperator (t₁ + t₂) (θ₁ + θ₂) z := by
  exact realLoxodromicAction_add
    (doubledHyperbolicOperator g) doubledComplexOperator
    (doubledHyperbolicOperator_sq g hg)
    (doubledComplexOperator_sq)
    (doubledOperators_commute g) t₁ θ₁ t₂ θ₂ z

theorem doubledLoxodromicAction_inverse (g : H)
    (hg : Quaternion.normSq g = 1)
    (t θ : ℝ) (z : DoubledSplitOctonion) :
    realLoxodromicAction (doubledHyperbolicOperator g)
        doubledComplexOperator (-t) (-θ)
        (realLoxodromicAction (doubledHyperbolicOperator g)
          doubledComplexOperator t θ z) = z := by
  exact realLoxodromicAction_inverse
    (doubledHyperbolicOperator g) doubledComplexOperator
    (doubledHyperbolicOperator_sq g hg)
    (doubledComplexOperator_sq)
    (doubledOperators_commute g) t θ z

end SplitOctonion
