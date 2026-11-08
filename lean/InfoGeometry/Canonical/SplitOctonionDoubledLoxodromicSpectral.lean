import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionDoubledLoxodromic

/-!
# Concrete spectral bridge for the doubled split-octonion loxodromic flow

Over the real doubled carrier the hyperbolic operator has genuine idempotent
spectral projectors.  The commuting complex structure is retained as a real
operator; no real ``± i`` projectors are introduced.
-/

noncomputable section

namespace SplitOctonion

open InfoGeometry.Canonical

def doubledHyperbolicProjectorPlus (g : H) :
    Module.End ℝ DoubledSplitOctonion :=
  (1 / 2 : ℝ) •
    ((LinearMap.id : Module.End ℝ DoubledSplitOctonion) +
      doubledHyperbolicOperator g)

def doubledHyperbolicProjectorMinus (g : H) :
    Module.End ℝ DoubledSplitOctonion :=
  (1 / 2 : ℝ) •
    ((LinearMap.id : Module.End ℝ DoubledSplitOctonion) -
      doubledHyperbolicOperator g)

theorem doubledHyperbolicProjectorPlus_add_minus (g : H) :
    doubledHyperbolicProjectorPlus g + doubledHyperbolicProjectorMinus g =
      (LinearMap.id : Module.End ℝ DoubledSplitOctonion) := by
  apply LinearMap.ext
  intro z
  simp [doubledHyperbolicProjectorPlus,
    doubledHyperbolicProjectorMinus]
  module

theorem doubledHyperbolicProjectorPlus_sq (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicProjectorPlus g).comp
        (doubledHyperbolicProjectorPlus g) =
      doubledHyperbolicProjectorPlus g := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorPlus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicProjectorMinus_sq (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicProjectorMinus g).comp
        (doubledHyperbolicProjectorMinus g) =
      doubledHyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorMinus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicProjectorPlus_comp_minus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicProjectorPlus g).comp
        (doubledHyperbolicProjectorMinus g) = 0 := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorPlus,
    doubledHyperbolicProjectorMinus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicProjectorMinus_comp_plus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicProjectorMinus g).comp
        (doubledHyperbolicProjectorPlus g) = 0 := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorPlus,
    doubledHyperbolicProjectorMinus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicOperator_comp_projectorPlus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicOperator g).comp
        (doubledHyperbolicProjectorPlus g) =
      doubledHyperbolicProjectorPlus g := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorPlus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicOperator_comp_projectorMinus (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicOperator g).comp
        (doubledHyperbolicProjectorMinus g) =
      -doubledHyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorMinus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicProjectorPlus_comp_operator (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicProjectorPlus g).comp
        (doubledHyperbolicOperator g) =
      doubledHyperbolicProjectorPlus g := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorPlus, LinearMap.comp_apply]
  rw [hz]
  module

theorem doubledHyperbolicProjectorMinus_comp_operator (g : H)
    (hg : Quaternion.normSq g = 1) :
    (doubledHyperbolicProjectorMinus g).comp
        (doubledHyperbolicOperator g) =
      -doubledHyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  have hz : doubledHyperbolicOperator g
      (doubledHyperbolicOperator g z) = z := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (doubledHyperbolicOperator_sq g hg) z
  simp [doubledHyperbolicProjectorMinus, LinearMap.comp_apply]
  rw [hz]
  module

def doubledHyperbolicFlow (g : H) (η : ℝ) :
    Module.End ℝ DoubledSplitOctonion :=
  (Real.cosh η) • (LinearMap.id : Module.End ℝ DoubledSplitOctonion) +
    (Real.sinh η) • doubledHyperbolicOperator g

theorem doubledHyperbolicFlow_projector_decomposition (g : H) (η : ℝ) :
    doubledHyperbolicFlow g η =
      (Real.exp η) • doubledHyperbolicProjectorPlus g +
        (Real.exp (-η)) • doubledHyperbolicProjectorMinus g := by
  apply LinearMap.ext
  intro z
  change Real.cosh η • z + Real.sinh η •
      doubledHyperbolicOperator g z =
    Real.exp η • ((1 / 2 : ℝ) •
      (z + doubledHyperbolicOperator g z)) +
      Real.exp (-η) • ((1 / 2 : ℝ) •
        (z - doubledHyperbolicOperator g z))
  rw [Real.cosh_eq, Real.sinh_eq]
  module

theorem doubledHyperbolicProjector_commutes_complex (g : H) :
    (doubledHyperbolicProjectorPlus g).comp doubledComplexOperator =
      doubledComplexOperator.comp (doubledHyperbolicProjectorPlus g) := by
  apply LinearMap.ext
  intro z
  unfold doubledHyperbolicProjectorPlus
  simp [doubledComplexOperator, doubledHyperbolicOperator]
  abel

theorem doubledHyperbolicProjectorMinus_commutes_complex (g : H) :
    (doubledHyperbolicProjectorMinus g).comp doubledComplexOperator =
      doubledComplexOperator.comp (doubledHyperbolicProjectorMinus g) := by
  apply LinearMap.ext
  intro z
  unfold doubledHyperbolicProjectorMinus
  simp [doubledComplexOperator, doubledHyperbolicOperator]
  module

theorem doubledLoxodromicAction_preserves_projectorPlus (g : H)
    (hg : Quaternion.normSq g = 1) (η θ : ℝ)
    (z : DoubledSplitOctonion) :
    doubledHyperbolicProjectorPlus g
        (realLoxodromicAction (doubledHyperbolicOperator g)
          doubledComplexOperator η θ z) =
      realLoxodromicAction (doubledHyperbolicOperator g)
        doubledComplexOperator η θ
          (doubledHyperbolicProjectorPlus g z) := by
  unfold realLoxodromicAction realBoostAction realRotorAction
  simp only [map_add, map_smul]
  have hKI : ∀ w : DoubledSplitOctonion,
      doubledHyperbolicOperator g (doubledComplexOperator w) =
        doubledComplexOperator (doubledHyperbolicOperator g w) := by
    intro w
    exact LinearMap.congr_fun (doubledOperators_commute g) w
  have hPK : ∀ w : DoubledSplitOctonion,
      doubledHyperbolicProjectorPlus g
        (doubledHyperbolicOperator g w) =
        doubledHyperbolicOperator g
          (doubledHyperbolicProjectorPlus g w) := by
    intro w
    calc
      doubledHyperbolicProjectorPlus g
          (doubledHyperbolicOperator g w) =
          doubledHyperbolicProjectorPlus g w :=
        LinearMap.congr_fun
          (doubledHyperbolicProjectorPlus_comp_operator g hg) w
      _ = doubledHyperbolicOperator g
          (doubledHyperbolicProjectorPlus g w) :=
        (LinearMap.congr_fun
          (doubledHyperbolicOperator_comp_projectorPlus g hg) w).symm
  have hPC : ∀ w : DoubledSplitOctonion,
      doubledHyperbolicProjectorPlus g (doubledComplexOperator w) =
        doubledComplexOperator (doubledHyperbolicProjectorPlus g w) := by
    intro w
    exact LinearMap.congr_fun
      (doubledHyperbolicProjector_commutes_complex g) w
  rw [hPK z, hPK (doubledComplexOperator z), hPC z]

theorem doubledLoxodromicAction_preserves_projectorMinus (g : H)
    (hg : Quaternion.normSq g = 1) (η θ : ℝ)
    (z : DoubledSplitOctonion) :
    doubledHyperbolicProjectorMinus g
        (realLoxodromicAction (doubledHyperbolicOperator g)
          doubledComplexOperator η θ z) =
      realLoxodromicAction (doubledHyperbolicOperator g)
        doubledComplexOperator η θ
          (doubledHyperbolicProjectorMinus g z) := by
  unfold realLoxodromicAction realBoostAction realRotorAction
  simp only [map_add, map_smul]
  have hKI : ∀ w : DoubledSplitOctonion,
      doubledHyperbolicOperator g (doubledComplexOperator w) =
        doubledComplexOperator (doubledHyperbolicOperator g w) := by
    intro w
    exact LinearMap.congr_fun (doubledOperators_commute g) w
  have hPK : ∀ w : DoubledSplitOctonion,
      doubledHyperbolicProjectorMinus g
          (doubledHyperbolicOperator g w) =
        doubledHyperbolicOperator g
          (doubledHyperbolicProjectorMinus g w) := by
    intro w
    calc
      doubledHyperbolicProjectorMinus g
          (doubledHyperbolicOperator g w) =
          -doubledHyperbolicProjectorMinus g w :=
        LinearMap.congr_fun
          (doubledHyperbolicProjectorMinus_comp_operator g hg) w
      _ = doubledHyperbolicOperator g
          (doubledHyperbolicProjectorMinus g w) := by
        symm
        exact LinearMap.congr_fun
          (doubledHyperbolicOperator_comp_projectorMinus g hg) w
  have hPC : ∀ w : DoubledSplitOctonion,
      doubledHyperbolicProjectorMinus g (doubledComplexOperator w) =
        doubledComplexOperator (doubledHyperbolicProjectorMinus g w) := by
    intro w
    exact LinearMap.congr_fun
      (doubledHyperbolicProjectorMinus_commutes_complex g) w
  rw [hPK z, hPK (doubledComplexOperator z), hPC z]

end SplitOctonion
