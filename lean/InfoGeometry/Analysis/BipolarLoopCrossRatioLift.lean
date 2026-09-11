import InfoGeometry.Analysis.BipolarLoopExpLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BipolarAdmissibleLoops

/-!
# Native exponential lift of the bipolar coordinate along admissible loops

This owner connects the repository's admissible-loop carrier to Mathlib's
exponential covering.  It proves existence of a genuine lifted path for the
nonvanishing coordinate `s / (1 - s)` and records its endpoint as an integral
deck translation.  It does not identify that integer with a winding number or
with a contour integral; those are separate downstream statements.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLoopCrossRatioLift

open Complex Set Topology
open InfoGeometry.Analysis.BipolarAdmissibleLoops
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Analysis.BipolarLoopExpLift

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}

/-- The base point of an admissible loop as a point of the punctured plane. -/
def basePoint (γ : AdmissibleLoop) : PuncturedPlaneCarrier :=
  ⟨γ.base, by
    simpa [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_source] using
      (path_mem_punctured γ (t := 0))⟩

@[simp] theorem basePoint_val (γ : AdmissibleLoop) :
    (basePoint γ : ℂ) = γ.base := rfl

/-- The rational bipolar coordinate transported along an admissible loop. -/
def crossRatioPath (γ : AdmissibleLoop) :
    Path (bipolarCrossRatioMap (basePoint γ))
      (bipolarCrossRatioMap (basePoint γ)) where
  toFun t := bipolarCrossRatioMap ⟨γ.path t, path_mem_punctured γ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro t
    have hmem : γ.path t ∈ punctured01 := path_mem_punctured γ
    have hden : 1 - γ.path t ≠ 0 := one_sub_ne_zero_of_mem hmem
    exact (continuousAt_id.div₀
      (continuousAt_const.sub continuousAt_id) hden).comp
      γ.path.continuous.continuousAt
  source' := by
    apply Subtype.ext
    simp [bipolarCrossRatioMap, basePoint]
  target' := by
    apply Subtype.ext
    simp [bipolarCrossRatioMap, basePoint]

@[simp] theorem crossRatioPath_apply (γ : AdmissibleLoop) (t : unitInterval) :
    (crossRatioPath γ t : ℂ) = crossRatio01 (γ.path t) := rfl

/-- The base point of the translated path around the second puncture. -/
def shiftedBasePoint (γ : AdmissibleLoop) : NonzeroComplex :=
  ⟨γ.base - 1, by
    have hmem : γ.path (0 : unitInterval) ∈ punctured01 :=
      path_mem_punctured γ
    rw [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_source] at hmem
    exact sub_ne_zero.mpr hmem.2⟩

@[simp] theorem shiftedBasePoint_val (γ : AdmissibleLoop) :
    (shiftedBasePoint γ : ℂ) = γ.base - 1 := rfl

theorem shiftedBasePoint_eq_exp_log (γ : AdmissibleLoop) :
    shiftedBasePoint γ =
      (⟨Complex.exp (Complex.log (γ.base - 1)),
        Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
  apply Subtype.ext
  change γ.base - 1 = Complex.exp (Complex.log (γ.base - 1))
  have hne : γ.base - 1 ≠ 0 := sub_ne_zero.mpr (by
    have hmem : γ.path (0 : unitInterval) ∈ punctured01 :=
      path_mem_punctured γ
    rw [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_source] at hmem
    exact hmem.2)
  exact (Complex.exp_log hne).symm

/-- The translated nonvanishing coordinate transported along the same loop. -/
def shiftedPath (γ : AdmissibleLoop) :
    Path (shiftedBasePoint γ) (shiftedBasePoint γ) where
  toFun t :=
    ⟨γ.path t - 1, sub_ne_zero.mpr (path_mem_punctured γ).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_id.sub continuousAt_const).comp
      γ.path.continuous.continuousAt
  source' := by
    apply Subtype.ext
    change γ.path 0 - 1 = γ.base - 1
    rw [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_source]
  target' := by
    apply Subtype.ext
    change γ.path 1 - 1 = γ.base - 1
    rw [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_target]

@[simp] theorem shiftedPath_apply (γ : AdmissibleLoop) (t : unitInterval) :
    (shiftedPath γ t : ℂ) = γ.path t - 1 := rfl

theorem shiftedPath_source_eq_exp_log (γ : AdmissibleLoop) :
    shiftedPath γ 0 =
      (⟨Complex.exp (Complex.log (γ.base - 1)),
        Complex.exp_ne_zero _⟩ : NonzeroComplex) := by
  exact (shiftedPath γ).source.trans (shiftedBasePoint_eq_exp_log γ)

theorem crossRatioPath_endpoint_period (γ : AdmissibleLoop) :
    ∃ n : ℤ,
      (Complex.isCoveringMap_exp.liftPath (crossRatioPath γ)
        (bipolarLog γ.base) (by
          apply Subtype.ext
          change crossRatio01 (γ.path 0) = Complex.exp (bipolarLog γ.base)
          rw [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_source]
          exact (exp_bipolarLog (basePoint γ).property).symm) ) 1 =
        bipolarLog γ.base + n * (2 * (Real.pi : ℂ) * Complex.I) := by
  exact exp_lift_loop_endpoint_period (crossRatioPath γ)
    (bipolarLog γ.base) (by
      apply Subtype.ext
      change crossRatio01 γ.base = Complex.exp (bipolarLog γ.base)
      exact (exp_bipolarLog (basePoint γ).property).symm)

theorem shiftedPath_endpoint_period (γ : AdmissibleLoop) :
    ∃ n : ℤ,
      (Complex.isCoveringMap_exp.liftPath (shiftedPath γ)
        (Complex.log (γ.base - 1)) (shiftedPath_source_eq_exp_log γ)) 1 =
        Complex.log (γ.base - 1) + n * (2 * (Real.pi : ℂ) * Complex.I) := by
  exact exp_lift_loop_endpoint_period (shiftedPath γ)
    (Complex.log (γ.base - 1)) (shiftedBasePoint_eq_exp_log γ)

theorem bipolar_endpoint_period_pair (γ : AdmissibleLoop) :
    (∃ n₀ : ℤ,
      (Complex.isCoveringMap_exp.liftPath (crossRatioPath γ)
        (bipolarLog γ.base) (by
          apply Subtype.ext
          change crossRatio01 (γ.path 0) = Complex.exp (bipolarLog γ.base)
          rw [InfoGeometry.Analysis.BipolarAdmissibleLoops.path_source]
          exact (exp_bipolarLog (basePoint γ).property).symm) ) 1 =
        bipolarLog γ.base + n₀ * (2 * (Real.pi : ℂ) * Complex.I)) ∧
    (∃ n₁ : ℤ,
      (Complex.isCoveringMap_exp.liftPath (shiftedPath γ)
        (Complex.log (γ.base - 1)) (shiftedPath_source_eq_exp_log γ)) 1 =
        Complex.log (γ.base - 1) + n₁ * (2 * (Real.pi : ℂ) * Complex.I)) := by
  exact ⟨crossRatioPath_endpoint_period γ, shiftedPath_endpoint_period γ⟩

end InfoGeometry.Analysis.BipolarLoopCrossRatioLift
