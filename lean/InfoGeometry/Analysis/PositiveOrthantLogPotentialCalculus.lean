import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import InfoGeometry.Analysis.LogVolumePathIntegral
import InfoGeometry.Projective.Bridge

/-!
# Calculus of the finite positive-orthant logarithmic potential

This owner works on the concrete open cone chart, not on the projective
quotient.  The quotient-valued `PositiveRay` is therefore not silently given
a manifold structure.  The coordinate logarithm is a genuine smooth scalar
potential on the finite-dimensional positive orthant, with its native
Fréchet derivative exposed for later pullback constructions.
-/

noncomputable section

namespace InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

open InfoGeometry.Projective
open InfoGeometry.Analysis.LogVolumePathIntegral
open InfoGeometry.Analysis.LogVolumeExactDifferential
open MeasureTheory
open scoped Interval

variable {α : Type*} [Fintype α]

abbrev Chart (α : Type*) := EuclideanSpace ℝ α

noncomputable def coordinateCLM (i : α) : Chart α →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    (EuclideanSpace.equiv α ℝ).toContinuousLinearMap

def coordinateLogPotential (i : α) : Chart α → ℝ :=
  fun x => Real.log (x i)

theorem coordinateCLM_apply (i : α) (x : Chart α) :
    coordinateCLM i x = x i := by
  simp [coordinateCLM]

theorem hasFDerivAt_coordinateLogPotential
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    HasFDerivAt (coordinateLogPotential i)
      ((1 / x i) • coordinateCLM i) x := by
  have hcoord : HasFDerivAt (coordinateCLM i) (coordinateCLM i) x :=
    (coordinateCLM i).hasFDerivAt
  have hlog : HasDerivAt Real.log (1 / (x i)) (x i) :=
    by simpa [one_div] using Real.hasDerivAt_log hx
  simpa [coordinateLogPotential, coordinateCLM_apply, smul_eq_mul,
    mul_comm] using hlog.comp_hasFDerivAt x hcoord

theorem differentiableOn_coordinateLogPotential
    (i : α) :
    DifferentiableOn ℝ (coordinateLogPotential i)
      (interior (positiveOrthantCone (α := α) : Set (Chart α))) := by
  intro x hx
  have hxi : 0 < x i :=
    (mem_interior_positiveOrthantCone_iff (α := α) x).mp hx i
  exact (hasFDerivAt_coordinateLogPotential i (ne_of_gt hxi)).differentiableAt.differentiableWithinAt

theorem coordinateLogPotential_contDiffOn
    (i : α) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (coordinateLogPotential i)
      (interior (positiveOrthantCone (α := α) : Set (Chart α))) := by
  intro x hx
  have hxi : 0 < x i :=
    (mem_interior_positiveOrthantCone_iff (α := α) x).mp hx i
  have hlog : ContDiffAt ℝ (⊤ : WithTop ℕ∞) Real.log (x i) :=
    (Real.contDiffAt_log).2 (ne_of_gt hxi)
  exact (hlog.comp x ((coordinateCLM i).contDiff.contDiffAt)).contDiffWithinAt

theorem integral_coordinateLogRate_eq_potential_sub
    (i : α) {γ : ℝ → Chart α} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < γ t i)
    (hint : IntervalIntegrable
      (logVolumeDifferential (fun t => γ t i)) volume a b) :
    ∫ t in a..b, logVolumeDifferential (fun t => γ t i) t =
      coordinateLogPotential i (γ b) - coordinateLogPotential i (γ a) := by
  simpa [coordinateLogPotential] using
    (InfoGeometry.Analysis.LogVolumePathIntegral.integral_logVolumeDifferential_eq_sub
      (Q := fun t => γ t i) (a := a) (b := b)
      (fun t ht => (coordinateCLM i).differentiableAt.comp t (hγ t ht))
      (fun t ht => ne_of_gt (hpos t ht)) hint)

end InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

end noncomputable section
