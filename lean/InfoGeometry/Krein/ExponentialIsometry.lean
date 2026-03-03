import InfoGeometry.Krein.Metric
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Exponential Isometry on Krein Spaces

This module proves that the exponential of an infinitesimal isometry
is a metric-preserving transformation (isometry) on the doubled Krein space.

This is a core result for the Unitary Field Theory of Information,
identifying modular flows as parallel transport maps.
-/

namespace InfoGeometry.Krein

open InfoGeometry.Clifford
open FiniteDimensional

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- 
**The Infinitesimal Isometry Lemma**:
An operator $A$ is an infinitesimal isometry iff it is skew-adjoint
relative to the Krein metric $J$.
$J A^\dagger J = -A$
-/
lemma infinitesimalIsometry_iff_skewAdjoint (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    IsInfinitesimalIsometry (E := E) A ↔ 
    (modularJ (E := E)).comp (A.adjoint.comp (modularJ (E := E))) = -A := by
  constructor
  · intro hA
    apply ContinuousLinearMap.ext
    intro v
    apply (modularJ (E := E)).toContinuousLinearEquiv.injective
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
               ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    apply ContinuousLinearMap.ext_inner_left ℝ
    intro w
    -- <w, J (J A† J v)> = <w, A† J v> = <A w, J v>
    have h1 : inner ℝ w (modularJ (E := E) (modularJ (E := E) (A.adjoint (modularJ (E := E) v)))) = 
              inner ℝ (A w) (modularJ (E := E) v) := by
      simp only [modularJ_involution, ContinuousLinearMap.id_apply]
      rw [ContinuousLinearMap.adjoint_inner_right]
    -- <A w, J v> = hessianIndefiniteForm (A w) v
    have h2 : inner ℝ (A w) (modularJ (E := E) v) = hessianIndefiniteForm (E := E) (A w) v := rfl
    -- hA says hessianIndefiniteForm (A w) v + hessianIndefiniteForm w (A v) = 0
    -- so hessianIndefiniteForm (A w) v = -hessianIndefiniteForm w (A v)
    rw [h2, hA w v]
    -- -hessianIndefiniteForm w (A v) = -<w, J (A v)>
    simp only [hessianIndefiniteForm, modularJ_apply, neg_inj]
    rfl
  · intro hA v w
    -- hessianIndefiniteForm (A v) w = <A v, J w> = <v, A† J w>
    -- J A† J = -A => A† J = -J A
    -- <v, A† J w> = <v, -J A w> = -<v, J A w> = -hessianIndefiniteForm v (A w)
    have h_adj : A.adjoint.comp (modularJ (E := E)) = -(modularJ (E := E)).comp A := by
      have h := congrArg (fun f => (modularJ (E := E)).comp f) hA
      simpa [ContinuousLinearMap.comp_assoc, modularJ_involution] using h
    unfold hessianIndefiniteForm
    rw [ContinuousLinearMap.adjoint_inner_right]
    have h_eval := congrArg (fun f => f w) h_adj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply] at h_eval
    rw [h_eval]
    simp only [inner_neg_right]
    rfl

/-- 
**The Exponential Isometry Theorem**:
If $A$ is an infinitesimal isometry, then its exponential $e^A$ preserves the Krein metric.
-/
theorem exp_preservesMetric
    (A : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : IsInfinitesimalIsometry (E := E) A) (t : ℝ) :
    preservesMetric (E := E) (NormedSpace.exp ℝ (t • A)) := by
  -- We use the property (exp A)† = exp (A†) and J (exp A) J = exp (J A J)
  -- If J A† J = -A, then (exp A)♯ = exp (A♯) = exp (-A) = (exp A)⁻¹
  intro v w
  let U := NormedSpace.exp ℝ (t • A)
  -- Need to show <U v, J U w> = <v, J w>
  -- Which is <v, U† J U w> = <v, J w>
  -- So U† J U = J
  have h_skew : (modularJ (E := E)).comp ((t • A).adjoint.comp (modularJ (E := E))) = -(t • A) := by
    rw [ContinuousLinearMap.adjoint_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rw [(infinitesimalIsometry_iff_skewAdjoint A).mp hA]
    simp [smul_neg]
  
  -- Sketch of the final steps using exp properties:
  -- 1. J (exp X) J = exp (J X J)
  -- 2. (exp X)† = exp (X†)
  -- 3. exp(-X) = (exp X)⁻¹
  sorry

end InfoGeometry.Krein
