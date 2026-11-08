/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Ring

/-!
# Effective transition operators and their induced norms

Initial and final model spaces and ambient Hilbert spaces may all differ.
For supplied wave embeddings, the effective operator is the adjoint sandwich
and the norm operator is its Gram operator. The normalized full-space matrix
element is recovered exactly using both induced norms.

This is bounded-operator transport over real or complex Hilbert spaces. A
physical E2 or M1 operator and the wave embeddings must be supplied by the
model. In particular, this file does not equip the algebraic nuclear common
carrier with an inner product or identify a CAR degree with a multipole rank.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearEffectiveObservables

open ContinuousLinearMap

variable {𝕜 Mᵢ Mf Hᵢ Hf : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup Mᵢ] [InnerProductSpace 𝕜 Mᵢ] [CompleteSpace Mᵢ]
variable [NormedAddCommGroup Mf] [InnerProductSpace 𝕜 Mf] [CompleteSpace Mf]
variable [NormedAddCommGroup Hᵢ] [InnerProductSpace 𝕜 Hᵢ] [CompleteSpace Hᵢ]
variable [NormedAddCommGroup Hf] [InnerProductSpace 𝕜 Hf] [CompleteSpace Hf]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The same wave embeddings that reconstruct states transport the observable. -/
def effectiveOperator (Ωᵢ : Mᵢ →L[𝕜] Hᵢ) (Ωf : Mf →L[𝕜] Hf)
    (O : Hᵢ →L[𝕜] Hf) : Mᵢ →L[𝕜] Mf :=
  Ωf.adjoint.comp (O.comp Ωᵢ)

/-- The positive semidefinite Gram operator induced by a wave embedding. -/
def normMetric (Ω : Mᵢ →L[𝕜] Hᵢ) : Mᵢ →L[𝕜] Mᵢ :=
  Ω.adjoint.comp Ω

/-- Squared norm of the reconstructed state, expressed in model coordinates. -/
def metricWeight (Ω : Mᵢ →L[𝕜] Hᵢ) (x : Mᵢ) : ℝ :=
  RCLike.re ⟪x, normMetric Ω x⟫

omit [CompleteSpace Mᵢ] [CompleteSpace Hᵢ] in
theorem inner_effectiveOperator (Ωᵢ : Mᵢ →L[𝕜] Hᵢ)
    (Ωf : Mf →L[𝕜] Hf) (O : Hᵢ →L[𝕜] Hf) (xᵢ : Mᵢ) (xf : Mf) :
    ⟪xf, effectiveOperator Ωᵢ Ωf O xᵢ⟫ = ⟪Ωf xf, O (Ωᵢ xᵢ)⟫ := by
  exact Ωf.adjoint_inner_right xf (O (Ωᵢ xᵢ))

theorem inner_normMetric (Ω : Mᵢ →L[𝕜] Hᵢ) (x y : Mᵢ) :
    ⟪x, normMetric Ω y⟫ = ⟪Ω x, Ω y⟫ := by
  exact Ω.adjoint_inner_right x (Ω y)

theorem normMetric_adjoint (Ω : Mᵢ →L[𝕜] Hᵢ) :
    (normMetric Ω).adjoint = normMetric Ω := by
  simp only [normMetric, adjoint_comp, adjoint_adjoint]

theorem metricWeight_eq_norm_sq (Ω : Mᵢ →L[𝕜] Hᵢ) (x : Mᵢ) :
    metricWeight Ω x = ‖Ω x‖ ^ 2 := by
  rw [metricWeight, inner_normMetric, inner_self_eq_norm_sq]

theorem metricWeight_nonneg (Ω : Mᵢ →L[𝕜] Hᵢ) (x : Mᵢ) :
    0 ≤ metricWeight Ω x := by
  rw [metricWeight_eq_norm_sq]
  exact sq_nonneg _

theorem metricWeight_pos (Ω : Mᵢ →L[𝕜] Hᵢ)
    (hΩ : Function.Injective Ω) {x : Mᵢ} (hx : x ≠ 0) :
    0 < metricWeight Ω x := by
  have hΩx : Ω x ≠ 0 := by
    intro h
    apply hx
    apply hΩ
    simpa using h
  rw [metricWeight_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hΩx)

theorem sqrt_metricWeight (Ω : Mᵢ →L[𝕜] Hᵢ) (x : Mᵢ) :
    Real.sqrt (metricWeight Ω x) = ‖Ω x‖ := by
  rw [metricWeight_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The image normalized by the induced metric. For the zero image this is zero. -/
def normalizedState (Ω : Mᵢ →L[𝕜] Hᵢ) (x : Mᵢ) : Hᵢ :=
  (Real.sqrt (metricWeight Ω x) : 𝕜)⁻¹ • Ω x

theorem norm_normalizedState (Ω : Mᵢ →L[𝕜] Hᵢ)
    (hΩ : Function.Injective Ω) {x : Mᵢ} (hx : x ≠ 0) :
    ‖normalizedState Ω x‖ = 1 := by
  have hΩx : Ω x ≠ 0 := by
    intro h
    apply hx
    apply hΩ
    simpa using h
  rw [normalizedState, sqrt_metricWeight]
  simpa only [RCLike.ofReal_inv] using (norm_smul_inv_norm (𝕜 := 𝕜) hΩx)

/-- Both external-state norm factors are necessary. The identity also uses
the totalized value zero when one of the supplied states vanishes. -/
theorem normalized_transition_amplitude (Ωᵢ : Mᵢ →L[𝕜] Hᵢ)
    (Ωf : Mf →L[𝕜] Hf) (O : Hᵢ →L[𝕜] Hf) (xᵢ : Mᵢ) (xf : Mf) :
    ⟪normalizedState Ωf xf, O (normalizedState Ωᵢ xᵢ)⟫ =
      ⟪xf, effectiveOperator Ωᵢ Ωf O xᵢ⟫ /
        ((Real.sqrt (metricWeight Ωf xf) : 𝕜) *
          (Real.sqrt (metricWeight Ωᵢ xᵢ) : 𝕜)) := by
  unfold normalizedState
  rw [map_smul, inner_smul_left, inner_smul_right]
  rw [RCLike.conj_inv, RCLike.conj_ofReal,
    ← inner_effectiveOperator Ωᵢ Ωf O xᵢ xf]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The normalized full-space strength is recovered by the effective operator
and the product of the two induced squared norms. -/
theorem normalized_transition_strength (Ωᵢ : Mᵢ →L[𝕜] Hᵢ)
    (Ωf : Mf →L[𝕜] Hf) (O : Hᵢ →L[𝕜] Hf) (xᵢ : Mᵢ) (xf : Mf) :
    ‖⟪normalizedState Ωf xf, O (normalizedState Ωᵢ xᵢ)⟫‖ ^ 2 =
      ‖⟪xf, effectiveOperator Ωᵢ Ωf O xᵢ⟫‖ ^ 2 /
        (metricWeight Ωf xf * metricWeight Ωᵢ xᵢ) := by
  rw [normalized_transition_amplitude, norm_div, norm_mul,
    RCLike.norm_ofReal, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, mul_pow, Real.sq_sqrt (metricWeight_nonneg Ωf xf),
    Real.sq_sqrt (metricWeight_nonneg Ωᵢ xᵢ)]

theorem effectiveOperator_adjoint (Ωᵢ : Mᵢ →L[𝕜] Hᵢ)
    (Ωf : Mf →L[𝕜] Hf) (O : Hᵢ →L[𝕜] Hf) :
    (effectiveOperator Ωᵢ Ωf O).adjoint =
      effectiveOperator Ωf Ωᵢ O.adjoint := by
  simp only [effectiveOperator, adjoint_comp, adjoint_adjoint, comp_assoc]

/-- Orthogonal eliminated components produce the usual `I + χ†χ` metric. -/
theorem normMetric_add_of_orthogonal (ι χ : Mᵢ →L[𝕜] Hᵢ)
    (hι : ι.adjoint.comp ι = ContinuousLinearMap.id 𝕜 Mᵢ)
    (horth : ι.adjoint.comp χ = 0) :
    normMetric (ι + χ) = ContinuousLinearMap.id 𝕜 Mᵢ + normMetric χ := by
  have horth' : χ.adjoint.comp ι = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint horth
    simpa only [adjoint_comp, adjoint_adjoint, map_zero] using h
  simp only [normMetric, map_add, add_comp, comp_add,
    hι, horth, horth', add_zero, zero_add]

omit [CompleteSpace Mᵢ] [CompleteSpace Hᵢ] in
/-- Self-adjoint symmetry intertwining survives effective transport. Applying
this to a supplied spatial-parity operator preserves its selection rule. -/
theorem effectiveOperator_intertwines (Ωᵢ : Mᵢ →L[𝕜] Hᵢ)
    (Ωf : Mf →L[𝕜] Hf) (O : Hᵢ →L[𝕜] Hf)
    (Sᵢ : Hᵢ →L[𝕜] Hᵢ) (Sf : Hf →L[𝕜] Hf)
    (sᵢ : Mᵢ →L[𝕜] Mᵢ) (sf : Mf →L[𝕜] Mf) (η : 𝕜)
    (hΩᵢ : Sᵢ.comp Ωᵢ = Ωᵢ.comp sᵢ)
    (hΩf : Sf.comp Ωf = Ωf.comp sf)
    (hSf : Sf.adjoint = Sf) (hsf : sf.adjoint = sf)
    (hO : Sf.comp O = η • O.comp Sᵢ) :
    sf.comp (effectiveOperator Ωᵢ Ωf O) =
      η • (effectiveOperator Ωᵢ Ωf O).comp sᵢ := by
  have hleft : sf.comp Ωf.adjoint = Ωf.adjoint.comp Sf := by
    have h := congrArg ContinuousLinearMap.adjoint hΩf
    simpa only [adjoint_comp, hSf, hsf] using h.symm
  unfold effectiveOperator
  calc
    sf.comp (Ωf.adjoint.comp (O.comp Ωᵢ)) =
        (sf.comp Ωf.adjoint).comp (O.comp Ωᵢ) := by rw [comp_assoc]
    _ = (Ωf.adjoint.comp Sf).comp (O.comp Ωᵢ) := by rw [hleft]
    _ = Ωf.adjoint.comp ((Sf.comp O).comp Ωᵢ) := by simp only [comp_assoc]
    _ = Ωf.adjoint.comp ((η • O.comp Sᵢ).comp Ωᵢ) := by rw [hO]
    _ = η • Ωf.adjoint.comp (O.comp (Sᵢ.comp Ωᵢ)) := by
      simp only [smul_comp, comp_smul, comp_assoc]
    _ = η • Ωf.adjoint.comp (O.comp (Ωᵢ.comp sᵢ)) := by rw [hΩᵢ]
    _ = η • (Ωf.adjoint.comp (O.comp Ωᵢ)).comp sᵢ := by
      simp only [comp_assoc]

end InfoGeometry.Physics.NuclearEffectiveObservables
