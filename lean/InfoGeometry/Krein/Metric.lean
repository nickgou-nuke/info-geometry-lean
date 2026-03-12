import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.HilbertBridge
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neutral Metric Layer (Phase 2 Integration)

This module refactors the neutral Hessian metric properties to use the canonical
`KreinSpace` predicates on the `DoubledSpace` carrier.
-/

open scoped InnerProductSpace

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InfoGeometry.Krein

/-! ### Coordinate-level Hessian (Off-diagonal) -/

/-- The neutral Hessian/Krein bilinear form on raw coordinates `(x, ξ)`. -/
noncomputable def hessian_indefinite_formCoord
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) : ℝ :=
  ⟪v.1, w.2⟫_ℝ + ⟪w.1, v.2⟫_ℝ

/-- Bridge theorem: the coordinate Hessian form equals the diagonal Krein form
via the 45-degree rotation. -/
private lemma one_div_sqrt_two_sq_metric : ((1 / Real.sqrt 2 : ℝ) ^ 2) = (1 / 2 : ℝ) := by
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsqrt : (Real.sqrt 2 : ℝ)^2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  field_simp [hs0]
  nlinarith [hsqrt]

private lemma hessian_indefinite_form_explicit (u v : DoubledSpace E) :
    hessian_indefinite_form (E := E) u v
      = ⟪WithLp.fst u, WithLp.fst v⟫_ℝ - ⟪WithLp.snd u, WithLp.snd v⟫_ℝ := by
  unfold hessian_indefinite_form
  unfold KreinSpace.kreinInner
  change
    ⟪WithLp.fst (spectral_epsilon (E := E) u), WithLp.fst v⟫_ℝ +
      ⟪WithLp.snd (spectral_epsilon (E := E) u), WithLp.snd v⟫_ℝ
      =
    ⟪WithLp.fst u, WithLp.fst v⟫_ℝ - ⟪WithLp.snd u, WithLp.snd v⟫_ℝ
  simp [spectral_epsilon, sub_eq_add_neg]

lemma hessian_indefinite_formCoord_eq_hessianDoubled (v w : E × E) :
    hessian_indefinite_formCoord v w =
      hessian_indefinite_form
        ((NeutralSpace.rotation45 (E := E)).symm (NeutralSpace.toLp (E := E) v))
        ((NeutralSpace.rotation45 (E := E)).symm (NeutralSpace.toLp (E := E) w)) := by
  rcases v with ⟨x, ξ⟩
  rcases w with ⟨y, η⟩
  let c : ℝ := 1 / Real.sqrt 2
  have hc2 : c ^ 2 = (1 / 2 : ℝ) := by
    simpa [c] using one_div_sqrt_two_sq_metric
  have hsymm : (NeutralSpace.rotation45 (E := E)).symm = NeutralSpace.rotation45 (E := E) := rfl
  have hrotv :
      (NeutralSpace.rotation45 (E := E)) (NeutralSpace.toLp (E := E) (x, ξ)) =
        InfoGeometry.Krein.to_doubled (c • x + c • ξ) (c • x - c • ξ) := by
    simp [NeutralSpace.rotation45, NeutralSpace.toLp, c, InfoGeometry.Krein.to_doubled]
  have hrotw :
      (NeutralSpace.rotation45 (E := E)) (NeutralSpace.toLp (E := E) (y, η)) =
        InfoGeometry.Krein.to_doubled (c • y + c • η) (c • y - c • η) := by
    simp [NeutralSpace.rotation45, NeutralSpace.toLp, c, InfoGeometry.Krein.to_doubled]
  unfold hessian_indefinite_formCoord
  -- Expand the rotated Krein form explicitly and simplify.
  have hrot :
      hessian_indefinite_form
          (InfoGeometry.Krein.to_doubled (c • x + c • ξ) (c • x - c • ξ))
          (InfoGeometry.Krein.to_doubled (c • y + c • η) (c • y - c • η))
        =
        c ^ 2 * (⟪x + ξ, y + η⟫_ℝ - ⟪x - ξ, y - η⟫_ℝ) := by
    rw [hessian_indefinite_form_explicit]
    -- Reduce to inner products of rotated coordinates.
    have h1 :
        ⟪c • x + c • ξ, c • y + c • η⟫_ℝ = c ^ 2 * ⟪x + ξ, y + η⟫_ℝ := by
      have h1a :
          ⟪c • x + c • ξ, c • y + c • η⟫_ℝ
            = c * ⟪x + ξ, c • y + c • η⟫_ℝ := by
          simpa [smul_add] using
            (real_inner_smul_left (x := x + ξ) (y := c • y + c • η) (r := c))
      have h1b :
          ⟪x + ξ, c • y + c • η⟫_ℝ = c * ⟪x + ξ, y + η⟫_ℝ := by
          simpa [smul_add] using
            (real_inner_smul_right (x := x + ξ) (y := y + η) (r := c))
      calc
        ⟪c • x + c • ξ, c • y + c • η⟫_ℝ
            = c * ⟪x + ξ, c • y + c • η⟫_ℝ := h1a
        _ = c * (c * ⟪x + ξ, y + η⟫_ℝ) := by
              simp [h1b, mul_assoc]
        _ = c ^ 2 * ⟪x + ξ, y + η⟫_ℝ := by ring
    have h2 :
        ⟪c • x - c • ξ, c • y - c • η⟫_ℝ = c ^ 2 * ⟪x - ξ, y - η⟫_ℝ := by
      have h2a :
          ⟪c • x - c • ξ, c • y - c • η⟫_ℝ
            = c * ⟪x - ξ, c • y - c • η⟫_ℝ := by
          simpa [smul_sub, sub_eq_add_neg] using
            (real_inner_smul_left (x := x - ξ) (y := c • y - c • η) (r := c))
      have h2b :
          ⟪x - ξ, c • y - c • η⟫_ℝ = c * ⟪x - ξ, y - η⟫_ℝ := by
          simpa [smul_sub, sub_eq_add_neg] using
            (real_inner_smul_right (x := x - ξ) (y := y - η) (r := c))
      calc
        ⟪c • x - c • ξ, c • y - c • η⟫_ℝ
            = c * ⟪x - ξ, c • y - c • η⟫_ℝ := h2a
        _ = c * (c * ⟪x - ξ, y - η⟫_ℝ) := by
              simp [h2b, mul_assoc]
        _ = c ^ 2 * ⟪x - ξ, y - η⟫_ℝ := by ring
    calc
      ⟪c • x + c • ξ, c • y + c • η⟫_ℝ - ⟪c • x - c • ξ, c • y - c • η⟫_ℝ
          = c ^ 2 * ⟪x + ξ, y + η⟫_ℝ - c ^ 2 * ⟪x - ξ, y - η⟫_ℝ := by
              simp [h1, h2]
      _ = c ^ 2 * (⟪x + ξ, y + η⟫_ℝ - ⟪x - ξ, y - η⟫_ℝ) := by ring
  have hsub :
      ⟪x + ξ, y + η⟫_ℝ - ⟪x - ξ, y - η⟫_ℝ
        = 2 * ⟪x, η⟫_ℝ + 2 * ⟪ξ, y⟫_ℝ := by
    simp [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    ring
  have hfinal :
      c ^ 2 * (⟪x + ξ, y + η⟫_ℝ - ⟪x - ξ, y - η⟫_ℝ)
        = ⟪x, η⟫_ℝ + ⟪y, ξ⟫_ℝ := by
    -- Use the computed square and commutativity of the inner product.
    calc
      c ^ 2 * (⟪x + ξ, y + η⟫_ℝ - ⟪x - ξ, y - η⟫_ℝ)
          = c ^ 2 * (2 * ⟪x, η⟫_ℝ + 2 * ⟪ξ, y⟫_ℝ) := by
              simp [hsub]
      _ = (1 / 2 : ℝ) * (2 * ⟪x, η⟫_ℝ + 2 * ⟪ξ, y⟫_ℝ) := by
            simpa [hc2]
      _ = ⟪x, η⟫_ℝ + ⟪ξ, y⟫_ℝ := by ring
      _ = ⟪x, η⟫_ℝ + ⟪y, ξ⟫_ℝ := by
            simp [real_inner_comm]
  -- Assemble the pieces.
  calc
    ⟪x, η⟫_ℝ + ⟪y, ξ⟫_ℝ
        = c ^ 2 * (⟪x + ξ, y + η⟫_ℝ - ⟪x - ξ, y - η⟫_ℝ) := by
            simpa [hfinal]
    _ = hessian_indefinite_form
          ((NeutralSpace.rotation45 (E := E)).symm (NeutralSpace.toLp (E := E) (x, ξ)))
          ((NeutralSpace.rotation45 (E := E)).symm (NeutralSpace.toLp (E := E) (y, η))) := by
            simpa [hsymm, hrotv, hrotw] using hrot.symm

end InfoGeometry.Krein

/-! ### Global Aliases -/

namespace InfoGeometry.Krein.NeutralSpace

/-- An operator on `NeutralSpace` is an infinitesimal isometry iff it is Krein-skew-adjoint. -/
def IsInfinitesimalIsometry (A : NeutralSpace E →L[ℝ] NeutralSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint (H := NeutralSpace E) A

/-- The Lie subalgebra of infinitesimal isometries for the neutral metric. -/
noncomputable def neutralLieSubalgebra :
    LieSubalgebra ℝ (NeutralSpace E →L[ℝ] NeutralSpace E) where
  carrier := {A | IsInfinitesimalIsometry (E := E) A}
  zero_mem' := by
    simp [IsInfinitesimalIsometry,
      KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := NeutralSpace E)]
  add_mem' := by
    intro A B hA hB
    simp [IsInfinitesimalIsometry,
      KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := NeutralSpace E)] at hA hB ⊢
    simpa [hA, hB, add_comm, add_left_comm, add_assoc]
  smul_mem' := by
    intro c A hA
    simp [IsInfinitesimalIsometry,
      KreinSpace.isKreinSkewAdjoint_iff_eq_neg (H := NeutralSpace E)] at hA ⊢
    simpa [hA, smul_neg]
  lie_mem' := by
    intro A B hA hB
    simpa [IsInfinitesimalIsometry] using
      (KreinSpace.isKreinSkewAdjoint_lie
        (H := NeutralSpace E) (hA := hA) (hB := hB))

end InfoGeometry.Krein.NeutralSpace
