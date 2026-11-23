/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Rectangular bounded homotopies on an L² operator pair

Given bounded maps `d₀ : H₀ → H₁` and `h₁ : H₁ → H₀`, their degree-raising
and degree-lowering blocks act on the genuine Hilbert direct sum
`WithLp 2 (H₀ × H₁)`. If `h₁ ∘ d₀ = I - P` and `d₀ ∘ P = 0`, the blocks
satisfy the contracting identity required by
`BoundedHomotopyCoercivity.coercivity_of_homotopy`. The estimate is conditional
on an explicit operator-norm bound for the lifted homotopy.

This theorem does not assert that an arbitrary unbounded differential has
such a bounded transform or that a quadratic-form inequality follows from a
single differential term.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Candidates.RectangularHomotopyCoercivity

open ContinuousLinearMap
open InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity

variable {H₀ H₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]

abbrev Pair := WithLp 2 (H₀ × H₁)

/-- Identify the `L²` product with the ordinary product without changing its
underlying degree components. -/
noncomputable def pairEquiv : Pair (H₀ := H₀) (H₁ := H₁) ≃L[ℝ] H₀ × H₁ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ H₀ H₁

/-- Assemble a rectangular differential as the lower-left block on the raw
product. -/
private def rawDifferential (d₀ : H₀ →L[ℝ] H₁) :
    (H₀ × H₁) →L[ℝ] (H₀ × H₁) :=
  (0 : (H₀ × H₁) →L[ℝ] H₀).prod
    (d₀.comp (ContinuousLinearMap.fst ℝ H₀ H₁))

/-- Assemble the rectangular homotopy as the upper-right block. -/
private def rawHomotopy (h₁ : H₁ →L[ℝ] H₀) :
    (H₀ × H₁) →L[ℝ] (H₀ × H₁) :=
  (h₁.comp (ContinuousLinearMap.snd ℝ H₀ H₁)).prod
    (0 : (H₀ × H₁) →L[ℝ] H₁)

/-- The total projection on degree zero and degree one. -/
private def rawProjection (d₀ : H₀ →L[ℝ] H₁)
    (h₁ : H₁ →L[ℝ] H₀) (P : H₀ →L[ℝ] H₀) :
    (H₀ × H₁) →L[ℝ] (H₀ × H₁) :=
  (P.comp (ContinuousLinearMap.fst ℝ H₀ H₁)).prod
    (((1 : H₁ →L[ℝ] H₁) - d₀.comp h₁).comp
      (ContinuousLinearMap.snd ℝ H₀ H₁))

/-- Conjugate a bounded operator on the ordinary product to the genuine L²
product. -/
private def onPair (T : (H₀ × H₁) →L[ℝ] (H₀ × H₁)) :
    Pair (H₀ := H₀) (H₁ := H₁) →L[ℝ] Pair (H₀ := H₀) (H₁ := H₁) :=
  (pairEquiv (H₀ := H₀) (H₁ := H₁)).symm.toContinuousLinearMap.comp
    (T.comp (pairEquiv (H₀ := H₀) (H₁ := H₁)).toContinuousLinearMap)

/-- The lifted degree-raising differential. -/
def differential (d₀ : H₀ →L[ℝ] H₁) :
    Pair (H₀ := H₀) (H₁ := H₁) →L[ℝ] Pair (H₀ := H₀) (H₁ := H₁) :=
  onPair (rawDifferential d₀)

/-- The lifted degree-lowering homotopy. -/
def homotopy (h₁ : H₁ →L[ℝ] H₀) :
    Pair (H₀ := H₀) (H₁ := H₁) →L[ℝ] Pair (H₀ := H₀) (H₁ := H₁) :=
  onPair (rawHomotopy h₁)

/-- The total vacuum/range projection on the L² product. -/
def totalProjection (d₀ : H₀ →L[ℝ] H₁) (h₁ : H₁ →L[ℝ] H₀)
    (P : H₀ →L[ℝ] H₀) :
    Pair (H₀ := H₀) (H₁ := H₁) →L[ℝ] Pair (H₀ := H₀) (H₁ := H₁) :=
  onPair (rawProjection d₀ h₁ P)

private theorem onPair_mul (S T : (H₀ × H₁) →L[ℝ] (H₀ × H₁)) :
    onPair (S * T) = onPair S * onPair T := by
  ext z
  simp [onPair]

private theorem onPair_add (S T : (H₀ × H₁) →L[ℝ] (H₀ × H₁)) :
    onPair (S + T) = onPair S + onPair T := by
  ext z
  simp [onPair]

private theorem onPair_one :
    onPair (1 : (H₀ × H₁) →L[ℝ] (H₀ × H₁)) = 1 := by
  ext z
  simp [onPair]

private theorem onPair_sub (S T : (H₀ × H₁) →L[ℝ] (H₀ × H₁)) :
    onPair (S - T) = onPair S - onPair T := by
  ext z
  simp [onPair]

private theorem raw_contracting_identity
    (d₀ : H₀ →L[ℝ] H₁) (h₁ : H₁ →L[ℝ] H₀) (P : H₀ →L[ℝ] H₀)
    (hhd : h₁.comp d₀ = 1 - P) :
    rawDifferential d₀ * rawHomotopy h₁ + rawHomotopy h₁ * rawDifferential d₀ =
      1 - rawProjection d₀ h₁ P := by
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨x, y⟩
  have hhdx : h₁ (d₀ x) = x - P x := by
    have h := congrArg (fun T : H₀ →L[ℝ] H₀ => T x) hhd
    simpa only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self] using h
  simp [rawDifferential, rawHomotopy, rawProjection,
    ContinuousLinearMap.comp_apply, hhdx]

@[simp] theorem differential_apply (d₀ : H₀ →L[ℝ] H₁) (z : Pair (H₀ := H₀) (H₁ := H₁)) :
    (pairEquiv (H₀ := H₀) (H₁ := H₁))
      (differential d₀ z) = (0, d₀ ((pairEquiv (H₀ := H₀) (H₁ := H₁) z).1)) := by
  simp [differential, onPair, rawDifferential]

/-- The lowering block acts in the reverse direction on the two graded
components. -/
@[simp] theorem homotopy_apply (h₁ : H₁ →L[ℝ] H₀)
    (z : Pair (H₀ := H₀) (H₁ := H₁)) :
    (pairEquiv (H₀ := H₀) (H₁ := H₁)) (homotopy h₁ z) =
      (h₁ ((pairEquiv (H₀ := H₀) (H₁ := H₁) z).2), 0) := by
  simp [homotopy, onPair, rawHomotopy]

/-- The block differential is square-zero because it maps degree zero to
degree one and vanishes on degree one. -/
theorem differential_sq_zero (d₀ : H₀ →L[ℝ] H₁) :
    (differential d₀).comp (differential d₀) = 0 := by
  ext z
  apply pairEquiv.injective
  simp

/-- The block homotopy is square-zero because it maps degree one to degree
zero and vanishes on degree zero. -/
theorem homotopy_sq_zero (h₁ : H₁ →L[ℝ] H₀) :
    (homotopy h₁).comp (homotopy h₁) = 0 := by
  ext z
  apply pairEquiv.injective
  simp

/-- The two off-diagonal blocks satisfy the contracting identity whenever the
degree-zero composite is identity modulo the specified projection. -/
theorem contracting_identity
    (d₀ : H₀ →L[ℝ] H₁) (h₁ : H₁ →L[ℝ] H₀) (P : H₀ →L[ℝ] H₀)
    (hhd : h₁.comp d₀ = 1 - P) :
    differential d₀ * homotopy h₁ + homotopy h₁ * differential d₀ =
      1 - totalProjection d₀ h₁ P := by
  dsimp [differential, homotopy, totalProjection]
  rw [← onPair_mul, ← onPair_mul, ← onPair_add, ← onPair_one, ← onPair_sub]
  exact congrArg onPair (raw_contracting_identity d₀ h₁ P hhd)

/-- If the degree-one-to-zero map is a two-sided inverse to the differential,
the projection term in the contracting identity vanishes. -/
theorem totalProjection_eq_zero_of_right_inverse
    (d₀ : H₀ →L[ℝ] H₁) (h₁ : H₁ →L[ℝ] H₀)
    (d₀h : d₀.comp h₁ = 1) :
    totalProjection d₀ h₁ 0 = 0 := by
  ext z
  apply pairEquiv.injective
  simp [totalProjection, onPair, rawProjection, d₀h]

/-- A bounded left inverse modulo the vacuum projection directly gives a
degree-zero lower bound. This is sharper than the doubled Hodge estimate and
does not require an adjoint term on degree zero. -/
theorem rectangular_left_inverse_coercivity
    (d₀ : H₀ →L[ℝ] H₁) (h₁ : H₁ →L[ℝ] H₀) (P : H₀ →L[ℝ] H₀)
    (hhd : h₁.comp d₀ = 1 - P)
    {C : ℝ} (hC : 0 < C) (hbound : ‖h₁‖ ≤ C)
    (ψ : H₀) (hψ : P ψ = 0) :
    (1 / C ^ 2) * ‖ψ‖ ^ 2 ≤ ‖d₀ ψ‖ ^ 2 := by
  have hleft : h₁ (d₀ ψ) = ψ := by
    have heq := congrArg (fun T : H₀ →L[ℝ] H₀ => T ψ) hhd
    change h₁ (d₀ ψ) = ψ - P ψ at heq
    rw [hψ, sub_zero] at heq
    exact heq
  have hnorm : ‖ψ‖ ≤ C * ‖d₀ ψ‖ := by
    calc
      ‖ψ‖ = ‖h₁ (d₀ ψ)‖ := by rw [hleft]
      _ ≤ ‖h₁‖ * ‖d₀ ψ‖ := h₁.le_opNorm (d₀ ψ)
      _ ≤ C * ‖d₀ ψ‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg (d₀ ψ))
  have hsquare := mul_self_le_mul_self (norm_nonneg ψ) hnorm
  have hscaled : ‖ψ‖ ^ 2 ≤ C ^ 2 * ‖d₀ ψ‖ ^ 2 := by
    nlinarith [hsquare]
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  calc
    (1 / C ^ 2) * ‖ψ‖ ^ 2 = ‖ψ‖ ^ 2 / C ^ 2 := by ring
    _ ≤ ‖d₀ ψ‖ ^ 2 :=
      (div_le_iff₀ hC2).mpr (by nlinarith [hscaled])

/-- The doubled construction supplies the bounded contracting identity to the
existing dimension-independent Hilbert estimate. -/
theorem rectangular_homotopy_coercivity
    [CompleteSpace H₀] [CompleteSpace H₁]
    (d₀ : H₀ →L[ℝ] H₁) (h₁ : H₁ →L[ℝ] H₀) (P : H₀ →L[ℝ] H₀)
    (hhd : h₁.comp d₀ = 1 - P)
    {C : ℝ} (hC : 0 < C)
    (hbound : ‖homotopy h₁‖ ≤ C)
    (ψ : H₀) (hψ : P ψ = 0) :
    (1 / (2 * C ^ 2)) * ‖WithLp.toLp 2 (ψ, (0 : H₁))‖ ^ 2 ≤
      inner ℝ (WithLp.toLp 2 (ψ, (0 : H₁)))
        (hodge (differential d₀) (WithLp.toLp 2 (ψ, (0 : H₁)))) := by
  let d := differential d₀
  let h := homotopy h₁
  let Q := totalProjection d₀ h₁ P
  have hcontract : d * h + h * d = 1 - Q := by
    dsimp [d, h, Q, differential, homotopy, totalProjection]
    rw [← onPair_mul, ← onPair_mul, ← onPair_add, ← onPair_one, ← onPair_sub]
    rw [raw_contracting_identity d₀ h₁ P hhd]
  have hQ : Q (WithLp.toLp 2 (ψ, (0 : H₁))) = 0 := by
    apply (pairEquiv (H₀ := H₀) (H₁ := H₁)).injective
    change rawProjection d₀ h₁ P (ψ, 0) = 0
    simp [rawProjection, hψ]
  simpa only [d] using
    (InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity.coercivity_of_homotopy
      d h Q hcontract hC hbound (WithLp.toLp 2 (ψ, (0 : H₁))) hQ)

end InfoGeometry.OperatorAlgebra.Candidates.RectangularHomotopyCoercivity

end
