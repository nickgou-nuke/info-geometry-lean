/-
InfoGeometry/Analysis/AsanoContractionNative.lean

Native algebraic pieces of the Asano contraction lemma.

This file deliberately proves only kernel-checkable algebraic cases of the
Asano contraction argument.  It does not package the full Ruelle/Asano theorem
as a witness and it does not claim the Möbius/Riemann-sphere case.

The sign convention used here is the standard signed product obstruction:
if the contraction `A + D z` vanishes, then the zero lies in `-K₁K₂`.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.Analysis.AsanoContractionNative

/--
The two-variable affine polynomial used in the Asano contraction lemma.
-/
def asanoPoly (A B C D : ℂ) (z₁ z₂ : ℂ) : ℂ :=
  A + B * z₁ + C * z₂ + D * z₁ * z₂

/-- The one-variable contracted polynomial. -/
def asanoContract (A D : ℂ) (z : ℂ) : ℂ :=
  A + D * z

/--
Signed product obstruction `-K₁K₂`.

With the convention `asanoContract A D z = A + D z`, the factorized/rank-one
case sends a contracted zero to the negative product of the two forbidden
one-variable zeros.
-/
def signedProductSet (K₁ K₂ : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ u : ℂ, u ∈ K₁ ∧ ∃ v : ℂ, v ∈ K₂ ∧ z = -(u * v)}

/--
Zero-freeness of the two-variable polynomial off the forbidden sets.
-/
def ZeroFreeOutside
    (K₁ K₂ : Set ℂ) (A B C D : ℂ) : Prop :=
  ∀ z₁ z₂ : ℂ,
    z₁ ∉ K₁ → z₂ ∉ K₂ → asanoPoly A B C D z₁ z₂ ≠ 0

/-- A contracted zero is just the equation `A + Dz = 0`. -/
def IsContractedZero (A D z : ℂ) : Prop :=
  asanoContract A D z = 0

/--
If the two-variable polynomial is zero-free outside `K₁,K₂`, and `0` lies in
both complements, then the constant coefficient `A` is nonzero.
-/
theorem coeff_A_ne_zero_of_zeroFreeOutside
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D) :
    A ≠ 0 := by
  intro hA
  exact hzf 0 0 h0₁ h0₂ (by simp [asanoPoly, hA])

/--
The `D = 0` case of Asano contraction is native algebra: the contraction is the
nonzero constant `A`.
-/
theorem asanoContract_ne_zero_of_D_eq_zero
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D = 0) :
    asanoContract A D z ≠ 0 := by
  have hA : A ≠ 0 :=
    coeff_A_ne_zero_of_zeroFreeOutside h0₁ h0₂ hzf
  intro hz
  apply hA
  simpa [asanoContract, hD] using hz

/--
In the rank-one case `AD - BC = 0`, with `D ≠ 0`, zero-freeness off
`K₁,K₂` forces the first factor zero `-C/D` to lie in `K₁`.
-/
theorem left_factor_zero_mem_of_rankOne
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C = 0) :
    -(C / D) ∈ K₁ := by
  by_contra hnot
  have hAD : A * D = B * C := by
    exact sub_eq_zero.mp hdet
  have hpoly : asanoPoly A B C D (-(C / D)) 0 = 0 := by
    unfold asanoPoly
    rw [show A = B * C / D by
      rw [← hAD]
      field_simp [hD]]
    field_simp [hD]
    ring
  exact hzf (-(C / D)) 0 hnot h0₂ hpoly

/--
In the rank-one case, zero-freeness also forces the second factor zero
`-A/C` to lie in `K₂`.  The proof first shows `C ≠ 0`; otherwise `A = 0`
and the original two-variable polynomial vanishes at `(0,0)`.
-/
theorem right_factor_zero_mem_of_rankOne
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C = 0) :
    -(A / C) ∈ K₂ := by
  have hC : C ≠ 0 := by
    intro hC
    have hAD : A * D = B * C := sub_eq_zero.mp hdet
    have hAD0 : A * D = 0 := by
      simpa [hC] using hAD
    have hA : A = 0 := by
      rcases mul_eq_zero.mp hAD0 with hA | hD0
      · exact hA
      · exact False.elim (hD hD0)
    exact hzf 0 0 h0₁ h0₂ (by simp [asanoPoly, hA])
  by_contra hnot
  have hpoly : asanoPoly A B C D 0 (-(A / C)) = 0 := by
    unfold asanoPoly
    field_simp [hC]
    ring
  exact hzf 0 (-(A / C)) h0₁ hnot hpoly



/-! ## Nondegenerate Möbius branch algebra -/

/--
The two-variable affine polynomial is affine in its second variable with
coefficient `C + D z₁`.
-/
theorem asanoPoly_rewrite_linear_in_second
    (A B C D z₁ z₂ : ℂ) :
    asanoPoly A B C D z₁ z₂ =
      A + B * z₁ + (C + D * z₁) * z₂ := by
  unfold asanoPoly
  ring

/--
If the second-variable coefficient is nonzero, then the Möbius root in the
second variable is an actual zero of the two-variable affine polynomial.
-/
theorem asanoPoly_zero_at_mobiusRoot_second
    {A B C D z₁ : ℂ}
    (hden : C + D * z₁ ≠ 0) :
    asanoPoly A B C D z₁
      (-(A + B * z₁) / (C + D * z₁)) = 0 := by
  rw [asanoPoly_rewrite_linear_in_second]
  have hdiv : (C + D * z₁) / (C + D * z₁) = (1 : ℂ) := div_self hden
  calc
    A + B * z₁ + (C + D * z₁) * (-(A + B * z₁) / (C + D * z₁))
        = A + B * z₁ - (A + B * z₁) := by
          field_simp [hden]
          simp [hdiv, mul_comm]
    _ = 0 := by ring

/--
If `z₁` lies outside `K₁` and the second-variable Möbius root exists,
zero-freeness forces that root to lie in `K₂`.
-/
theorem mobiusSecondRoot_mem_K2_of_zeroFreeOutside
    {K₁ K₂ : Set ℂ} {A B C D z₁ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hz₁ : z₁ ∉ K₁)
    (hden : C + D * z₁ ≠ 0) :
    -(A + B * z₁) / (C + D * z₁) ∈ K₂ := by
  by_contra hnot
  exact hzf
    z₁
    (-(A + B * z₁) / (C + D * z₁))
    hz₁
    hnot
    (asanoPoly_zero_at_mobiusRoot_second hden)

/--
The two-variable affine polynomial is affine in its first variable with
coefficient `B + D z₂`.
-/
theorem asanoPoly_rewrite_linear_in_first
    (A B C D z₁ z₂ : ℂ) :
    asanoPoly A B C D z₁ z₂ =
      A + C * z₂ + (B + D * z₂) * z₁ := by
  unfold asanoPoly
  ring

/--
If the first-variable coefficient is nonzero, then the Möbius root in the
first variable is an actual zero of the two-variable affine polynomial.
-/
theorem asanoPoly_zero_at_mobiusRoot_first
    {A B C D z₂ : ℂ}
    (hden : B + D * z₂ ≠ 0) :
    asanoPoly A B C D
      (-(A + C * z₂) / (B + D * z₂)) z₂ = 0 := by
  rw [asanoPoly_rewrite_linear_in_first]
  have hcancel :
      (B + D * z₂) * (-(A + C * z₂) / (B + D * z₂)) = -(A + C * z₂) := by
    field_simp [hden]
  rw [hcancel]
  ring

/--
If `z₂` lies outside `K₂` and the first-variable Möbius root exists,
zero-freeness forces that root to lie in `K₁`.
-/
theorem mobiusFirstRoot_mem_K1_of_zeroFreeOutside
    {K₁ K₂ : Set ℂ} {A B C D z₂ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hz₂ : z₂ ∉ K₂)
    (hden : B + D * z₂ ≠ 0) :
    -(A + C * z₂) / (B + D * z₂) ∈ K₁ := by
  by_contra hnot
  exact hzf
    (-(A + C * z₂) / (B + D * z₂))
    z₂
    hnot
    hz₂
    (asanoPoly_zero_at_mobiusRoot_first hden)

/--
For a nonzero first-variable coefficient, vanishing of the affine polynomial
is equivalent to the first coordinate being the Möbius root.
-/
theorem asanoPoly_eq_zero_iff_first_coord_eq_mobiusRoot
    {A B C D z₁ z₂ : ℂ}
    (hden : B + D * z₂ ≠ 0) :
    asanoPoly A B C D z₁ z₂ = 0 ↔
      z₁ = -(A + C * z₂) / (B + D * z₂) := by
  rw [asanoPoly_rewrite_linear_in_first]
  constructor
  · intro hzero
    have hmul : (B + D * z₂) * z₁ = -(A + C * z₂) := by
      calc
        (B + D * z₂) * z₁
            = (A + C * z₂ + (B + D * z₂) * z₁) - (A + C * z₂) := by
                ring
        _ = 0 - (A + C * z₂) := by
                rw [hzero]
        _ = -(A + C * z₂) := by
                ring
    calc
      z₁ = ((B + D * z₂) * z₁) / (B + D * z₂) := by
            field_simp [hden]
      _ = -(A + C * z₂) / (B + D * z₂) := by
            rw [hmul]
  · intro hz₁
    rw [hz₁]
    have hroot := asanoPoly_zero_at_mobiusRoot_first (A := A) (B := B) (C := C) (D := D) (z₂ := z₂) hden
    simpa [asanoPoly_rewrite_linear_in_first] using hroot

/--
If the second-variable coefficient is nonzero, every zero of the two-variable
affine polynomial has the stated Möbius second coordinate.
-/
theorem second_coord_eq_mobiusRoot_of_asanoPoly_eq_zero
    {A B C D z₁ z₂ : ℂ}
    (hden : C + D * z₁ ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    z₂ = -(A + B * z₁) / (C + D * z₁) := by
  have hlinear : A + B * z₁ + (C + D * z₁) * z₂ = 0 := by
    rw [← asanoPoly_rewrite_linear_in_second]
    exact hzero
  have hmul : (C + D * z₁) * z₂ = -(A + B * z₁) := by
    calc
      (C + D * z₁) * z₂
          = (A + B * z₁ + (C + D * z₁) * z₂) - (A + B * z₁) := by
              ring
      _ = 0 - (A + B * z₁) := by
              rw [hlinear]
      _ = -(A + B * z₁) := by
              ring
  calc
    z₂ = ((C + D * z₁) * z₂) / (C + D * z₁) := by
          field_simp [hden]
    _ = -(A + B * z₁) / (C + D * z₁) := by
          rw [hmul]

/--
For a nonzero second-variable coefficient, vanishing of the affine polynomial
is equivalent to the second coordinate being the Möbius root.
-/
theorem asanoPoly_eq_zero_iff_second_coord_eq_mobiusRoot
    {A B C D z₁ z₂ : ℂ}
    (hden : C + D * z₁ ≠ 0) :
    asanoPoly A B C D z₁ z₂ = 0 ↔
      z₂ = -(A + B * z₁) / (C + D * z₁) := by
  constructor
  · exact second_coord_eq_mobiusRoot_of_asanoPoly_eq_zero hden
  · intro hz₂
    rw [hz₂]
    exact asanoPoly_zero_at_mobiusRoot_second hden

/--
In the nondegenerate determinant branch, a zero of the affine polynomial cannot
occur at the pole `C + D z₁ = 0` of the Möbius second-coordinate map.
-/
theorem denominator_second_ne_zero_of_asanoPoly_eq_zero_of_det_ne_zero
    {A B C D z₁ z₂ : ℂ}
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    C + D * z₁ ≠ 0 := by
  intro hden
  have hz₁ : z₁ = -C / D := by
    have hDz₁ : D * z₁ = -C := by
      calc
        D * z₁ = C + D * z₁ - C := by
            ring
        _ = 0 - C := by
            rw [hden]
        _ = -C := by
            ring
    calc
      z₁ = (D * z₁) / D := by
          field_simp [hD]
      _ = (-C) / D := by
          rw [hDz₁]
      _ = -C / D := rfl
  have hval :
      asanoPoly A B C D z₁ z₂ = (A * D - B * C) / D := by
    rw [asanoPoly_rewrite_linear_in_second, hz₁]
    field_simp [hD]
    ring
  have hdivzero : (A * D - B * C) / D = 0 := by
    rw [← hval]
    exact hzero
  have hnumzero : A * D - B * C = 0 := by
    calc
      A * D - B * C = ((A * D - B * C) / D) * D := by
          field_simp [hD]
      _ = 0 * D := by
          rw [hdivzero]
      _ = 0 := by
          simp
  exact hdet hnumzero

/--
In the nondegenerate determinant branch, every zero lies on the genuine
Möbius graph in the second coordinate.
-/
theorem second_coord_eq_mobiusRoot_of_asanoPoly_eq_zero_of_det_ne_zero
    {A B C D z₁ z₂ : ℂ}
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    z₂ = -(A + B * z₁) / (C + D * z₁) :=
  second_coord_eq_mobiusRoot_of_asanoPoly_eq_zero
    (denominator_second_ne_zero_of_asanoPoly_eq_zero_of_det_ne_zero
      hD hdet hzero)
    hzero

/--
Nondegenerate branch membership forcing in the second coordinate.

If the affine polynomial vanishes at `(z₁,z₂)`, the determinant branch is
nondegenerate, and `z₁` is outside `K₁`, then `z₂` is forced into `K₂`.
-/
theorem second_coord_mem_K2_of_zeroFreeOutside_of_det_ne_zero
    {K₁ K₂ : Set ℂ} {A B C D z₁ z₂ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hz₁ : z₁ ∉ K₁)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    z₂ ∈ K₂ := by
  have hden : C + D * z₁ ≠ 0 :=
    denominator_second_ne_zero_of_asanoPoly_eq_zero_of_det_ne_zero hD hdet hzero
  have hz₂eq :
      z₂ = -(A + B * z₁) / (C + D * z₁) :=
    second_coord_eq_mobiusRoot_of_asanoPoly_eq_zero_of_det_ne_zero hD hdet hzero
  rw [hz₂eq]
  exact mobiusSecondRoot_mem_K2_of_zeroFreeOutside hzf hz₁ hden

/--
In the nondegenerate determinant branch, a zero of the affine polynomial cannot
occur at the pole `B + D z₂ = 0` of the Möbius first-coordinate map.
-/
theorem denominator_first_ne_zero_of_asanoPoly_eq_zero_of_det_ne_zero
    {A B C D z₁ z₂ : ℂ}
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    B + D * z₂ ≠ 0 := by
  intro hden
  have hz₂ : z₂ = -B / D := by
    have hDz₂ : D * z₂ = -B := by
      calc
        D * z₂ = B + D * z₂ - B := by
            ring
        _ = 0 - B := by
            rw [hden]
        _ = -B := by
            ring
    calc
      z₂ = (D * z₂) / D := by
          field_simp [hD]
      _ = (-B) / D := by
          rw [hDz₂]
      _ = -B / D := rfl
  have hval :
      asanoPoly A B C D z₁ z₂ = (A * D - B * C) / D := by
    rw [asanoPoly_rewrite_linear_in_first, hz₂]
    field_simp [hD]
    ring
  have hdivzero : (A * D - B * C) / D = 0 := by
    rw [← hval]
    exact hzero
  have hnumzero : A * D - B * C = 0 := by
    calc
      A * D - B * C = ((A * D - B * C) / D) * D := by
          field_simp [hD]
      _ = 0 * D := by
          rw [hdivzero]
      _ = 0 := by
          simp
  exact hdet hnumzero

/--
In the nondegenerate determinant branch, every zero lies on the genuine
Möbius graph in the first coordinate.
-/
theorem first_coord_eq_mobiusRoot_of_asanoPoly_eq_zero_of_det_ne_zero
    {A B C D z₁ z₂ : ℂ}
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    z₁ = -(A + C * z₂) / (B + D * z₂) :=
  (asanoPoly_eq_zero_iff_first_coord_eq_mobiusRoot
    (denominator_first_ne_zero_of_asanoPoly_eq_zero_of_det_ne_zero hD hdet hzero)).1 hzero

/--
Nondegenerate branch membership forcing in the first coordinate.

If the affine polynomial vanishes at `(z₁,z₂)`, the determinant branch is
nondegenerate, and `z₂` is outside `K₂`, then `z₁` is forced into `K₁`.
-/
theorem first_coord_mem_K1_of_zeroFreeOutside_of_det_ne_zero
    {K₁ K₂ : Set ℂ} {A B C D z₁ z₂ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hz₂ : z₂ ∉ K₂)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    z₁ ∈ K₁ := by
  have hden : B + D * z₂ ≠ 0 :=
    denominator_first_ne_zero_of_asanoPoly_eq_zero_of_det_ne_zero hD hdet hzero
  have hz₁eq :
      z₁ = -(A + C * z₂) / (B + D * z₂) :=
    first_coord_eq_mobiusRoot_of_asanoPoly_eq_zero_of_det_ne_zero hD hdet hzero
  rw [hz₁eq]
  exact mobiusFirstRoot_mem_K1_of_zeroFreeOutside hzf hz₂ hden

/--
Nondegenerate branch exclusion law.

If `z₁` lies outside `K₁` and `z₂` lies outside `K₂`, then in the
nondegenerate determinant branch the affine polynomial cannot vanish.
-/
theorem asanoPoly_ne_zero_of_outside_of_det_ne_zero
    {K₁ K₂ : Set ℂ} {A B C D z₁ z₂ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hz₁ : z₁ ∉ K₁)
    (hz₂ : z₂ ∉ K₂)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0) :
    asanoPoly A B C D z₁ z₂ ≠ 0 := by
  intro hzero
  have hz₂_mem : z₂ ∈ K₂ :=
    second_coord_mem_K2_of_zeroFreeOutside_of_det_ne_zero hzf hz₁ hD hdet hzero
  exact hz₂ hz₂_mem

/--
Nondegenerate branch zero localization.

If the affine polynomial vanishes in the nondegenerate determinant branch,
then at least one coordinate lies in its forbidden set.
-/
theorem asanoPoly_zero_imp_mem_left_or_right_of_det_ne_zero
    {K₁ K₂ : Set ℂ} {A B C D z₁ z₂ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    z₁ ∈ K₁ ∨ z₂ ∈ K₂ := by
  by_cases hz₁ : z₁ ∈ K₁
  · exact Or.inl hz₁
  · right
    exact second_coord_mem_K2_of_zeroFreeOutside_of_det_ne_zero hzf hz₁ hD hdet hzero

/--
Nondegenerate branch outside-exclusion in conjunctive form.

If the affine polynomial vanishes in the nondegenerate determinant branch,
then it is impossible for both coordinates to lie outside their forbidden sets.
-/
theorem asanoPoly_zero_not_outside_pair_of_det_ne_zero
    {K₁ K₂ : Set ℂ} {A B C D z₁ z₂ : ℂ}
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hzero : asanoPoly A B C D z₁ z₂ = 0) :
    ¬ (z₁ ∉ K₁ ∧ z₂ ∉ K₂) := by
  intro hout
  have hmem : z₁ ∈ K₁ ∨ z₂ ∈ K₂ :=
    asanoPoly_zero_imp_mem_left_or_right_of_det_ne_zero hzf hD hdet hzero
  rcases hmem with hz₁ | hz₂
  · exact hout.1 hz₁
  · exact hout.2 hz₂

/--
Nondegenerate endpoint branch: contracted root localization.

Assume `D ≠ 0`, outside zero-freeness for the two-variable affine block, and
one of the two endpoint alternatives
`(C ≠ 0 ∧ -(C/D) ∈ K₁)` or `(B ≠ 0 ∧ -(B/D) ∈ K₂)`.
Then any contracted root `A + D z = 0` lies in `-K₁K₂`.
-/
theorem contracted_zero_mem_signedProduct_of_nonDegenerate_endpoint
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hend : (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  have hroot : A + D * z = 0 := by
    simpa [IsContractedZero, asanoContract] using hzero
  rcases hend with hleft | hright
  · rcases hleft with ⟨hC, hpole⟩
    have hslice : -(A / C) ∈ K₂ := by
      by_contra hnot
      have hzeroSlice : asanoPoly A B C D 0 (-(A / C)) = 0 := by
        unfold asanoPoly
        field_simp [hC]
        ring
      exact (hzf 0 (-(A / C)) h0₁ hnot) hzeroSlice
    have hz : z = -(A / D) := by
      have hDz : D * z = -A := by
        calc
          D * z = A + D * z - A := by ring
          _ = 0 - A := by rw [hroot]
          _ = -A := by ring
      field_simp [hD]
      simpa [mul_comm] using hDz
    refine ⟨-(C / D), hpole, -(A / C), hslice, ?_⟩
    rw [hz]
    field_simp [hC, hD]
  · rcases hright with ⟨hB, hinfty⟩
    have hslice : -(A / B) ∈ K₁ := by
      by_contra hnot
      have hzeroSlice : asanoPoly A B C D (-(A / B)) 0 = 0 := by
        unfold asanoPoly
        field_simp [hB]
        ring
      exact (hzf (-(A / B)) 0 hnot h0₂) hzeroSlice
    have hz : z = -(A / D) := by
      have hDz : D * z = -A := by
        calc
          D * z = A + D * z - A := by ring
          _ = 0 - A := by rw [hroot]
          _ = -A := by ring
      field_simp [hD]
      simpa [mul_comm] using hDz
    refine ⟨-(A / B), hslice, -(B / D), hinfty, ?_⟩
    rw [hz]
    field_simp [hB, hD]

/--
Nondegenerate endpoint branch: outside the signed product obstruction,
the contracted polynomial is nonzero.
-/
theorem asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate_endpoint
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hend : (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  intro hzero
  exact hz_not
    (contracted_zero_mem_signedProduct_of_nonDegenerate_endpoint
      h0₁ h0₂ hzf hD hend hzero)

/--
Endpoint alternative discharges the nondegenerate Asano-Ruelle premise:
every contracted zero lies in the signed-product obstruction set.
-/
theorem asanoRuelle_premise_of_nonDegenerate_endpoint
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hend : (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)) :
    ∀ w : ℂ, IsContractedZero A D w → w ∈ signedProductSet K₁ K₂ := by
  intro w hw
  exact contracted_zero_mem_signedProduct_of_nonDegenerate_endpoint
    h0₁ h0₂ hzf hD hend hw

/--
Rank-one algebraic Asano closure.

Assume the original two-variable affine polynomial is zero-free whenever
`z₁ ∉ K₁` and `z₂ ∉ K₂`.  If `D ≠ 0`, `AD - BC = 0`, and the contracted
polynomial vanishes at `z`, then `z` lies in the signed product obstruction
`-K₁K₂`.
-/
theorem contracted_zero_mem_signedProduct_of_rankOne
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C = 0)
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  have hC : C ≠ 0 := by
    intro hC
    have hAD : A * D = B * C := sub_eq_zero.mp hdet
    have hAD0 : A * D = 0 := by
      simpa [hC] using hAD
    have hA : A = 0 := by
      rcases mul_eq_zero.mp hAD0 with hA | hD0
      · exact hA
      · exact False.elim (hD hD0)
    exact hzf 0 0 h0₁ h0₂ (by simp [asanoPoly, hA])

  have hu : -(C / D) ∈ K₁ :=
    left_factor_zero_mem_of_rankOne h0₂ hzf hD hdet
  have hv : -(A / C) ∈ K₂ :=
    right_factor_zero_mem_of_rankOne h0₁ h0₂ hzf hD hdet

  refine ⟨-(C / D), hu, -(A / C), hv, ?_⟩

  have hzero' : A + D * z = 0 := by
    simpa [IsContractedZero, asanoContract] using hzero
  have hzD : D * z = -A := by
    calc
      D * z = A + D * z - A := by ring
      _ = 0 - A := by rw [hzero']
      _ = -A := by ring
  have hz : z = -A / D := by
    field_simp [hD]
    simpa [mul_comm] using hzD

  calc
    z = -A / D := hz
    _ = -((-(C / D)) * (-(A / C))) := by
      field_simp [hC, hD]

/--
Rank-one Asano contraction zero-freeness outside the signed product
obstruction.
-/
theorem asanoContract_ne_zero_outside_signedProduct_of_rankOne
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C = 0)
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  intro hzero
  exact hz_not
    (contracted_zero_mem_signedProduct_of_rankOne
      h0₁ h0₂ hzf hD hdet hzero)

/--
A combined native algebraic closure for the two easy branches of the Asano
proof split: `D = 0`, or `D ≠ 0` with rank-one determinant `AD - BC = 0`.

The remaining branch `D ≠ 0 ∧ AD - BC ≠ 0` is the genuine Möbius/Riemann-sphere
argument and is intentionally not asserted here.
-/
theorem asanoContract_ne_zero_outside_signedProduct_of_degenerate_or_rankOne
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hcase : D = 0 ∨ (D ≠ 0 ∧ A * D - B * C = 0))
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  rcases hcase with hD | ⟨hD, hdet⟩
  · exact asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
  · exact asanoContract_ne_zero_outside_signedProduct_of_rankOne
      h0₁ h0₂ hzf hD hdet hz_not

/--
Combined branch contracted-zero localization.

In the algebraic split (`D = 0` or rank-one with `D ≠ 0`), any contracted zero
must lie in the signed product obstruction set.
-/
theorem contracted_zero_mem_signedProduct_of_degenerate_or_rankOne
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hcase : D = 0 ∨ (D ≠ 0 ∧ A * D - B * C = 0))
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  rcases hcase with hD | ⟨hD, hdet⟩
  · have hneq : asanoContract A D z ≠ 0 :=
      asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
    exact False.elim (hneq hzero)
  · exact contracted_zero_mem_signedProduct_of_rankOne
      h0₁ h0₂ hzf hD hdet hzero

/--
Combined branch contracted-zero localization (implication form).

Under the algebraic split (`D = 0` or rank-one with `D ≠ 0`), contracted
vanishing implies membership in the signed-product obstruction set.
-/
theorem isContractedZero_imp_mem_signedProduct_of_degenerate_or_rankOne
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hcase : D = 0 ∨ (D ≠ 0 ∧ A * D - B * C = 0))
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  exact contracted_zero_mem_signedProduct_of_degenerate_or_rankOne
    h0₁ h0₂ hzf hcase hzero

/--
Combined branch outside obstruction implies no contracted zero.

This is the direct logical contrapositive of contracted-zero localization in
the algebraic split (`D = 0` or rank-one with `D ≠ 0`).
-/
theorem not_isContractedZero_of_not_mem_signedProduct_of_degenerate_or_rankOne
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hcase : D = 0 ∨ (D ≠ 0 ∧ A * D - B * C = 0))
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    ¬ IsContractedZero A D z := by
  intro hzero
  exact hz_not
    (isContractedZero_imp_mem_signedProduct_of_degenerate_or_rankOne
      h0₁ h0₂ hzf hcase hzero)

/--
Nondegenerate contracted Asano closure under the explicit Asano-Ruelle root
membership premise.

This theorem isolates the exact remaining geometric debt in the nondegenerate
branch (`D ≠ 0`, `AD - BC ≠ 0`) as a single input hypothesis:
every contracted zero belongs to the signed product obstruction set.
-/
theorem asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate
    {K₁ K₂ : Set ℂ} {A D z : ℂ}
    (hAsanoRuelle :
      ∀ w : ℂ, IsContractedZero A D w → w ∈ signedProductSet K₁ K₂)
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  intro hzero
  exact hz_not (hAsanoRuelle z hzero)

/--
Adapter: the existing nondegenerate closure theorem can be discharged from
the concrete endpoint condition.
-/
theorem asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate_via_endpoint
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hend : (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  exact asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate
    (K₁ := K₁) (K₂ := K₂) (A := A) (D := D) (z := z)
    (asanoRuelle_premise_of_nonDegenerate_endpoint
      (K₁ := K₁) (K₂ := K₂) (A := A) (B := B) (C := C) (D := D)
      h0₁ h0₂ hzf hD hend)
    hz_not

/--
Adapter: root-localization in the nondegenerate branch from the concrete
endpoint condition.
-/
theorem contracted_zero_mem_signedProduct_of_nonDegenerate_via_endpoint
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hend : (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  exact asanoRuelle_premise_of_nonDegenerate_endpoint
    (K₁ := K₁) (K₂ := K₂) (A := A) (B := B) (C := C) (D := D)
    h0₁ h0₂ hzf hD hend z hzero

/--
Paired nondegenerate endpoint adapters:
1) outside signed-product implies nonvanishing contraction;
2) contracted root implies signed-product membership.
-/
theorem nonDegenerate_endpoint_adapter_pair
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hend : (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)) :
    (z ∉ signedProductSet K₁ K₂ → asanoContract A D z ≠ 0)
      ∧ (IsContractedZero A D z → z ∈ signedProductSet K₁ K₂) := by
  refine ⟨?_, ?_⟩
  · intro hz_not
    exact asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate_via_endpoint
      h0₁ h0₂ hzf hD hend hz_not
  · intro hzero
    exact contracted_zero_mem_signedProduct_of_nonDegenerate_via_endpoint
      h0₁ h0₂ hzf hD hend hzero

/--
Full contracted Asano closure assembled from all determinant branches:

* `D = 0`,
* `D ≠ 0 ∧ AD - BC = 0`,
* `D ≠ 0 ∧ AD - BC ≠ 0` (via explicit Asano-Ruelle premise).
-/
theorem asanoContract_ne_zero_outside_signedProduct
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hAsanoRuelleNonDeg :
      D ≠ 0 →
      A * D - B * C ≠ 0 →
      ∀ w : ℂ, IsContractedZero A D w → w ∈ signedProductSet K₁ K₂)
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  by_cases hD : D = 0
  · exact asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
  · by_cases hdet : A * D - B * C = 0
    · exact asanoContract_ne_zero_outside_signedProduct_of_rankOne
        h0₁ h0₂ hzf hD hdet hz_not
    · exact asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate
        (K₁ := K₁) (K₂ := K₂) (A := A) (D := D) (z := z)
        (hAsanoRuelleNonDeg hD hdet) hz_not

/--
Full contracted Asano closure assembled from all determinant branches, with
the nondegenerate branch discharged by the concrete endpoint alternative.
-/
theorem asanoContract_ne_zero_outside_signedProduct_of_endpoint_nonDeg
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hEndpointNonDeg :
      D ≠ 0 →
      A * D - B * C ≠ 0 →
      ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    asanoContract A D z ≠ 0 := by
  by_cases hD : D = 0
  · exact asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
  · by_cases hdet : A * D - B * C = 0
    · exact asanoContract_ne_zero_outside_signedProduct_of_rankOne
        h0₁ h0₂ hzf hD hdet hz_not
    · exact asanoContract_ne_zero_outside_signedProduct_of_nonDegenerate_via_endpoint
        h0₁ h0₂ hzf hD (hEndpointNonDeg hD hdet) hz_not

/--
Full contracted-root localization across all determinant branches, where the
nondegenerate branch is supplied by the concrete endpoint alternative.
-/
theorem contracted_zero_mem_signedProduct_of_endpoint_nonDeg
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hEndpointNonDeg :
      D ≠ 0 →
      A * D - B * C ≠ 0 →
      ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    (hzero : IsContractedZero A D z) :
    z ∈ signedProductSet K₁ K₂ := by
  by_cases hD : D = 0
  · have hneq : asanoContract A D z ≠ 0 :=
      asanoContract_ne_zero_of_D_eq_zero h0₁ h0₂ hzf hD
    exact False.elim (hneq hzero)
  · by_cases hdet : A * D - B * C = 0
    · exact contracted_zero_mem_signedProduct_of_rankOne
        h0₁ h0₂ hzf hD hdet hzero
    · exact contracted_zero_mem_signedProduct_of_nonDegenerate_via_endpoint
        h0₁ h0₂ hzf hD (hEndpointNonDeg hD hdet) hzero

/--
Contrapositive full closure under the endpoint-nondegenerate hypothesis:
outside the signed-product obstruction, there is no contracted zero.
-/
theorem not_isContractedZero_of_not_mem_signedProduct_of_endpoint_nonDeg
    {K₁ K₂ : Set ℂ} {A B C D z : ℂ}
    (h0₁ : (0 : ℂ) ∉ K₁)
    (h0₂ : (0 : ℂ) ∉ K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hEndpointNonDeg :
      D ≠ 0 →
      A * D - B * C ≠ 0 →
      ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂)))
    (hz_not : z ∉ signedProductSet K₁ K₂) :
    ¬ IsContractedZero A D z := by
  intro hzero
  exact hz_not
    (contracted_zero_mem_signedProduct_of_endpoint_nonDeg
      h0₁ h0₂ hzf hEndpointNonDeg hzero)

end InfoGeometry.Analysis.AsanoContractionNative
