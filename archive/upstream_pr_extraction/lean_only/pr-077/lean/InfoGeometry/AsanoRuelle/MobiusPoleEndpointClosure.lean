import InfoGeometry.Analysis.AsanoContractionNative
import InfoGeometry.AsanoRuelle.MobiusPoleBlowup

/-!
# Closed/bounded endpoint closure for the nondegenerate Möbius branch

This file composes the existing local Möbius-root and pole-blowup theorems.
It proves only the conditional endpoint statement; it does not introduce a
categorical colimit or a Weyl/conformal interpretation.
-/

noncomputable section

open scoped Topology
open Filter
open Bornology

namespace InfoGeometry.AsanoRuelle

open InfoGeometry.Analysis.AsanoContractionNative

/--
Closedness of the first forbidden set and boundedness of the second force the
left Möbius pole into the first set in the nondegenerate zero-free branch.
-/
theorem mobius_left_pole_mem_of_closed_bounded_zeroFree
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (hK₁ : IsClosed K₁)
    (hK₂ : IsBounded K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0) :
    -(C / D) ∈ K₁ := by
  by_contra hpole
  have hcomp : K₁ᶜ ∈ 𝓝 (-(C / D)) :=
    hK₁.isOpen_compl.mem_nhds hpole
  have hshift :
      Tendsto (fun ε : ℂ => -(C / D) + ε)
        (𝓝 (0 : ℂ)) (𝓝 (-(C / D))) := by
      simpa using
        (tendsto_const_nhds.add
        (tendsto_id : Tendsto id (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ))))
  have hsource :
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), -(C / D) + ε ∈ K₁ᶜ :=
    (hshift.eventually hcomp).filter_mono nhdsWithin_le_nhds
  have htarget :
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), mobiusPolePath A B C D ε ∈ K₂ := by
    filter_upwards [hsource, self_mem_nhdsWithin] with ε hε hε0
    have hden : C + D * (-(C / D) + ε) ≠ 0 := by
      have hidentity : C + D * (-(C / D) + ε) = D * ε := by
        calc
          C + D * (-(C / D) + ε) = C + D * (-(C / D)) + D * ε := by ring
          _ = C - C + D * ε := by
            have hcancel : D * (-(C / D)) = -C := by
              calc
                D * (-(C / D)) = (D * -C) / D := by ring
                _ = -C := by rw [mul_div_cancel_left₀ (-C) hD]
            rw [hcancel]
            ring
          _ = D * ε := by ring
      rw [hidentity]
      exact mul_ne_zero hD hε0
    rw [mobiusPolePath]
    convert
      (mobiusSecondRoot_mem_K2_of_zeroFreeOutside
        (A := A) (B := B) (C := C) (D := D)
        hzf hε hden) using 1 <;> ring
  exact mobiusPolePath_not_eventually_mem_bounded
    A B C D hD hdet hK₂ htarget

/--
The symmetric endpoint statement: closedness of the second forbidden set and
boundedness of the first force the right Möbius pole into the second set.
It is obtained from the same native root and blow-up kernels after swapping
the two variables.
-/
theorem mobius_right_pole_mem_of_closed_bounded_zeroFree
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (hK₂ : IsClosed K₂)
    (hK₁ : IsBounded K₁)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0) :
    -(B / D) ∈ K₂ := by
  by_contra hpole
  have hcomp : K₂ᶜ ∈ 𝓝 (-(B / D)) :=
    hK₂.isOpen_compl.mem_nhds hpole
  have hshift :
      Tendsto (fun ε : ℂ => -(B / D) + ε)
        (𝓝 (0 : ℂ)) (𝓝 (-(B / D))) := by
    simpa using
      (tendsto_const_nhds.add
        (tendsto_id : Tendsto id (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ))))
  have hsource :
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), -(B / D) + ε ∈ K₂ᶜ :=
    (hshift.eventually hcomp).filter_mono nhdsWithin_le_nhds
  have htarget :
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), mobiusPolePath A C B D ε ∈ K₁ := by
    filter_upwards [hsource, self_mem_nhdsWithin] with ε hε hε0
    have hden : B + D * (-(B / D) + ε) ≠ 0 := by
      have hidentity : B + D * (-(B / D) + ε) = D * ε := by
        calc
          B + D * (-(B / D) + ε) = B + D * (-(B / D)) + D * ε := by ring
          _ = B - B + D * ε := by
            have hcancel : D * (-(B / D)) = -B := by
              calc
                D * (-(B / D)) = (D * -B) / D := by ring
                _ = -B := by rw [mul_div_cancel_left₀ (-B) hD]
            rw [hcancel]
            ring
          _ = D * ε := by ring
      rw [hidentity]
      exact mul_ne_zero hD hε0
    rw [mobiusPolePath]
    convert
      (mobiusFirstRoot_mem_K1_of_zeroFreeOutside
        (A := A) (B := B) (C := C) (D := D)
        hzf hε hden) using 1 <;> ring
  have hdet' : A * D - C * B ≠ 0 := by
    simpa [mul_comm] using hdet
  exact mobiusPolePath_not_eventually_mem_bounded
    A C B D hD hdet' hK₁ htarget

theorem mobius_both_poles_mem_of_closed_bounded_zeroFree
    {K₁ K₂ : Set ℂ} {A B C D : ℂ}
    (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂)
    (hK₁_bounded : IsBounded K₁)
    (hK₂_bounded : IsBounded K₂)
    (hzf : ZeroFreeOutside K₁ K₂ A B C D)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0) :
    -(C / D) ∈ K₁ ∧ -(B / D) ∈ K₂ := by
  exact
    ⟨mobius_left_pole_mem_of_closed_bounded_zeroFree
        hK₁ hK₂_bounded hzf hD hdet,
      mobius_right_pole_mem_of_closed_bounded_zeroFree
        hK₂ hK₁_bounded hzf hD hdet⟩

end InfoGeometry.AsanoRuelle
