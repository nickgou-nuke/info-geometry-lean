import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.LeeYangAsanoNativeCore
import InfoGeometry.Canonical.LeeYangAsanoNondegeneratePrep
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint

/-!
# InfoGeometry.Canonical.LeeYangAsanoEndpointNative

Native endpoint/slice lemmas for the nondegenerate Asano branch.

Closed here:
* zero of the `z₂`-slice at `z₁ = 0` lies in `K₂`;
* zero of the `z₁`-slice at `z₂ = 0` lies in `K₁`;
* if the Möbius pole is in `K₁`, the contracted root lies in `-K₁K₂`;
* if the value at infinity is in `K₂`, the contracted root lies in `-K₁K₂`.

Still open:
* the Riemann-sphere/topological theorem proving one of the needed endpoint
  alternatives, or an equivalent global covering argument.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeCore

/--
If `C ≠ 0`, then the zero of the `z₂`-slice at `z₁ = 0`,
namely `-A/C`, must lie in `K₂`.
-/
@[rep_depth operator]
theorem zeroSlice_z₂_mem_K₂
    {K₁ K₂ : Set ℂ}
    {A B C D : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (hC : C ≠ 0)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0) :
    -(A / C) ∈ K₂ := by
  by_contra hnot
  have hzero : asanoPhi A B C D 0 (-(A / C)) = 0 := by
    unfold asanoPhi
    field_simp [hC]
    ring_nf
  exact (hPhi 0 (-(A / C)) h0K₁ hnot) hzero

/--
If `B ≠ 0`, then the zero of the `z₁`-slice at `z₂ = 0`,
namely `-A/B`, must lie in `K₁`.
-/
@[rep_depth operator]
theorem zeroSlice_z₁_mem_K₁
    {K₁ K₂ : Set ℂ}
    {A B C D : ℂ}
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hB : B ≠ 0)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0) :
    -(A / B) ∈ K₁ := by
  by_contra hnot
  have hzero : asanoPhi A B C D (-(A / B)) 0 = 0 := by
    unfold asanoPhi
    field_simp [hB]
    ring_nf
  exact (hPhi (-(A / B)) 0 hnot h0K₂) hzero

/--
If the Möbius pole `-C/D` lies in `K₁`, then together with the forced
slice zero `-A/C ∈ K₂`, the contracted root lies in `-K₁K₂`.
-/
@[rep_depth operator]
theorem contracted_root_mem_negProductSet_of_pole_mem_K₁
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (hD : D ≠ 0)
    (hC : C ≠ 0)
    (hroot : A + D * z = 0)
    (hpole : -(C / D) ∈ K₁)
    (hzeroSlice : -(A / C) ∈ K₂) :
    z ∈ negProductSet K₁ K₂ := by
  have hz : z = -(A / D) :=
    contracted_root_eq_neg_div hD hroot
  refine ⟨-(C / D), hpole, -(A / C), hzeroSlice, ?_⟩
  rw [hz]
  field_simp [hC, hD]

/--
If the value at infinity `-B/D` lies in `K₂`, then together with the forced
slice zero `-A/B ∈ K₁`, the contracted root lies in `-K₁K₂`.
-/
@[rep_depth operator]
theorem contracted_root_mem_negProductSet_of_inftyValue_mem_K₂
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (hD : D ≠ 0)
    (hB : B ≠ 0)
    (hroot : A + D * z = 0)
    (hzeroSlice : -(A / B) ∈ K₁)
    (hinfty : -(B / D) ∈ K₂) :
    z ∈ negProductSet K₁ K₂ := by
  have hz : z = -(A / D) :=
    contracted_root_eq_neg_div hD hroot
  refine ⟨-(A / B), hzeroSlice, -(B / D), hinfty, ?_⟩
  rw [hz]
  field_simp [hB, hD]

/--
Algebraic reduction: if either endpoint alternative is available, the
nondegenerate Asano conclusion follows.

The missing topological proof must provide one of these alternatives, or an
equivalent global argument.
-/
@[rep_depth operator]
theorem asano_nondegenerate_root_mem_negProductSet_of_endpoint
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hD : D ≠ 0)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hroot : A + D * z = 0)
    (hend :
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨
      (B ≠ 0 ∧ -(B / D) ∈ K₂)) :
    z ∈ negProductSet K₁ K₂ := by
  rcases hend with hleft | hright
  · rcases hleft with ⟨hC, hpole⟩
    have hzeroSlice : -(A / C) ∈ K₂ :=
      zeroSlice_z₂_mem_K₂ h0K₁ hC hPhi
    exact
      contracted_root_mem_negProductSet_of_pole_mem_K₁
        (A := A) (B := B) (C := C) hD hC hroot hpole hzeroSlice
  · rcases hright with ⟨hB, hinfty⟩
    have hzeroSlice : -(A / B) ∈ K₁ :=
      zeroSlice_z₁_mem_K₁ h0K₂ hB hPhi
    exact
      contracted_root_mem_negProductSet_of_inftyValue_mem_K₂
        (A := A) (B := B) (C := C) hD hB hroot hzeroSlice hinfty

/--
Contrapositive endpoint form: if `z` is outside the contracted forbidden set,
then `A + D*z ≠ 0`, assuming one endpoint alternative.
-/
@[rep_depth operator]
theorem asano_nondegenerate_not_root_of_not_mem_negProductSet_of_endpoint
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hD : D ≠ 0)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hend :
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨
      (B ≠ 0 ∧ -(B / D) ∈ K₂))
    (hzOff : z ∉ negProductSet K₁ K₂) :
    A + D * z ≠ 0 := by
  intro hroot
  exact hzOff
    (asano_nondegenerate_root_mem_negProductSet_of_endpoint
      h0K₁ h0K₂ hD hPhi hroot hend)

/--
Topological-left endpoint specialization:
if the bounded/closed nondegenerate topological hypotheses hold, the endpoint
disjunction is provided by
`AsanoRuelleTopologicalEndpoint.asano_endpoint_disjunction_left`, hence the
native nondegenerate Asano root-membership theorem follows directly.
-/
@[rep_depth operator]
theorem asano_nondegenerate_root_mem_negProductSet_of_topological_left
    {K₁ K₂ : Set ℂ}
    {A B C D z : ℂ}
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hClosed₁ : IsClosed K₁)
    (hBdd₂ : Bornology.IsBounded K₂)
    (hD : D ≠ 0)
    (hDet : A * D - B * C ≠ 0)
    (hPhi :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        asanoPhi A B C D z₁ z₂ ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ := by
  have hend :
      (C ≠ 0 ∧ -(C / D) ∈ K₁) ∨
      (B ≠ 0 ∧ -(B / D) ∈ K₂) :=
    by
      simpa [neg_div] using
        InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint.asano_endpoint_disjunction_left
          A B C D K₁ K₂ hD hDet hClosed₁ hBdd₂ h0K₁ hPhi
  exact asano_nondegenerate_root_mem_negProductSet_of_endpoint
    h0K₁ h0K₂ hD hPhi hroot hend

end InfoGeometry.Canonical.LeeYangAsanoNativeCore
