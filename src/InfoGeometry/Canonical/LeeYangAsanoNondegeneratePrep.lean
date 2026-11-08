import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-!
# InfoGeometry.Canonical.LeeYangAsanoNondegeneratePrep

Native preparation lemmas for the nondegenerate branch of Asano A.1.

This file proves only elementary consequences needed before the genuine
Riemann-sphere/topological step.

Closed here:
* off-product-set elimination;
* division form of the forbidden hyperbola;
* contracted root algebra;
* pole/numerator exclusion in the nondegenerate Möbius map.

Not closed here:
* the final nondegenerate Asano topological theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeCore

open Set

/--
If `z` is outside the contracted forbidden set, then no forbidden pair
`u ∈ K₁`, `v ∈ K₂` can satisfy `z = -(u*v)`.
-/
@[rep_depth operator]
theorem off_negProductSet_forall
    {K₁ K₂ : Set ℂ}
    {z : ℂ}
    (hzOff : z ∉ negProductSet K₁ K₂) :
    ∀ u v : ℂ, u ∈ K₁ → v ∈ K₂ → z ≠ -(u * v) := by
  intro u v hu hv hz
  exact hzOff ⟨u, hu, v, hv, hz⟩

/--
If `z ∉ -K₁K₂`, then for every nonzero `u ∈ K₁`,
the point `-(z/u)` is outside `K₂`.
-/
@[rep_depth operator]
theorem neg_div_not_mem_K₂_of_mem_K₁_off_negProductSet
    {K₁ K₂ : Set ℂ}
    {z u : ℂ}
    (hzOff : z ∉ negProductSet K₁ K₂)
    (hu : u ∈ K₁)
    (hu0 : u ≠ 0) :
    -(z / u) ∉ K₂ := by
  intro hv
  apply hzOff
  refine ⟨u, hu, -(z / u), hv, ?_⟩
  field_simp [hu0]

/--
Symmetric division form: if `z ∉ -K₁K₂`, then for every nonzero `v ∈ K₂`,
the point `-(z/v)` is outside `K₁`.
-/
@[rep_depth operator]
theorem neg_div_not_mem_K₁_of_mem_K₂_off_negProductSet
    {K₁ K₂ : Set ℂ}
    {z v : ℂ}
    (hzOff : z ∉ negProductSet K₁ K₂)
    (hv : v ∈ K₂)
    (hv0 : v ≠ 0) :
    -(z / v) ∉ K₁ := by
  intro hu
  apply hzOff
  refine ⟨-(z / v), hu, v, hv, ?_⟩
  field_simp [hv0]

/--
A root of the contracted polynomial `A + D*z` is `z = -A/D`
when `D ≠ 0`.
-/
@[rep_depth operator]
theorem contracted_root_eq_neg_div
    {A D z : ℂ}
    (hD : D ≠ 0)
    (hroot : A + D * z = 0) :
    z = -(A / D) := by
  have hDz : D * z = -A := by
    calc
      D * z = (A + D * z) - A := by ring
      _ = 0 - A := by rw [hroot]
      _ = -A := by ring
  calc
    z = (D * z) / D := by
          have hdiv : (D * z) / D = z := by
            field_simp [hD]
          exact hdiv.symm
    _ = (-A) / D := by rw [hDz]
    _ = -(A / D) := by ring

/--
In the nondegenerate branch, the pole point of the root map is not also
a zero of the numerator.
-/
@[rep_depth operator]
theorem rootMap_pole_not_numerator_zero
    {A B C D z₁ : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hden : C + D * z₁ = 0) :
    A + B * z₁ ≠ 0 := by
  intro hnum
  apply hNondeg
  calc
    A * D - B * C
        = D * (A + B * z₁) - B * (C + D * z₁) := by ring
    _ = D * 0 - B * 0 := by rw [hnum, hden]
    _ = 0 := by ring

/--
Swapped pole/numerator exclusion for the inverse root map.
-/
@[rep_depth operator]
theorem invRootMap_pole_not_numerator_zero
    {A B C D z₂ : ℂ}
    (hNondeg : A * D - B * C ≠ 0)
    (hden : B + D * z₂ = 0) :
    A + C * z₂ ≠ 0 := by
  intro hnum
  apply hNondeg
  calc
    A * D - B * C
        = D * (A + C * z₂) - C * (B + D * z₂) := by ring
    _ = D * 0 - C * 0 := by rw [hnum, hden]
    _ = 0 := by ring

/--
If `z = -A/D` and `z ∉ -K₁K₂`, then every nonzero `u ∈ K₁`
excludes the point `A/(D*u)` from `K₂`.
-/
@[rep_depth operator]
theorem contracted_root_excludes_K₂_hyperbola
    {K₁ K₂ : Set ℂ}
    {A D z u : ℂ}
    (hD : D ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂)
    (hroot : A + D * z = 0)
    (hu : u ∈ K₁)
    (hu0 : u ≠ 0) :
    A / (D * u) ∉ K₂ := by
  have hz : z = -(A / D) :=
    contracted_root_eq_neg_div hD hroot
  have hnot : -(z / u) ∉ K₂ :=
    neg_div_not_mem_K₂_of_mem_K₁_off_negProductSet
      hzOff hu hu0
  have hpoint : -(z / u) = A / (D * u) := by
    rw [hz]
    field_simp [hD, hu0]
  simpa [hpoint] using hnot

/--
Symmetric contracted-root hyperbola exclusion.
-/
@[rep_depth operator]
theorem contracted_root_excludes_K₁_hyperbola
    {K₁ K₂ : Set ℂ}
    {A D z v : ℂ}
    (hD : D ≠ 0)
    (hzOff : z ∉ negProductSet K₁ K₂)
    (hroot : A + D * z = 0)
    (hv : v ∈ K₂)
    (hv0 : v ≠ 0) :
    A / (D * v) ∉ K₁ := by
  have hz : z = -(A / D) :=
    contracted_root_eq_neg_div hD hroot
  have hnot : -(z / v) ∉ K₁ :=
    neg_div_not_mem_K₁_of_mem_K₂_off_negProductSet
      hzOff hv hv0
  have hpoint : -(z / v) = A / (D * v) := by
    rw [hz]
    field_simp [hD, hv0]
  simpa [hpoint] using hnot

end InfoGeometry.Canonical.LeeYangAsanoNativeCore
