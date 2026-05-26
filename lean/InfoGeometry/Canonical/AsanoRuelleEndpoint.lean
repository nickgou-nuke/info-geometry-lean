import Mathlib

/-!
# InfoGeometry.Canonical.AsanoRuelleEndpoint

Algebraic endpoint lemmas for the Asano--Ruelle contraction step.

This file proves the product-set membership algebra once the endpoint data
has been supplied.

It does not prove the nondegenerate circular-region/topological endpoint
lemma. That remains the Grace/Ruelle analytic step.
-/

namespace InfoGeometry.Canonical.AsanoRuelleEndpoint

open Set

/--
The forbidden product set used in Asano contraction:

  -(K₁ K₂) = { -u*v | u ∈ K₁, v ∈ K₂ }.
-/
def negProductSet (K₁ K₂ : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ u ∈ K₁, ∃ v ∈ K₂, z = -(u * v)}

/--
Endpoint product membership.

If a root `z` of the contracted polynomial `A + D z` is equal to `-u*v`
with `u ∈ K₁` and `v ∈ K₂`, then `z ∈ -(K₁K₂)`.

This is the final algebraic step after the nondegenerate Grace/Ruelle endpoint
argument has produced the two endpoint elements.
-/
theorem contracted_root_mem_negProductSet_of_endpoint
    (K₁ K₂ : Set ℂ)
    {u v z : ℂ}
    (hu : u ∈ K₁)
    (hv : v ∈ K₂)
    (hz : z = -(u * v)) :
    z ∈ negProductSet K₁ K₂ := by
  exact ⟨u, hu, v, hv, hz⟩

/--
If two values are roots of the same nonconstant contracted affine polynomial
`A + D z`, then they are equal.

This is the algebraic uniqueness step used after one has shown that
`-u*v` is also a contracted root.
-/
theorem contracted_affine_root_unique
    {A D z w : ℂ}
    (hD : D ≠ 0)
    (hz : A + D * z = 0)
    (hw : A + D * w = 0) :
    z = w := by
  have hsub : D * z - D * w = 0 := by
    calc
      D * z - D * w
          = (A + D * z) - (A + D * w) := by ring
      _   = 0 := by rw [hz, hw]; ring
  have hmul : D * (z - w) = 0 := by
    calc
      D * (z - w) = D * z - D * w := by ring
      _ = 0 := hsub
  have hzw : z - w = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hD
  exact sub_eq_zero.mp hzw

/--
Scaling invariance of the contracted affine root equation.

For nonzero `λ`, the equation `A + D z = 0` is equivalent to
`(λA) + (λD) z = 0`.
-/
theorem contracted_affine_root_scale_iff
    {A D z l : ℂ}
    (hl : l ≠ 0) :
    A + D * z = 0 ↔ (l * A) + (l * D) * z = 0 := by
  constructor
  · intro hz
    calc
      (l * A) + (l * D) * z
          = l * (A + D * z) := by ring
      _ = l * 0 := by rw [hz]
      _ = 0 := by ring
  · intro hscaled
    have hmul : l * (A + D * z) = 0 := by
      calc
        l * (A + D * z) = (l * A) + (l * D) * z := by ring
        _ = 0 := hscaled
    exact (mul_eq_zero.mp hmul).resolve_left hl

/--
Scaling formula for the Asano nondegeneracy discriminant.
-/
theorem asano_discriminant_scale
    {A B C D l : ℂ} :
    (l * A) * (l * D) - (l * B) * (l * C)
      = l^2 * (A * D - B * C) := by
  ring

/--
For nonzero `l`, nondegeneracy `AD - BC ≠ 0` is invariant under scaling
`(A,B,C,D) ↦ (lA,lB,lC,lD)`.
-/
theorem asano_discriminant_scale_ne_zero_iff
    {A B C D l : ℂ}
    (hl : l ≠ 0) :
    (A * D - B * C ≠ 0) ↔
      ((l * A) * (l * D) - (l * B) * (l * C) ≠ 0) := by
  rw [asano_discriminant_scale]
  have hl2 : l^2 ≠ 0 := by
    simpa [pow_two] using mul_ne_zero hl hl
  constructor
  · intro h
    exact mul_ne_zero hl2 h
  · intro h
    exact (mul_ne_zero_iff.mp h).2

/--
For nonzero `l`, degeneracy `AD - BC = 0` is invariant under scaling
`(A,B,C,D) ↦ (lA,lB,lC,lD)`.
-/
theorem asano_discriminant_scale_eq_zero_iff
    {A B C D l : ℂ}
    (hl : l ≠ 0) :
    (A * D - B * C = 0) ↔
      ((l * A) * (l * D) - (l * B) * (l * C) = 0) := by
  rw [asano_discriminant_scale]
  constructor
  · intro h
    simp [h]
  · intro h
    have hl2 : l^2 ≠ 0 := by
      simpa [pow_two] using mul_ne_zero hl hl
    exact (mul_eq_zero.mp h).resolve_left hl2

/--
Root uniqueness is invariant under nonzero coefficient scaling.

If `D ≠ 0`, scaling by `l ≠ 0` preserves uniqueness of roots of the affine
contracted equation.
-/
theorem contracted_affine_root_unique_scaled
    {A D z w l : ℂ}
    (hl : l ≠ 0)
    (hD : D ≠ 0)
    (hz : (l * A) + (l * D) * z = 0)
    (hw : (l * A) + (l * D) * w = 0) :
    z = w := by
  have hDl : l * D ≠ 0 := mul_ne_zero hl hD
  exact contracted_affine_root_unique hDl hz hw

/--
Scaled endpoint-root criterion.

If a scaled affine equation has root `z` and the scaled endpoint `-(u*v)` is
also a root, then `z ∈ -(K₁K₂)`; this is the scaled form of
`contracted_root_mem_negProductSet_of_endpoint_root`.
-/
theorem contracted_root_mem_negProductSet_of_endpoint_root_scaled
    (K₁ K₂ : Set ℂ)
    {A D u v z l : ℂ}
    (hl : l ≠ 0)
    (hD : D ≠ 0)
    (hu : u ∈ K₁)
    (hv : v ∈ K₂)
    (hz : (l * A) + (l * D) * z = 0)
    (hendpoint : (l * A) + (l * D) * (-(u * v)) = 0) :
    z ∈ negProductSet K₁ K₂ := by
  have hz_eq : z = -(u * v) := by
    exact contracted_affine_root_unique_scaled hl hD hz hendpoint
  exact contracted_root_mem_negProductSet_of_endpoint K₁ K₂ hu hv hz_eq

/--
Endpoint root criterion.

If `z` is a root of `A + D z`, and the endpoint product `-u*v`
is also a root, then `z ∈ -(K₁K₂)`.
-/
theorem contracted_root_mem_negProductSet_of_endpoint_root
    (K₁ K₂ : Set ℂ)
    {A D u v z : ℂ}
    (hD : D ≠ 0)
    (hu : u ∈ K₁)
    (hv : v ∈ K₂)
    (hz : A + D * z = 0)
    (hendpoint : A + D * (-(u * v)) = 0) :
    z ∈ negProductSet K₁ K₂ := by
  have hz_eq : z = -(u * v) :=
    contracted_affine_root_unique hD hz hendpoint
  exact contracted_root_mem_negProductSet_of_endpoint K₁ K₂ hu hv hz_eq

/--
Degenerate Asano branch algebra.

Assume

  D ≠ 0,
  AD - BC = 0,
  -C/D ∈ K₁,
  -B/D ∈ K₂,
  A + D z = 0.

Then the contracted root lies in the forbidden product set:

  z ∈ -(K₁K₂).

This is the algebraic part of Ruelle A.1, Case `AD - BC = 0`.
-/
theorem degenerate_contracted_root_mem_negProductSet
    (K₁ K₂ : Set ℂ)
    {A B C D z : ℂ}
    (hD : D ≠ 0)
    (hdeg : A * D - B * C = 0)
    (hK₁ : -(C / D) ∈ K₁)
    (hK₂ : -(B / D) ∈ K₂)
    (hz : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ := by
  refine ⟨-(C / D), hK₁, -(B / D), hK₂, ?_⟩

  have hAD : A * D = B * C := by
    exact sub_eq_zero.mp hdeg

  have hz_eq : z = -A / D := by
    have hDz : D * z = -A := by
      have hz' : D * z + A = 0 := by simpa [add_comm] using hz
      exact eq_neg_of_add_eq_zero_left hz'
    calc
      z = (D * z) / D := by
        field_simp [hD]
      _ = (-A) / D := by rw [hDz]
      _ = -A / D := rfl

  rw [hz_eq]

  -- Now prove `-A/D = -((-C/D) * (-B/D))` from `A*D = B*C`.
  field_simp [hD]
  rw [hAD]
  ring

/--
Degenerate branch packaged as a root exclusion theorem.

If `D ≠ 0`, `AD - BC = 0`, and the two degenerate endpoints lie in `K₁`
and `K₂`, then no contracted root can lie outside `-(K₁K₂)`.
-/
theorem degenerate_contracted_zero_forces_forbidden
    (K₁ K₂ : Set ℂ)
    {A B C D z : ℂ}
    (hD : D ≠ 0)
    (hdeg : A * D - B * C = 0)
    (hK₁ : -(C / D) ∈ K₁)
    (hK₂ : -(B / D) ∈ K₂)
    (hz : A + D * z = 0) :
    z ∈ negProductSet K₁ K₂ :=
  degenerate_contracted_root_mem_negProductSet
    K₁ K₂ hD hdeg hK₁ hK₂ hz

end InfoGeometry.Canonical.AsanoRuelleEndpoint
