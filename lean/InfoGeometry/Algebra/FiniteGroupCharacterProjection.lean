/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finite-group projection onto a character sector

Twist a native representation by the inverse of a genuine unit-valued
character, then use Mathlib's `Representation.averageMap`. The group need
not be abelian and the module need not be finite dimensional. Invertibility
of the group order is required only for the normalized projector.

The projected-span statements distinguish a spanning family from a family
whose projection happens to span. No inner product or orthogonality is
assumed. See `docs/OPBASIS_SYMMETRY_QUOTIENT_CONTRACT.md` for provenance.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteGroupCharacterProjection

variable {k G V W : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The inverse-character twist is a native representation. -/
def twist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (↑((χ g)⁻¹) : k) • ρ g
  map_one' := by ext v; simp
  map_mul' g h := by
    ext v
    simp [Module.End.mul_apply, smul_smul, mul_comm]

@[simp] theorem twist_apply (ρ : Representation k G V) (χ : G →* kˣ)
    (g : G) (v : V) : twist ρ χ g v = (↑((χ g)⁻¹) : k) • ρ g v := rfl

/-- The scalar-character sector, represented as a native invariant submodule. -/
def sector (ρ : Representation k G V) (χ : G →* kˣ) : Submodule k V :=
  (twist ρ χ).invariants

theorem mem_sector_iff (ρ : Representation k G V) (χ : G →* kˣ) (v : V) :
    v ∈ sector ρ χ ↔ ∀ g, ρ g v = (χ g : k) • v := by
  change (∀ g, (↑((χ g)⁻¹) : k) • ρ g v = v) ↔ _
  constructor
  · intro hv g
    simpa only [smul_smul, Units.mul_inv, one_smul] using
      congrArg (fun w : V => (χ g : k) • w) (hv g)
  · intro hv g
    rw [hv g, smul_smul, Units.inv_mul, one_smul]

section Average

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- Normalized projection, with all averaging supplied by Mathlib. -/
def projector (ρ : Representation k G V) (χ : G →* kˣ) : V →ₗ[k] V :=
  (twist ρ χ).averageMap

theorem projector_apply (ρ : Representation k G V) (χ : G →* kˣ) (v : V) :
    projector ρ χ v =
      ⅟(Fintype.card G : k) • ∑ g : G, (↑((χ g)⁻¹) : k) • ρ g v := by
  simp [projector, Representation.averageMap, GroupAlgebra.average, map_sum,
    MonoidAlgebra.of_apply]

theorem projector_mem (ρ : Representation k G V) (χ : G →* kˣ) (v : V) :
    projector ρ χ v ∈ sector ρ χ :=
  Representation.averageMap_invariant (twist ρ χ) v

theorem projector_id (ρ : Representation k G V) (χ : G →* kˣ)
    (v : V) (hv : v ∈ sector ρ χ) : projector ρ χ v = v :=
  Representation.averageMap_id (twist ρ χ) v hv

theorem projector_isProj (ρ : Representation k G V) (χ : G →* kˣ) :
    LinearMap.IsProj (sector ρ χ) (projector ρ χ) :=
  Representation.isProj_averageMap (twist ρ χ)

theorem projector_idempotent (ρ : Representation k G V) (χ : G →* kˣ) :
    projector ρ χ * projector ρ χ = projector ρ χ :=
  (projector_isProj ρ χ).isIdempotentElem.eq

theorem range_projector (ρ : Representation k G V) (χ : G →* kˣ) :
    LinearMap.range (projector ρ χ) = sector ρ χ :=
  (projector_isProj ρ χ).range

/-- An equivariant linear map commutes with projection for the same character. -/
theorem projector_natural {ρ : Representation k G V} {σ : Representation k G W}
    (f : Representation.IntertwiningMap ρ σ) (χ : G →* kˣ) (v : V) :
    f (projector ρ χ v) = projector σ χ (f v) := by
  simp only [projector_apply, map_smul, map_sum, f.isIntertwining]

/-- A stable relation or candidate submodule is preserved by the projector. -/
theorem projector_mem_of_stable (ρ : Representation k G V) (χ : G →* kˣ)
    (U : Submodule k V) (hU : ∀ g, U ≤ U.comap (ρ g))
    (v : V) (hv : v ∈ U) : projector ρ χ v ∈ U := by
  rw [projector_apply]
  apply U.smul_mem
  exact U.sum_mem fun g _ => U.smul_mem _ (hU g hv)

/-- Exact completeness statement before any spanning or stability assumption. -/
theorem span_projector_image (ρ : Representation k G V) (χ : G →* kˣ)
    (C : Set V) :
    Submodule.span k (projector ρ χ '' C) = (Submodule.span k C).map (projector ρ χ) :=
  Submodule.span_image (projector ρ χ)

theorem span_projector_image_of_span_top (ρ : Representation k G V) (χ : G →* kˣ)
    (C : Set V) (hC : Submodule.span k C = ⊤) :
    Submodule.span k (projector ρ χ '' C) = sector ρ χ := by
  rw [span_projector_image, hC, Submodule.map_top, range_projector]

/-- For a projection-stable submodule the image is its intersection with the sector. -/
theorem map_projector_eq_inf (ρ : Representation k G V) (χ : G →* kˣ)
    (U : Submodule k V) (hU : ∀ v ∈ U, projector ρ χ v ∈ U) :
    U.map (projector ρ χ) = U ⊓ sector ρ χ := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hU w hw, projector_mem ρ χ w⟩
  · intro hv
    exact ⟨v, hv.1, projector_id ρ χ v hv.2⟩

theorem span_projector_image_of_stable (ρ : Representation k G V) (χ : G →* kˣ)
    (C : Set V) (hC : ∀ g, Submodule.span k C ≤ (Submodule.span k C).comap (ρ g)) :
    Submodule.span k (projector ρ χ '' C) = Submodule.span k C ⊓ sector ρ χ := by
  rw [span_projector_image]
  exact map_projector_eq_inf ρ χ _ (projector_mem_of_stable ρ χ _ hC)

end Average

end InfoGeometry.Algebra.FiniteGroupCharacterProjection
