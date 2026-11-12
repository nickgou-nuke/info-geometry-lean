/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteGroupCharacterProjection
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Character sectors commute with stable relation quotients

The relation space is explicit and stable under the native representation.
The quotient map intertwines the character projectors. Averaging a lift
proves surjectivity on character sectors, giving the actual equivalence
`E / (R.comap E.subtype) ≃ₗ[k] Ebar` by the first isomorphism theorem.

The module can be infinite dimensional and the coefficient ring need not
be a field. Invertibility of the finite group order is the substantive
assumption used to average a lift. This is a module quotient; no operator
multiplication is asserted to descend.
-/

noncomputable section

namespace InfoGeometry.Algebra.CharacterRelationQuotient

open FiniteGroupCharacterProjection

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (χ : G →* kˣ)
  (R : Submodule k V) (hR : ∀ g, R ≤ R.comap (ρ g))

/-- The native quotient map is an intertwiner for the native quotient action. -/
def quotientIntertwining : Representation.IntertwiningMap ρ (ρ.quotient R hR) where
  toLinearMap := R.mkQ
  isIntertwining' g := by ext v; rfl

/-- A vector in the original character sector maps into the quotient sector. -/
theorem mkQ_mem_sector (v : V) (hv : v ∈ sector ρ χ) :
    R.mkQ v ∈ sector (ρ.quotient R hR) χ := by
  apply (mem_sector_iff _ _ _).2
  intro g
  change R.mkQ (ρ g v) = (χ g : k) • R.mkQ v
  rw [(mem_sector_iff ρ χ v).1 hv g, map_smul]

/-- Restriction of the quotient map to the two native character submodules. -/
def sectorQuotientMap : sector ρ χ →ₗ[k] sector (ρ.quotient R hR) χ :=
  R.mkQ.restrict (mkQ_mem_sector ρ χ R hR)

@[simp] theorem sectorQuotientMap_apply (v : sector ρ χ) :
    (sectorQuotientMap ρ χ R hR v : V ⧸ R) = R.mkQ (v : V) := rfl

theorem ker_sectorQuotientMap :
    LinearMap.ker (sectorQuotientMap ρ χ R hR) = R.comap (sector ρ χ).subtype := by
  simp only [sectorQuotientMap, LinearMap.ker_restrict, Submodule.ker_mkQ]

section Average

variable [Fintype G] [Invertible (Fintype.card G : k)]

theorem mkQ_projector (v : V) :
    R.mkQ (projector ρ χ v) = projector (ρ.quotient R hR) χ (R.mkQ v) :=
  projector_natural (quotientIntertwining ρ R hR) χ v

/-- Every quotient-sector vector has a sector lift, obtained by averaging any lift. -/
theorem sectorQuotientMap_surjective : Function.Surjective (sectorQuotientMap ρ χ R hR) := by
  intro w
  obtain ⟨v, hv⟩ := R.mkQ_surjective (w : V ⧸ R)
  refine ⟨⟨projector ρ χ v, projector_mem ρ χ v⟩, ?_⟩
  apply Subtype.ext
  change R.mkQ (projector ρ χ v) = (w : V ⧸ R)
  rw [mkQ_projector ρ χ R hR, hv, projector_id _ _ _ w.property]

/-- Taking a scalar-character sector commutes with a stable relation quotient. -/
def sectorQuotientEquiv :
    (sector ρ χ ⧸ R.comap (sector ρ χ).subtype) ≃ₗ[k] sector (ρ.quotient R hR) χ :=
  (Submodule.quotEquivOfEq _ _ (ker_sectorQuotientMap ρ χ R hR).symm).trans
    ((sectorQuotientMap ρ χ R hR).quotKerEquivOfSurjective
      (sectorQuotientMap_surjective ρ χ R hR))

@[simp] theorem sectorQuotientEquiv_mk (v : sector ρ χ) :
    (sectorQuotientEquiv ρ χ R hR (Submodule.Quotient.mk v) : V ⧸ R) =
      R.mkQ (v : V) := rfl

end Average

end InfoGeometry.Algebra.CharacterRelationQuotient
