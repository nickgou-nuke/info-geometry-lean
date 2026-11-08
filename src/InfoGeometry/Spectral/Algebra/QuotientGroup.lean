import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quotient groups

The old reference builds quotient groups from a custom set quotient.  This
port delegates the carrier and its universal property to Mathlib's native
`QuotientGroup` construction.
-/

namespace InfoGeometry.Spectral.Algebra.QuotientGroup

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

abbrev Carrier (N : Subgroup G) [N.Normal] := G ⧸ N

def quotientMap (N : Subgroup G) [N.Normal] : G →* Carrier N :=
  QuotientGroup.mk' N

@[simp] theorem quotientMap_apply (N : Subgroup G) [N.Normal] (x : G) :
    quotientMap N x = (x : Carrier N) := rfl

theorem quotientMap_surjective (N : Subgroup G) [N.Normal] :
    Function.Surjective (quotientMap N) := by
  exact QuotientGroup.mk'_surjective N

def descend (N : Subgroup G) [N.Normal] (f : G →* H)
    (hN : N ≤ f.ker) : Carrier N →* H :=
  QuotientGroup.lift N f hN

@[simp] theorem descend_quotientMap (N : Subgroup G) [N.Normal]
    (f : G →* H) (hN : N ≤ f.ker) (x : G) :
    descend N f hN (quotientMap N x) = f x := by
  change (QuotientGroup.lift N f hN) (x : G ⧸ N) = f x
  exact QuotientGroup.lift_mk' N hN x

theorem descend_unique (N : Subgroup G) [N.Normal]
    (f : G →* H) (hN : N ≤ f.ker) (g : Carrier N →* H)
    (hg : ∀ x : G, g (quotientMap N x) = f x) :
    g = descend N f hN := by
  ext y
  obtain ⟨x, hx⟩ := quotientMap_surjective N y
  change g y = descend N f hN y
  calc
    g y = g (quotientMap N x) := congrArg g hx.symm
    _ = f x := hg x
    _ = descend N f hN (quotientMap N x) :=
      (descend_quotientMap N f hN x).symm
    _ = descend N f hN y := congrArg (descend N f hN) hx

theorem quotient_eq_iff (N : Subgroup G) [N.Normal] (x y : G) :
    quotientMap N x = quotientMap N y ↔ ∃ z ∈ N, x * z = y := by
  simpa [quotientMap] using
    (QuotientGroup.mk'_eq_mk' (N := N) (x := x) (y := y))

/-- Noether's first isomorphism theorem in the native quotient carrier. -/
noncomputable def kernelQuotientEquivRange (f : G →* H) :
    Carrier f.ker ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f

@[simp] theorem kernelQuotientEquivRange_quotientMap (f : G →* H) (x : G) :
    kernelQuotientEquivRange f (quotientMap f.ker x) = f.rangeRestrict x := by
  rfl

end InfoGeometry.Spectral.Algebra.QuotientGroup
