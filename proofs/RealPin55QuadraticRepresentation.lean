import proofs.RealPin55OrthogonalAction

/-! # The full real Pin representation in the native quadratic group -/

noncomputable section
namespace RealPin55QuadraticRepresentation

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction

/-- The native orthogonal group of the split quadratic carrier. -/
def OQ55 : Subgroup (V55 ≃ₗ[ℝ] V55) where
  carrier := {f | ∀ v, Q55 (f v) = Q55 v}
  one_mem' := by intro v; rfl
  mul_mem' := by
    intro f g hf hg v
    change Q55 (f (g v)) = Q55 v
    exact (hf (g v)).trans (hg v)
  inv_mem' := by
    intro f hf v
    have h := hf (f.symm v)
    simpa using h.symm

theorem mem_OQ55_iff (f : V55 ≃ₗ[ℝ] V55) :
    f ∈ OQ55 ↔ ∀ v, Q55 (f v) = Q55 v := Iff.rfl

/-- The signature-correct twisted Clifford action lands in the genuine
orthogonal group of `Q55`. -/
def fullPinToOQ55 : FullPin55 →* OQ55 where
  toFun g := ⟨fullPinVectorRepresentation g, fullPin55_preserves_Q g⟩
  map_one' := by
    apply Subtype.ext
    exact fullPinVectorRepresentation.map_one
  map_mul' g h := by
    apply Subtype.ext
    exact fullPinVectorRepresentation.map_mul g h

@[simp] theorem fullPinToOQ55_apply (g : FullPin55) (v : V55) :
    ((fullPinToOQ55 g : OQ55) : V55 ≃ₗ[ℝ] V55) v = twistedVector g v := rfl

/-- The representation of every normalized vector generator is its explicit
split-signature reflection. -/
theorem fullPinToOQ55_generator {u : Cl55ˣ} {a : V55}
    (hu : u ∈ normalizedVectorUnits) (hua : (u : Cl55) = ι55 a)
    (ha : Q55 a = 1 ∨ Q55 a = -1) (v : V55) :
    ((fullPinToOQ55
        (⟨u, Subgroup.subset_closure hu⟩ : FullPin55) : OQ55) :
          V55 ≃ₗ[ℝ] V55) v =
      reflectedVector a v (Q55 a) :=
  generator_twisted_reflection hu hua ha v

end RealPin55QuadraticRepresentation
end noncomputable section
