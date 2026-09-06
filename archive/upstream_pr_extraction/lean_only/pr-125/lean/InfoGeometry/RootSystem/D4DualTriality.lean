import InfoGeometry.RootSystem.D4DiscriminantCardinality
import InfoGeometry.RootSystem.D4DualExponentTwo
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The Klein-four identification of the `D₄` discriminant carrier

The quotient has four elements and exponent two.  Mathlib's native
`IsAddKleinFour` interface therefore supplies the additive identification with
`ZMod 2 × ZMod 2`.  An explicit permutation of the three nonzero classes is a
separate triality layer and is intentionally not hidden in this equivalence.
-/

namespace InfoGeometry.RootSystem.D4

noncomputable instance : Nontrivial discriminantCarrier :=
  discriminantCarrier_nontrivial

instance : IsAddKleinFour discriminantCarrier where
  card_four := by
    rw [Nat.card_eq_fintype_card]
    exact discriminantCarrier_fintype_card
  exponent_two := by
    apply (AddMonoid.exponent_eq_prime_iff Nat.prime_two).2
    intro x hx
    apply addOrderOf_eq_prime (p := 2)
    · obtain ⟨u, rfl⟩ := discriminantMap_surjective x
      simpa [two_nsmul] using discriminantCarrier_add_self_eq_zero u
    · exact hx

noncomputable def discriminantCarrier_v4Equiv :
    discriminantCarrier ≃+ (ZMod 2 × ZMod 2) :=
  Classical.choice (IsAddKleinFour.nonempty_addEquiv)

theorem discriminantCarrier_is_add_klein_four :
    IsAddKleinFour discriminantCarrier := inferInstance

theorem discriminantCarrier_v4_equiv_exists :
    Nonempty (discriminantCarrier ≃+ (ZMod 2 × ZMod 2)) :=
  ⟨discriminantCarrier_v4Equiv⟩

end InfoGeometry.RootSystem.D4
