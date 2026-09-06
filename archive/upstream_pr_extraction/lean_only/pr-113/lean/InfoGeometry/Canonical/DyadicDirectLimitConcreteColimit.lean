import InfoGeometry.Canonical.DyadicDimensionGroupTopCat

/-!
# Concrete carrier interface for the dyadic stage colimit

The categorical `TopCat` colimit is kept separate from this explicit quotient
carrier.  This owner exposes the representative and equality lemmas needed
to compare the two constructions without treating categorical points as
quotient terms by definitional reduction.
-/

namespace InfoGeometry.Canonical.DyadicDirectLimitConcreteColimit

open InfoGeometry.Canonical

theorem exists_dyadicStage_rep (x : DyadicDirectLimit) :
    ∃ n : ℕ, ∃ z : ℤ, dyadicStage n z = x := by
  induction x using Quotient.inductionOn with
  | _ rep =>
      rcases rep with ⟨z, n⟩
      exact ⟨n, z, rfl⟩

theorem dyadicStage_eq_iff_cross (n m : ℕ) (z w : ℤ) :
    dyadicStage n z = dyadicStage m w ↔
      (2 : ℤ) ^ m * z = (2 : ℤ) ^ n * w := by
  change Quotient.mk' (⟨z, n⟩ : DyadicRepresentative) =
      Quotient.mk' (⟨w, m⟩ : DyadicRepresentative) ↔ _
  rw [Quotient.eq']
  exact dyadicRepresentativeRel_iff_cross
    (⟨z, n⟩ : DyadicRepresentative)
    (⟨w, m⟩ : DyadicRepresentative)

theorem dyadicStage_eq_iff_readout (n m : ℕ) (z w : ℤ) :
    dyadicStage n z = dyadicStage m w ↔
      dyadicStageMap n z = dyadicStageMap m w := by
  rw [dyadicStage_eq_iff_cross]
  constructor
  · intro h
    apply Subtype.ext
    exact (dyadicRepresentativeRel_iff_cross
      (⟨z, n⟩ : DyadicRepresentative)
      (⟨w, m⟩ : DyadicRepresentative)).mpr h
  · intro h
    apply (dyadicRepresentativeRel_iff_cross
      (⟨z, n⟩ : DyadicRepresentative)
      (⟨w, m⟩ : DyadicRepresentative)).mp
    exact congrArg Subtype.val h

end InfoGeometry.Canonical.DyadicDirectLimitConcreteColimit
