import InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical permutation labels of a celestial configuration fiber

For a fixed ordered celestial configuration, the fiber of the finite
reindexing quotient is canonically the permutation orbit.  This is the
celestial specialization of the generic projective-null fiber equivalence;
it is purely algebraic and makes no claim about braid groups or monodromy.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialConfigurationFiberEquiv

open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding

noncomputable def celestialOrderedFiberEquivPerm
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    Equiv.Perm (Fin n) ≃
      {q : CelestialOrderedConfiguration n //
        Quotient.mk' q = (Quotient.mk' p : CelestialUnorderedConfiguration n)} := by
  let f : Equiv.Perm (Fin n) →
      {q : CelestialOrderedConfiguration n //
        Quotient.mk' q = (Quotient.mk' p : CelestialUnorderedConfiguration n)} :=
    fun σ =>
      ⟨celestialPermute n σ p, by
        apply Quotient.sound
        refine (celestialReindexSetoid_iff n
          (celestialPermute n σ p) p).2 ⟨σ.symm, ?_⟩
        apply Subtype.ext
        funext i
        simp [celestialPermute]⟩
  apply Equiv.ofBijective f
  constructor
  · intro σ τ h
    apply Equiv.ext
    intro i
    by_contra hne
    have hp : p.1 (σ i) = p.1 (τ i) := by
      exact congrArg (fun q => q.1.1 i) h
    exact (p.2 (σ i) (τ i) hne) hp
  · intro q
    obtain ⟨σ, hσ⟩ := Quotient.exact q.property
    refine ⟨σ.symm, ?_⟩
    dsimp [f]
    apply Subtype.ext
    apply celestialOrderedConfigurationMap_injective n
    apply Subtype.ext
    funext j
    have hpoint := congrFun (congrArg Subtype.val hσ) (σ.symm j)
    simpa [celestialPermute] using hpoint

@[simp] theorem celestialOrderedFiberEquivPerm_apply
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (σ : Equiv.Perm (Fin n)) :
    (celestialOrderedFiberEquivPerm n p σ).1 =
      celestialPermute n σ p :=
  rfl

end InfoGeometry.Twistor.Cl55CelestialConfigurationFiberEquiv
