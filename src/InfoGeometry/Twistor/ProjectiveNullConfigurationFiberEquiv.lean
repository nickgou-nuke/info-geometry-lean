import InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ordered fiber of the finite configuration quotient

For a fixed ordered distinct-null configuration, the fiber of the canonical
ordered-to-unordered quotient is concretely the permutation orbit.  Freeness
of reindexing upgrades that orbit description to an equivalence with
`Equiv.Perm (Fin n)`.  This is an algebraic fiber readout; no braid-group or
monodromy identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The permutation orbit of an ordered configuration, viewed as the fiber of
the unordered quotient over its image. -/
noncomputable def orderedFiberEquivPerm
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n) :
    Equiv.Perm (Fin n) ≃
      {q : Ordered Q n //
        Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} := by
  let f : Equiv.Perm (Fin n) →
      {q : Ordered Q n //
        Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} := fun σ =>
    ⟨permute Q n σ p, by
      apply Quotient.sound
      refine ⟨σ.symm, ?_⟩
      apply Subtype.ext
      funext j
      rw [permute_comp]
      simp⟩
  apply Equiv.ofBijective f
  constructor
  · intro σ τ h
    exact permute_eq_of_eq Q n σ τ p (congrArg Subtype.val h)
  · intro q
    obtain ⟨σ, hσ⟩ := Quotient.exact q.property
    refine ⟨σ.symm, ?_⟩
    dsimp [f]
    apply Subtype.ext
    apply Subtype.ext
    funext j
    have hpoint := congrFun (congrArg Subtype.val hσ) (σ.symm j)
    simpa [permute] using hpoint

@[simp] theorem orderedFiberEquivPerm_apply
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (σ : Equiv.Perm (Fin n)) :
    (orderedFiberEquivPerm Q n p σ).1 = permute Q n σ p :=
  rfl

end InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv
