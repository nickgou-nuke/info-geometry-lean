import InfoGeometry.Physics.CStarCuntzTensorQuotient

/-!
# Automorphisms of a supplied C⋆ Cuntz completion

This owner works at the exact boundary exposed by
`CStarCuntzCompletion`: a universal C⋆ realization is an input.  It does not
construct `O₆` or claim that every finite Cuntz family has a completion.

Once forward and inverse star homomorphisms are supplied and agree on the
universal generators, the universal property proves the two inverse laws.
This is the genuine automorphism theorem available in the current algebraic /
inductive-colimit architecture.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCompletionAutomorphism

open InfoGeometry.Physics.CStarCuntzTensorQuotient

universe uι uA

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure Data (U : CStarCuntzCompletion.{uι, uA, uA} ι) where
  forward : U.carrier →⋆ₐ[ℂ] U.carrier
  inverse : U.carrier →⋆ₐ[ℂ] U.carrier
  forwardFamily : CStarCuntzFamily U.carrier ι
  inverseFamily : CStarCuntzFamily U.carrier ι
  forward_generator : ∀ i : ι, forward (U.family.S i) = forwardFamily.S i
  inverse_forward_generator :
    ∀ i : ι, inverse (forwardFamily.S i) = U.family.S i
  inverse_generator : ∀ i : ι, inverse (U.family.S i) = inverseFamily.S i
  forward_inverse_generator :
    ∀ i : ι, forward (inverseFamily.S i) = U.family.S i

namespace Data

variable {U : CStarCuntzCompletion.{uι, uA, uA} ι} (D : Data U)

private theorem forward_comp_generator (i : ι) :
    (D.inverse.comp D.forward) (U.family.S i) = U.family.S i := by
  change D.inverse (D.forward (U.family.S i)) = U.family.S i
  rw [D.forward_generator i, D.inverse_forward_generator i]

private theorem inverse_comp_generator (i : ι) :
    (D.forward.comp D.inverse) (U.family.S i) = U.family.S i := by
  change D.forward (D.inverse (U.family.S i)) = U.family.S i
  rw [D.inverse_generator i, D.forward_inverse_generator i]

theorem inverse_comp_forward :
    D.inverse.comp D.forward = StarAlgHom.id ℂ U.carrier := by
  obtain ⟨φ, hφ, hφuniq⟩ := U.universalStarHomProperty U.carrier U.family
  have hcomp : D.inverse.comp D.forward = φ := by
    apply hφuniq
    intro i
    exact D.forward_comp_generator i
  have hid : StarAlgHom.id ℂ U.carrier = φ := by
    apply hφuniq
    intro i
    simp
  exact hcomp.trans hid.symm

theorem forward_comp_inverse :
    D.forward.comp D.inverse = StarAlgHom.id ℂ U.carrier := by
  obtain ⟨φ, hφ, hφuniq⟩ := U.universalStarHomProperty U.carrier U.family
  have hcomp : D.forward.comp D.inverse = φ := by
    apply hφuniq
    intro i
    exact D.inverse_comp_generator i
  have hid : StarAlgHom.id ℂ U.carrier = φ := by
    apply hφuniq
    intro i
    simp
  exact hcomp.trans hid.symm

end Data

end InfoGeometry.Canonical.CuntzCompletionAutomorphism
