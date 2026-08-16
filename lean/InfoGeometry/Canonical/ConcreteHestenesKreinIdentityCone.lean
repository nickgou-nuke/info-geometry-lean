import InfoGeometry.Canonical.FilteredHestenesKreinColimit

/-!
# A concrete finite Hestenes--Krein filtered cone

This is the smallest genuine inhabitant of `HestenesKreinCone`: the base is
the canonical real Hilbert space `EuclideanSpace ℝ (Fin 4)`, the doubled
carrier is eight-dimensional, and every transition is the identity.

It is a validation object for the filtered Hestenes/Krein API.  It does not
identify the carrier with split-octonion multiplication and does not assert an
analytic completion or a spectral theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteHestenesKreinIdentityCone

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Krein

abbrev IdentityBase := EuclideanSpace ℝ (Fin 4)

noncomputable def identityCone : HestenesKreinCone where
  Base := fun _ => IdentityBase
  baseNormedAddCommGroup := fun _ => inferInstance
  baseInnerProductSpace := fun _ => inferInstance
  baseCompleteSpace := fun _ => inferInstance
  LimitBase := IdentityBase
  limitNormedAddCommGroup := inferInstance
  limitInnerProductSpace := inferInstance
  limitCompleteSpace := inferInstance
  bond := fun _ => ContinuousLinearMap.id ℝ (DoubledSpace IdentityBase)
  bond_hestenes := fun _ => id_isHestenesHolomorphicDifferential
  ι := fun _ => ContinuousLinearMap.id ℝ (DoubledSpace IdentityBase)
  ι_hestenes := fun _ => id_isHestenesHolomorphicDifferential
  ι_bond := by
    intro n
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

@[simp] theorem identityCone_bond_apply
    (n : ℕ) (x : DoubledSpace IdentityBase) :
    identityCone.bond n x = x := by
  rfl

@[simp] theorem identityCone_ι_apply
    (n : ℕ) (x : DoubledSpace IdentityBase) :
    identityCone.ι n x = x := by
  rfl

theorem identityCone_bond_phaseLinear (n : ℕ) :
    (clockPhaseStructure IdentityBase).IsPhaseLinearMap
      (identityCone.bond n) (clockPhaseStructure IdentityBase) := by
  exact identityCone.bond_phaseLinear

theorem identityCone_ι_phaseLinear (n : ℕ) :
    (clockPhaseStructure IdentityBase).IsPhaseLinearMap
      (identityCone.ι n) (clockPhaseStructure IdentityBase) := by
  exact identityCone.ι_phaseLinear

theorem identityCone_stage_maps_are_cauchyAnalytic
    (n : ℕ) (x : DoubledSpace IdentityBase) :
    (identityCone.ιCauchyAnalyticAt n x).deriv = identityCone.ι n := by
  exact identityCone.ιCauchyAnalyticAt_deriv n x

theorem identityCone_bond_maps_are_cauchyAnalytic
    (n : ℕ) (x : DoubledSpace IdentityBase) :
    (identityCone.bondCauchyAnalyticAt n x).deriv = identityCone.bond n := by
  exact identityCone.bondCauchyAnalyticAt_deriv n x

end InfoGeometry.Canonical.ConcreteHestenesKreinIdentityCone
