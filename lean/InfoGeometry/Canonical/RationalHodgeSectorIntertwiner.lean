import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A linear map preserves a submodule when it maps every member back into it. -/
def LinearMapPreservesSubmodule
    (L : V →ₗ[ℚ] V) (S : Submodule ℚ V) : Prop :=
  ∀ x, x ∈ S → L x ∈ S

theorem conjugateCodifferential_preserves_sector
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (S : Submodule ℚ V)
    (hStar : LinearMapPreservesSubmodule H.star.toLinearMap S)
    (hStarSymm : LinearMapPreservesSubmodule H.star.symm.toLinearMap S)
    (hD : LinearMapPreservesSubmodule d S) :
    LinearMapPreservesSubmodule (conjugateCodifferential H d) S := by
  intro x hx
  exact hStarSymm (d (H.star x)) (hD (H.star x) (hStar x hx))

theorem conjugateCodifferential_preserves_sector_of_equiv
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (S : Submodule ℚ V)
    (hStar : LinearMapPreservesSubmodule H.star.toLinearMap S)
    (hStarSymm : LinearMapPreservesSubmodule H.star.symm.toLinearMap S)
    (hD : LinearMapPreservesSubmodule d S) :
    LinearMapPreservesSubmodule
      (H.star.symm.toLinearMap.comp (d.comp H.star.toLinearMap)) S :=
  conjugateCodifferential_preserves_sector H d S hStar hStarSymm hD

theorem linearMap_comp_preserves_submodule
    (L M : V →ₗ[ℚ] V)
    (S : Submodule ℚ V)
    (hL : LinearMapPreservesSubmodule L S)
    (hM : LinearMapPreservesSubmodule M S) :
    LinearMapPreservesSubmodule (L.comp M) S := by
  intro x hx
  exact hL (M x) (hM x hx)

theorem rationalDiracKahler_preserves_sector
    (d cod : V →ₗ[ℚ] V)
    (S : Submodule ℚ V)
    (hd : LinearMapPreservesSubmodule d S)
    (hcod : LinearMapPreservesSubmodule cod S) :
    LinearMapPreservesSubmodule (rationalDiracKahler d cod) S := by
  intro x hx
  exact S.add_mem (hd x hx) (hcod x hx)

theorem rationalHodgeLaplacian_preserves_sector
    (d cod : V →ₗ[ℚ] V)
    (S : Submodule ℚ V)
    (hd : LinearMapPreservesSubmodule d S)
    (hcod : LinearMapPreservesSubmodule cod S) :
    LinearMapPreservesSubmodule (rationalHodgeLaplacian d cod) S := by
  intro x hx
  exact S.add_mem
    (linearMap_comp_preserves_submodule d cod S hd hcod x hx)
    (linearMap_comp_preserves_submodule cod d S hcod hd x hx)

end InfoGeometry.Canonical
