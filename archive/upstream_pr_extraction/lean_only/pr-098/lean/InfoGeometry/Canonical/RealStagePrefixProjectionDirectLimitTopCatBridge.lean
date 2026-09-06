import InfoGeometry.Canonical.RealStagePrefixProjectionReadout
import InfoGeometry.Canonical.DyadicDimensionGroupTopCat

/-!
# Direct-limit TopCat bridge for explicit prefix readouts

The finite prefix parameter space already has a canonical dyadic readout.
This owner exposes the same data as a morphism into the existing dyadic
direct-limit carrier and proves its factorization through the canonical
direct-limit/readout isomorphism.  It does not identify the direct limit with
`K₀`, `KO₀`, or a completed UHF algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open DyadicDimensionGroupTopCat

def prefixRankDyadicRational (p : PrefixRankParameter) : DyadicRational :=
  ⟨(p.2.1 : ℚ) / (2 : ℚ) ^ p.1, p.2.1, p.1, rfl⟩

@[simp] theorem prefixRankDyadicRational_value
    (p : PrefixRankParameter) :
    (prefixRankDyadicRational p : ℚ) =
      (prefixRankDyadicPoint p : ℚ) := rfl

noncomputable def prefixRankDyadicRationalTopCatHom :
    TopCat.of PrefixRankParameter ⟶ TopCat.of DyadicRational :=
  TopCat.ofHom
    { toFun := prefixRankDyadicRational
      continuous_toFun := continuous_of_discreteTopology }

noncomputable def prefixRankDirectLimitTopCatHom :
    TopCat.of PrefixRankParameter ⟶
      DyadicDimensionGroupTopCat.dyadicDirectLimitTopCat :=
  TopCat.ofHom
    { toFun := fun p =>
        dyadicDirectLimitEquiv.symm (prefixRankDyadicRational p)
      continuous_toFun := continuous_of_discreteTopology }

@[simp] theorem prefixRankDirectLimitTopCatHom_apply
    (p : PrefixRankParameter) :
    prefixRankDirectLimitTopCatHom p =
      dyadicDirectLimitEquiv.symm (prefixRankDyadicRational p) := rfl

@[simp] theorem prefixRankDyadicRationalTopCatHom_apply
    (p : PrefixRankParameter) :
    prefixRankDyadicRationalTopCatHom p =
      prefixRankDyadicRational p := rfl

theorem prefixRank_directLimit_readout_factorization :
    prefixRankDirectLimitTopCatHom ≫
        dyadicDirectLimitReadoutTopCatHom =
      prefixRankDyadicRationalTopCatHom := by
  apply TopCat.hom_ext
  ext p
  rw [TopCat.comp_app]
  change dyadicDirectLimitEquiv
      (dyadicDirectLimitEquiv.symm (prefixRankDyadicRational p)) =
    prefixRankDyadicRational p
  exact dyadicDirectLimitEquiv.apply_symm_apply _

end InfoGeometry.Canonical
