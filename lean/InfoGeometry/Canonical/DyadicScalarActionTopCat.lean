import InfoGeometry.Canonical.DyadicScalarActionLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TopCat packaging of the dyadic scalar action

The dyadic direct-limit carrier already has a transported topology and a
continuous `DyadicRational`-action.  This owner exposes that action as a
`TopCat` morphism and records only its existing algebraic laws.
It makes no claim about `K₀`, `KO₀`, or a completed UHF algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.DyadicScalarActionTopCat

open CategoryTheory
open InfoGeometry.Canonical

noncomputable def dyadicScalarActionTopCatHom :
    TopCat.of (DyadicRational × DyadicDirectLimit) ⟶
      TopCat.of DyadicDirectLimit :=
  TopCat.ofHom
    (ContinuousMap.mk
      (fun p : DyadicRational × DyadicDirectLimit => p.1 • p.2)
      continuous_dyadicDirectLimit_dyadic_smul)

@[simp] theorem dyadicScalarActionTopCatHom_apply
    (p : DyadicRational × DyadicDirectLimit) :
    dyadicScalarActionTopCatHom p = p.1 • p.2 := rfl

theorem dyadicScalarActionTopCatHom_one
    (x : DyadicDirectLimit) :
    dyadicScalarActionTopCatHom (dyadicOne, x) = x := by
  change dyadicOne • x = x
  exact dyadicDirectLimit_dyadic_smul_one x

theorem dyadicScalarActionTopCatHom_assoc
    (a b : DyadicRational) (x : DyadicDirectLimit) :
    dyadicScalarActionTopCatHom
        (a, dyadicScalarActionTopCatHom (b, x)) =
      dyadicScalarMul a b • x := by
  change a • (b • x) = dyadicScalarMul a b • x
  exact dyadicDirectLimit_dyadic_smul_assoc a b x

end InfoGeometry.Canonical.DyadicScalarActionTopCat
