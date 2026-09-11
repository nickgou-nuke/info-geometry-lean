import InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

/-!
# Branch self-similarity on the concrete projective-limit carrier

The categorical inverse-limit owner already transports `prependBit` to its
limit object.  This owner transports the same branch map to the concrete
coherent-family carrier and proves the two descriptions are conjugate.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

def projectivePrependBitTopCatHom (b : Bool) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of PrefixProjectiveLimit :=
  cantorProjectiveLimitTopCatIso.inv ≫ prependBitHom b ≫
    cantorProjectiveLimitTopCatIso.hom

theorem projectivePrependBitTopCatHom_apply (b : Bool)
    (p : PrefixProjectiveLimit) :
    projectivePrependBitTopCatHom b p =
      cantorHomeomorphPrefixProjectiveLimit
        (prependBit b (toCantor p)) := by
  rfl

theorem projective_categorical_branch_conjugacy (b : Bool) :
    projectiveToCategoricalLimitTopCatIso.hom ≫ prefixLimitPrependBit b =
      projectivePrependBitTopCatHom b ≫
        projectiveToCategoricalLimitTopCatIso.hom := by
  simp [projectiveToCategoricalLimitTopCatIso,
    projectivePrependBitTopCatHom, prefixLimitPrependBit, Category.assoc]

end InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat
