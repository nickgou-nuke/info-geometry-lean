import InfoGeometry.Algebra.Zorn.G2BruhatResidual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv
import InfoGeometry.Algebra.Zorn.G2BruhatResidualTopEquiv

/-!
# Boundary of residual-exponent realization

`BruhatResidualExponent p` is a combinatorial inversion-coordinate carrier,
whereas `residualSubgroup p` is the concrete intersection used by the native
finite group.  This file makes the bridge an explicit predicate.  In
particular, the corrected parameter `(2,true)` is a certified counterexample
to treating the two carriers as definitionally interchangeable.
-/

namespace InfoGeometry.Algebra.Zorn.G2ResidualExponentRealizationBoundary

open InfoGeometry.Algebra.Zorn.G2BruhatResidual
open InfoGeometry.Algebra.Zorn.G2BruhatResidualSimpleEquiv
open InfoGeometry.Algebra.Zorn.G2BruhatResidualTopEquiv
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.GroupTheory.G2BruhatInversions

def ResidualExponentRealizes (p : WeylG2) : Prop :=
  Nonempty (BruhatResidualExponent p ≃ residualSubgroup p)

theorem residualExponentRealizes_card
    (p : WeylG2) (h : ResidualExponentRealizes p) :
    Nat.card (residualSubgroup p) = 2 ^ dihedralLength p := by
  rcases h with ⟨e⟩
  exact residualSubgroup_card_eq_pow_of_bruhat_equiv p e

theorem not_residualExponentRealizes_corrected_simple :
    ¬ ResidualExponentRealizes (2, true) := by
  exact no_residualExponent_equiv_simple

theorem residualExponentRealizes_top :
    ResidualExponentRealizes (3, false) := by
  exact ⟨bruhatTopResidualSubgroupEquiv⟩

theorem residualExponentRealizes_iff_nonempty_equiv (p : WeylG2) :
    ResidualExponentRealizes p ↔
      Nonempty (BruhatResidualExponent p ≃ residualSubgroup p) := by
  rfl

end InfoGeometry.Algebra.Zorn.G2ResidualExponentRealizationBoundary
