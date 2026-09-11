import InfoGeometry.Canonical.BipolarTwoSheetCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Finite deck-monodromy model: traversal parity acts by the sheet involution. -/
namespace InfoGeometry.Canonical.BipolarDeckMonodromy

open InfoGeometry.Canonical.BipolarTwoSheetCore
open InfoGeometry.Topology.Weyl

def traversalParity : Bool → ChiralSheet → ChiralSheet
  | false, sh => sh
  | true, sh => sh.swap

@[simp] theorem traversalParity_even (sh : ChiralSheet) :
    traversalParity false sh = sh := rfl

@[simp] theorem traversalParity_odd (sh : ChiralSheet) :
    traversalParity true sh = sh.swap := rfl

@[simp] theorem traversalParity_twice (sh : ChiralSheet) :
    traversalParity true (traversalParity true sh) = sh := by
  cases sh <;> rfl

theorem traversalParity_two_circuits (sh : ChiralSheet) :
    traversalParity true (traversalParity true sh) = traversalParity false sh := by
  simp

theorem traversalParity_preserves_base (p : Bool) (x : TwoSheet ℂ) :
    baseProjection (traversalParity p x.1, x.2) = baseProjection x := rfl

/-! The parity action is the native deck action on the lifted carrier. -/

theorem traversalParity_lift_even (x : TwoSheet ℂ) :
    (traversalParity false x.1, x.2) = x := by
  rfl

theorem traversalParity_lift_odd (x : TwoSheet ℂ) :
    (traversalParity true x.1, x.2) = deck x := by
  rfl

theorem traversalParity_lift_two_circuits (x : TwoSheet ℂ) :
    deck (deck x) = x := by
  exact deck_involutive x

end InfoGeometry.Canonical.BipolarDeckMonodromy
