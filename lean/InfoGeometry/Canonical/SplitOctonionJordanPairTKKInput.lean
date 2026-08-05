import InfoGeometry.Canonical.ThreeColorChiralJordanPair
import InfoGeometry.OperatorAlgebra.TKKClosure

/-!
# Two-sheet Jordan-triple input for the native TKK socket

The repository already owns the upper/lower rectangular Jordan pair on the
two chiral three-colour lanes.  The TKK socket, however, consumes one carrier
with a Jordan triple product.  This file supplies exactly that adapter on the
direct sum of the two lanes.

It does not construct a TKK Lie carrier or identify one with a classical Lie
algebra.  It only converts the verified Jordan-pair identities into the
`JordanTripleSystem` input expected by the native TKK owner.
-/

namespace InfoGeometry.Canonical.SplitOctonionJordanPairTKKInput

open TKKJordanPairData
open InfoGeometry.OperatorAlgebra

abbrev Sheet := ChiralVector ℝ
abbrev TwoSheet := Sheet × Sheet

def triple : TwoSheet → TwoSheet → TwoSheet → TwoSheet
  | x, y, z =>
      (chiralTriplePlus x.1 y.2 z.1,
        chiralTripleMinus x.2 y.1 z.2)

theorem triple_outer (x y z : TwoSheet) :
    triple x y z = triple z y x := by
  apply Prod.ext
  · exact chiralTriplePlus_outer x.1 y.2 z.1
  · exact chiralTripleMinus_outer x.2 y.1 z.2

theorem triple_add_left (u v x y : TwoSheet) :
    triple (u + v) x y = triple u x y + triple v x y := by
  apply Prod.ext
  · funext i
    simp [triple, chiralTriplePlus, chiralPairing, Fin.sum_univ_three]
    ring
  · funext i
    simp [triple, chiralTripleMinus, chiralPairing, Fin.sum_univ_three]
    ring

theorem triple_smul_left (c : ℝ) (x y z : TwoSheet) :
    triple (c • x) y z = c • triple x y z := by
  apply Prod.ext
  · funext i
    simp [triple, chiralTriplePlus, chiralPairing, Fin.sum_univ_three]
    ring
  · funext i
    simp [triple, chiralTripleMinus, chiralPairing, Fin.sum_univ_three]
    ring

theorem triple_identity (u v x y z : TwoSheet) :
    triple u v (triple x y z) - triple x y (triple u v z) =
      triple (triple u v x) y z - triple x (triple v u y) z := by
  apply Prod.ext
  · exact chiralTriplePlus_fundamental
      u.1 x.1 z.1 v.2 y.2
  · exact chiralTripleMinus_fundamental
      u.2 x.2 z.2 v.1 y.1

def jordanTripleSystem : JordanTripleSystem TwoSheet where
  triple := triple
  outer_symm := triple_outer
  triple_add_left := triple_add_left
  triple_smul_left := triple_smul_left
  triple_identity := triple_identity

@[simp] theorem jordanTripleSystem_apply
    (x y z : TwoSheet) :
    jordanTripleSystem.triple x y z = triple x y z :=
  rfl

theorem jordanTripleSystem_is_native_tkk_input :
    (∀ x y z : TwoSheet, triple x y z = triple z y x) ∧
      (∀ u v x y : TwoSheet,
        triple (u + v) x y = triple u x y + triple v x y) ∧
      (∀ (c : ℝ) (x y z : TwoSheet),
        triple (c • x) y z = c • triple x y z) ∧
      (∀ u v x y z : TwoSheet,
        triple u v (triple x y z) - triple x y (triple u v z) =
          triple (triple u v x) y z - triple x (triple v u y) z) := by
  exact ⟨triple_outer, triple_add_left, triple_smul_left, triple_identity⟩

theorem plus_sheet_readout (x y z : Sheet) :
    (jordanTripleSystem.triple (x, 0) (0, y) (z, 0)).1 =
      chiralTriplePlus x y z := by
  rfl

theorem minus_sheet_readout (x y z : Sheet) :
    (jordanTripleSystem.triple (0, x) (y, 0) (0, z)).2 =
      chiralTripleMinus x y z := by
  rfl

end InfoGeometry.Canonical.SplitOctonionJordanPairTKKInput
