import InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Physics.Algebra.NPotentOperatorSpectralHull

/-!
# Left/right chiral representations in the operator-Zorn shell

A pair of group representations acts on the two diagonal sheets.  The upper
and lower off-diagonal operators are intertwiners in the two opposite
directions.  Their Zorn block is invariant under the induced block-diagonal
action.

The same owner records two distinct polynomial sectors:

* diagonal cyclotomic clocks, whose powers are roots of the identity;
* strict upper/lower Peirce channels, whose square is zero in the associative
  shell.

No assertion is made that an arbitrary representation pair is the Lorentz
spin representation; `SL(2,C)` becomes a realization only after supplying the
corresponding left and right homomorphisms.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation

open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

variable {G B : Type*}
variable [Group G]
variable [Ring B] [StarRing B]

/-- Two polarized unit representations on a common operator ring. -/
structure ChiralRepresentationPair (G B : Type*)
    [Group G] [Ring B] where
  left : G ->* Units B
  right : G ->* Units B

namespace ChiralRepresentationPair

variable (R : ChiralRepresentationPair G B)

/-- Block-diagonal action of the left/right representation pair. -/
def groupBlock (g : G) : ZornBlock B :=
  ⟨(R.left g : B), (R.right g : B), 0, 0⟩

/-- Explicit inverse block. -/
def groupBlockInv (g : G) : ZornBlock B :=
  ⟨((R.left g)⁻¹ : Units B), ((R.right g)⁻¹ : Units B), 0, 0⟩

@[simp] theorem groupBlock_mul_groupBlockInv (g : G) :
    R.groupBlock g * R.groupBlockInv g = 1 := by
  apply zornBlock_ext <;>
    simp [groupBlock, groupBlockInv]

@[simp] theorem groupBlockInv_mul_groupBlock (g : G) :
    R.groupBlockInv g * R.groupBlock g = 1 := by
  apply zornBlock_ext <;>
    simp [groupBlock, groupBlockInv]

/-- Conjugation action on a two-sheet operator block. -/
def conjugate (g : G) (Z : ZornBlock B) : ZornBlock B :=
  R.groupBlock g * Z * R.groupBlockInv g

/-- A pair of opposite chiral intertwiners. -/
structure ChiralIntertwiner where
  plus : B
  minus : B
  plus_intertwines : forall g : G,
    (R.left g : B) * plus = plus * (R.right g : B)
  minus_intertwines : forall g : G,
    (R.right g : B) * minus = minus * (R.left g : B)

/-- Pure off-diagonal gauge/Weyl block. -/
def pureChiralBlock (Q : R.ChiralIntertwiner) : ZornBlock B :=
  ⟨0, 0, Q.plus, Q.minus⟩

/-- Coordinate form of the left/right conjugation action on an off-diagonal
block. -/
theorem conjugate_pureChiralBlock_coordinates
    (g : G) (Q : R.ChiralIntertwiner) :
    R.conjugate g (R.pureChiralBlock Q) =
      (⟨0, 0,
        (R.left g : B) * Q.plus * ((R.right g)⁻¹ : Units B),
        (R.right g : B) * Q.minus * ((R.left g)⁻¹ : Units B)⟩ :
        ZornBlock B) := by
  apply zornBlock_ext <;>
    simp [conjugate, groupBlock, groupBlockInv, pureChiralBlock]

/-- A left/right intertwiner block is invariant under the paired group action. -/
theorem conjugate_pureChiralBlock
    (g : G) (Q : R.ChiralIntertwiner) :
    R.conjugate g (R.pureChiralBlock Q) = R.pureChiralBlock Q := by
  rw [R.conjugate_pureChiralBlock_coordinates]
  apply zornBlock_ext
  · rfl
  · rfl
  · calc
      (R.left g : B) * Q.plus * ((R.right g)⁻¹ : Units B) =
          (Q.plus * (R.right g : B)) * ((R.right g)⁻¹ : Units B) := by
            rw [Q.plus_intertwines]
      _ = Q.plus := by rw [mul_assoc, Units.mul_inv, mul_one]
  · calc
      (R.right g : B) * Q.minus * ((R.left g)⁻¹ : Units B) =
          (Q.minus * (R.left g : B)) * ((R.left g)⁻¹ : Units B) := by
            rw [Q.minus_intertwines]
      _ = Q.minus := by rw [mul_assoc, Units.mul_inv, mul_one]

end ChiralRepresentationPair

/-- Cartan clock `diag(zeta,zeta^{-1})`. -/
def cartanClock (zeta : Units B) : ZornBlock B :=
  ⟨(zeta : B), (zeta⁻¹ : Units B), 0, 0⟩

/-- Exact power display for the Cartan clock. -/
theorem cartanClock_pow (zeta : Units B) (n : Nat) :
    cartanClock zeta ^ n =
      (⟨(zeta ^ n : Units B), ((zeta⁻¹) ^ n : Units B), 0, 0⟩ :
        ZornBlock B) := by
  induction n with
  | zero =>
      apply zornBlock_ext <;> simp [cartanClock]
  | succ n ih =>
      rw [pow_succ, ih]
      apply zornBlock_ext <;>
        simp [cartanClock, pow_succ]

/-- A root of unity in the coefficient units produces a root-of-identity
Cartan operator. -/
theorem cartanClock_pow_eq_one
    (zeta : Units B) (n : Nat) (hzeta : zeta ^ n = 1) :
    cartanClock zeta ^ n = 1 := by
  rw [cartanClock_pow, hzeta]
  have hinv : (zeta⁻¹) ^ n = (1 : Units B) := by
    simpa only [inv_pow, hzeta, inv_one]
  rw [hinv]
  apply zornBlock_ext <;> simp

/-- Strict upper Peirce channel. -/
def upperChannel (q : B) : ZornBlock B :=
  ⟨0, 0, q, 0⟩

/-- Strict lower Peirce channel. -/
def lowerChannel (q : B) : ZornBlock B :=
  ⟨0, 0, 0, q⟩

/-- Every strict upper associative channel is a square root of zero. -/
@[simp] theorem upperChannel_sq_zero (q : B) :
    upperChannel q * upperChannel q = 0 := by
  apply zornBlock_ext <;> simp [upperChannel]

/-- Every strict lower associative channel is a square root of zero. -/
@[simp] theorem lowerChannel_sq_zero (q : B) :
    lowerChannel q * lowerChannel q = 0 := by
  apply zornBlock_ext <;> simp [lowerChannel]

/-- Cartan-clock conjugation of an upper channel.  In a noncommutative ring the
weight is the two-sided expression `zeta q zeta`; it collapses to a scalar
square only in a central realization. -/
theorem cartanClock_conjugates_upper
    (zeta : Units B) (q : B) :
    cartanClock zeta * upperChannel q * cartanClock zeta⁻¹ =
      upperChannel ((zeta : B) * q * (zeta : B)) := by
  apply zornBlock_ext <;>
    simp [cartanClock, upperChannel]

/-- Dual lower-channel conjugation law. -/
theorem cartanClock_conjugates_lower
    (zeta : Units B) (q : B) :
    cartanClock zeta * lowerChannel q * cartanClock zeta⁻¹ =
      lowerChannel (((zeta⁻¹ : Units B) : B) * q *
        ((zeta⁻¹ : Units B) : B)) := by
  apply zornBlock_ext <;>
    simp [cartanClock, lowerChannel]

/-- Re-export the concrete two-sheet/three-colour cyclotomic packet already
proved in the repository. -/
theorem existing_two_sheet_three_colour_packet
    (omega : C) (homega : omega ^ 3 = 1) :
    InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixClock omega ^ 3 = 1 /\
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixShift ^ 3 = 1 /\
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixSheetExchange ^ 2 = 1 := by
  exact ⟨
    InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixClock_cubed omega homega,
    InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixShift_cubed,
    InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixSheetExchange_involutive⟩

end InfoGeometry.OperatorAlgebra.ChiralWeylOperatorZornRepresentation
