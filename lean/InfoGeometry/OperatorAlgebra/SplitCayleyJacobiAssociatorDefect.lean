import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option maxHeartbeats 800000

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-!
# Commutator Jacobi defect for the concrete split Cayley product

The operator commutator theorem in an associative envelope has zero Jacobiator.
For the concrete Zorn product below, the corresponding coordinate identity is
the exact negative six associator formula.  This owner keeps the two statements
separate and does not install a Lie structure on `SplitOct`.
-/

/-- Commutator for the concrete split-octonion multiplication. -/
def commutatorZ (X Y : SplitOct) : SplitOct :=
  subZ (mulZ X Y) (mulZ Y X)

/-- Right-nested cyclic commutator expression. -/
def rightJacobiatorZ (X Y Z : SplitOct) : SplitOct :=
  commutatorZ X (commutatorZ Y Z) +
    commutatorZ Y (commutatorZ Z X) +
    commutatorZ Z (commutatorZ X Y)

/-- Left-nested cyclic commutator expression for the concrete Cayley product. -/
def leftJacobiatorZ (X Y Z : SplitOct) : SplitOct :=
  commutatorZ (commutatorZ X Y) Z +
    commutatorZ (commutatorZ Y Z) X +
    commutatorZ (commutatorZ Z X) Y

/-- The concrete Zorn commutator Jacobiator is `-6` times the associator. -/
theorem rightJacobiatorZ_eq_neg_six_associator (X Y Z : SplitOct) :
    rightJacobiatorZ X Y Z = scaleZ (-6) (associator X Y Z) := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      cases Z with
      | mk e f r0 r1 r2 s0 s1 s2 =>
        ext <;> simp [rightJacobiatorZ, commutatorZ, associator,
          mulZ, subZ, scaleZ] <;> ring_nf

/-- The left-nested Cayley commutator Jacobiator is `+6` times the associator. -/
theorem leftJacobiatorZ_eq_six_associator (X Y Z : SplitOct) :
    leftJacobiatorZ X Y Z = scaleZ 6 (associator X Y Z) := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      cases Z with
      | mk e f r0 r1 r2 s0 s1 s2 =>
        ext <;> simp [leftJacobiatorZ, commutatorZ, associator,
          mulZ, subZ, scaleZ] <;> ring_nf

/-- The concrete split Cayley associator is alternating in its first two
arguments. -/
theorem associator_swap_left (X Y Z : SplitOct) :
    associator Y X Z = negZ (associator X Y Z) := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      cases Z with
      | mk e f r0 r1 r2 s0 s1 s2 =>
        ext <;> simp [associator, mulZ, subZ, negZ] <;> ring_nf

/-- The concrete split Cayley associator is alternating in its last two
arguments. -/
theorem associator_swap_right (X Y Z : SplitOct) :
    associator X Z Y = negZ (associator X Y Z) := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      cases Z with
      | mk e f r0 r1 r2 s0 s1 s2 =>
        ext <;> simp [associator, mulZ, subZ, negZ] <;> ring_nf

/-- The concrete associator is alternating under exchanging its outer
arguments, as obtained from the two adjacent transpositions above. -/
theorem associator_swap_outer (X Y Z : SplitOct) :
    associator Z Y X = negZ (associator X Y Z) := by
  calc
    associator Z Y X = negZ (associator Y Z X) := by
      rw [associator_swap_left Z Y X]
      simp [negZ]
    _ = negZ (negZ (associator Y X Z)) := by
      rw [associator_swap_right Y Z X]
      simp [negZ]
    _ = negZ (negZ (negZ (associator X Y Z))) := by
      rw [associator_swap_left Y X Z]
      simp [negZ]
    _ = negZ (associator X Y Z) := by
      simp [negZ]

/-- The left/right regular commutator is the negative associator defect. -/
theorem leftRightRegular_commutator_eq_neg_associator
    (X Y Z : SplitOct) :
    subZ (mulZ X (mulZ Z Y)) (mulZ (mulZ X Z) Y) =
      negZ (associator X Z Y) := by
  exact leftRegular_mul_defect X Z Y

/-- The three upper basis units exhibit the nonzero Jacobi defect. -/
theorem rightJacobiatorZ_up0_up1_up2 :
    rightJacobiatorZ up0 up1 up2 = scaleZ 6 (subZ ePlus eMinus) := by
  rw [rightJacobiatorZ_eq_neg_six_associator]
  decide

/-- A named basis triple has the corresponding nonzero right Jacobiator. -/
theorem rightJacobiatorZ_up0_up1_down1 :
    rightJacobiatorZ up0 up1 down1 = scaleZ (-6) up0 := by
  rw [rightJacobiatorZ_eq_neg_six_associator,
    associator_up0_up1_down1]

theorem rightJacobiatorZ_up0_up1_down1_ne_zero :
    rightJacobiatorZ up0 up1 down1 ≠ zeroZ := by
  rw [rightJacobiatorZ_up0_up1_down1]
  decide

end InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
