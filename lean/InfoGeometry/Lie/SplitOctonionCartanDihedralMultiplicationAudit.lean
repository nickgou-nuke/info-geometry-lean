import InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms

/-!
# Multiplication audit for the raw hexagonal reindexing

The order-twelve dihedral action on the six circular labels is a genuine
weight/channel symmetry, but its unsigned step-one rotation and reflection do
not preserve the native Zorn multiplication table.  The counterexamples below
are concrete basis computations.  They prevent promotion of the raw label
action to a split-octonion automorphism action.

The separate rational owner `SplitOctonionColorS3Automorphisms` supplies the
orientation-corrected multiplicative color cycle and reflection.  This file
does not identify that signed action with the raw hexagon permutation.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCartanDihedralMultiplicationAudit

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.D6SixModeAction
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
open InfoGeometry.Lie.SplitOctonionCartanDihedralHexagon
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Canonical.HexagonalSixRootTiling

private theorem cyclotomicChannel_one :
    cyclotomicChannel (1 : D6Index) =
      cartesianZornLinearEquiv (rootMinus 2) := by
  change circularChannel ((ZMod.finEquiv 6).symm (1 : ZMod 6)) =
    cartesianZornLinearEquiv (rootMinus 2)
  change circularChannel (1 : HexIndex) =
    cartesianZornLinearEquiv (rootMinus 2)
  have h : (1 : HexIndex) = negativeVertex 2 := by decide
  rw [h, circularChannel_negative]

private theorem cyclotomicChannel_three :
    cyclotomicChannel (3 : D6Index) =
      cartesianZornLinearEquiv (rootMinus 0) := by
  change circularChannel ((ZMod.finEquiv 6).symm (3 : ZMod 6)) =
    cartesianZornLinearEquiv (rootMinus 0)
  change circularChannel (3 : HexIndex) =
    cartesianZornLinearEquiv (rootMinus 0)
  have h : (3 : HexIndex) = negativeVertex 0 := by decide
  rw [h, circularChannel_negative]

private theorem cyclotomicChannel_two :
    cyclotomicChannel (2 : D6Index) =
      cartesianZornLinearEquiv (rootPlus 1) := by
  change circularChannel ((ZMod.finEquiv 6).symm (2 : ZMod 6)) =
    cartesianZornLinearEquiv (rootPlus 1)
  change circularChannel (2 : HexIndex) =
    cartesianZornLinearEquiv (rootPlus 1)
  have h : (2 : HexIndex) = positiveVertex 1 := by decide
  rw [h, circularChannel_positive]

private theorem cyclotomicChannel_zero :
    cyclotomicChannel (0 : D6Index) =
      cartesianZornLinearEquiv (rootPlus 0) := by
  change circularChannel ((ZMod.finEquiv 6).symm (0 : ZMod 6)) =
    cartesianZornLinearEquiv (rootPlus 0)
  change circularChannel (0 : HexIndex) =
    cartesianZornLinearEquiv (rootPlus 0)
  have h : (0 : HexIndex) = positiveVertex 0 := by decide
  rw [h, circularChannel_positive]

private theorem cyclotomicChannel_four :
    cyclotomicChannel (4 : D6Index) =
      cartesianZornLinearEquiv (rootPlus 2) := by
  change circularChannel ((ZMod.finEquiv 6).symm (4 : ZMod 6)) =
    cartesianZornLinearEquiv (rootPlus 2)
  change circularChannel (4 : HexIndex) =
    cartesianZornLinearEquiv (rootPlus 2)
  have h : (4 : HexIndex) = positiveVertex 2 := by decide
  rw [h, circularChannel_positive]

private theorem cyclotomicChannel_five :
    cyclotomicChannel (5 : D6Index) =
      cartesianZornLinearEquiv (rootMinus 1) := by
  change circularChannel ((ZMod.finEquiv 6).symm (5 : ZMod 6)) =
    cartesianZornLinearEquiv (rootMinus 1)
  change circularChannel (5 : HexIndex) =
    cartesianZornLinearEquiv (rootMinus 1)
  have h : (5 : HexIndex) = negativeVertex 1 := by decide
  rw [h, circularChannel_negative]

/-- One hexagon step does not preserve the product of channels `0` and `2`. -/
theorem rotation_one_not_multiplicative_on_channels :
    cyclotomicChannel (rotation 1 0) * cyclotomicChannel (rotation 1 2) ≠
      cyclotomicChannel (rotation 1 1) := by
  have hr0 : InfoGeometry.Canonical.D6SixModeAction.rotation 1 0 = 1 := by
    decide
  have hr2 : InfoGeometry.Canonical.D6SixModeAction.rotation 1 2 = 3 := by
    decide
  have hr1 : InfoGeometry.Canonical.D6SixModeAction.rotation 1 1 = 2 := by
    decide
  rw [hr0, hr2, hr1, cyclotomicChannel_one, cyclotomicChannel_three,
    cyclotomicChannel_two]
  intro h
  have hx := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix ℝ => z.x 1) h
  norm_num [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.quaternionAxis,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.ellAxis,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.axis,
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at hx
  simp at hx
  have hx' : (-1 : ℝ) = 1 := by simpa using hx
  norm_num at hx'

theorem no_multiplicative_rotation_one_channel_lift :
    ¬ ∃ F : InfoGeometry.Canonical.ZornMatrix ℝ →
      InfoGeometry.Canonical.ZornMatrix ℝ,
        (∀ n : D6Index,
          F (cyclotomicChannel n) = cyclotomicChannel (rotation 1 n)) ∧
        (∀ X Y : InfoGeometry.Canonical.ZornMatrix ℝ,
          F (InfoGeometry.Canonical.ZornMatrix.mul X Y) =
            InfoGeometry.Canonical.ZornMatrix.mul (F X) (F Y)) := by
  intro h
  rcases h with ⟨F, hchannel, hmul⟩
  have hbase :
      InfoGeometry.Canonical.ZornMatrix.mul
        (cyclotomicChannel 0) (cyclotomicChannel 2) =
        cyclotomicChannel 1 := by
    rw [cyclotomicChannel_zero, cyclotomicChannel_two,
      cyclotomicChannel_one]
    change cartesianZornLinearEquiv (rootPlus 0) *
      cartesianZornLinearEquiv (rootPlus 1) =
      cartesianZornLinearEquiv (rootMinus 2)
    rw [cartesianZorn_rootPlus_mul_rootPlus_leviCivita]
    simp [Algebra.Zorn.ParityTwistedLeviCivita.leviCivita3, Fin.sum_univ_three,
      rootMinus, quaternionAxis, ellAxis,
      axis, Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  apply rotation_one_not_multiplicative_on_channels
  calc
    cyclotomicChannel (rotation 1 0) *
          cyclotomicChannel (rotation 1 2) =
        F (cyclotomicChannel 0) * F (cyclotomicChannel 2) := by
          rw [hchannel 0, hchannel 2]
    _ = F (InfoGeometry.Canonical.ZornMatrix.mul
      (cyclotomicChannel 0) (cyclotomicChannel 2)) :=
      (hmul (cyclotomicChannel 0) (cyclotomicChannel 2)).symm
    _ = F (cyclotomicChannel 1) := by rw [hbase]
    _ = cyclotomicChannel (rotation 1 1) := hchannel 1

/-- The raw unsigned hexagon reflection also fails multiplication covariance. -/
theorem reflection_not_multiplicative_on_channels :
    cyclotomicChannel (reflection 0) * cyclotomicChannel (reflection 2) ≠
      cyclotomicChannel (reflection 1) := by
  have hs0 : InfoGeometry.Canonical.D6SixModeAction.reflection 0 = 0 := by
    decide
  have hs2 : InfoGeometry.Canonical.D6SixModeAction.reflection 2 = 4 := by
    decide
  have hs1 : InfoGeometry.Canonical.D6SixModeAction.reflection 1 = 5 := by
    decide
  rw [hs0, hs2, hs1, cyclotomicChannel_zero, cyclotomicChannel_four,
    cyclotomicChannel_five]
  intro h
  have hy := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix ℝ => z.y 1) h
  norm_num [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootPlus,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.rootMinus,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.quaternionAxis,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.ellAxis,
    InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.axis,
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at hy
  simp at hy
  have hy' : (-1 : ℝ) = 1 := by simpa using hy
  norm_num at hy'

end InfoGeometry.Lie.SplitOctonionCartanDihedralMultiplicationAudit
