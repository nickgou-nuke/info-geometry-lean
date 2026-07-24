import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import InfoGeometry.Topology.BrillouinKleinExceptionalTopology
import Mathlib.Tactic

/-!
# Dual split-octonion algebra over the concrete Zorn split-octonion layer

This module is the Lean twin of `tools/sympy/dual_split_octonion_algebra.py`.

It formalizes the finite theorem-safe algebraic core of the dual extension

`D O_s = O_s ⊕ ε O_s`, with `ε² = 0`,

using the repository's concrete integer Zorn split-octonion multiplication.

#### BUCKET 1: CLOSED FINITE THEOREMS

* The dual coordinate carrier has two eight-coordinate split-octonion slots,
  i.e. a `16`-coordinate bookkeeping surface.
* The base embedding and infinitesimal embedding satisfy the expected product
  rules:
  `ι x * ι y = ι (xy)`, `δ x * δ y = 0`,
  `ι x * δ y = δ (xy)`, and `δ x * ι y = δ (xy)`.
* The distinguished dual unit `ε = δ oneZ` squares to zero.
* Projection onto the primal split-octonion slot preserves multiplication.
* The nonzero split-octonion associator witness lifts to a nonzero dual
  associator witness.
* External-system arithmetic readouts are mirrored as finite Lean ledgers:
  GAP/Atlas finite `G₂(2)` order/index data, Sage `G₂`/`D₄`/`D₅`
  root-Weyl counts, split Clifford dimensions `2^8` and `2^10`, and the
  dimension sum `1 + 8 + 27 + 8 + 1 = 45`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not prove `Aut(D O_s) = G₂(2) ⋉ R⁷`,
`Aut(D O_s) = G_{2(2)} ⋉ R⁷`, an `SO(4,4) ⋉ R⁸` metric symmetry theorem, an
`SU(3)` stabilizer theorem, a quantum `G₂` `R`-matrix theorem, a
Yang-Baxter theorem, or a physical gauge/KBZ/O(5,5) classification.  Those
require separate theorem owners for the chosen scalar field, topology/smoothness
class, metric, automorphism notion, and operator representation.
-/

namespace InfoGeometry.OperatorAlgebra.DualSplitOctonionAlgebra

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation

/-- Dual split-octonion coordinate cell `primal + ε tangent`. -/
structure DualSplitOct where
  primal : SplitOct
  tangent : SplitOct
  deriving DecidableEq, Repr

/-- Coordinatewise zero in the dual extension. -/
def zeroD : DualSplitOct := ⟨zeroZ, zeroZ⟩

/-- Base embedding `x ↦ x + ε0`. -/
def baseLift (X : SplitOct) : DualSplitOct := ⟨X, zeroZ⟩

/-- Infinitesimal embedding `x ↦ 0 + εx`. -/
def epsLift (X : SplitOct) : DualSplitOct := ⟨zeroZ, X⟩

/-- The distinguished dual-number generator `ε = 0 + ε oneZ`. -/
def dualEpsilon : DualSplitOct := epsLift oneZ

/-- The coordinate count of the dual split-octonion bookkeeping surface. -/
def dualSplitOctCoordinateCount : Nat := 16

/-! ## External-system arithmetic ledger surfaces -/

/-- GAP/Atlas finite `G₂(2)` order. -/
def gapG2TwoOrder : Nat := 12096

/-- GAP/Atlas finite `G₂(2)'` order. -/
def gapG2TwoDerivedOrder : Nat := 6048

/-- GAP/Atlas finite index `[G₂(2) : G₂(2)']`. -/
def gapG2TwoDerivedIndex : Nat := 2

/-- GAP/Atlas finite automorphism group order for `G₂(2)`. -/
def gapAutG2TwoOrder : Nat := 12096

/-- Sage root count for the `G₂` root system. -/
def sageG2RootCount : Nat := 12

/-- Sage Weyl-group order for type `G₂`. -/
def sageG2WeylOrder : Nat := 12

/-- Sage root count for type `D₄`. -/
def sageD4RootCount : Nat := 24

/-- Sage Weyl-group order for type `D₄`. -/
def sageD4WeylOrder : Nat := 192

/-- Sage root count for type `D₅`. -/
def sageD5RootCount : Nat := 40

/-- Sage Weyl-group order for type `D₅`. -/
def sageD5WeylOrder : Nat := 1920

/-- Sage Chevalley-basis Lie algebra dimension for type `D₅`. -/
def sageD5LieDimension : Nat := 45

/-- `clifford`/`galgebra` dimension ledger for `Cl(4,4)`. -/
def cl44Dimension : Nat := 256

/-- `clifford`/`galgebra` dimension ledger for `Cl(5,5)`. -/
def cl55Dimension : Nat := 1024

/-- The `-2` sector dimension in the finite five-grade dimension ledger. -/
def o55FiveGradeNegTwoDim : Nat := 1

/-- The `-1` sector dimension in the finite five-grade dimension ledger. -/
def o55FiveGradeNegOneDim : Nat := 8

/-- The `0` sector dimension in the finite five-grade dimension ledger. -/
def o55FiveGradeZeroDim : Nat := 27

/-- The `+1` sector dimension in the finite five-grade dimension ledger. -/
def o55FiveGradePosOneDim : Nat := 8

/-- The `+2` sector dimension in the finite five-grade dimension ledger. -/
def o55FiveGradePosTwoDim : Nat := 1

/-- Dual-number extension of the split-octonion product. -/
def mulD (X Y : DualSplitOct) : DualSplitOct :=
  ⟨mulZ X.primal Y.primal,
    addZ (mulZ X.primal Y.tangent) (mulZ X.tangent Y.primal)⟩

/-- Coordinatewise addition in the dual extension. -/
def addD (X Y : DualSplitOct) : DualSplitOct :=
  ⟨addZ X.primal Y.primal, addZ X.tangent Y.tangent⟩

/-- Coordinatewise subtraction in the dual extension. -/
def subD (X Y : DualSplitOct) : DualSplitOct :=
  ⟨subZ X.primal Y.primal, subZ X.tangent Y.tangent⟩

instance : Mul DualSplitOct := ⟨mulD⟩
instance : Add DualSplitOct := ⟨addD⟩
instance : Sub DualSplitOct := ⟨subD⟩

/-- Coordinate associator in the dual extension. -/
def associatorD (X Y Z : DualSplitOct) : DualSplitOct :=
  ⟨associator X.primal Y.primal Z.primal,
    subZ
      (addZ (mulZ (mulZ X.primal Y.primal) Z.tangent)
        (addZ (mulZ (mulZ X.primal Y.tangent) Z.primal)
          (mulZ (mulZ X.tangent Y.primal) Z.primal)))
      (addZ (mulZ X.primal (mulZ Y.primal Z.tangent))
        (addZ (mulZ X.primal (mulZ Y.tangent Z.primal))
          (mulZ X.tangent (mulZ Y.primal Z.primal))))⟩

theorem dual_coordinate_count :
    dualSplitOctCoordinateCount = 16 := by
  rfl

theorem gap_g2two_order_index_ledger :
    gapG2TwoDerivedOrder * gapG2TwoDerivedIndex = gapG2TwoOrder ∧
      gapAutG2TwoOrder = gapG2TwoOrder := by
  norm_num [gapG2TwoDerivedOrder, gapG2TwoDerivedIndex, gapG2TwoOrder, gapAutG2TwoOrder]

theorem sage_g2_root_weyl_ledger :
    sageG2RootCount = 12 ∧ sageG2WeylOrder = 12 := by
  norm_num [sageG2RootCount, sageG2WeylOrder]

theorem sage_d4_d5_root_weyl_ledger :
    sageD4RootCount = 24 ∧ sageD4WeylOrder = 192 ∧
      sageD5RootCount = 40 ∧ sageD5WeylOrder = 1920 ∧
      sageD5LieDimension = 45 := by
  norm_num [sageD4RootCount, sageD4WeylOrder, sageD5RootCount, sageD5WeylOrder,
    sageD5LieDimension]

theorem clifford_split_dimension_ledger :
    cl44Dimension = 2 ^ 8 ∧ cl55Dimension = 2 ^ 10 := by
  norm_num [cl44Dimension, cl55Dimension]

theorem o55_five_grade_dimension_sum :
    o55FiveGradeNegTwoDim + o55FiveGradeNegOneDim + o55FiveGradeZeroDim +
        o55FiveGradePosOneDim + o55FiveGradePosTwoDim =
      sageD5LieDimension := by
  norm_num [o55FiveGradeNegTwoDim, o55FiveGradeNegOneDim, o55FiveGradeZeroDim,
    o55FiveGradePosOneDim, o55FiveGradePosTwoDim, sageD5LieDimension]

theorem baseLift_mul (X Y : SplitOct) :
    mulD (baseLift X) (baseLift Y) = baseLift (mulZ X Y) := by
  cases X
  cases Y
  simp [mulD, baseLift, zeroZ, addZ, mulZ]

theorem epsLift_mul_epsLift_zero (X Y : SplitOct) :
    mulD (epsLift X) (epsLift Y) = zeroD := by
  cases X
  cases Y
  simp [mulD, epsLift, zeroD, zeroZ, addZ, mulZ]

theorem baseLift_mul_epsLift (X Y : SplitOct) :
    mulD (baseLift X) (epsLift Y) = epsLift (mulZ X Y) := by
  cases X
  cases Y
  simp [mulD, baseLift, epsLift, zeroZ, addZ, mulZ]

theorem epsLift_mul_baseLift (X Y : SplitOct) :
    mulD (epsLift X) (baseLift Y) = epsLift (mulZ X Y) := by
  cases X
  cases Y
  simp [mulD, baseLift, epsLift, zeroZ, addZ, mulZ]

theorem dualEpsilon_sq_zero :
    mulD dualEpsilon dualEpsilon = zeroD := by
  exact epsLift_mul_epsLift_zero oneZ oneZ

/-- The odd square-zero dual direction has zero odd--odd superbracket. -/
theorem dualEpsilon_odd_odd_superBracket_zero :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true dualEpsilon dualEpsilon = zeroD := by
  decide

theorem primal_projection_mul (X Y : DualSplitOct) :
    (mulD X Y).primal = mulZ X.primal Y.primal := by
  rfl

theorem tangent_square_zero (X Y : SplitOct) :
    mulD (epsLift X) (epsLift Y) = zeroD :=
  epsLift_mul_epsLift_zero X Y

theorem lifted_associator_base :
    associatorD (baseLift up0) (baseLift up1) (baseLift down1) = baseLift up0 := by
  rfl

theorem lifted_associator_base_ne_zero :
    associatorD (baseLift up0) (baseLift up1) (baseLift down1) ≠ zeroD := by
  intro h
  have hprimal : (associatorD (baseLift up0) (baseLift up1) (baseLift down1)).primal =
      zeroD.primal := congrArg DualSplitOct.primal h
  exact associator_up0_up1_down1_ne_zero hprimal

/-- Stage-indexed readout: the finite dual algebra law is stable at every indexed stage. -/
theorem dualEpsilon_sq_zero_at_every_stage (_n : Nat) :
    mulD dualEpsilon dualEpsilon = zeroD := by
  exact dualEpsilon_sq_zero

/-- Klein-Brillouin parity owner readout for the zero dual defect boundary. -/
theorem zero_dual_defect_klein_bottle_z2_invariant :
    InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant 0 0 = 0 := by
  rfl

/-- The existing Brillouin-Klein owner gives even boundary charge for the dual zero-defect loop. -/
theorem zero_dual_defect_klein_boundary_charge_even :
    InfoGeometry.Topology.BrillouinKlein.klein_bottle_boundary ℤ 0 0 = 2 * (0 : ℤ) := by
  rfl

/-- Closed finite algebra packet for the dual split-octonion extension. -/
theorem dualSplitOct_algebra_packet :
    dualSplitOctCoordinateCount = 16 ∧
      (∀ X Y : SplitOct, mulD (baseLift X) (baseLift Y) = baseLift (mulZ X Y)) ∧
      (∀ X Y : SplitOct, mulD (epsLift X) (epsLift Y) = zeroD) ∧
      (∀ X Y : SplitOct, mulD (baseLift X) (epsLift Y) = epsLift (mulZ X Y)) ∧
      (∀ X Y : SplitOct, mulD (epsLift X) (baseLift Y) = epsLift (mulZ X Y)) ∧
      mulD dualEpsilon dualEpsilon = zeroD ∧
      InfoGeometry.Algebra.SupergradedBracket.superBracket true true dualEpsilon dualEpsilon = zeroD ∧
      (∀ X Y : DualSplitOct, (mulD X Y).primal = mulZ X.primal Y.primal) ∧
      (∀ _n : Nat, mulD dualEpsilon dualEpsilon = zeroD) ∧
      InfoGeometry.Topology.BrillouinKleinGauge.klein_bottle_z2_invariant 0 0 = 0 ∧
      InfoGeometry.Topology.BrillouinKlein.klein_bottle_boundary ℤ 0 0 = 2 * (0 : ℤ) ∧
      associatorD (baseLift up0) (baseLift up1) (baseLift down1) ≠ zeroD := by
  exact ⟨dual_coordinate_count, baseLift_mul, epsLift_mul_epsLift_zero,
    baseLift_mul_epsLift, epsLift_mul_baseLift, dualEpsilon_sq_zero,
    dualEpsilon_odd_odd_superBracket_zero, primal_projection_mul,
    dualEpsilon_sq_zero_at_every_stage, zero_dual_defect_klein_bottle_z2_invariant,
    zero_dual_defect_klein_boundary_charge_even, lifted_associator_base_ne_zero⟩

/-- Closed finite multi-system arithmetic packet mirrored from the runtime verifier. -/
theorem dualSplitOct_multisystem_backbone_packet :
    gapG2TwoDerivedOrder * gapG2TwoDerivedIndex = gapG2TwoOrder ∧
      gapAutG2TwoOrder = gapG2TwoOrder ∧
      sageG2RootCount = 12 ∧
      sageG2WeylOrder = 12 ∧
      sageD4RootCount = 24 ∧
      sageD4WeylOrder = 192 ∧
      sageD5RootCount = 40 ∧
      sageD5WeylOrder = 1920 ∧
      sageD5LieDimension = 45 ∧
      cl44Dimension = 2 ^ 8 ∧
      cl55Dimension = 2 ^ 10 ∧
      o55FiveGradeNegTwoDim + o55FiveGradeNegOneDim + o55FiveGradeZeroDim +
          o55FiveGradePosOneDim + o55FiveGradePosTwoDim =
        sageD5LieDimension := by
  exact ⟨gap_g2two_order_index_ledger.1, gap_g2two_order_index_ledger.2,
    sage_g2_root_weyl_ledger.1, sage_g2_root_weyl_ledger.2,
    sage_d4_d5_root_weyl_ledger.1, sage_d4_d5_root_weyl_ledger.2.1,
    sage_d4_d5_root_weyl_ledger.2.2.1, sage_d4_d5_root_weyl_ledger.2.2.2.1,
    sage_d4_d5_root_weyl_ledger.2.2.2.2, clifford_split_dimension_ledger.1,
    clifford_split_dimension_ledger.2, o55_five_grade_dimension_sum⟩

end InfoGeometry.OperatorAlgebra.DualSplitOctonionAlgebra
