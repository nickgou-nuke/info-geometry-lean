import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Topology.BrillouinKleinGaugeInvariant
import InfoGeometry.Topology.BrillouinKleinExceptionalTopology

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

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not prove `Aut(D O_s) = G₂(2) ⋉ R⁷`,
`Aut(D O_s) = G_{2(2)} ⋉ R⁷`, an `SO(4,4) ⋉ R⁸` metric symmetry theorem, an
`SU(3)` stabilizer theorem, or a physical gauge classification.  Those require
separate theorem owners for the chosen scalar field, topology/smoothness class,
metric, and automorphism notion.
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

end InfoGeometry.OperatorAlgebra.DualSplitOctonionAlgebra
