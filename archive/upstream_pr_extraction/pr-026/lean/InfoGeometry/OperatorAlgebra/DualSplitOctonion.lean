import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence

/-!
# Theorem-safe dual split-octonion backbone

This module is the Lean twin of `tools/sympy/dual_split_octonion.py`.

It formalizes only the safe algebraic dual-number extension of the repository's
concrete integer Zorn split-octonion layer:

`DO_s = O_s ⊕ ε O_s`, with `ε² = 0`, and
`(a + εu)(b + εv) = ab + ε(av + ub)`.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `DualSplitOct` has two eight-coordinate split-octonion slots, so the
  bookkeeping carrier has `16` coordinates.
* `baseLift` and `epsLift` obey the four dual-number product rules.
* `dualEpsilon² = 0`.
* Projection to the base/primal slot is multiplicative.
* The tangent/epsilon ideal is square-zero.
* The existing finite `G₂(2)` ledger is imported only to separate counts:
  the selected outer `C₂` representative has seven fixed points but exactly
  `3` internal `H(2)` lines, not `7`.

#### BUCKET 3: OPEN / NON-ASSERTED CLASSIFICATION CLAIMS

This file deliberately does not assert any of:

* `Aut(DO_s) = G_{2(2)} ⋉ R⁷`;
* `SO(4,4) ⋉ R⁸` norm/affine isometry classification;
* `SU(3) ⋉ R⁶` gauge/stabilizer classification;
* that the seven finite `G₂(2)` fixed points are a Fano plane;
* that those seven finite fixed points are an `R⁷` infinitesimal translation
  module;
* any `Pin(5,5)`, Klein-bottle, parafermion, or quantum `R`-matrix closure.

The automorphism section below is only an interface/predicate surface for future
certificates.  It is not a classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.DualSplitOctonion

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation

/-- Dual split octonion coordinate cell `primal + ε tangent`. -/
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
def coordinateCount : Nat := 16

/-- Coordinatewise addition in the dual extension. -/
def addD (X Y : DualSplitOct) : DualSplitOct :=
  ⟨addZ X.primal Y.primal, addZ X.tangent Y.tangent⟩

/-- Coordinatewise subtraction in the dual extension. -/
def subD (X Y : DualSplitOct) : DualSplitOct :=
  ⟨subZ X.primal Y.primal, subZ X.tangent Y.tangent⟩

/-- Dual-number extension of the split-octonion product. -/
def mulD (X Y : DualSplitOct) : DualSplitOct :=
  ⟨mulZ X.primal Y.primal,
    addZ (mulZ X.primal Y.tangent) (mulZ X.tangent Y.primal)⟩

instance : Add DualSplitOct := ⟨addD⟩
instance : Sub DualSplitOct := ⟨subD⟩
instance : Mul DualSplitOct := ⟨mulD⟩

/-- Coordinate associator in the dual extension. -/
def associatorD (X Y Z : DualSplitOct) : DualSplitOct :=
  subD (mulD (mulD X Y) Z) (mulD X (mulD Y Z))

theorem coordinate_count : coordinateCount = 16 := by
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

theorem primal_projection_mul (X Y : DualSplitOct) :
    (mulD X Y).primal = mulZ X.primal Y.primal := by
  rfl

theorem tangent_ideal_square_zero (X Y : SplitOct) :
    mulD (epsLift X) (epsLift Y) = zeroD := by
  exact epsLift_mul_epsLift_zero X Y

/-- The known nonzero split-octonion associator lifts to the base dual slot. -/
theorem lifted_associator_base :
    associatorD (baseLift up0) (baseLift up1) (baseLift down1) = baseLift up0 := by
  rfl

theorem lifted_associator_base_ne_zero :
    associatorD (baseLift up0) (baseLift up1) (baseLift down1) ≠ zeroD := by
  intro h
  have hprimal : (associatorD (baseLift up0) (baseLift up1) (baseLift down1)).primal =
      zeroD.primal := congrArg DualSplitOct.primal h
  exact associator_up0_up1_down1_ne_zero hprimal

/-- A raw endomap candidate for future dual split-octonion automorphism checks.

This is carrier data only.  The product/ideal conditions are predicates below,
not fields smuggled as closure. -/
structure AutCandidate where
  carrierMap : DualSplitOct → DualSplitOct

namespace AutCandidate

/-- Candidate preserves the dual product.  Predicate only; not assumed globally. -/
def PreservesMul (F : AutCandidate) : Prop :=
  ∀ X Y : DualSplitOct, F.carrierMap (mulD X Y) = mulD (F.carrierMap X) (F.carrierMap Y)

/-- Candidate maps the square-zero epsilon ideal into the epsilon ideal. -/
def PreservesEpsilonIdeal (F : AutCandidate) : Prop :=
  ∀ X : SplitOct, ∃ Y : SplitOct, F.carrierMap (epsLift X) = epsLift Y

/-- Candidate fixes the distinguished dual-number generator. -/
def FixesEpsilon (F : AutCandidate) : Prop :=
  F.carrierMap dualEpsilon = dualEpsilon

/-- Predicate package for a future certificate.  This is not a classification. -/
def IsDualSplitOctonionAutCandidate (F : AutCandidate) : Prop :=
  PreservesMul F ∧ PreservesEpsilonIdeal F

/-- Identity candidate. -/
def idCandidate : AutCandidate :=
  ⟨id⟩

theorem id_preserves_mul : PreservesMul idCandidate := by
  intro X Y
  rfl

theorem id_preserves_epsilon_ideal : PreservesEpsilonIdeal idCandidate := by
  intro X
  exact ⟨X, rfl⟩

theorem id_fixes_epsilon : FixesEpsilon idCandidate := by
  rfl

theorem id_is_candidate : IsDualSplitOctonionAutCandidate idCandidate := by
  exact ⟨id_preserves_mul, id_preserves_epsilon_ideal⟩

end AutCandidate

/-- Imported finite `G₂(2)` boundary: seven fixed points, but not seven internal lines. -/
theorem finite_g2_outerC2_fixed_count_not_fano_line_count :
    InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence.outerC2FixedPointCount = 7 ∧
      InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence.fixedInternalLineCount = 3 ∧
      InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence.fixedInternalLineCount ≠
        InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence.fanoPlaneLineCount := by
  exact ⟨rfl, rfl,
    InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence.fixedInternalLineCount_ne_fanoPlaneLineCount⟩

end InfoGeometry.OperatorAlgebra.DualSplitOctonion
