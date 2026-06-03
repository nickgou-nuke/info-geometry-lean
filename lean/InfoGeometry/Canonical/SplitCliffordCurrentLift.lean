import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

open scoped TensorProduct

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordCurrentLift

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

set_option synthInstance.maxHeartbeats 200000

/-- The split direct limit is a Lie algebra over `ℝ` via its commutator ring structure. -/
noncomputable instance splitCliffordInfinityLieAlgebra :
    LieAlgebra ℝ SplitCliffordInfinity where
  lie_smul r x y := by
    refine DirectLimit.induction₂ (f := fun m n h => splitCliffordMap m n h)
      (C := fun x y => ⁅x, r • y⁆ = r • ⁅x, y⁆) ?_ x y
    intro i a b
    simp [LieRing.of_associative_ring_bracket, DirectLimit.smul_def, DirectLimit.mul_def,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, sub_eq_add_neg]

/-- A zero-central current datum on the split direct limit. -/
-- DEBT_ID: SCCL_ZERO_CENTRAL_DATUM
-- DEBT_KIND: ZERO_DATUM
-- ZERO_DATUM: Zero central charge lift for split direct limit
noncomputable def splitCliffordInfinityCurrentDatum :
    AffineCurrentDatum SplitCliffordInfinity SplitCliffordInfinity where
  Current := fun _ X => X
  kCentral := 0
  killingForm := fun _ _ => 0

/-- The split completion satisfies the current-mode bracket law in the zero-central lift. -/
theorem splitCliffordInfinity_current_mode_bracket
    (m n : ℤ) (X Y : SplitCliffordInfinity) :
    ⁅splitCliffordInfinityCurrentDatum.Current m X,
      splitCliffordInfinityCurrentDatum.Current n Y⁆ =
      splitCliffordInfinityCurrentDatum.Current (m + n)
        ⁅X, Y⁆ +
        ((m : ℝ) * splitCliffordInfinityCurrentDatum.killingForm X Y) •
          (if m + n = 0 then splitCliffordInfinityCurrentDatum.kCentral else 0) :=
by
  simp [splitCliffordInfinityCurrentDatum]

/-- The split completion's current central element commutes with everything. -/
theorem splitCliffordInfinity_current_central_commutes
    (X : SplitCliffordInfinity) :
    ⁅splitCliffordInfinityCurrentDatum.kCentral, X⁆ = 0 :=
by
  simp [splitCliffordInfinityCurrentDatum]

/--
Boundary package for the split completion as a current datum.

The current-mode bracket and central-commutation laws are supplied as separate
theorems below, not as proof fields of this structure.
-/
structure SplitCliffordCurrentMorphism where
  /-- The affine current datum on the split direct limit. -/
  datum :
    AffineCurrentDatum SplitCliffordInfinity SplitCliffordInfinity

/--
Concrete witness of the split completion current boundary.

This is the actual owner object for the split completion current boundary. It is the maximal
current-layer surface currently supported by the split completion file.
-/
noncomputable def splitCliffordInfinityCurrentMorphism :
    SplitCliffordCurrentMorphism where
  datum := splitCliffordInfinityCurrentDatum

/-- The split completion's current-mode bracket law is inherited from the split lift. -/
theorem splitCliffordInfinityCurrentMorphism_current_mode_bracket :
    ∀ (m n : ℤ) (X Y : SplitCliffordInfinity),
      ⁅splitCliffordInfinityCurrentMorphism.datum.Current m X,
          splitCliffordInfinityCurrentMorphism.datum.Current n Y⁆ =
        splitCliffordInfinityCurrentMorphism.datum.Current (m + n) ⁅X, Y⁆ +
          ((m : ℝ) * splitCliffordInfinityCurrentMorphism.datum.killingForm X Y) •
            (if m + n = 0 then splitCliffordInfinityCurrentMorphism.datum.kCentral else 0) := by
  intro m n X Y
  simpa [splitCliffordInfinityCurrentMorphism] using
    splitCliffordInfinity_current_mode_bracket m n X Y

/-- The split completion's current central element commutes with everything. -/
theorem splitCliffordInfinityCurrentMorphism_current_central_commutes :
    ∀ X : SplitCliffordInfinity,
      ⁅splitCliffordInfinityCurrentMorphism.datum.kCentral, X⁆ = 0 := by
  intro X
  simpa [splitCliffordInfinityCurrentMorphism] using
    splitCliffordInfinity_current_central_commutes X

end InfoGeometry.Canonical.SplitCliffordCurrentLift
