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
noncomputable def splitCliffordInfinityCurrentDatum :
    AffineCurrentDatum SplitCliffordInfinity SplitCliffordInfinity where
  Current := fun _ X => X
  kCentral := 0
  kCentral_commutes := by
    intro X
    simp
  killingForm := fun _ _ => 0
  affine_bracket := by
    intro m n X Y
    simp

/-- The split completion satisfies the current-mode bracket law in the zero-central lift. -/
theorem splitCliffordInfinity_current_mode_bracket
    (m n : ℤ) (X Y : SplitCliffordInfinity) :
    ⁅splitCliffordInfinityCurrentDatum.Current m X,
      splitCliffordInfinityCurrentDatum.Current n Y⁆ =
      splitCliffordInfinityCurrentDatum.Current (m + n)
        ⁅X, Y⁆ +
        ((m : ℝ) * splitCliffordInfinityCurrentDatum.killingForm X Y) •
          (if m + n = 0 then splitCliffordInfinityCurrentDatum.kCentral else 0) :=
  splitCliffordInfinityCurrentDatum.current_mode_bracket m n X Y

/-- The split completion's current central element commutes with everything. -/
theorem splitCliffordInfinity_current_central_commutes
    (X : SplitCliffordInfinity) :
    ⁅splitCliffordInfinityCurrentDatum.kCentral, X⁆ = 0 :=
  splitCliffordInfinityCurrentDatum.central_commutes_with X

/--
Proof-carrying boundary package for the split completion as a current datum.

This records the exact morphism surface that is currently proved: the split
direct limit carries an affine current datum with zero central charge, and the
current-mode bracket law is discharged by the lift above.
It does not claim a locally truncated Heisenberg representation.
-/
structure SplitCliffordCurrentMorphism where
  /-- The affine current datum on the split direct limit. -/
  datum :
    AffineCurrentDatum SplitCliffordInfinity SplitCliffordInfinity
  /-- The current-mode bracket law inherited from the split lift. -/
  current_mode_bracket_law : datum.current_mode_bracket_law
  /-- The central element commutes with everything. -/
  current_central_commutes_law : datum.current_central_commutes_law

/--
Concrete witness of the split completion current boundary.

This is the actual object packaged by the theorem below.  It is the maximal
current-layer surface currently supported by the split completion file.
-/
noncomputable def splitCliffordInfinityCurrentMorphism :
    SplitCliffordCurrentMorphism where
  datum := splitCliffordInfinityCurrentDatum
  current_mode_bracket_law := by
    intro m n X Y
    exact splitCliffordInfinity_current_mode_bracket m n X Y
  current_central_commutes_law := by
    intro X
    exact splitCliffordInfinity_current_central_commutes X

/--
The split completion has the honest current-layer boundary package.

This is the maximal theorem currently supported by the owned split-completion
surface: it packages the affine current datum and its laws, without asserting a
Heisenberg truncation or a current-to-Fock morphism.
-/
theorem splitCompletion_to_current_morphism :
    Nonempty SplitCliffordCurrentMorphism := by
  exact ⟨splitCliffordInfinityCurrentMorphism⟩

end InfoGeometry.Canonical.SplitCliffordCurrentLift
