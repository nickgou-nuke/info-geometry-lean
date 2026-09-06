/- 
InfoGeometry/Algebraic/NarainOrthogonalCore.lean

Orthogonal core for the split/Narain charge lattice.

This file packages exact lattice symmetries of the hyperbolic charge form.
It does not introduce modular generators, Clifford lifts, or Berry phases.
-/

import InfoGeometry.Algebraic.SplitChargeLattice

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Algebraic.Split

/--
A symmetry of the split charge lattice preserving the hyperbolic pairing.

This is the correct orthogonal gate for Narain-charge data.
-/
structure NarainChargeSymmetry (n : ℕ) where
  toLinearEquiv : SplitCharge n ≃ₗ[ℤ] SplitCharge n
  preserves_hyperbolicPair :
    ∀ q r : SplitCharge n,
      SplitCharge.hyperbolicPair (toLinearEquiv q) (toLinearEquiv r) =
        SplitCharge.hyperbolicPair q r

namespace NarainChargeSymmetry

/-- Apply a Narain charge symmetry to a charge. -/
def apply {n : ℕ} (S : NarainChargeSymmetry n) : SplitCharge n → SplitCharge n :=
  S.toLinearEquiv

@[simp]
theorem apply_eq {n : ℕ} (S : NarainChargeSymmetry n) (q : SplitCharge n) :
    S.apply q = S.toLinearEquiv q :=
  rfl

end NarainChargeSymmetry

/--
Swap momentum and winding.

This is the basic T-duality-style orthogonal symmetry of the hyperbolic charge
lattice.
-/
def chargeSwapLinearEquiv (n : ℕ) : SplitCharge n ≃ₗ[ℤ] SplitCharge n where
  toFun q := (q.2, q.1)
  invFun q := (q.2, q.1)
  left_inv := by
    intro q
    ext <;> rfl
  right_inv := by
    intro q
    ext <;> rfl
  map_add' := by
    intro q r
    ext <;> rfl
  map_smul' := by
    intro a q
    ext <;> rfl

@[simp]
theorem chargeSwapLinearEquiv_apply
    (n : ℕ) (q : SplitCharge n) :
    chargeSwapLinearEquiv n q = (q.2, q.1) :=
  rfl

/-- The momentum/winding swap preserves the hyperbolic pairing. -/
theorem chargeSwap_preserves_hyperbolicPair
    (n : ℕ) (q r : SplitCharge n) :
    SplitCharge.hyperbolicPair (chargeSwapLinearEquiv n q)
        (chargeSwapLinearEquiv n r) =
      SplitCharge.hyperbolicPair q r := by
  simp only [SplitCharge.hyperbolicPair, chargeSwapLinearEquiv_apply, SplitCharge.momentum,
    SplitCharge.winding, add_comm]

@[simp]
theorem chargeSwap_involutive (n : ℕ) (q : SplitCharge n) :
    chargeSwapLinearEquiv n (chargeSwapLinearEquiv n q) = q := by
  rfl

theorem chargeSwap_preserves_hyperbolicNorm
    (n : ℕ) (q : SplitCharge n) :
    SplitCharge.hyperbolicNorm (chargeSwapLinearEquiv n q) =
      SplitCharge.hyperbolicNorm q := by
  unfold SplitCharge.hyperbolicNorm
  exact chargeSwap_preserves_hyperbolicPair n q q

/--
Global sign flip of the split charge lattice.

This is the `CPT`-style central involution on the charge sectors.
-/
def chargeParityTwistLinearEquiv (n : ℕ) : SplitCharge n ≃ₗ[ℤ] SplitCharge n where
  toFun q := (-q.1, -q.2)
  invFun q := (-q.1, -q.2)
  left_inv := by
    intro q
    ext <;> simp
  right_inv := by
    intro q
    ext <;> simp
  map_add' := by
    intro q r
    ext x <;> dsimp <;> ring
  map_smul' := by
    intro a q
    ext x <;> dsimp <;> ring

@[simp]
theorem chargeParityTwistLinearEquiv_apply
    (n : ℕ) (q : SplitCharge n) :
    chargeParityTwistLinearEquiv n q = (-q.1, -q.2) :=
  rfl

/-- The global sign twist preserves the hyperbolic pairing. -/
theorem chargeParityTwist_preserves_hyperbolicPair
    (n : ℕ) (q r : SplitCharge n) :
    SplitCharge.hyperbolicPair (chargeParityTwistLinearEquiv n q)
        (chargeParityTwistLinearEquiv n r) =
      SplitCharge.hyperbolicPair q r := by
  unfold SplitCharge.hyperbolicPair
  simp only [chargeParityTwistLinearEquiv_apply, SplitCharge.momentum, SplitCharge.winding]
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  ring

@[simp]
theorem chargeParityTwist_involutive (n : ℕ) (q : SplitCharge n) :
    chargeParityTwistLinearEquiv n (chargeParityTwistLinearEquiv n q) = q := by
  ext i <;> simp [chargeParityTwistLinearEquiv_apply]

theorem chargeParityTwist_preserves_hyperbolicNorm
    (n : ℕ) (q : SplitCharge n) :
    SplitCharge.hyperbolicNorm (chargeParityTwistLinearEquiv n q) =
      SplitCharge.hyperbolicNorm q := by
  unfold SplitCharge.hyperbolicNorm
  exact chargeParityTwist_preserves_hyperbolicPair n q q

/--
Canonical orthogonal symmetries of the Narain charge lattice.

These are the discrete gates needed before any Clifford lift or modular
specialization.
-/
structure NarainOrthogonalCore (n : ℕ) where
  swap : NarainChargeSymmetry n
  parityTwist : NarainChargeSymmetry n

/-- Canonical Narain orthogonal core built from swap and parity twist. -/
def canonicalNarainOrthogonalCore (n : ℕ) : NarainOrthogonalCore n where
  swap :=
    { toLinearEquiv := chargeSwapLinearEquiv n
      preserves_hyperbolicPair := chargeSwap_preserves_hyperbolicPair n }
  parityTwist :=
    { toLinearEquiv := chargeParityTwistLinearEquiv n
      preserves_hyperbolicPair := chargeParityTwist_preserves_hyperbolicPair n }

end InfoGeometry.Algebraic.Split
