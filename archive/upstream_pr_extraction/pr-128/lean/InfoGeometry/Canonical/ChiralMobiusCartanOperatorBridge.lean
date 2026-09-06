import InfoGeometry.Canonical.KKTLorentzOrbitBridge
import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import Mathlib.Tactic

open scoped InnerProductSpace

/-!
# Chiral Cartan operator bridge

This is the finite algebraic bridge from the split scalar idempotent lanes to
the already existing split `Cl(1,1)` operator action.  The diagonal scalar
lanes are represented by `plusProjector` and `minusProjector`; the names
`uPlus` and `uMinus` are deliberately reserved for the off-diagonal KKT
channels owned by `KKTCore`.

No analytic continuation or projective quotient is introduced here.  This
owner only proves the commuting scalar-to-operator readout and its
hyperbolic-flow specialization.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralMobiusCartanOperatorBridge

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.KKTLorentzOrbitBridge
open InfoGeometry.Quantum
open InfoGeometry.Thermo.SplitChiralPolarizationBasis

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H
local notation "IdH" => ContinuousLinearMap.id ℝ H

/-- The Cartan/grading operator of the chiral Peirce decomposition. -/
noncomputable def ell (X : RealSplitCl11Action H) : EndH :=
  X.eps

/-- The diagonal scalar readout into the operator endomorphism algebra. -/
noncomputable def chiralScalarOperatorReadout
    (X : RealSplitCl11Action H) (z : ChiralScalar) : EndH :=
  leftPart z • plusProjector X + rightPart z • minusProjector X

@[simp] theorem ell_eq_plusProjector_sub_minusProjector
    (X : RealSplitCl11Action H) :
    ell X = plusProjector X - minusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  simp [ell, plusProjector, minusProjector, sub_eq_add_neg]
  module

@[simp] theorem ell_sq_one (X : RealSplitCl11Action H) :
    ell X * ell X = (1 : EndH) := by
  simpa [ell] using X.eps_sq

@[simp] theorem chiralScalarOperatorReadout_splitOne
    (X : RealSplitCl11Action H) :
    chiralScalarOperatorReadout X splitOne = IdH := by
  rw [show splitOne = ePlus + eMinus by
    exact ePlus_add_eMinus.symm]
  simp [chiralScalarOperatorReadout, add_smul, add_assoc,
    plusProjector_add_minusProjector]

@[simp] theorem chiralScalarOperatorReadout_ePlus
    (X : RealSplitCl11Action H) :
    chiralScalarOperatorReadout X ePlus = plusProjector X := by
  simp [chiralScalarOperatorReadout]

@[simp] theorem chiralScalarOperatorReadout_eMinus
    (X : RealSplitCl11Action H) :
    chiralScalarOperatorReadout X eMinus = minusProjector X := by
  simp [chiralScalarOperatorReadout]

@[simp] theorem chiralScalarOperatorReadout_j
    (X : RealSplitCl11Action H) :
    chiralScalarOperatorReadout X j = ell X := by
  simp [chiralScalarOperatorReadout, ell]
  apply ContinuousLinearMap.ext
  intro u
  simp [plusProjector, minusProjector, sub_eq_add_neg]
  module

theorem chiralScalarOperatorReadout_chiralMul
    (X : RealSplitCl11Action H) (x y : ChiralScalar) :
    chiralScalarOperatorReadout X (chiralMul x y) =
      chiralScalarOperatorReadout X x * chiralScalarOperatorReadout X y := by
  change (x.1 * y.1) • plusProjector X + (x.2 * y.2) • minusProjector X =
      (x.1 • plusProjector X + x.2 • minusProjector X) *
        (y.1 • plusProjector X + y.2 • minusProjector X)
  rw [add_mul, mul_add, mul_add]
  rw [smul_mul_smul, smul_mul_smul, smul_mul_smul, smul_mul_smul]
  rw [plusProjector_idempotent, plusProjector_mul_minusProjector,
    minusProjector_mul_plusProjector, minusProjector_idempotent]
  simp [smul_add, add_smul, add_assoc, add_left_comm, add_comm]

@[simp] theorem chiralScalarOperatorReadout_hyperbolicExp
    (X : RealSplitCl11Action H) (θ : ℝ) :
    chiralScalarOperatorReadout X (hyperbolicExp θ) =
      (Real.exp θ) • plusProjector X +
        (Real.exp (-θ)) • minusProjector X := by
  rfl

theorem chiralScalarOperatorReadout_hyperbolicExp_eq_channelBoost
    (X : RealSplitCl11Action H) (θ : ℝ) :
    chiralScalarOperatorReadout X (hyperbolicExp θ) =
      channelBoost X θ := by
  rw [chiralScalarOperatorReadout_hyperbolicExp]
  unfold channelBoost
  change (Real.exp θ) • plusProjector X +
      (Real.exp (-θ)) • minusProjector X =
    Real.cosh θ • IdH + Real.sinh θ • ell X
  rw [ell_eq_plusProjector_sub_minusProjector (X := X)]
  apply ContinuousLinearMap.ext
  intro u
  simp [plusProjector, minusProjector, sub_eq_add_neg]
  rw [← Real.cosh_add_sinh θ, ← Real.cosh_sub_sinh θ]
  module

end InfoGeometry.Canonical.ChiralMobiusCartanOperatorBridge
