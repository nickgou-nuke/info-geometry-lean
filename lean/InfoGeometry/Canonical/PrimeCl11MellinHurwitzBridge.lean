import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.DiscreteMellinModularBridge
import InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge
import InfoGeometry.Canonical.PrimeCl11ModularAtomCore
import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.Clifford.Cl11Matrix

/-!
# InfoGeometry.Canonical.PrimeCl11MellinHurwitzBridge

Finite theorem-safe bridge between:

* the existing binary Cantor / prime / Hurwitz owner surface,
* the discrete Mellin scale channel,
* the finite `Cl(1,1)` algebra core.

This file does not construct an infinite `Cl(1,1)^∞` tensor product, nor does
it prove a zeta-zero theorem.  It only packages the finite scale/symmetry
readout already available in the repo.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeCl11MellinHurwitzBridge

open InfoGeometry.Canonical.DiscreteMellinModularBridge
open InfoGeometry.Canonical.PrimeBinaryCantorSuperalgebraBridge
open InfoGeometry.Canonical.PrimeCl11ModularAtomCore
open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
open InfoGeometry.Clifford.Cl11Matrix

/-! ## Scale channel -/

/--
Generic scale-invariance readout for a weight-zero Weyl homogeneous operator.

This is the theorem-safe abstraction of the Mellin scale channel.
-/
@[rep_depth operator]
theorem scaleInvariant_of_weight_zero
    {Op : Type*}
    (W : WeylHomogeneousOperatorReadout Op)
    (hW : W.weight = 0) :
    ∀ c A, W.readout (W.scale c A) = W.readout A := by
  intro c A
  simpa [hW] using (W.readout_scale_of_weight_zero hW c A)

/-- The logarithmic Mellin sample advances by the expected exponential scale factor. -/
@[rep_depth operator]
theorem logarithmicSample_scale_step
    (η0 Δη : ℝ) (k : ℤ) :
    logarithmicSample η0 Δη (k + 1)
      = Real.exp Δη * logarithmicSample η0 Δη k := by
  simpa using (logarithmicSample_succ_eq_exp_mul η0 Δη k)

/-! ## Cl(1,1) and Hurwitz readout -/

/-- The local `Cl(1,1)` pseudoscalar parity is an involution. -/
@[rep_depth operator]
theorem cl11_mobiusParity_sq_eq_one
    {A : Type*} [Ring A] (atom : Cl11Atom A) :
    atom.mobiusParity * atom.mobiusParity = 1 :=
  Cl11Atom.mobiusParity_sq_eq_one (A := A) (atom := atom)

/-- The real `Cl(1,1)` algebra has finite dimension four. -/
@[rep_depth operator]
theorem cl11_finrank_four :
    Module.finrank ℝ (CliffordAlgebra q11) = 4 :=
  finrank_cl11

/-! ## Combined bridge target -/

/--
Combined theorem-safe bridge.

This packages the already-proved finite owner surfaces:

* Cantor cylinder splitting plus the finite prime superalgebra / Hurwitz shell
  target;
* Mellin scale-step law;
* weight-zero scale invariance;
* local `Cl(1,1)` parity involution;
* `Cl(1,1)` finite-dimensional core.
-/
@[rep_depth operator]
def PrimeCl11MellinHurwitzOwnerTarget : Prop :=
  PrimeBinaryCantorSuperalgebraOwnerTarget
    ∧ (∀ η0 Δη k,
        Real.log (logarithmicSample η0 Δη k) = discreteRapidity η0 Δη k)
    ∧ (∀ {Op : Type*} (W : WeylHomogeneousOperatorReadout Op),
        W.weight = 0 → ∀ c A, W.readout (W.scale c A) = W.readout A)
    ∧ (∀ (A : Type*) [Ring A] (atom : Cl11Atom A),
        atom.mobiusParity * atom.mobiusParity = 1)
    ∧ (Module.finrank ℝ (CliffordAlgebra q11) = 4)

/-- The combined bridge follows from the existing repo owner theorems. -/
@[rep_depth operator]
theorem primeCl11MellinHurwitzOwnerTarget :
    PrimeCl11MellinHurwitzOwnerTarget := by
  constructor
  · exact primeBinaryCantorSuperalgebraOwnerTarget
  · constructor
    · intro η0 Δη k
      simpa using (log_logarithmicSample η0 Δη k)
    · constructor
      · intro Op W hW c A
        exact W.readout_scale_of_weight_zero hW c A
      · constructor
        · intro A inst atom
          exact Cl11Atom.mobiusParity_sq_eq_one (A := A) (atom := atom)
        · exact cl11_finrank_four

end InfoGeometry.Canonical.PrimeCl11MellinHurwitzBridge
