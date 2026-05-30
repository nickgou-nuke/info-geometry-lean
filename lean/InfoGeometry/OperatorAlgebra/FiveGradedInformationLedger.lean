/-
InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean

Projected information accounting identity.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

variable
    {J L Obs : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L]
    [AddCommGroup Obs] [Module ℝ Obs]

/--
Projected information accounting identity.

If the observed cross term is the observation of the visible Lie bracket plus
two hidden memory terms, then the observed defect is exactly the observation
of the hidden total.

This is the proof-bearing content behind the five-grade ledger slogan:

`observed defect = observed hidden memory`.

No five-grading structure.
No direct-sum placeholder.
No recovery packet.
No `sorry`.
-/
theorem observedDefect_eq_obs_hidden_of_cross_identity
    (neg pos : J →ₗ[ℝ] L)
    (hiddenNegTwo hiddenPosTwo : J → J → L)
    (obs : L →ₗ[ℝ] Obs)
    (observedCross : J → J → Obs)
    (hcross :
      ∀ x y : J,
        observedCross x y =
          obs (⁅neg x, pos y⁆ + hiddenNegTwo x y + hiddenPosTwo x y))
    (x y : J) :
    observedCross x y - obs ⁅neg x, pos y⁆ =
      obs (hiddenNegTwo x y + hiddenPosTwo x y) := by
  let br : L := ⁅neg x, pos y⁆
  let hn : L := hiddenNegTwo x y
  let hp : L := hiddenPosTwo x y
  change observedCross x y - obs br = obs (hn + hp)
  rw [hcross x y]
  change obs (br + hn + hp) - obs br = obs (hn + hp)
  have hassoc : br + hn + hp = br + (hn + hp) := by
    abel
  rw [hassoc, map_add]
  abel

end InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `observedDefect_eq_obs_hidden_of_cross_identity` : Proves natively that observed defect is equal to the observed hidden memory.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/
