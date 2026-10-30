/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.Algebra.Star.Basic

/-!
# Ordered two-chart sandwiches

For the graph-chart elements `P - N₊` and `P + N₋`, this file records their
ordered products with the four Peirce generators. These are identities in an
arbitrary associative ring; no group action or scalar-valued transition
probability is inferred.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
include hP

def chartBruhatConj (P A C X : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * X *
    (1 + coneMinus P C) * (1 - conePlus P A)

/-- Conjugation by the inverse of the two-factor chart element. -/
def chartBruhatConjInv (P A C X : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A) * X *
    (1 + conePlus P A) * (1 - coneMinus P C)

/-- The chart sandwich readout on the four generators `(Φ, J, V, Σ)`. -/
theorem chart_two_state_generator_sandwich :
    (P - conePlus P A) * genPhi P A C * (P + coneMinus P C) = 0 ∧
    (P - conePlus P A) * genJ P A C * (P + coneMinus P C) =
      (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
    (P - conePlus P A) * genV P A C * (P + coneMinus P C) =
      -((conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) -
        conePlus P A * coneMinus P C) ∧
    (P - conePlus P A) * genSig P A C * (P + coneMinus P C) =
      conePlus P A * coneMinus P C +
        (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- Products of the two chart elements with the linear combinations `Φ ± J`. -/
theorem chart_spinor_selection_products :
    (genPhi P A C + genJ P A C) * (P + coneMinus P C) =
      (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
    (genPhi P A C - genJ P A C) * (P + coneMinus P C) =
      (2 : ℤ) • coneMinus P C ∧
    (P - conePlus P A) * (genPhi P A C - genJ P A C) =
      -((2 : ℤ) • (conePlus P A * coneMinus P C)) ∧
    (P - conePlus P A) * (genPhi P A C + genJ P A C) =
      (2 : ℤ) • conePlus P A := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The product of the two chart points is the base corner minus the upper
cycle; the off-diagonal terms vanish by Peirce support. -/
theorem chart_point_product :
    (P - conePlus P A) * (P + coneMinus P C) =
      P - conePlus P A * coneMinus P C := by
  peirce_nf hP

/-- The two-factor chart conjugation sends the lower chart point to the upper
chart point. -/
theorem chart_bruhat_conjugation_transition :
    chartBruhatConj P A C (P + coneMinus P C) = P - conePlus P A ∧
    chartBruhatConjInv P A C (P - conePlus P A) = P + coneMinus P C := by
  constructor
  · unfold chartBruhatConj
    peirce_nf hP
  · unfold chartBruhatConjInv
    peirce_nf hP

/-- The `Σ` chart sandwich differs from the Euler-compressed `Q₊` value by
exactly twice the quadratic cycle. This is the finite-depth obstruction to
the A82 transcript's proposed `Σ` sandwich formula at depth zero. -/
theorem chart_sigma_euler_compression_residual :
    (P - conePlus P A) * genSig P A C * (P + coneMinus P C) -
      (1 - genV P A C) * (conePlus P A * coneMinus P C) =
        (2 : ℤ) •
          ((conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C)) := by
  peirce_nf hP

variable [StarRing B] (hPs : star P = P) (X : B)
include hPs

/-- The complementary ideal pairing with the left cycle in its actual order. -/
theorem complementary_twisted_ideal_pairing :
    (invS P * star (X * (1 - P)) * invS P) * (X * (1 - P)) =
      peirce00 P (star X) * peirce00 P X -
        coneMinus P (star X) * conePlus P X := by
  simp only [invS, star_mul, star_sub, star_one, hPs,
    peirce00, coneMinus, conePlus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
