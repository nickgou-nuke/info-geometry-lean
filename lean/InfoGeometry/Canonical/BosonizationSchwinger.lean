import InfoGeometry.Canonical.BosonizationBoundary
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.BosonizationSchwinger

Conservative Schwinger boundary for the finite Tomita/Krein atom.

This module proves the signed crossing-number identity and the target
Heisenberg current law.  The source-side construction from raw CAR modes lives
in `InfoGeometry.Canonical.BosonizationConstructiveCurrent`, where the current
law is derived from normal-ordered matrix units and the crossing-count theorem.
-/

namespace BosonizationSchwinger

open InfoGeometry.Canonical.BosonizationBoundary
open VirasoroProject

section CrossingNumber

/-- Positive part of an integer crossing count. -/
def positiveCrossingNumber (m : ℤ) : ℤ :=
  if 0 < m then m else 0

/-- Negative part of an integer crossing count. -/
def negativeCrossingNumber (m : ℤ) : ℤ :=
  if m < 0 then -m else 0

/-- Signed crossing number, written as positive minus negative part. -/
def signedCrossingNumber (m : ℤ) : ℤ :=
  positiveCrossingNumber m - negativeCrossingNumber m

/-- The signed crossing number is exactly the integer `m`. -/
@[simp]
theorem signedCrossingNumber_eq_self (m : ℤ) :
    signedCrossingNumber m = m := by
  by_cases hmpos : 0 < m
  · have hpos : positiveCrossingNumber m = m := by
      simp [positiveCrossingNumber, hmpos]
    have hneg : negativeCrossingNumber m = 0 := by
      have hnot : ¬ m < 0 := by omega
      simp [negativeCrossingNumber, hnot]
    simp [signedCrossingNumber, hpos, hneg]
  · have hmle : m ≤ 0 := le_of_not_gt hmpos
    by_cases hm0 : m = 0
    · subst hm0
      simp [signedCrossingNumber, positiveCrossingNumber, negativeCrossingNumber]
    · have hmneg : m < 0 := lt_of_le_of_ne hmle hm0
      have hpos : positiveCrossingNumber m = 0 := by
        simp [positiveCrossingNumber, hmpos]
      have hneg : negativeCrossingNumber m = -m := by
        simp [negativeCrossingNumber, hmneg]
      have hcalc : (0 : ℤ) - (-m) = m := by omega
      simp [signedCrossingNumber, hpos, hneg, hcalc]

/-- The Schwinger cocycle coefficient has the expected delta form. -/
def schwingerCocycle (m n : ℤ) : ℤ :=
  if m + n = 0 then signedCrossingNumber m else 0

/-- The Schwinger cocycle coefficient reduces to `m δ[m+n,0]`. -/
@[simp]
theorem schwingerCocycle_eq (m n : ℤ) :
    schwingerCocycle m n = if m + n = 0 then m else 0 := by
  simp [schwingerCocycle]

/-- Alias used by the normal-ordered current interface. -/
def schwingerCocycleCoeff (m n : ℤ) : ℤ :=
  schwingerCocycle m n

/-- The Schwinger cocycle coefficient reduces to `m δ[m+n,0]`. -/
@[simp]
theorem schwingerCocycleCoeff_eq (m n : ℤ) :
    schwingerCocycleCoeff m n = if m + n = 0 then m else 0 := by
  simp [schwingerCocycleCoeff]

/-- Real scalar form of the Schwinger coefficient. -/
theorem schwingerCocycleCoeff_real_smul
    {V : Type*} [AddCommMonoid V] [Module ℝ V] (K : V) (m n : ℤ) :
    (schwingerCocycleCoeff m n : ℝ) • K =
      (if m + n = 0 then (m : ℝ) • K else 0) := by
  by_cases h : m + n = 0
  · simp [h]
  · simp [h]

end CrossingNumber

section TargetHeisenberg

/-! ## Constructive target current law -/

/--
Target normal-ordered current object in the already-constructed Heisenberg
current algebra.

This names the target current generator in the already-constructed external
Heisenberg algebra.  The raw-CAR construction is supplied separately by
`BosonizationConstructiveCurrent`.
-/
@[rep_depth transport]
noncomputable abbrev normalOrderedCurrentTarget (n : ℤ) : HeisenbergAlgebra ℝ :=
  HeisenbergAlgebra.jgen ℝ n

/-- Central current element in the target Heisenberg algebra. -/
@[rep_depth transport]
noncomputable abbrev normalOrderedCurrentCentral : HeisenbergAlgebra ℝ :=
  HeisenbergAlgebra.kgen ℝ

/--
The target normal-ordered currents satisfy the Heisenberg current law.

This is the target current law:
`normal-ordered current -> [J_m,J_n] = m δ[m+n,0] K`.
-/
@[rep_depth transport]
theorem normalOrderedCurrentTarget_commutator (m n : ℤ) :
    ⁅normalOrderedCurrentTarget m, normalOrderedCurrentTarget n⁆ =
      if m + n = 0 then (m : ℝ) • normalOrderedCurrentCentral else 0 :=
  HeisenbergAlgebra.lie_jgen ℝ m n

/--
The same target current law written through the constructive Schwinger
coefficient already proved above.
-/
@[rep_depth transport]
theorem normalOrderedCurrentTarget_commutator_schwingerCoeff (m n : ℤ) :
    ⁅normalOrderedCurrentTarget m, normalOrderedCurrentTarget n⁆ =
      (schwingerCocycleCoeff m n : ℝ) • normalOrderedCurrentCentral := by
  calc
    ⁅normalOrderedCurrentTarget m, normalOrderedCurrentTarget n⁆
        = if m + n = 0 then (m : ℝ) • normalOrderedCurrentCentral else 0 :=
          normalOrderedCurrentTarget_commutator m n
    _ = (schwingerCocycleCoeff m n : ℝ) • normalOrderedCurrentCentral :=
          (schwingerCocycleCoeff_real_smul normalOrderedCurrentCentral m n).symm

end TargetHeisenberg

end BosonizationSchwinger
