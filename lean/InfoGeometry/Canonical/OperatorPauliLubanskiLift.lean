import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorZornSpinCasimirLift
import InfoGeometry.Physics.PauliLubanskiFiniteBridge

/-!
# InfoGeometry.Canonical.OperatorPauliLubanskiLift

Concrete spin-1/2 Pauli--Lubanski realization on the repository-owned
`2 × 2` Pauli carrier, followed by transport through the existing associative
`OperatorZornMatrix` equivalence.

The real finite owner `Physics.PauliLubanskiFiniteBridge` already proves
orthogonality for arbitrary finite rotation/boost data.  This file supplies
the missing fundamental Pauli representation:

* `S_i = σ_i / 2`;
* left-handed boosts `K_i = -i S_i`;
* `W^0 = p · S` and `W⃗ = E S⃗ + p⃗ × K⃗`;
* `P · W = 0`;
* `W² = -(3/4) Q(P) I₂ = -Q(P) S²`;
* exact transport of the second Casimir to the diagonal operator-Zorn sector.

The massless identity `W^μ = λ P^μ` is not asserted as an operator identity:
it holds after restriction to a helicity eigenspace.  The theorem-supported
massless consequence proved here is the vanishing quadratic Casimir.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorPauliLubanskiLift

open Matrix
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Canonical.OperatorZornSpinCasimirLift
open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev OperatorZornC := OperatorZornMatrix ℂ

/-- Complexified finite momentum coordinates. -/
structure PauliMomentum where
  E : ℂ
  px : ℂ
  py : ℂ
  pz : ℂ

/-- First Poincare Casimir in the complexified Pauli coordinates. -/
def massCasimir (P : PauliMomentum) : ℂ :=
  P.E ^ 2 - P.px ^ 2 - P.py ^ 2 - P.pz ^ 2

/-- Spatial spin contraction `p · S`. -/
def momentumDotSpin (P : PauliMomentum) : Mat2C :=
  P.px • spinX + P.py • spinY + P.pz • spinZ

/-- Left-handed boost generators `K_i = -i S_i`. -/
def boostX : Mat2C := (-Complex.I) • spinX
/-- Left-handed boost generator in the second spatial direction. -/
def boostY : Mat2C := (-Complex.I) • spinY
/-- Left-handed boost generator in the third spatial direction. -/
def boostZ : Mat2C := (-Complex.I) • spinZ

/-- Temporal Pauli--Lubanski component `W⁰ = p · S`. -/
def pauliLubanski0 (P : PauliMomentum) : Mat2C :=
  momentumDotSpin P

/-- First spatial Pauli--Lubanski component
`W¹ = E S₁ + p_y K₃ - p_z K₂`. -/
def pauliLubanski1 (P : PauliMomentum) : Mat2C :=
  P.E • spinX + P.py • boostZ - P.pz • boostY

/-- Second spatial Pauli--Lubanski component
`W² = E S₂ + p_z K₁ - p_x K₃`. -/
def pauliLubanski2 (P : PauliMomentum) : Mat2C :=
  P.E • spinY + P.pz • boostX - P.px • boostZ

/-- Third spatial Pauli--Lubanski component
`W³ = E S₃ + p_x K₂ - p_y K₁`. -/
def pauliLubanski3 (P : PauliMomentum) : Mat2C :=
  P.E • spinZ + P.px • boostY - P.py • boostX

/-- Minkowski contraction `P_μ W^μ`. -/
def momentumPauliLubanskiContraction (P : PauliMomentum) : Mat2C :=
  P.E • pauliLubanski0 P - P.px • pauliLubanski1 P -
    P.py • pauliLubanski2 P - P.pz • pauliLubanski3 P

/-- The Pauli--Lubanski vector is orthogonal to momentum in the concrete
spin-half realization. -/
theorem pauliLubanski_momentum_orthogonal (P : PauliMomentum) :
    momentumPauliLubanskiContraction P = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumPauliLubanskiContraction, pauliLubanski0,
      pauliLubanski1, pauliLubanski2, pauliLubanski3,
      momentumDotSpin, boostX, boostY, boostZ,
      spinX, spinY, spinZ, σ1, σ2, σ3] <;>
    ring

/-- Minkowski square of the four Pauli--Lubanski matrix components. -/
def pauliLubanskiSq (P : PauliMomentum) : Mat2C :=
  pauliLubanski0 P * pauliLubanski0 P -
    pauliLubanski1 P * pauliLubanski1 P -
    pauliLubanski2 P * pauliLubanski2 P -
    pauliLubanski3 P * pauliLubanski3 P

/-- Exact spin-half second Poincare Casimir. -/
theorem pauliLubanski_sq_eq_three_quarters_mass (P : PauliMomentum) :
    pauliLubanskiSq P =
      (-(3 / 4 : ℂ) * massCasimir P) • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLubanskiSq, pauliLubanski0,
      pauliLubanski1, pauliLubanski2, pauliLubanski3,
      momentumDotSpin, boostX, boostY, boostZ,
      massCasimir, spinX, spinY, spinZ,
      σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_sq] <;>
    ring

/-- The same identity factored through the already-proved internal spin
Casimir `S² = 3/4 I`. -/
theorem pauliLubanski_sq_eq_mass_spin_casimir (P : PauliMomentum) :
    pauliLubanskiSq P = -(massCasimir P) • spinHalfCasimir := by
  rw [spinHalfCasimir_eq_three_quarters,
    pauliLubanski_sq_eq_three_quarters_mass]
  module

/-- Null momentum forces the quadratic Pauli--Lubanski Casimir to vanish.
This is the representation-independent part of the massless helicity limit. -/
theorem pauliLubanski_null_limit
    (P : PauliMomentum) (hP : massCasimir P = 0) :
    pauliLubanskiSq P = 0 := by
  rw [pauliLubanski_sq_eq_three_quarters_mass, hP]
  simp

/-- Transport the Pauli--Lubanski quadratic Casimir through the existing
matrix-to-operator-Zorn equivalence. -/
def zornPauliLubanskiSq (P : PauliMomentum) : OperatorZornC :=
  zornLift (pauliLubanskiSq P)

/-- The second Poincare Casimir is scalar-central in the chiral operator-Zorn
coordinates. -/
theorem zornPauliLubanski_sq (P : PauliMomentum) :
    zornPauliLubanskiSq P =
      ({ n_plus_op := -(3 / 4 : ℂ) * massCasimir P,
         n_minus_op := -(3 / 4 : ℂ) * massCasimir P,
         sigma_plus_op := 0,
         sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  rw [toMatrix_zornLift, pauliLubanski_sq_eq_three_quarters_mass]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix]

/-- Operator-Zorn second Casimir as the product of the external mass Casimir
and the already-lifted internal spin Casimir. -/
theorem zornPauliLubanski_sq_eq_mass_spin (P : PauliMomentum) :
    zornPauliLubanskiSq P =
      -(massCasimir P) • zornSpinHalfCasimir := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornPauliLubanskiSq, zornSpinHalfCasimir, zornLift,
    pauliLubanski_sq_eq_mass_spin_casimir]

/-- Consolidated finite Poincare spin packet. -/
theorem pauliLubanski_spin_half_packet (P : PauliMomentum) :
    momentumPauliLubanskiContraction P = 0 ∧
      pauliLubanskiSq P = -(massCasimir P) • spinHalfCasimir ∧
      toMatrix (zornPauliLubanskiSq P) =
        (-(3 / 4 : ℂ) * massCasimir P) • (1 : Mat2C) := by
  refine ⟨pauliLubanski_momentum_orthogonal P,
    pauliLubanski_sq_eq_mass_spin_casimir P, ?_⟩
  rw [toMatrix_zornLift, pauliLubanski_sq_eq_three_quarters_mass]

end InfoGeometry.Canonical.OperatorPauliLubanskiLift
