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
* exact transport of the second Casimir to the diagonal operator-Zorn sector;
* for the null ray `P = (E,0,0,E)`, the left Weyl sector obeys
  `W_L^μ P₊ = +(1/2) P^μ P₊`, while the right Weyl companion obeys
  `W_R^μ P₋ = -(1/2) P^μ P₋`.

The two signs belong to the two Weyl chiralities.  They are not asserted
simultaneously for one fixed choice of boost generators.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorPauliLubanskiLift

open Matrix
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Canonical.OperatorZornSpinCasimirLift
open InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge
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
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    calc (Complex.I : ℂ) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
    _ = 1 := by rw [Complex.I_sq]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLubanskiSq, pauliLubanski0,
      pauliLubanski1, pauliLubanski2, pauliLubanski3,
      momentumDotSpin, boostX, boostY, boostZ,
      massCasimir, spinX, spinY, spinZ,
      σ1, σ2, σ3] <;>
    ring_nf <;>
    simp (config := { failIfUnchanged := false }) only [Complex.I_sq, hI4] <;>
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

/-! ## Null z-axis momentum and helicity projection -/

/-- Future-pointing algebraic null ray aligned with the circular `z` axis. -/
def nullZMomentum (E : ℂ) : PauliMomentum :=
  ⟨E, 0, 0, E⟩

@[simp] theorem nullZMomentum_massCasimir (E : ℂ) :
    massCasimir (nullZMomentum E) = 0 := by
  simp [massCasimir, nullZMomentum]

/-- Contravariant momentum component readout in the order `(0,1,2,3)`. -/
def momentumComponent (P : PauliMomentum) : Fin 4 → ℂ
  | 0 => P.E
  | 1 => P.px
  | 2 => P.py
  | 3 => P.pz

/-- Left-handed Pauli--Lubanski component readout. -/
def pauliLubanskiComponent (P : PauliMomentum) : Fin 4 → Mat2C
  | 0 => pauliLubanski0 P
  | 1 => pauliLubanski1 P
  | 2 => pauliLubanski2 P
  | 3 => pauliLubanski3 P

/-- On the `+z` null ray the left-handed transverse components are the
positive circular raising rail. -/
theorem nullZ_left_transverse_packet (E : ℂ) :
    pauliLubanski1 (nullZMomentum E) = E • spinRaise ∧
      pauliLubanski2 (nullZMomentum E) = (-Complex.I * E) • spinRaise := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [nullZMomentum, pauliLubanski1, pauliLubanski2,
        boostX, boostY, boostZ, spinRaise, sigmaPlus,
        InfoGeometry.Optics.ChiralLorentzOperatorLift.create,
        spinX, spinY, spinZ, σ1, σ2, σ3] <;>
      ring_nf <;>
      simp (config := { failIfUnchanged := false }) only [Complex.I_sq] <;>
      ring

set_option linter.unnecessarySeqFocus false in
/-- The positive circular sector is the physical helicity `+1/2` eigenspace
for the left-handed Weyl representation on the future `+z` null ray:
`W_L^μ P₊ = +(1/2) P^μ P₊` for all four components. -/
theorem pauliLubanski_nullZ_positive_helicity
    (E : ℂ) (mu : Fin 4) :
    pauliLubanskiComponent (nullZMomentum E) mu * circularPlus =
      (((2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularPlus) := by
  fin_cases mu <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pauliLubanskiComponent, momentumComponent, nullZMomentum,
        pauliLubanski0, pauliLubanski1, pauliLubanski2, pauliLubanski3,
        momentumDotSpin, boostX, boostY, boostZ,
        spinX, spinY, spinZ,
        circularPlus,
        InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularPlusProjector,
        InfoGeometry.Optics.FiniteJonesModel.sProjector,
        InfoGeometry.Optics.FiniteJonesModel.diagJones,
        σ1, σ2, σ3, Matrix.mul_apply] <;>
      ring_nf <;>
      simp (config := { failIfUnchanged := false }) only [Complex.I_sq] <;>
      ring

/-- Right-handed boost generators `K_i^R = +i S_i`. -/
def rightBoostX : Mat2C := Complex.I • spinX
/-- Right-handed second boost generator. -/
def rightBoostY : Mat2C := Complex.I • spinY
/-- Right-handed third boost generator. -/
def rightBoostZ : Mat2C := Complex.I • spinZ

/-- Right-handed temporal component; rotations are unchanged. -/
def rightPauliLubanski0 (P : PauliMomentum) : Mat2C :=
  momentumDotSpin P

/-- Right-handed first spatial component. -/
def rightPauliLubanski1 (P : PauliMomentum) : Mat2C :=
  P.E • spinX + P.py • rightBoostZ - P.pz • rightBoostY

/-- Right-handed second spatial component. -/
def rightPauliLubanski2 (P : PauliMomentum) : Mat2C :=
  P.E • spinY + P.pz • rightBoostX - P.px • rightBoostZ

/-- Right-handed third spatial component. -/
def rightPauliLubanski3 (P : PauliMomentum) : Mat2C :=
  P.E • spinZ + P.px • rightBoostY - P.py • rightBoostX

/-- Right-handed Pauli--Lubanski component readout. -/
def rightPauliLubanskiComponent (P : PauliMomentum) : Fin 4 → Mat2C
  | 0 => rightPauliLubanski0 P
  | 1 => rightPauliLubanski1 P
  | 2 => rightPauliLubanski2 P
  | 3 => rightPauliLubanski3 P

/-- On the `+z` null ray the right-handed transverse components are the
negative circular lowering rail. -/
theorem nullZ_right_transverse_packet (E : ℂ) :
    rightPauliLubanski1 (nullZMomentum E) = E • spinLower ∧
      rightPauliLubanski2 (nullZMomentum E) = (Complex.I * E) • spinLower := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [nullZMomentum, rightPauliLubanski1, rightPauliLubanski2,
        rightBoostX, rightBoostY, rightBoostZ, spinLower, sigmaMinus,
        InfoGeometry.Optics.ChiralLorentzOperatorLift.annihilate,
        spinX, spinY, spinZ, σ1, σ2, σ3] <;>
      ring_nf <;>
      simp (config := { failIfUnchanged := false }) only [Complex.I_sq] <;>
      ring

set_option linter.unnecessarySeqFocus false in
/-- The negative circular sector is the physical helicity `-1/2` eigenspace
for the right-handed Weyl representation on the same future `+z` null ray:
`W_R^μ P₋ = -(1/2) P^μ P₋`. -/
theorem pauliLubanski_nullZ_negative_helicity
    (E : ℂ) (mu : Fin 4) :
    rightPauliLubanskiComponent (nullZMomentum E) mu * circularMinus =
      ((-(2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularMinus) := by
  fin_cases mu <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [rightPauliLubanskiComponent, momentumComponent, nullZMomentum,
        rightPauliLubanski0, rightPauliLubanski1,
        rightPauliLubanski2, rightPauliLubanski3,
        momentumDotSpin, rightBoostX, rightBoostY, rightBoostZ,
        spinX, spinY, spinZ,
        circularMinus,
        InfoGeometry.Optics.JonesPoincareSphere.JonesSpinor.circularMinusProjector,
        InfoGeometry.Optics.FiniteJonesModel.pProjector,
        InfoGeometry.Optics.FiniteJonesModel.diagJones,
        σ1, σ2, σ3, Matrix.mul_apply] <;>
      ring_nf <;>
      simp (config := { failIfUnchanged := false }) only [Complex.I_sq] <;>
      ring

/-- Paired finite Wigner-helicity packet on a future null `z` ray. -/
theorem pauliLubanski_nullZ_helicity_packet
    (E : ℂ) (mu : Fin 4) :
    pauliLubanskiComponent (nullZMomentum E) mu * circularPlus =
        (((2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularPlus) ∧
      rightPauliLubanskiComponent (nullZMomentum E) mu * circularMinus =
        ((-(2 : ℂ)⁻¹ * momentumComponent (nullZMomentum E) mu) • circularMinus) :=
  ⟨pauliLubanski_nullZ_positive_helicity E mu,
    pauliLubanski_nullZ_negative_helicity E mu⟩

/-- Transport the Pauli--Lubanski quadratic Casimir through the existing
matrix-to-operator-Zorn equivalence. -/
def zornPauliLubanskiSq (P : PauliMomentum) : OperatorZornC :=
  zornLift (pauliLubanskiSq P)

/-- Internal spin-half Casimir lifted to the operator-Zorn carrier. -/
def zornSpinHalfCasimir : OperatorZornC :=
  zornLift spinHalfCasimir

/-- The second Poincare Casimir is scalar-central in the chiral operator-Zorn
coordinates. -/
theorem zornPauliLubanski_sq (P : PauliMomentum) :
    zornPauliLubanskiSq P =
      ({ n_plus_op := -(3 / 4 : ℂ) * massCasimir P,
         n_minus_op := -(3 / 4 : ℂ) * massCasimir P,
         sigma_plus_op := 0,
         sigma_minus_op := 0 } : OperatorZornC) := by
  apply (equivMatrix (A := ℂ)).injective
  simp [zornPauliLubanskiSq, zornLift, ofMatrix, toMatrix,
    pauliLubanski_sq_eq_three_quarters_mass]

/-- Operator-Zorn second Casimir as the product of the external mass Casimir
and the already-lifted internal spin Casimir. -/
theorem zornPauliLubanski_sq_eq_mass_spin (P : PauliMomentum) :
    zornPauliLubanskiSq P =
      zornLift (-(massCasimir P) • spinHalfCasimir) := by
  simp [zornPauliLubanskiSq, pauliLubanski_sq_eq_mass_spin_casimir]

/-- Consolidated finite Poincare spin packet. -/
theorem pauliLubanski_spin_half_packet (P : PauliMomentum) :
    momentumPauliLubanskiContraction P = 0 ∧
      pauliLubanskiSq P = -(massCasimir P) • spinHalfCasimir ∧
      toMatrix (zornPauliLubanskiSq P) =
        (-(3 / 4 : ℂ) * massCasimir P) • (1 : Mat2C) := by
  refine ⟨pauliLubanski_momentum_orthogonal P,
    pauliLubanski_sq_eq_mass_spin_casimir P, ?_⟩
  simp [zornPauliLubanskiSq, pauliLubanski_sq_eq_three_quarters_mass]

set_option maxHeartbeats 2000000 in
/-- The six independent Pauli--Lubanski commutators in the convention of
this owner.  The temporal--spatial equations carry a minus sign because
the left-handed boosts are defined by Kᵢ = -i Sᵢ; this is checked directly
from the Pauli multiplication table. -/
theorem pauliLubanski_commutator_packet (P : PauliMomentum) :
    pauliLubanski0 P * pauliLubanski1 P -
          pauliLubanski1 P * pauliLubanski0 P =
        (-Complex.I) •
          (P.py • pauliLubanski3 P - P.pz • pauliLubanski2 P) ∧
      pauliLubanski0 P * pauliLubanski2 P -
          pauliLubanski2 P * pauliLubanski0 P =
        (-Complex.I) •
          (P.pz • pauliLubanski1 P - P.px • pauliLubanski3 P) ∧
      pauliLubanski0 P * pauliLubanski3 P -
          pauliLubanski3 P * pauliLubanski0 P =
        (-Complex.I) •
          (P.px • pauliLubanski2 P - P.py • pauliLubanski1 P) ∧
      pauliLubanski1 P * pauliLubanski2 P -
          pauliLubanski2 P * pauliLubanski1 P =
        Complex.I • (P.E • pauliLubanski3 P - P.pz • pauliLubanski0 P) ∧
      pauliLubanski2 P * pauliLubanski3 P -
          pauliLubanski3 P * pauliLubanski2 P =
        Complex.I • (P.E • pauliLubanski1 P - P.px • pauliLubanski0 P) ∧
      pauliLubanski3 P * pauliLubanski1 P -
          pauliLubanski1 P * pauliLubanski3 P =
        Complex.I • (P.E • pauliLubanski2 P - P.py • pauliLubanski0 P) := by
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    calc (Complex.I : ℂ) ^ 3 = Complex.I ^ 2 * Complex.I := by ring
    _ = -Complex.I := by rw [Complex.I_sq, neg_one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliLubanski0, pauliLubanski1, pauliLubanski2,
      pauliLubanski3, momentumDotSpin, boostX, boostY, boostZ,
      spinX, spinY, spinZ, σ1, σ2, σ3] <;>
    ring_nf <;>
    simp (config := { failIfUnchanged := false }) only [Complex.I_sq, hI3] <;>
    ring

end InfoGeometry.Canonical.OperatorPauliLubanskiLift
