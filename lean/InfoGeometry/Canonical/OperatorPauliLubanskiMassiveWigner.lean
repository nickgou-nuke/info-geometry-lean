import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorPauliLubanskiLift

/-!
# InfoGeometry.Canonical.OperatorPauliLubanskiMassiveWigner

Massive companion to the null-helicity branch of
`OperatorPauliLubanskiLift`.

The general finite Pauli--Lubanski owner already proves the six relativistic
commutator identities.  This file specializes them to the rest momentum

`P = (m,0,0,0)`

and records the finite spin-`1/2` Wigner little-group algebra:

* `W^0 = 0`;
* `W^i = m S_i`;
* `[W_i,W_j] = i m ε_{ijk} W_k`;
* `W^2 = -(3/4) m^2 I_2`.

No orbital differential operator, Hilbert-space domain, or continuous-group
construction is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorPauliLubanskiMassiveWigner

open Matrix
open scoped BigOperators
open InfoGeometry.Canonical.OperatorZornSpinCasimirLift
open InfoGeometry.Canonical.OperatorPauliLubanskiLift

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Massive rest-frame momentum `(m,0,0,0)`. -/
def massiveRestMomentum (m : ℂ) : PauliMomentum :=
  ⟨m, 0, 0, 0⟩

@[simp] theorem massiveRestMomentum_massCasimir (m : ℂ) :
    massCasimir (massiveRestMomentum m) = m ^ 2 := by
  simp [massCasimir, massiveRestMomentum]

/-- In the rest frame the Pauli--Lubanski time component vanishes. -/
@[simp] theorem massive_pauliLubanski0 (m : ℂ) :
    pauliLubanski0 (massiveRestMomentum m) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLubanski0, momentumDotSpin, massiveRestMomentum]

/-- First spatial component is `m S₁`. -/
@[simp] theorem massive_pauliLubanski1 (m : ℂ) :
    pauliLubanski1 (massiveRestMomentum m) = m • spinX := by
  simp [pauliLubanski1, massiveRestMomentum]

/-- Second spatial component is `m S₂`. -/
@[simp] theorem massive_pauliLubanski2 (m : ℂ) :
    pauliLubanski2 (massiveRestMomentum m) = m • spinY := by
  simp [pauliLubanski2, massiveRestMomentum]

/-- Third spatial component is `m S₃`. -/
@[simp] theorem massive_pauliLubanski3 (m : ℂ) :
    pauliLubanski3 (massiveRestMomentum m) = m • spinZ := by
  simp [pauliLubanski3, massiveRestMomentum]

/-- Spatial rest-frame Pauli--Lubanski vector. -/
def massiveW (m : ℂ) : Fin 3 → Mat2C
  | 0 => pauliLubanski1 (massiveRestMomentum m)
  | 1 => pauliLubanski2 (massiveRestMomentum m)
  | 2 => pauliLubanski3 (massiveRestMomentum m)

/-- Spin generator packet in spatial order `(S₁,S₂,S₃)`. -/
def spinSpatial : Fin 3 → Mat2C
  | 0 => spinX
  | 1 => spinY
  | 2 => spinZ

/-- Uniform rest-frame identity `W_i = m S_i`. -/
theorem massiveW_eq_mass_smul_spin (m : ℂ) (i : Fin 3) :
    massiveW m i = m • spinSpatial i := by
  fin_cases i <;> simp [massiveW, spinSpatial]

/-- First cyclic little-group commutator `[W₁,W₂] = i m W₃`. -/
theorem massive_W1_W2_commutator (m : ℂ) :
    massiveW m 0 * massiveW m 1 - massiveW m 1 * massiveW m 0 =
      (Complex.I * m) • massiveW m 2 := by
  rcases pauliLubanski_commutator_packet (massiveRestMomentum m) with
    ⟨_, _, _, h12, _, _⟩
  simpa [massiveW, massiveRestMomentum, smul_smul] using h12

/-- Second cyclic little-group commutator `[W₂,W₃] = i m W₁`. -/
theorem massive_W2_W3_commutator (m : ℂ) :
    massiveW m 1 * massiveW m 2 - massiveW m 2 * massiveW m 1 =
      (Complex.I * m) • massiveW m 0 := by
  rcases pauliLubanski_commutator_packet (massiveRestMomentum m) with
    ⟨_, _, _, _, h23, _⟩
  simpa [massiveW, massiveRestMomentum, smul_smul] using h23

/-- Third cyclic little-group commutator `[W₃,W₁] = i m W₂`. -/
theorem massive_W3_W1_commutator (m : ℂ) :
    massiveW m 2 * massiveW m 0 - massiveW m 0 * massiveW m 2 =
      (Complex.I * m) • massiveW m 1 := by
  rcases pauliLubanski_commutator_packet (massiveRestMomentum m) with
    ⟨_, _, _, _, _, h31⟩
  simpa [massiveW, massiveRestMomentum, smul_smul] using h31

/-- Three-dimensional Levi--Civita symbol in the spatial basis. -/
def epsilon3 : Fin 3 → Fin 3 → Fin 3 → ℂ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 1, 0, 2 => -1
  | 2, 1, 0 => -1
  | 0, 2, 1 => -1
  | _, _, _ => 0

/-- Full massive `su(2)` little-group relation
`[W_i,W_j] = i m ∑_k ε_{ijk} W_k`. -/
theorem massive_pauliLubanski_su2
    (m : ℂ) (i j : Fin 3) :
    massiveW m i * massiveW m j - massiveW m j * massiveW m i =
      (Complex.I * m) • (∑ k : Fin 3, epsilon3 i j k • massiveW m k) := by
  fin_cases i <;> fin_cases j
  · simp [epsilon3]
  · simpa [epsilon3, Fin.sum_univ_three] using massive_W1_W2_commutator m
  · have h := massive_W3_W1_commutator m
    simpa [epsilon3, Fin.sum_univ_three, sub_eq_neg_add] using congrArg Neg.neg h
  · have h := massive_W1_W2_commutator m
    simpa [epsilon3, Fin.sum_univ_three, sub_eq_neg_add] using congrArg Neg.neg h
  · simp [epsilon3]
  · simpa [epsilon3, Fin.sum_univ_three] using massive_W2_W3_commutator m
  · simpa [epsilon3, Fin.sum_univ_three] using massive_W3_W1_commutator m
  · have h := massive_W2_W3_commutator m
    simpa [epsilon3, Fin.sum_univ_three, sub_eq_neg_add] using congrArg Neg.neg h
  · simp [epsilon3]

/-- Massive rest-frame quadratic Casimir. -/
theorem massive_pauliLubanski_sq (m : ℂ) :
    pauliLubanskiSq (massiveRestMomentum m) =
      (-(3 / 4 : ℂ) * m ^ 2) • (1 : Mat2C) := by
  simpa [massiveRestMomentum_massCasimir] using
    pauliLubanski_sq_eq_three_quarters_mass (massiveRestMomentum m)

/-- Massive finite Wigner packet: rest-frame reduction, `su(2)` closure, and
spin-`1/2` quadratic Casimir. -/
theorem massive_wigner_spin_half_packet (m : ℂ) :
    pauliLubanski0 (massiveRestMomentum m) = 0 ∧
      (∀ i : Fin 3, massiveW m i = m • spinSpatial i) ∧
      (∀ i j : Fin 3,
        massiveW m i * massiveW m j - massiveW m j * massiveW m i =
          (Complex.I * m) •
            (∑ k : Fin 3, epsilon3 i j k • massiveW m k)) ∧
      pauliLubanskiSq (massiveRestMomentum m) =
        (-(3 / 4 : ℂ) * m ^ 2) • (1 : Mat2C) := by
  exact ⟨massive_pauliLubanski0 m,
    massiveW_eq_mass_smul_spin m,
    massive_pauliLubanski_su2 m,
    massive_pauliLubanski_sq m⟩

end InfoGeometry.Canonical.OperatorPauliLubanskiMassiveWigner

