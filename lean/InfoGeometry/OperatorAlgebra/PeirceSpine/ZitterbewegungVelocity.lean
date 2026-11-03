/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DiracPolynomialAction
import InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness

/-!
# Chiral zitterbewegung velocity and two-connection curvature

Completes the Dirac polynomial archetype row on the `[Ring B]` Peirce carrier.
`DiracPolynomialAction` owns the dispersion law `peirceMassDirac² = 1 + V`
(`peirce_mass_dirac_square`) and the quartic action decomposition
`D⁴ - D² = 2V + δ(V)`.  This file adds the two kinetic identities that were
still missing on this carrier, and one falsification:

1. **Chiral zitterbewegung velocity (`SA₃`).**
   `zitterVelocity P A C := comm (peirceMassDirac P A C) (invS P)` equals
   `-(2 : ℤ) • genJ P A C`; it squares to `-(4 : ℤ) • genV P A C`; the chiral
   partner `comm (peirceChiralDirac P A C) (invS P)` equals
   `-(2 : ℤ) • genPhi P A C`; and the second-order oscillation is the exact
   ring identity `comm D (comm D J) = 4 • (D² J)`.
2. **Two-connection square (corrected `SA₄`).**  For the two one-form
   connections `genPhi P A₁ C₁` and `genJ P A₂ C₂`, the true square is
   `(Φ₁ + J₂)² = (genV P A₁ C₁ - genV P A₂ C₂) + {Φ₁, J₂}`, and the cross
   anticommutator is central under the cut: `comm P {Φ₁, J₂} = 0`.
3. **Falsified raw claim (`SA₄` as stated).**  The raw stream's stronger
   "field-strength" regularization
   `(Φ₁ + J₂)² = (V₁ - V₂) - F₁₂` with
   `F₁₂ = [conePlus P A₁, coneMinus P C₂] - [conePlus P A₂, coneMinus P C₁]`
   is not a ring identity.  `cross_connection_field_strength_counterexample`
   refutes it in `M₂(ℚ)` using the shared nontrivial idempotent cut of
   `PeirceDefectMatrixWitness` and the two matrix units `E₁₂`, `E₂₁`.

All statements are pure path-algebra identities proved by `peirce_nf` (the
confluent corner normal form of `PeirceSpine.Basic`) or by entrywise finite
matrix evaluation.  No analytic spectral triple, Hamiltonian, ODE flow, or
frequency is asserted anywhere.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype `SA₃` (`zitterVelocity`).** The velocity operator of the
massive Peirce Dirac operator: the commutator of
`peirceMassDirac P A C = invS P + genPhi P A C` with the chirality grading
`invS P`. -/
def zitterVelocity (P A C : B) : B := comm (peirceMassDirac P A C) (invS P)

/-- **Two-connection mixed curvature.** The cross anticommutator of the
one-form operator `genPhi P A₁ C₁` with the bivector operator
`genJ P A₂ C₂`. -/
def crossConnectionAnticommutator (P A₁ C₁ A₂ C₂ : B) : B :=
  anticomm (genPhi P A₁ C₁) (genJ P A₂ C₂)

section VelocityLaws

variable {P : B} (hP : P * P = P)
include hP

/-- The chiral zitterbewegung velocity is the bivector `J` doubled. -/
theorem zitterVelocity_genJ (A C : B) :
    zitterVelocity P A C = -(2 : ℤ) • genJ P A C := by
  unfold zitterVelocity peirceMassDirac
  peirce_nf hP

/-- The chiral zitterbewegung velocity squares to minus four times the even
metric `V`. -/
theorem zitterVelocity_square (A C : B) :
    zitterVelocity P A C * zitterVelocity P A C = -(4 : ℤ) • genV P A C := by
  unfold zitterVelocity peirceMassDirac
  peirce_nf hP

/-- The chiral partner velocity is the one-form `Φ` doubled. -/
theorem peirceChiralDirac_velocity_genPhi (A C : B) :
    comm (peirceChiralDirac P A C) (invS P) = -(2 : ℤ) • genPhi P A C := by
  unfold peirceChiralDirac
  peirce_nf hP

/-- **Zitterbewegung oscillation.** The second velocity commutator is an
exact harmonic identity: with `D = peirceMassDirac P A C` and `D² = 1 + V`
(`peirce_mass_dirac_square`), `comm D (comm D J) = 4 • (D² J)`. -/
theorem zitter_velocity_oscillation (A C : B) :
    comm (peirceMassDirac P A C) (comm (peirceMassDirac P A C) (genJ P A C))
        = (4 : ℤ) • (peirceMassDirac P A C * peirceMassDirac P A C * genJ P A C) := by
  unfold peirceMassDirac
  peirce_nf hP

/-- The first commutator in the oscillation law separates the one-form and
spin-curvature terms: `[D,J] = 2Φ - 2Σ`. -/
theorem peirceMassDirac_comm_genJ (A C : B) :
    comm (peirceMassDirac P A C) (genJ P A C) =
      (2 : ℤ) • genPhi P A C - (2 : ℤ) • genSig P A C := by
  unfold peirceMassDirac
  peirce_nf hP

/-- The oscillation law expanded in the two directed nilpotent cones. The
cubic terms are retained because they need not vanish in a general ring. -/
theorem zitter_velocity_oscillation_expanded (A C : B) :
    comm (peirceMassDirac P A C)
        (comm (peirceMassDirac P A C) (genJ P A C)) =
      (4 : ℤ) • genJ P A C -
        (4 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C) +
        (4 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A) := by
  unfold peirceMassDirac
  peirce_nf hP

end VelocityLaws

section TwoConnection

variable {P : B} (hP : P * P = P)
include hP

/-- **True two-connection square (corrected `SA₄`).** The Dirac square of
the two-connection sum decomposes exactly as the difference of the two
corner metrics plus the cross anticommutator; no field-strength
regularization term exists. -/
theorem twoConnectionDiracSquare (A₁ C₁ A₂ C₂ : B) :
    (genPhi P A₁ C₁ + genJ P A₂ C₂) * (genPhi P A₁ C₁ + genJ P A₂ C₂)
        = (genV P A₁ C₁ - genV P A₂ C₂)
          + crossConnectionAnticommutator P A₁ C₁ A₂ C₂ := by
  unfold crossConnectionAnticommutator
  peirce_nf hP

/-- The two-connection cross anticommutator is central under the cut: each
mixed double-corner product `N₊₁ N₋₂`, `N₊₂ N₋₁` commutes with `P` and each
same-sheet product `N₋₁ N₊₂`, `N₋₂ N₊₁` is annihilated on both sides. -/
theorem crossConnectionAnticommutator_cut_central (A₁ C₁ A₂ C₂ : B) :
    comm P (crossConnectionAnticommutator P A₁ C₁ A₂ C₂) = 0 := by
  unfold crossConnectionAnticommutator
  peirce_nf hP

end TwoConnection

/- **Glide-pair reflection (the Möbius sign ledger).**  The two cone
generators form a σ-glide pair: `Φ = conePlus + coneMinus` and
`J = conePlus - coneMinus`, so their anticommutator resolves as
`2 • (conePlus² - coneMinus²)` — an even slot — while their plain
commutator `ΦJ - JΦ` keeps the unmatched cross-terms
`±(conePlus · coneMinus) ∓ (coneMinus · conePlus)`.  The raw `SA₄`
"field-strength" substitution of this even slot by a commutator slot is
exactly the failure to acknowledge the glide reflection: on the
`M₂(ℚ)` witness the unmatched cross-terms appear as the sheet swap
`E₁₂E₂₁ = cut` vs `E₂₁E₁₂ = 1 - cut` (the Möbius half-twist), which
`cross_connection_field_strength_counterexample` exhibits as the anomaly.
The σ-glide conjugation itself
(`invS P * genPhi P A C = genJ P A C`,
`genPhi P A C * invS P = -genJ P A C`) is owned in
`InfoGeometry.Physics.CobaltAsymmetryDependency`; this row is its
anticommutator shadow at ring level.  Pure pull-apart algebra: no cut
hypothesis is used. -/
theorem glide_pair_reflection (P A C : B) :
    genPhi P A C * genJ P A C + genJ P A C * genPhi P A C
      = (2 : ℤ) • (conePlus P A * conePlus P A - coneMinus P C * coneMinus P C) := by
  unfold genPhi genJ conePlus coneMinus
  noncomm_ring

section MasterSynthesis

variable {P : B} (hP : P * P = P)
include hP

/-- **Master synthesis of the kinetic row.** -/
theorem zitterbewegung_velocity_master_synthesis
    (A C A₁ C₁ A₂ C₂ : B) :
    zitterVelocity P A C = -(2 : ℤ) • genJ P A C ∧
      zitterVelocity P A C * zitterVelocity P A C = -(4 : ℤ) • genV P A C ∧
      comm (peirceChiralDirac P A C) (invS P) = -(2 : ℤ) • genPhi P A C ∧
      comm (peirceMassDirac P A C) (comm (peirceMassDirac P A C) (genJ P A C))
        = (4 : ℤ) • (peirceMassDirac P A C * peirceMassDirac P A C * genJ P A C) ∧
      (genPhi P A₁ C₁ + genJ P A₂ C₂) * (genPhi P A₁ C₁ + genJ P A₂ C₂)
        = (genV P A₁ C₁ - genV P A₂ C₂)
          + crossConnectionAnticommutator P A₁ C₁ A₂ C₂ ∧
      comm P (crossConnectionAnticommutator P A₁ C₁ A₂ C₂) = 0 := by
  refine ⟨zitterVelocity_genJ hP A C, zitterVelocity_square hP A C,
    peirceChiralDirac_velocity_genPhi hP A C, zitter_velocity_oscillation hP A C,
    twoConnectionDiracSquare hP A₁ C₁ A₂ C₂,
    crossConnectionAnticommutator_cut_central hP A₁ C₁ A₂ C₂⟩

end MasterSynthesis

section MatrixCounterexample

open InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness

/-- The upper matrix unit `E₁₂`, the nonzero `conePlus` corner of the cut. -/
def unitUpper : Op := !![0, 1; 0, 0]

/-- The lower matrix unit `E₂₁`, the nonzero `coneMinus` corner of the cut. -/
def unitLower : Op := !![0, 0; 1, 0]

/-- The upper unit is exactly the forward corner of the cut. -/
theorem conePlus_cut_unitUpper : conePlus cut unitUpper = unitUpper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conePlus, cut, unitUpper, Matrix.mul_apply, Matrix.one_apply,
      Matrix.sub_apply, Fin.sum_univ_two]

/-- The lower unit is exactly the backward corner of the cut. -/
theorem coneMinus_cut_unitLower : coneMinus cut unitLower = unitLower := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coneMinus, cut, unitLower, Matrix.mul_apply, Matrix.one_apply,
      Matrix.sub_apply, Fin.sum_univ_two]

/-- The vanishing products of the two matrix units. -/
theorem unitUpper_mul_unitUpper : unitUpper * unitUpper = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitUpper, Matrix.mul_apply, Fin.sum_univ_two]

theorem unitLower_mul_unitLower : unitLower * unitLower = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitLower, Matrix.mul_apply, Fin.sum_univ_two]

/-- The graded cross products: `E₁₂ E₂₁ = E₁₁` and `E₂₁ E₁₂ = E₂₂ = 1 - cut`. -/
theorem unitUpper_mul_unitLower : unitUpper * unitLower = cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitUpper, unitLower, cut, Matrix.mul_apply, Fin.sum_univ_two]

theorem unitLower_mul_unitUpper : unitLower * unitUpper = 1 - cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unitUpper, unitLower, cut, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The generators collapse to the two matrix units on this witness pair. -/
theorem genPhi_cut_zero_unitLower : genPhi cut (0 : Op) unitLower = unitLower := by
  rw [genPhi, conePlus_zero, zero_add, coneMinus_cut_unitLower]

theorem genJ_cut_unitUpper_zero : genJ cut unitUpper (0 : Op) = unitUpper := by
  rw [genJ, coneMinus_zero, sub_zero, conePlus_cut_unitUpper]

/-- The two-connection square evaluates to the identity matrix. -/
theorem twoConnections_square_eq_one :
    (genPhi cut (0 : Op) unitLower + genJ cut unitUpper (0 : Op)) *
        (genPhi cut (0 : Op) unitLower + genJ cut unitUpper (0 : Op)) = 1 := by
  rw [genPhi_cut_zero_unitLower, genJ_cut_unitUpper_zero]
  simp only [Matrix.add_mul, Matrix.mul_add]
  simp [unitUpper_mul_unitUpper, unitLower_mul_unitUpper, unitUpper_mul_unitLower,
    unitLower_mul_unitLower]

/-- The raw field-strength right side evaluates to `E₁₁ - E₂₂`. -/
theorem fieldStrength_rhs_eq_cut_sub :
    (genV cut (0 : Op) unitLower - genV cut unitUpper (0 : Op)) -
      (comm (conePlus cut (0 : Op)) (coneMinus cut (0 : Op)) -
        comm (conePlus cut unitUpper) (coneMinus cut unitLower))
      = cut - (1 - cut) := by
  have hV1 : genV cut (0 : Op) unitLower = 0 := by
    simp [genV, anticomm, conePlus_zero, coneMinus_cut_unitLower, zero_mul, mul_zero]
  have hV2 : genV cut unitUpper (0 : Op) = 0 := by
    simp [genV, anticomm, conePlus_cut_unitUpper, coneMinus_zero, zero_mul, mul_zero]
  have hC12 : comm (conePlus cut (0 : Op)) (coneMinus cut (0 : Op)) = 0 := by
    simp [comm, conePlus_zero, coneMinus_zero, mul_zero]
  have hC21 : comm (conePlus cut unitUpper) (coneMinus cut unitLower)
      = cut - (1 - cut) := by
    rw [conePlus_cut_unitUpper, coneMinus_cut_unitLower]
    simp only [comm]
    rw [unitUpper_mul_unitLower, unitLower_mul_unitUpper]
  rw [hV1, hV2, hC12, hC21]
  simp [zero_sub]

/-- The concrete `Fin 2` entry separating the two sides of the raw `SA₄`
field-strength claim: at index `(1,1)`, the square has value `1` and the
proposed right side has value `-1`. -/
theorem field_strength_witness_bottom_right_entries :
    ((genPhi cut (0 : Op) unitLower + genJ cut unitUpper (0 : Op)) *
        (genPhi cut (0 : Op) unitLower + genJ cut unitUpper (0 : Op))) 1 1 = 1 ∧
      ((genV cut (0 : Op) unitLower - genV cut unitUpper (0 : Op)) -
        (comm (conePlus cut (0 : Op)) (coneMinus cut (0 : Op)) -
          comm (conePlus cut unitUpper) (coneMinus cut unitLower))) 1 1 = -1 := by
  constructor
  · rw [twoConnections_square_eq_one]
    norm_num [Matrix.one_apply]
  · rw [fieldStrength_rhs_eq_cut_sub]
    norm_num [cut, Matrix.one_apply, Matrix.sub_apply]

/-- **Socratic aporia: the raw `SA₄` field-strength claim is false.** In
`M₂(ℚ)` with the idempotent cut `P = diag(1, 0)`, forward amplitude
`A₂ = E₁₂` and backward amplitude `C₁ = E₂₁` (the other amplitudes zero),
the two-connection square is `(E₁₂ + E₂₁)² = 1`, while the raw stream's
proposed right side `(V₁ - V₂) - F₁₂` collapses to `E₁₁ - E₂₂ ≠ 1` at the
`(1, 1)` entry.  The correct statement is `twoConnectionDiracSquare`. -/
theorem cross_connection_field_strength_counterexample :
    ∃ A₁ C₁ A₂ C₂ : Op, cut * cut = cut ∧
      (genPhi cut A₁ C₁ + genJ cut A₂ C₂) * (genPhi cut A₁ C₁ + genJ cut A₂ C₂) ≠
        (genV cut A₁ C₁ - genV cut A₂ C₂) -
          (comm (conePlus cut A₁) (coneMinus cut C₂) -
            comm (conePlus cut A₂) (coneMinus cut C₁)) := by
  refine ⟨0, unitLower, unitUpper, 0, cut_idempotent, ?_⟩
  intro h
  rw [twoConnections_square_eq_one, fieldStrength_rhs_eq_cut_sub] at h
  have h11 := congrArg (fun M : Op => M 1 1) h
  norm_num [cut, Matrix.one_apply, Matrix.sub_apply, Matrix.of_apply] at h11

end MatrixCounterexample

end InfoGeometry.OperatorAlgebra.PeirceSpine
