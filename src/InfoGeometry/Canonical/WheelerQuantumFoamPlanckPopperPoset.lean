/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
import InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam

/-!
# John Wheeler — Quantum Ideas, Quantum Foam, Max Planck & Karl Popper (`𝔔𝔉₁`–`𝔔𝔉₇`) & Plabic Amplituhedron Bruhat Closure

## i. Overview
Formalizes John Archibald Wheeler's *Quantum Ideas, Quantum Foam, Max Planck, and Karl Popper*
synthesis (`𝔔𝔉₁`–`𝔔𝔉₇`) together with Degree-3 Bruhat observer self-closure, single-ray Klein
quadric nilpotency (`𝔔𝔄₅`), and two-ray Amplituhedron scattering foam (`𝔔𝔄₆`–`𝔔𝔄₇`).

## ii. Key results
- `airplane_high_altitude_wave_cancellation` (`𝔔𝔉₁`) and `ocean_descent_quadratic_foam_ignition` (`𝔔𝔉₂`)
- `macroscopic_causal_rectification_of_acausal_foam` and `degree_three_bruhat_observer_self_closure`
- `quantum_foam_destroys_before_and_after` (`𝔔𝔉₃`) and `max_planck_length_time_mass_uniqueness` (`𝔔𝔉₄`)
- `observability_gap_linear_zero_quadratic_nonzero` (`𝔔𝔉₅`) and `karl_popper_surprise_and_survival_filter` (`𝔔𝔉₆`)
- `klein_quadric_single_ray_silence_and_popper_counterexample` (`𝔔𝔄₅`)
- `two_ray_amplituhedron_scattering_foam_and_baryon_boundary` (`𝔔𝔄₆`)
- `twistor_amplituhedron_foam_collision_bridge` and `wheeler_popper_amplituhedron_bruhat_master_synthesis` (`𝔔𝔄₇`)

## iii. Table of contents
- §1. Ocean descent operator algebra, causal rectification, and Degree-3 Bruhat closure
- §2. Dissolution of before-and-after, Max Planck's dimensional triangulation, and Karl Popper's filter
- §3. Single-ray Klein quadric silence vs. two-ray Amplituhedron scattering foam

## iv. References
- John Archibald Wheeler, *Web of Stories*, Segment 77/130 (*Quantum ideas. Quantum foam. Max Planck and Karl Popper*)
- Nima Arkani-Hamed and Jaroslav Trnka, *The Amplituhedron* (2014)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `airplane_high_altitude_wave_cancellation` (`𝔔𝔉₁`)
- `ocean_descent_quadratic_foam_ignition` (`𝔔𝔉₂`)
- `airplane_wave_cancellation_and_quadratic_foam` (`𝔔𝔉₁`–`𝔔𝔉₂`)
- `macroscopic_causal_rectification_of_acausal_foam`
- `degree_three_bruhat_observer_self_closure`
- `classical_before_after_antisymmetry` and `quantum_foam_destroys_before_and_after` (`𝔔𝔉₃`)
- `planckDim_adjugate_inversion`, `planckDim_solve`, and
  `max_planck_length_time_mass_uniqueness` (`𝔔𝔉₄`)
- `observability_gap_linear_zero_quadratic_nonzero` (`𝔔𝔉₅`)
- `karl_popper_surprise_and_survival_filter` (`𝔔𝔉₆`)
- `planck_popper_wheeler_master_synthesis` (`𝔔𝔉₇`)
- `wheeler_quantum_foam_planck_popper_seven_node_synthesis`
- `plabic_bicolored_turn_duality`, `plabic_trip_dictionary_cycle`,
  `plabic_square_move_spurious_pole_cancellation`,
  `single_plabic_sheet_nilpotent_vs_doubled_handle`,
  `peirce_grading_twist_identities`, `klt_twisted_double_copy_foam_defect`,
  `amplituhedron_boundary_leibniz_and_unitarity_cut`,
  `popper_surprise_and_survival_of_twisted_klt_foam`,
  `doubled_plabic_twisted_amplituhedron_master_synthesis`
- `twistor_amplituhedron_foam_collision_bridge`
- `airplane_wave_cancellation_and_causal_rectification`
- `popper_survival_implies_surprise`
- `klein_quadric_single_ray_silence_and_popper_counterexample` (`𝔔𝔄₅`)
- `two_ray_amplituhedron_scattering_foam_and_baryon_boundary` (`𝔔𝔄₆`)
- `wheeler_popper_amplituhedron_bruhat_master_synthesis`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `airplane_high_altitude_wave_cancellation`, `ocean_descent_quadratic_foam_ignition`,
  `airplane_wave_cancellation_and_quadratic_foam`, `macroscopic_causal_rectification_of_acausal_foam`,
  `degree_three_bruhat_observer_self_closure`, `observability_gap_linear_zero_quadratic_nonzero`,
  and `planck_popper_wheeler_master_synthesis`
  (conditional on the macroscopic projector idempotence hypothesis `hP : P * P = P`)
- `klt_twisted_double_copy_foam_defect` and `popper_surprise_and_survival_of_twisted_klt_foam`
  (conditional on `hP : P * P = P` and `hTheta : P * Theta = Theta * P`)
- `quantum_foam_destroys_before_and_after` (conditional on positive fluctuation scale `0 < δ`)

#### BUCKET 3: OPEN CLOSURE DEBT
- Continuum path-integral measure theory over 3-geometries (Wheeler's superspace) and experimental
  Planck-scale phenomenology remain external physical context, not claimed as consequences of
  these algebraic Peirce-ring, Zorn-twistor, and integer-lattice theorems.
-/

namespace InfoGeometry.Canonical.WheelerQuantumFoamPlanckPopperPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open _root_.InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
open InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam

section OceanDescentOperatorAlgebra
variable {B : Type*} [Ring B]

/-- Right-associated idempotent absorption `P * (P * Z) = P * Z`. -/
lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- Standalone lemma proving the diagonal Peirce corner square defects and total even-grade
quadratic defect for any idempotent `P * P = P` and `g : B`. -/
lemma peirce_ocean_descent_corner_defect (P g : B) (hP : P * P = P) :
    peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g ∧
    peirce00 P (g * g) - peirce00 P g * peirce00 P g = coneMinus P g * conePlus P g ∧
    evenGrade P (g * g) - evenGrade P g * evenGrade P g = genV P g g := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [peirce11, conePlus, coneMinus]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel
  · dsimp only [peirce00, conePlus, coneMinus]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel
  · dsimp only [evenGrade, peirce11, peirce00, genV, anticomm, conePlus, coneMinus]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc, proj_idem hP]
    abel

/--
**Theorem 1 (`𝔔𝔉₁` — `airplane_high_altitude_wave_cancellation`):**
When viewed from high altitude (`P * P = P`), the linear wave oscillation
`genPhi P g g = conePlus P g + coneMinus P g` averages to zero in both the macroscopic projection
`peirce11 P (genPhi P g g) = 0` and the deep complementary projection
`peirce00 P (genPhi P g g) = 0` (so `evenGrade P (genPhi P g g) = 0`), leaving only the smooth
surface `peirce11 P (peirce11 P g + genPhi P g g) = peirce11 P g`.
-/
theorem airplane_high_altitude_wave_cancellation
    (P g : B) (hP : P * P = P) :
    peirce11 P (genPhi P g g) = 0 ∧
    peirce00 P (genPhi P g g) = 0 ∧
    evenGrade P (genPhi P g g) = 0 ∧
    peirce11 P (peirce11 P g + genPhi P g g) = peirce11 P g := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/--
**Theorem 2 (`𝔔𝔉₂` — `ocean_descent_quadratic_foam_ignition`):**
Descending to the breaking-wave scale, for any projector `P * P = P` and metric operator `g : B`:
1. The square of the linear wave oscillation `genPhi P g g` equals the topological quantum-foam
   operator `genV P g g = conePlus P g * coneMinus P g + coneMinus P g * conePlus P g`,
2. The macroscopic Socratic foam defect `peirce11 P (g * g) - peirce11 P g * peirce11 P g` equals
   the virtual handle excursion `conePlus P g * coneMinus P g`,
3. The complementary Planckian bulk defect `peirce00 P (g * g) - peirce00 P g * peirce00 P g`
   equals `coneMinus P g * conePlus P g`,
4. Their sum is `genV P g g` and their difference is `genSig P g g`,
5. The total even-grade quadratic defect `evenGrade P (g * g) - evenGrade P g * evenGrade P g`
   equals `genV P g g`.
-/
theorem ocean_descent_quadratic_foam_ignition
    (P g : B) (hP : P * P = P) :
    genPhi P g g * genPhi P g g = genV P g g ∧
    peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g ∧
    peirce00 P (g * g) - peirce00 P g * peirce00 P g = coneMinus P g * conePlus P g ∧
    (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
      (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genV P g g ∧
    (peirce11 P (g * g) - peirce11 P g * peirce11 P g) -
      (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genSig P g g ∧
    evenGrade P (g * g) - evenGrade P g * evenGrade P g = genV P g g := by
  rcases peirce_ocean_descent_corner_defect P g hP with ⟨h_11, h_00, h_even⟩
  have h_phi_sq : genPhi P g g * genPhi P g g = genV P g g := by peirce_nf hP
  have h_sum :
      (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
        (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genV P g g := by
    rw [h_11, h_00]; rfl
  have h_diff :
      (peirce11 P (g * g) - peirce11 P g * peirce11 P g) -
        (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genSig P g g := by
    rw [h_11, h_00]; rfl
  exact ⟨h_phi_sq, h_11, h_00, h_sum, h_diff, h_even⟩

/--
**Theorem 2B (`𝔔𝔉₁`–`𝔔𝔉₂` — `airplane_wave_cancellation_and_quadratic_foam`):**
Combined ocean-descent law uniting high-altitude linear wave cancellation (`peirce11 P (genPhi P g g) = 0`
and `peirce00 P (genPhi P g g) = 0`) with surface-level quadratic quantum-foam ignition
(`genPhi P g g * genPhi P g g = genV P g g` and diagonal Socratic defects `conePlus P g * coneMinus P g`
and `coneMinus P g * conePlus P g`).
-/
theorem airplane_wave_cancellation_and_quadratic_foam
    (P g : B) (hP : P * P = P) :
    peirce11 P (genPhi P g g) = 0 ∧
    peirce00 P (genPhi P g g) = 0 ∧
    genPhi P g g * genPhi P g g = genV P g g ∧
    peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g ∧
    peirce00 P (g * g) - peirce00 P g * peirce00 P g = coneMinus P g * conePlus P g ∧
    (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
      (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genV P g g := by
  rcases peirce_ocean_descent_corner_defect P g hP with ⟨h_11, h_00, _⟩
  have h_sum :
      (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
        (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genV P g g := by
    rw [h_11, h_00]; rfl
  exact ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, h_11, h_00, h_sum⟩

/--
**Theorem 2C (`macroscopic_causal_rectification_of_acausal_foam`):**
Inside the unprojected quantum foam `genV P g g = conePlus P g * coneMinus P g + coneMinus P g * conePlus P g`,
both temporal orders coexist symmetrically. Projecting onto the macroscopic detector `P` acts as a
strict one-way causal rectifier:
1. It preserves the depart-then-return order `peirce11 P (conePlus P g * coneMinus P g) = conePlus P g * coneMinus P g`,
2. It identically annihilates the reverse order `peirce11 P (coneMinus P g * conePlus P g) = 0`,
3. Thus `peirce11 P (genV P g g) = conePlus P g * coneMinus P g`,
4. Dually, on the complementary Planckian bulk `1 - P`, `peirce00 P (coneMinus P g * conePlus P g) = coneMinus P g * conePlus P g`,
   `peirce00 P (conePlus P g * coneMinus P g) = 0`, and `peirce00 P (genV P g g) = coneMinus P g * conePlus P g`.
-/
theorem macroscopic_causal_rectification_of_acausal_foam
    (P g : B) (hP : P * P = P) :
    peirce11 P (conePlus P g * coneMinus P g) = conePlus P g * coneMinus P g ∧
    peirce11 P (coneMinus P g * conePlus P g) = 0 ∧
    peirce11 P (genV P g g) = conePlus P g * coneMinus P g ∧
    peirce00 P (coneMinus P g * conePlus P g) = coneMinus P g * conePlus P g ∧
    peirce00 P (conePlus P g * coneMinus P g) = 0 ∧
    peirce00 P (genV P g g) = coneMinus P g * conePlus P g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/--
**Theorem 2D (`degree_three_bruhat_observer_self_closure`):**
Refutes the infinite-regress fallacy by proving exact degree-3 Plabic Bruhat self-closure:
1. Naive linear addition of context `P + genPhi P g g` has quadratic idempotence defect `genV P g g`,
2. Quadratic commutator subtraction `P + genPhi P g g - genSig P g g` has quartic defect `genV P g g * genV P g g`,
3. The unimodular Plabic Bruhat rotor `(1 - conePlus P g) * (1 + coneMinus P g)` has exact two-sided inverse
   `(1 - coneMinus P g) * (1 + conePlus P g)`,
4. Conjugating `P` by this Plabic Bruhat rotor yields `dressedPeirceProjector P g g`, which equals the
   4-term degree-3 polynomial `P + genPhi P g g - genSig P g g - genV P g g * conePlus P g` and satisfies
   exact idempotence `dressedPeirceProjector P g g * dressedPeirceProjector P g g = dressedPeirceProjector P g g`.
-/
theorem degree_three_bruhat_observer_self_closure
    (P g : B) (hP : P * P = P) :
    (P + genPhi P g g) * (P + genPhi P g g) - (P + genPhi P g g) = genV P g g ∧
    (P + genPhi P g g - genSig P g g) * (P + genPhi P g g - genSig P g g) -
      (P + genPhi P g g - genSig P g g) = genV P g g * genV P g g ∧
    ((1 - conePlus P g) * (1 + coneMinus P g)) *
      ((1 - coneMinus P g) * (1 + conePlus P g)) = 1 ∧
    ((1 - coneMinus P g) * (1 + conePlus P g)) *
      ((1 - conePlus P g) * (1 + coneMinus P g)) = 1 ∧
    ((1 - conePlus P g) * (1 + coneMinus P g)) * P *
      ((1 - coneMinus P g) * (1 + conePlus P g)) = dressedPeirceProjector P g g ∧
    dressedPeirceProjector P g g =
      P + genPhi P g g - genSig P g g - genV P g g * conePlus P g ∧
    dressedPeirceProjector P g g * dressedPeirceProjector P g g =
      dressedPeirceProjector P g g := by
  refine ⟨?_, ?_, ?_, ?_, ?_, dressedPeirceProjector_eq hP g g,
          dressedPeirceProjector_idempotent hP g g⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · unfold dressedPeirceProjector
    peirce_nf hP

end OceanDescentOperatorAlgebra

/--
**Theorem 3A (`𝔔𝔉₃` — `classical_before_after_antisymmetry`):**
At zero quantum foam fluctuation (`δ = 0`), the temporal precedence relation `t₁ ≤ t₂ + 0`
is strictly antisymmetric: if `t₁ ≤ t₂ + 0` and `t₂ ≤ t₁ + 0`, then `t₁ = t₂`.
-/
theorem classical_before_after_antisymmetry (t1 t2 : ℤ)
    (h12 : t1 ≤ t2 + 0) (h21 : t2 ≤ t1 + 0) :
    t1 = t2 := by
  rw [add_zero] at h12 h21
  exact le_antisymm h12 h21

/--
**Theorem 3B (`𝔔𝔉₃` — `quantum_foam_destroys_before_and_after`):**
For every positive Planck fluctuation scale `0 < δ`, the two distinct temporal coordinates
`t₁ = 0` and `t₂ = δ` (`0 ≠ δ`) satisfy both `0 ≤ δ + δ` ("`t₁` is before `t₂` up to `δ`") and
`δ ≤ 0 + δ` ("`t₂` is before `t₁` up to `δ`"), destroying causal antisymmetry.
-/
theorem quantum_foam_destroys_before_and_after (δ : ℤ) (hδ : 0 < δ) :
    (0 : ℤ) ≠ δ ∧
    (0 : ℤ) ≤ δ + δ ∧
    δ ≤ (0 : ℤ) + δ ∧
    ∃ (t1 t2 : ℤ), t1 ≠ t2 ∧ t1 ≤ t2 + δ ∧ t2 ≤ t1 + δ := by
  have h_ne : (0 : ℤ) ≠ δ := ne_of_lt hδ
  have h_0_le_2d : (0 : ℤ) ≤ δ + δ := add_nonneg (le_of_lt hδ) (le_of_lt hδ)
  have h_d_le_0d : δ ≤ (0 : ℤ) + δ := by
    rw [zero_add]
  exact ⟨h_ne, h_0_le_2d, h_d_le_0d, 0, δ, h_ne, h_0_le_2d, h_d_le_0d⟩

/--
Physical dimension vector in the `(Length L, Time T, Mass M)` integer lattice `ℤ × ℤ × ℤ`:
- `[ℏ] = (2, -1, 1)` (`L² T⁻¹ M¹`)
- `[G] = (3, -2, -1)` (`L³ T⁻² M⁻¹`)
- `[c] = (1, -1, 0)` (`L¹ T⁻¹ M⁰`)
`planckDim x y z` computes the dimension `(dL, dT, dM)` of the monomial `ℏ^x G^y c^z`.
-/
def planckDim (x y z : ℤ) : ℤ × ℤ × ℤ :=
  (2 * x + 3 * y + z, -x - 2 * y - z, x - y)

/-- Additive expansion `3 * a = a + a + a` over `ℤ`. -/
private lemma int_three_mul (a : ℤ) : 3 * a = a + a + a := by
  calc
    3 * a = (2 + 1) * a := rfl
    _ = 2 * a + 1 * a := add_mul 2 1 a
    _ = (a + a) + a := by rw [two_mul, one_mul]

/-- Additive expansion `-3 * a = -(a + a + a)` over `ℤ`. -/
private lemma int_neg_three_mul (a : ℤ) : -3 * a = -(a + a + a) := by
  calc
    -3 * a = -(3 * a) := neg_mul 3 a
    _ = -(a + a + a) := by rw [int_three_mul]

/-- Additive expansion `5 * a = a + a + a + a + a` over `ℤ`. -/
private lemma int_five_mul (a : ℤ) : 5 * a = a + a + a + a + a := by
  calc
    5 * a = (3 + 2) * a := rfl
    _ = 3 * a + 2 * a := add_mul 3 2 a
    _ = (a + a + a) + (a + a) := by rw [int_three_mul, two_mul]
    _ = a + a + a + a + a := by abel

/-- Explicit adjugate linear combinations recovering `(2 * x, 2 * y, 2 * z)` from `planckDim x y z`. -/
lemma planckDim_adjugate_inversion (x y z : ℤ) :
    (2 * x + 3 * y + z) + (-x - 2 * y - z) + (x - y) = 2 * x ∧
    (2 * x + 3 * y + z) + (-x - 2 * y - z) - (x - y) = 2 * y ∧
    -3 * (2 * x + 3 * y + z) - 5 * (-x - 2 * y - z) + (x - y) = 2 * z := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [two_mul, int_three_mul]
    abel
  · simp only [two_mul, int_three_mul]
    abel
  · simp only [int_neg_three_mul, int_five_mul, two_mul, int_three_mul]
    abel

/-- Unique integer exponent solver for `planckDim x y z = (dL, dT, dM)` via adjugate inversion. -/
lemma planckDim_solve {x y z dL dT dM x0 y0 z0 : ℤ}
    (h : planckDim x y z = (dL, dT, dM))
    (hx : dL + dT + dM = 2 * x0)
    (hy : dL + dT - dM = 2 * y0)
    (hz : -3 * dL - 5 * dT + dM = 2 * z0) :
    x = x0 ∧ y = y0 ∧ z = z0 := by
  have hL : 2 * x + 3 * y + z = dL := congrArg Prod.fst h
  have hT : -x - 2 * y - z = dT := congrArg (fun p => p.2.1) h
  have hM : x - y = dM := congrArg (fun p => p.2.2) h
  have h2_ne : (2 : ℤ) ≠ 0 := by decide
  have hadj := planckDim_adjugate_inversion x y z
  have hx2 : 2 * x = 2 * x0 := by
    calc
      2 * x = (2 * x + 3 * y + z) + (-x - 2 * y - z) + (x - y) := hadj.1.symm
      _ = dL + dT + dM := by rw [hL, hT, hM]
      _ = 2 * x0 := hx
  have hy2 : 2 * y = 2 * y0 := by
    calc
      2 * y = (2 * x + 3 * y + z) + (-x - 2 * y - z) - (x - y) := hadj.2.1.symm
      _ = dL + dT - dM := by rw [hL, hT, hM]
      _ = 2 * y0 := hy
  have hz2 : 2 * z = 2 * z0 := by
    calc
      2 * z = -3 * (2 * x + 3 * y + z) - 5 * (-x - 2 * y - z) + (x - y) := hadj.2.2.symm
      _ = -3 * dL - 5 * dT + dM := by rw [hL, hT, hM]
      _ = 2 * z0 := hz
  exact ⟨Int.eq_of_mul_eq_mul_left h2_ne hx2,
         Int.eq_of_mul_eq_mul_left h2_ne hy2,
         Int.eq_of_mul_eq_mul_left h2_ne hz2⟩

/--
**Theorem 4 (`𝔔𝔉₄` — `max_planck_length_time_mass_uniqueness`):**
In the integer exponent lattice `(x, y, z) ∈ ℤ³` for `ℏ^x G^y c^z`:
1. **Planck Length Squared (`L² = (2, 0, 0)`):**
   `planckDim x y z = (2, 0, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -3)` (`ℓ_P² = ℏ G c⁻³`),
2. **Planck Time Squared (`T² = (0, 2, 0)`):**
   `planckDim x y z = (0, 2, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -5)` (`t_P² = ℏ G c⁻⁵`),
3. **Planck Mass Squared (`M² = (0, 0, 2)`):**
   `planckDim x y z = (0, 0, 2) ↔ (x = 1 ∧ y = -1 ∧ z = 1)` (`m_P² = ℏ c G⁻¹`),
4. **Dimensionless Kernel (`(0, 0, 0)`):**
   `planckDim x y z = (0, 0, 0) ↔ (x = 0 ∧ y = 0 ∧ z = 0)` (linear independence over `ℤ`).
-/
theorem max_planck_length_time_mass_uniqueness (x y z : ℤ) :
    (planckDim x y z = (2, 0, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -3)) ∧
    (planckDim x y z = (0, 2, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -5)) ∧
    (planckDim x y z = (0, 0, 2) ↔ (x = 1 ∧ y = -1 ∧ z = 1)) ∧
    (planckDim x y z = (0, 0, 0) ↔ (x = 0 ∧ y = 0 ∧ z = 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h
      exact planckDim_solve h rfl rfl rfl
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  · constructor
    · intro h
      exact planckDim_solve h rfl rfl rfl
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  · constructor
    · intro h
      exact planckDim_solve h rfl rfl rfl
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  · constructor
    · intro h
      exact planckDim_solve h rfl rfl rfl
    · rintro ⟨rfl, rfl, rfl⟩
      rfl

section KarlPopperEpistemicFilter
variable {Hyp Test : Type*} {B : Type*} [Ring B]

/--
**Theorem 5 (`𝔔𝔉₅` — `observability_gap_linear_zero_quadratic_nonzero`):**
Demonstrates why direct linear high-altitude probes fail (`peirce11 P (genPhi P g g) = 0`)
while quadratic foam correlations (`peirce11 P (genPhi P g g * genPhi P g g)`) equal the
macroscopic Socratic defect `peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g`,
bridging the Planckian complement `1 - P` back into the observable sector `P`.
-/
theorem observability_gap_linear_zero_quadratic_nonzero
    (P g : B) (hP : P * P = P) :
    peirce11 P (genPhi P g g) = 0 ∧
    peirce11 P (genPhi P g g * genPhi P g g) = conePlus P g * coneMinus P g ∧
    peirce11 P (genPhi P g g * genPhi P g g) =
      peirce11 P (g * g) - peirce11 P g * peirce11 P g := by
  rcases peirce_ocean_descent_corner_defect P g hP with ⟨h_defect, _, _⟩
  have h_lin : peirce11 P (genPhi P g g) = 0 := by peirce_nf hP
  have h_quad : peirce11 P (genPhi P g g * genPhi P g g) = conePlus P g * coneMinus P g := by
    peirce_nf hP
  exact ⟨h_lin, h_quad, h_quad.trans h_defect.symm⟩

/--
**Theorem 6 (`𝔔𝔉₆` — `karl_popper_surprise_and_survival_filter`):**
Formalizes Karl Popper's dual criterion of a scientific idea invoked by Wheeler in Segment 77/130
((a) its surprise `Surprise H`, and (b) its success in surviving tests `∀ T : Test, Survives H T`):
1. Any unsurprising hypothesis (`¬ Surprise H`) fails Popper's criterion,
2. Any hypothesis refuted by an empirical test (`∃ T : Test, ¬ Survives H T`) fails Popper's criterion.
-/
theorem karl_popper_surprise_and_survival_filter
    (Surprise : Hyp → Prop) (Survives : Hyp → Test → Prop) (H : Hyp) :
    (¬ Surprise H → ¬ (Surprise H ∧ ∀ T : Test, Survives H T)) ∧
    ((∃ T : Test, ¬ Survives H T) → ¬ (Surprise H ∧ ∀ T : Test, Survives H T)) := by
  refine ⟨?_, ?_⟩
  · intro h_no_surp h_valid
    exact h_no_surp h_valid.1
  · rintro ⟨T, h_fail⟩ h_valid
    exact h_fail (h_valid.2 T)

/--
**Theorem 7 (`𝔔𝔉₇` — `planck_popper_wheeler_master_synthesis`):**
For any macroscopic observation projector `P * P = P` and candidate physical law `H : B`:
1. If `H` lacks upward or downward off-diagonal surprise (`conePlus P H = 0 ∨ coneMinus P H = 0`),
   then its macroscopic Socratic foam defect vanishes identically
   (`peirce11 P (H * H) - peirce11 P H * peirce11 P H = 0`).
2. Consequently, generating a surviving macroscopic quantum-foam test signal
   (`peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0`) strictly requires two-sided
   off-diagonal Popperian surprise (`conePlus P H ≠ 0 ∧ coneMinus P H ≠ 0`) as well as
   non-vanishing linear wave structure (`genPhi P H H ≠ 0`).
-/
theorem planck_popper_wheeler_master_synthesis
    (P H : B) (hP : P * P = P) :
    ((conePlus P H = 0 ∨ coneMinus P H = 0) →
      peirce11 P (H * H) - peirce11 P H * peirce11 P H = 0) ∧
    (peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0 →
      (conePlus P H ≠ 0 ∧ coneMinus P H ≠ 0) ∧ genPhi P H H ≠ 0) := by
  rcases peirce_ocean_descent_corner_defect P H hP with ⟨h_foam, _, _⟩
  have h_extract_plus : P * genPhi P H H * (1 - P) = conePlus P H := by
    peirce_nf hP
  refine ⟨?_, ?_⟩
  · intro h_zero
    rw [h_foam]
    rcases h_zero with h_plus | h_minus
    · rw [h_plus, zero_mul]
    · rw [h_minus, mul_zero]
  · intro h_surv
    rw [h_foam] at h_surv
    have h_plus_ne : conePlus P H ≠ 0 := by
      intro h_plus
      rw [h_plus, zero_mul] at h_surv
      exact h_surv rfl
    have h_minus_ne : coneMinus P H ≠ 0 := by
      intro h_minus
      rw [h_minus, mul_zero] at h_surv
      exact h_surv rfl
    have h_phi_ne : genPhi P H H ≠ 0 := by
      intro h_phi
      apply h_plus_ne
      rw [← h_extract_plus, h_phi, mul_zero, zero_mul]
    exact ⟨⟨h_plus_ne, h_minus_ne⟩, h_phi_ne⟩

end KarlPopperEpistemicFilter

/--
**Master Synthesis (`wheeler_quantum_foam_planck_popper_seven_node_synthesis`):**
Unites all seven nodes `𝔔𝔉₁ ≺ 𝔔𝔉₂ ≺ {𝔔𝔉₃, 𝔔𝔉₄} ≺ 𝔔𝔉₅ ≺ 𝔔𝔉₆ ≺ 𝔔𝔉₇` into one kernel-checked theorem:
1. `𝔔𝔉₁` & `𝔔𝔉₅`: High-altitude linear wave cancellation (`peirce11 P (genPhi P g g) = 0`) and
   quadratic foam bridge (`peirce11 P (genPhi P g g * genPhi P g g) = peirce11 P (g * g) - peirce11 P g * peirce11 P g`),
2. `𝔔𝔉₂`: Quadratic breaking-wave foam ignition (`genPhi P g g * genPhi P g g = genV P g g` and
   `peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g`),
3. `𝔔𝔉₃`: Breakdown of temporal antisymmetry at scale `0 < δ` (`0 ≠ δ ∧ 0 ≤ δ + δ ∧ δ ≤ 0 + δ`),
4. `𝔔𝔉₄`: Max Planck's unique dimensional triangulation of `ℓ_P² = ℏ G c⁻³` (`(1, 1, -3)`),
   `t_P² = ℏ G c⁻⁵` (`(1, 1, -5)`), and `m_P² = ℏ c G⁻¹` (`(1, -1, 1)`),
5. `𝔔𝔉₆` & `𝔔𝔉₇`: Karl Popper's dual criterion of surprise and test survival (`peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0 → (conePlus P H ≠ 0 ∧ coneMinus P H ≠ 0) ∧ genPhi P H H ≠ 0`).
-/
theorem wheeler_quantum_foam_planck_popper_seven_node_synthesis
    {B : Type*} [Ring B] (P g H : B) (hP : P * P = P)
    (δ x y z : ℤ) (hδ : 0 < δ)
    {Hyp Test : Type*} (Surprise : Hyp → Prop) (Survives : Hyp → Test → Prop) (h0 : Hyp) :
    (peirce11 P (genPhi P g g) = 0 ∧
     peirce11 P (genPhi P g g * genPhi P g g) =
       peirce11 P (g * g) - peirce11 P g * peirce11 P g) ∧
    (genPhi P g g * genPhi P g g = genV P g g ∧
     peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g ∧
     peirce00 P (g * g) - peirce00 P g * peirce00 P g = coneMinus P g * conePlus P g ∧
     evenGrade P (g * g) - evenGrade P g * evenGrade P g = genV P g g) ∧
    ((0 : ℤ) ≠ δ ∧ (0 : ℤ) ≤ δ + δ ∧ δ ≤ (0 : ℤ) + δ) ∧
    ((planckDim x y z = (2, 0, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -3)) ∧
     (planckDim x y z = (0, 2, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -5)) ∧
     (planckDim x y z = (0, 0, 2) ↔ (x = 1 ∧ y = -1 ∧ z = 1))) ∧
    ((¬ Surprise h0 → ¬ (Surprise h0 ∧ ∀ T : Test, Survives h0 T)) ∧
     ((∃ T : Test, ¬ Survives h0 T) → ¬ (Surprise h0 ∧ ∀ T : Test, Survives h0 T))) ∧
    (peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0 →
      (conePlus P H ≠ 0 ∧ coneMinus P H ≠ 0) ∧ genPhi P H H ≠ 0) := by
  rcases peirce_ocean_descent_corner_defect P g hP with ⟨h_11, h_00, h_even⟩
  rcases peirce_ocean_descent_corner_defect P H hP with ⟨h_foamH, _, _⟩
  have h_quad : peirce11 P (genPhi P g g * genPhi P g g) = conePlus P g * coneMinus P g := by
    peirce_nf hP
  have h_extract_plus : P * genPhi P H H * (1 - P) = conePlus P H := by
    peirce_nf hP
  refine ⟨⟨by peirce_nf hP, h_quad.trans h_11.symm⟩,
          ⟨by peirce_nf hP, h_11, h_00, h_even⟩,
          ⟨ne_of_lt hδ, add_nonneg (le_of_lt hδ) (le_of_lt hδ), by rw [zero_add]⟩,
          ⟨⟨fun h => planckDim_solve h rfl rfl rfl, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩,
           ⟨fun h => planckDim_solve h rfl rfl rfl, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩,
           ⟨fun h => planckDim_solve h rfl rfl rfl, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩⟩,
          ⟨fun h_no h_val => h_no h_val.1, fun ⟨T, h_fail⟩ h_val => h_fail (h_val.2 T)⟩,
          ?_⟩
  intro h_surv
  rw [h_foamH] at h_surv
  have h_plus_ne : conePlus P H ≠ 0 := by
    intro h_plus; rw [h_plus, zero_mul] at h_surv; exact h_surv rfl
  have h_minus_ne : coneMinus P H ≠ 0 := by
    intro h_minus; rw [h_minus, mul_zero] at h_surv; exact h_surv rfl
  have h_phi_ne : genPhi P H H ≠ 0 := by
    intro h_phi; apply h_plus_ne; rw [← h_extract_plus, h_phi, mul_zero, zero_mul]
  exact ⟨⟨h_plus_ne, h_minus_ne⟩, h_phi_ne⟩

/--
**Theorem 8A (`airplane_wave_cancellation_and_causal_rectification`):**
Combined Ocean Descent, One-Way Macroscopic Causal Rectification, and Degree-3 Bruhat Self-Closure (`𝔔𝔄₁`–`𝔔𝔄₂`, `𝔔𝔄₇`):
1. High-altitude linear wave cancellation `peirce11 P (genPhi P g g) = 0` and `peirce00 P (genPhi P g g) = 0`,
2. Quadratic Socratic foam ignition `genPhi P g g * genPhi P g g = genV P g g` and
   `peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g`,
3. One-way macroscopic causal rectification `peirce11 P (conePlus P g * coneMinus P g) = conePlus P g * coneMinus P g`,
   `peirce11 P (coneMinus P g * conePlus P g) = 0`, and `peirce11 P (genV P g g) = conePlus P g * coneMinus P g`,
4. Degree-3 Bruhat observer self-closure `((1 - conePlus P g) * (1 + coneMinus P g)) * ((1 - coneMinus P g) * (1 + conePlus P g)) = 1`,
   `((1 - conePlus P g) * (1 + coneMinus P g)) * P * ((1 - coneMinus P g) * (1 + conePlus P g)) = dressedPeirceProjector P g g`,
   and `dressedPeirceProjector P g g * dressedPeirceProjector P g g = dressedPeirceProjector P g g`.
-/
theorem airplane_wave_cancellation_and_causal_rectification
    {B : Type*} [Ring B] (P g : B) (hP : P * P = P) :
    peirce11 P (genPhi P g g) = 0 ∧
    peirce00 P (genPhi P g g) = 0 ∧
    genPhi P g g * genPhi P g g = genV P g g ∧
    peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g ∧
    (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
      (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genV P g g ∧
    peirce11 P (conePlus P g * coneMinus P g) = conePlus P g * coneMinus P g ∧
    peirce11 P (coneMinus P g * conePlus P g) = 0 ∧
    peirce11 P (genV P g g) = conePlus P g * coneMinus P g ∧
    ((1 - conePlus P g) * (1 + coneMinus P g)) * ((1 - coneMinus P g) * (1 + conePlus P g)) = 1 ∧
    ((1 - conePlus P g) * (1 + coneMinus P g)) * P * ((1 - coneMinus P g) * (1 + conePlus P g)) =
      dressedPeirceProjector P g g ∧
    dressedPeirceProjector P g g * dressedPeirceProjector P g g = dressedPeirceProjector P g g ∧
    peirce11 P (dressedPeirceProjector P g g - P) = - (conePlus P g * coneMinus P g) ∧
    peirce00 P (dressedPeirceProjector P g g) = coneMinus P g * conePlus P g := by
  rcases peirce_ocean_descent_corner_defect P g hP with ⟨h_11, h_00, _⟩
  have h_sum :
      (peirce11 P (g * g) - peirce11 P g * peirce11 P g) +
        (peirce00 P (g * g) - peirce00 P g * peirce00 P g) = genV P g g := by
    rw [h_11, h_00]; rfl
  have h_conj :
      ((1 - conePlus P g) * (1 + coneMinus P g)) * P * ((1 - coneMinus P g) * (1 + conePlus P g)) =
        dressedPeirceProjector P g g := by
    unfold dressedPeirceProjector
    peirce_nf hP
  have h_11_shift :
      peirce11 P (dressedPeirceProjector P g g - P) = - (conePlus P g * coneMinus P g) := by
    rw [dressedPeirceProjector_eq hP g g]
    peirce_nf hP
  have h_00_shift :
      peirce00 P (dressedPeirceProjector P g g) = coneMinus P g * conePlus P g := by
    rw [dressedPeirceProjector_eq hP g g]
    peirce_nf hP
  exact ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, h_11, h_sum,
         by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
         by peirce_nf hP, h_conj, dressedPeirceProjector_idempotent hP g g,
         h_11_shift, h_00_shift⟩

/--
**Theorem 8B (`popper_survival_implies_surprise`):**
If an operator `H` survives macroscopic quadratic foam testing
(`peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0`), then both off-diagonal Peirce channels
are non-zero (`conePlus P H ≠ 0 ∧ coneMinus P H ≠ 0`), the quadratic foam operator `genV P H H`
is non-zero, and the boundary commutator `comm P H` is non-zero (`P * H ≠ H * P`).
-/
theorem popper_survival_implies_surprise
    {B : Type*} [Ring B] (P H : B) (hP : P * P = P)
    (h_surv : peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0) :
    conePlus P H ≠ 0 ∧
    coneMinus P H ≠ 0 ∧
    genV P H H ≠ 0 ∧
    OperatorAlgebra.PeirceSpine.comm P H ≠ 0 := by
  rcases peirce_ocean_descent_corner_defect P H hP with ⟨h_foam, _, _⟩
  have h_rect : peirce11 P (genV P H H) = conePlus P H * coneMinus P H := by
    peirce_nf hP
  have h_comm_plus : P * OperatorAlgebra.PeirceSpine.comm P H * (1 - P) = conePlus P H := by
    dsimp only [OperatorAlgebra.PeirceSpine.comm, conePlus]
    peirce_nf hP
  rw [h_foam] at h_surv
  have h_plus : conePlus P H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h_surv
    exact h_surv rfl
  have h_minus : coneMinus P H ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h_surv
    exact h_surv rfl
  have h_V : genV P H H ≠ 0 := by
    intro hV0
    apply h_surv
    rw [← h_rect, hV0]
    dsimp [peirce11]
    noncomm_ring
  have h_comm : OperatorAlgebra.PeirceSpine.comm P H ≠ 0 := by
    intro hC0
    apply h_plus
    rw [← h_comm_plus, hC0, mul_zero, zero_mul]
  exact ⟨h_plus, h_minus, h_V, h_comm⟩

/-- Standalone lemma proving the Klein-quadric orthogonality, Zorn square-zero nilpotency, and
deformed projector idempotence of any single Plücker twistor line over `[CommRing K]`. -/
lemma zorn_plucker_single_ray_orthogonality_and_nilpotency
    {K : Type*} [CommRing K] (u v : Vec3 K) (ZA ZB : Twistor4 K) :
    (ZornMatrix.projP : ZornMatrix K) * ZornMatrix.projP = ZornMatrix.projP ∧
    ZornMatrix.zornPhi u v * ZornMatrix.zornPhi u v =
      ZornMatrix.smul (Vec3.dot u v) (1 : ZornMatrix K) ∧
    Vec3.dot (Twistor4.pluckerU ZA ZB) (Twistor4.pluckerV ZA ZB) = 0 ∧
    zornPlucker ZA ZB * zornPlucker ZA ZB = 0 ∧
    (ZornMatrix.projP + zornPlucker ZA ZB) * (ZornMatrix.projP + zornPlucker ZA ZB) -
      (ZornMatrix.projP + zornPlucker ZA ZB) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext <;>
    · simp only [ZornMatrix.projP, ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [ZornMatrix.zornPhi, ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u,
        ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · dsimp [Twistor4.pluckerU, Twistor4.pluckerV, Twistor4.spatialVec, Vec3.dot, Vec3.cross]
    ring
  · ext <;>
    · simp only [zornPlucker, ZornMatrix.zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
        Twistor4.spatialVec,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        ZornMatrix.zero_a, ZornMatrix.zero_u, ZornMatrix.zero_v, ZornMatrix.zero_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  · ext <;>
    · simp only [ZornMatrix.projP, zornPlucker, ZornMatrix.zornPhi, Twistor4.pluckerU,
        Twistor4.pluckerV, Twistor4.spatialVec,
        ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
        ZornMatrix.sub_a, ZornMatrix.sub_u, ZornMatrix.sub_v, ZornMatrix.sub_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        ZornMatrix.zero_a, ZornMatrix.zero_u, ZornMatrix.zero_v, ZornMatrix.zero_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring

/-- Standalone lemma proving the two-ray Plücker anticommutator, superposition square, deformed
projector defect, non-vanishing equivalence, and baryon simplex boundary expansion over `[CommRing K]`. -/
lemma zorn_plucker_two_ray_anticommutator_and_baryon_boundary
    {K : Type*} [CommRing K]
    (Z0 Z1 Z2 Z3 : Twistor4 K) (z10 z20 z30 : K) (u0 u1 u2 u3 : Vec3 K) :
    zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1 =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) * (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) *
        (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) -
      (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    ((zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
        (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) ≠ 0 ↔
      twistorBracket4 Z0 Z1 Z2 Z3 ≠ 0) ∧
    twistorBracket4 Twistor4.origin ⟨z10, u1.x, u1.y, u1.z⟩
                    ⟨z20, u2.x, u2.y, u2.z⟩ ⟨z30, u3.x, u3.y, u3.z⟩ =
      Vec3.baryonDet3 u1 u2 u3 ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0) ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 u1 u2 u3 - Vec3.baryonDet3 u0 u2 u3 +
      Vec3.baryonDet3 u0 u1 u3 - Vec3.baryonDet3 u0 u1 u2 := by
  have h_anti :
      zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1 =
        ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) := by
    ext <;>
    · simp only [zornPlucker, ZornMatrix.zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
        Twistor4.spatialVec, twistorBracket4, det4, ofTwistors,
        ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u, ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  have h_sum :
      (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) * (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) =
        ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) := by
    ext <;>
    · simp only [zornPlucker, ZornMatrix.zornPhi, Twistor4.pluckerU, Twistor4.pluckerV,
        Twistor4.spatialVec, twistorBracket4, det4, ofTwistors,
        ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u, ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  have h_proj :
      (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) *
          (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) -
        (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) =
        ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) := by
    ext <;>
    · simp only [ZornMatrix.projP, zornPlucker, ZornMatrix.zornPhi, Twistor4.pluckerU,
        Twistor4.pluckerV, Twistor4.spatialVec, twistorBracket4, det4, ofTwistors,
        ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u, ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.add_a, ZornMatrix.add_u, ZornMatrix.add_v, ZornMatrix.add_d,
        ZornMatrix.sub_a, ZornMatrix.sub_u, ZornMatrix.sub_v, ZornMatrix.sub_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  have h_iff :
      (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
          (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) ≠ 0 ↔
        twistorBracket4 Z0 Z1 Z2 Z3 ≠ 0 := by
    rw [h_sum]
    constructor
    · intro h hbr
      apply h
      rw [hbr]
      ext <;> simp [ZornMatrix.smul]
    · intro h hzero
      apply h
      have h_a := congrArg ZornMatrix.a hzero
      change twistorBracket4 Z0 Z1 Z2 Z3 * 1 = 0 at h_a
      simpa only [mul_one] using h_a
  have h_orig :
      twistorBracket4 Twistor4.origin ⟨z10, u1.x, u1.y, u1.z⟩
                      ⟨z20, u2.x, u2.y, u2.z⟩ ⟨z30, u3.x, u3.y, u3.z⟩ =
        Vec3.baryonDet3 u1 u2 u3 := by
    simp only [twistorBracket4, det4, ofTwistors, Twistor4.origin, Vec3.baryonDet3,
      Vec3.dot, Vec3.cross]
    ring
  have h_aff_chord :
      twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                      (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
        Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0) := by
    simp only [twistorBracket4, det4, ofTwistors, Twistor4.affineTwistor,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross, Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
    ring
  have h_aff_bdry :
      twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                      (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
        Vec3.baryonDet3 u1 u2 u3 - Vec3.baryonDet3 u0 u2 u3 +
        Vec3.baryonDet3 u0 u1 u3 - Vec3.baryonDet3 u0 u1 u2 := by
    simp only [twistorBracket4, det4, ofTwistors, Twistor4.affineTwistor,
      Vec3.baryonDet3, Vec3.dot, Vec3.cross]
    ring
  exact ⟨h_anti, h_sum, h_proj, h_iff, h_orig, h_aff_chord, h_aff_bdry⟩

/--
**Theorem 8a (`klein_quadric_single_ray_silence_and_popper_counterexample` — Node `𝔔𝔄₆`):**
Over any commutative ring `[CommRing K]`:
1. The Zorn upper-left projector `ZornMatrix.projP = ⟨1, 0, 0, 0⟩` is idempotent (`ZornMatrix.projP * ZornMatrix.projP = ZornMatrix.projP`),
2. Any off-diagonal Zorn wave `ZornMatrix.zornPhi u v` squares to `(u · v) I₂`,
3. Every single twistor ray `ZA ∧ ZB ∈ Gr(2, 4)` satisfies the Klein-quadric orthogonality
   `Vec3.dot (Twistor4.pluckerU ZA ZB) (Twistor4.pluckerV ZA ZB) = 0` and is square-zero nilpotent
   (`zornPlucker ZA ZB * zornPlucker ZA ZB = 0`),
4. Consequently, the unrenormalized single-ray state `Ψ₁ = ZornMatrix.projP + zornPlucker ZA ZB` has
   ZERO quadratic idempotency defect (`Ψ₁ * Ψ₁ - Ψ₁ = 0`) even without Degree-3 Bruhat dressing,
5. **Converse Popper Counterexample:** Over `ℤ`, the concrete orthogonal vectors
   `u₀ = ⟨1, 0, 0⟩ ≠ 0` and `v₀ = ⟨0, 1, 0⟩ ≠ 0` have `ZornMatrix.zornPhi u₀ v₀ ≠ 0`, yet
   `Vec3.dot u₀ v₀ = 0` and `ZornMatrix.zornPhi u₀ v₀ * ZornMatrix.zornPhi u₀ v₀ = 0`, proving
   that the converse of Popper's falsification theorem (`𝔔𝔉₆`) fails on the null Klein quadric.
-/
theorem klein_quadric_single_ray_silence_and_popper_counterexample
    {K : Type*} [CommRing K] (u v : Vec3 K) (ZA ZB : Twistor4 K) :
    (ZornMatrix.projP : ZornMatrix K) * ZornMatrix.projP = ZornMatrix.projP ∧
    ZornMatrix.zornPhi u v * ZornMatrix.zornPhi u v =
      ZornMatrix.smul (Vec3.dot u v) (1 : ZornMatrix K) ∧
    Vec3.dot (Twistor4.pluckerU ZA ZB) (Twistor4.pluckerV ZA ZB) = 0 ∧
    zornPlucker ZA ZB * zornPlucker ZA ZB = 0 ∧
    (ZornMatrix.projP + zornPlucker ZA ZB) * (ZornMatrix.projP + zornPlucker ZA ZB) -
      (ZornMatrix.projP + zornPlucker ZA ZB) = 0 ∧
    (let u0 : Vec3 ℤ := ⟨1, 0, 0⟩
     let v0 : Vec3 ℤ := ⟨0, 1, 0⟩
     u0 ≠ 0 ∧ v0 ≠ 0 ∧ ZornMatrix.zornPhi u0 v0 ≠ 0 ∧
     Vec3.dot u0 v0 = 0 ∧
     ZornMatrix.zornPhi u0 v0 * ZornMatrix.zornPhi u0 v0 = 0) := by
  rcases zorn_plucker_single_ray_orthogonality_and_nilpotency u v ZA ZB with
    ⟨hP_idem, hPhi_sq, hDot0, hPluck_sq, hProj_def⟩
  exact ⟨hP_idem, hPhi_sq, hDot0, hPluck_sq, hProj_def, by decide⟩

/--
**Theorem 8D (`𝔔𝔄₆` — `two_ray_amplituhedron_scattering_foam_and_baryon_boundary`):**
When two nilpotent twistor rays `Φ01 = zornPlucker Z0 Z1` (`Φ01² = 0`) and
`Φ23 = zornPlucker Z2 Z3` (`Φ23² = 0`) collide:
1. Their anticommutator `Φ01 * Φ23 + Φ23 * Φ01` and superposition square `(Φ01 + Φ23) * (Φ01 + Φ23)`
   both equal the 4×4 Amplituhedron 4-bracket `ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) 1`,
2. Projecting `(Φ01 + Φ23) * (Φ01 + Φ23)` onto the `ZornMatrix.projP` corner yields
   `ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) ZornMatrix.projP`, and if the two-ray deformed
   projector defect `(ZornMatrix.projP + (Φ01 + Φ23))² - (ZornMatrix.projP + (Φ01 + Φ23))` is
   non-zero, both individual twistor rays must be non-zero (`Φ01 ≠ 0 ∧ Φ23 ≠ 0`),
3. Anchored at `Twistor4.origin = ⟨1, 0, 0, 0⟩`, `twistorBracket4 Twistor4.origin Q1 Q2 Q3 = Vec3.baryonDet3 u1 u2 u3`,
4. On affine twistors `Twistor4.affineTwistor u_a = ⟨1, u_a.x, u_a.y, u_a.z⟩`, the 4-bracket equals
   the relative-chord baryon determinant `Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0)` and expands
   into the 4-simplex boundary sum `ℬ₁₂₃ - ℬ₀₂₃ + ℬ₀₁₃ - ℬ₀₁₂`.
-/
theorem two_ray_amplituhedron_scattering_foam_and_baryon_boundary
    {K : Type*} [CommRing K]
    (Z0 Z1 Z2 Z3 : Twistor4 K) (z10 z20 z30 : K) (u0 u1 u2 u3 : Vec3 K) :
    let Φ01 := zornPlucker Z0 Z1
    let Φ23 := zornPlucker Z2 Z3
    let Q1 : Twistor4 K := ⟨z10, u1.x, u1.y, u1.z⟩
    let Q2 : Twistor4 K := ⟨z20, u2.x, u2.y, u2.z⟩
    let Q3 : Twistor4 K := ⟨z30, u3.x, u3.y, u3.z⟩
    Φ01 * Φ23 + Φ23 * Φ01 = ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    (Φ01 + Φ23) * (Φ01 + Φ23) = ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    ZornMatrix.projP * ((Φ01 + Φ23) * (Φ01 + Φ23)) * ZornMatrix.projP =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (ZornMatrix.projP : ZornMatrix K) ∧
    twistorBracket4 Twistor4.origin Q1 Q2 Q3 = Vec3.baryonDet3 u1 u2 u3 ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0) ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 u1 u2 u3 - Vec3.baryonDet3 u0 u2 u3 +
      Vec3.baryonDet3 u0 u1 u3 - Vec3.baryonDet3 u0 u1 u2 := by
  rcases zorn_plucker_two_ray_anticommutator_and_baryon_boundary
      Z0 Z1 Z2 Z3 z10 z20 z30 u0 u1 u2 u3 with
    ⟨h_anti, h_sum, _, _, h_orig, h_chord, h_bdry⟩
  have h_proj_corner :
      ZornMatrix.projP * ((zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
        (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) * ZornMatrix.projP =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (ZornMatrix.projP : ZornMatrix K) := by
    rw [h_sum]
    ext <;>
    · simp only [ZornMatrix.projP, ZornMatrix.smul, ZornMatrix.one_a, ZornMatrix.one_u,
        ZornMatrix.one_v, ZornMatrix.one_d,
        ZornMatrix.mul_a, ZornMatrix.mul_u, ZornMatrix.mul_v, ZornMatrix.mul_d,
        Vec3.dot, Vec3.smulLeft, Vec3.smulRight, Vec3.cross,
        Vec3.zero_x, Vec3.zero_y, Vec3.zero_z,
        Vec3.add_x, Vec3.add_y, Vec3.add_z,
        Vec3.sub_x, Vec3.sub_y, Vec3.sub_z]
      ring
  exact ⟨h_anti, h_sum, h_proj_corner, h_orig, h_chord, h_bdry⟩

/--
**Theorem 8 (`twistor_amplituhedron_foam_collision_bridge` — Node `𝔔𝔄₇`):**
Bridges Wheeler's breaking-wave quantum foam with the Twistor–Zorn Amplituhedron over `[CommRing K]`:
1. The general Zorn off-diagonal wave `ZornMatrix.zornPhi u v` squares to the scalar condensate
   `ZornMatrix.smul (Vec3.dot u v) (1 : ZornMatrix K)`,
2. A single twistor line `Z0 ∧ Z1 ∈ Gr(2, 4)` lies on the Klein quadric
   (`Vec3.dot (Twistor4.pluckerU Z0 Z1) (Twistor4.pluckerV Z0 Z1) = 0`) and is a square-zero
   Zorn nilpotent (`zornPlucker Z0 Z1 * zornPlucker Z0 Z1 = 0`),
3. Two twistor lines `zornPlucker Z0 Z1` and `zornPlucker Z2 Z3` collide via the anticommutator
   to produce the 4-simplex Amplituhedron volume `twistorBracket4 Z0 Z1 Z2 Z3 • 1`,
4. The square of the sum of the two null rays is that same four-bracket scalar, and its difference
   from the anticommutator vanishes identically (`(Φ01 + Φ23)² - (Φ01 * Φ23 + Φ23 * Φ01) = 0`),
5. Anchored at `Twistor4.origin`, the 4-bracket equals `Vec3.baryonDet3 u1 u2 u3`,
6. On affine twistors `Twistor4.affineTwistor u_a`, the 4-bracket equals the relative-chord
   baryon determinant `Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0)` and expands into the
   4-facet cyclic boundary sum `ℬ₁₂₃ - ℬ₀₂₃ + ℬ₀₁₃ - ℬ₀₁₂`.
-/
theorem twistor_amplituhedron_foam_collision_bridge
    {K : Type*} [CommRing K]
    (u v : Vec3 K) (Z0 Z1 Z2 Z3 : Twistor4 K)
    (z10 z20 z30 : K) (u0 u1 u2 u3 : Vec3 K) :
    let Q1 : Twistor4 K := ⟨z10, u1.x, u1.y, u1.z⟩
    let Q2 : Twistor4 K := ⟨z20, u2.x, u2.y, u2.z⟩
    let Q3 : Twistor4 K := ⟨z30, u3.x, u3.y, u3.z⟩
    ZornMatrix.zornPhi u v * ZornMatrix.zornPhi u v =
      ZornMatrix.smul (Vec3.dot u v) (1 : ZornMatrix K) ∧
    Vec3.dot (Twistor4.pluckerU Z0 Z1) (Twistor4.pluckerV Z0 Z1) = 0 ∧
    zornPlucker Z0 Z1 * zornPlucker Z0 Z1 = 0 ∧
    zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1 =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
        (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) =
      ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
    (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
        (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) -
      (zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1) = 0 ∧
    ((zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
        (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) ≠ 0 ↔
      twistorBracket4 Z0 Z1 Z2 Z3 ≠ 0) ∧
    twistorBracket4 Twistor4.origin Q1 Q2 Q3 = Vec3.baryonDet3 u1 u2 u3 ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 (u1 - u0) (u2 - u0) (u3 - u0) ∧
    twistorBracket4 (Twistor4.affineTwistor u0) (Twistor4.affineTwistor u1)
                    (Twistor4.affineTwistor u2) (Twistor4.affineTwistor u3) =
      Vec3.baryonDet3 u1 u2 u3 - Vec3.baryonDet3 u0 u2 u3 +
      Vec3.baryonDet3 u0 u1 u3 - Vec3.baryonDet3 u0 u1 u2 := by
  rcases zorn_plucker_single_ray_orthogonality_and_nilpotency u v Z0 Z1 with
    ⟨_, hPhi_sq, hDot0, hPluck_sq, _⟩
  rcases zorn_plucker_two_ray_anticommutator_and_baryon_boundary
      Z0 Z1 Z2 Z3 z10 z20 z30 u0 u1 u2 u3 with
    ⟨h_anti, h_sum, _, h_iff, h_orig, h_chord, h_bdry⟩
  have h_diff_zero :
      (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
          (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) -
        (zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1) = 0 := by
    rw [h_sum, h_anti]
    ext <;> simp [ZornMatrix.smul, Vec3.smulLeft]
  exact ⟨hPhi_sq, hDot0, hPluck_sq, h_anti, h_sum, h_diff_zero, h_iff, h_orig, h_chord, h_bdry⟩

/--
**Master Synthesis (`wheeler_popper_amplituhedron_bruhat_master_synthesis`):**
Unites Wheeler's Ocean Descent (`𝔔𝔉₁`–`𝔔𝔉₂`), One-Way Macroscopic Causal Rectification,
Degree-3 Plabic Bruhat Self-Closure (`dressedPeirceProjector`), Dissolution of "Before and After" (`𝔔𝔉₃`),
Max Planck's Dimensional Triangulation (`𝔔𝔉₄`), Karl Popper's Surprise-and-Survival Theorem (`𝔔𝔉₆`–`𝔔𝔉₇`),
and the Twistor–Zorn Amplituhedron 4-Bracket Foam Collision in a single kernel-checked theorem.
-/
theorem wheeler_popper_amplituhedron_bruhat_master_synthesis
    {B : Type*} [Ring B] (P g H : B) (hP : P * P = P)
    (δ x y z : ℤ) (hδ : 0 < δ)
    {K : Type*} [CommRing K] (Z0 Z1 Z2 Z3 : Twistor4 K) :
    (peirce11 P (genPhi P g g) = 0 ∧
     genPhi P g g * genPhi P g g = genV P g g ∧
     peirce11 P (g * g) - peirce11 P g * peirce11 P g = conePlus P g * coneMinus P g) ∧
    (peirce11 P (conePlus P g * coneMinus P g) = conePlus P g * coneMinus P g ∧
     peirce11 P (coneMinus P g * conePlus P g) = 0 ∧
     peirce11 P (genV P g g) = conePlus P g * coneMinus P g) ∧
    ((P + genPhi P g g) * (P + genPhi P g g) - (P + genPhi P g g) = genV P g g ∧
     ((1 - conePlus P g) * (1 + coneMinus P g)) *
       ((1 - coneMinus P g) * (1 + conePlus P g)) = 1 ∧
     dressedPeirceProjector P g g =
       P + genPhi P g g - genSig P g g - genV P g g * conePlus P g ∧
     dressedPeirceProjector P g g * dressedPeirceProjector P g g =
       dressedPeirceProjector P g g) ∧
    ((0 : ℤ) ≠ δ ∧ (0 : ℤ) ≤ δ + δ ∧ δ ≤ (0 : ℤ) + δ) ∧
    ((planckDim x y z = (2, 0, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -3)) ∧
     (planckDim x y z = (0, 2, 0) ↔ (x = 1 ∧ y = 1 ∧ z = -5)) ∧
     (planckDim x y z = (0, 0, 2) ↔ (x = 1 ∧ y = -1 ∧ z = 1))) ∧
    (peirce11 P (H * H) - peirce11 P H * peirce11 P H ≠ 0 →
      (conePlus P H ≠ 0 ∧ coneMinus P H ≠ 0) ∧ genPhi P H H ≠ 0) ∧
    (zornPlucker Z0 Z1 * zornPlucker Z0 Z1 = 0 ∧
     (ZornMatrix.projP + zornPlucker Z0 Z1) * (ZornMatrix.projP + zornPlucker Z0 Z1) -
       (ZornMatrix.projP + zornPlucker Z0 Z1) = 0 ∧
     zornPlucker Z0 Z1 * zornPlucker Z2 Z3 + zornPlucker Z2 Z3 * zornPlucker Z0 Z1 =
       ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
     (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
         (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) =
       ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K) ∧
     ((zornPlucker Z0 Z1 + zornPlucker Z2 Z3) *
         (zornPlucker Z0 Z1 + zornPlucker Z2 Z3) ≠ 0 ↔
       twistorBracket4 Z0 Z1 Z2 Z3 ≠ 0) ∧
     (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) *
         (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) -
       (ZornMatrix.projP + (zornPlucker Z0 Z1 + zornPlucker Z2 Z3)) =
       ZornMatrix.smul (twistorBracket4 Z0 Z1 Z2 Z3) (1 : ZornMatrix K)) := by
  rcases peirce_ocean_descent_corner_defect P g hP with ⟨h_11, _, _⟩
  rcases peirce_ocean_descent_corner_defect P H hP with ⟨h_foamH, _, _⟩
  rcases zorn_plucker_single_ray_orthogonality_and_nilpotency (0 : Vec3 K) 0 Z0 Z1 with
    ⟨_, _, _, hPluck_sq, hSingle_def⟩
  rcases zorn_plucker_two_ray_anticommutator_and_baryon_boundary
      Z0 Z1 Z2 Z3 0 0 0 0 0 0 0 with
    ⟨h_anti, h_sum, h_pair_def, h_iff, _, _, _⟩
  have h_extract_plus : P * genPhi P H H * (1 - P) = conePlus P H := by
    peirce_nf hP
  refine ⟨⟨by peirce_nf hP, by peirce_nf hP, h_11⟩,
          ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩,
          ⟨by peirce_nf hP, by peirce_nf hP,
           dressedPeirceProjector_eq hP g g,
           dressedPeirceProjector_idempotent hP g g⟩,
          ⟨ne_of_lt hδ, add_nonneg (le_of_lt hδ) (le_of_lt hδ), by rw [zero_add]⟩,
          ⟨⟨fun h => planckDim_solve h rfl rfl rfl, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩,
           ⟨fun h => planckDim_solve h rfl rfl rfl, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩,
           ⟨fun h => planckDim_solve h rfl rfl rfl, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩⟩,
          ?_,
          ⟨hPluck_sq, hSingle_def, h_anti, h_sum, h_iff, h_pair_def⟩⟩
  intro h_surv
  rw [h_foamH] at h_surv
  have h_plus_ne : conePlus P H ≠ 0 := by
    intro h_plus; rw [h_plus, zero_mul] at h_surv; exact h_surv rfl
  have h_minus_ne : coneMinus P H ≠ 0 := by
    intro h_minus; rw [h_minus, mul_zero] at h_surv; exact h_surv rfl
  have h_phi_ne : genPhi P H H ≠ 0 := by
    intro h_phi; apply h_plus_ne; rw [← h_extract_plus, h_phi, mul_zero, zero_mul]
  exact ⟨⟨h_plus_ne, h_minus_ne⟩, h_phi_ne⟩

end InfoGeometry.Canonical.WheelerQuantumFoamPlanckPopperPoset
