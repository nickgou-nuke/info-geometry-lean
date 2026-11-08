/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# The Wheeler–Gödel Quantum & Existence Synthesis (`𝔍𝔚₁`–`𝔍𝔚₇`)

## i. Overview
Formalizes the seven-node Wheeler–Gödel oral-history synthesis (*Thoughts on Gödel, Part 2*) across
additive commutative groups, finite parity involutions, and non-commutative Peirce rings.

## ii. Key results
- `mach_relational_translation_invariance` (`𝔍𝔚₁`)
- `godel_closed_timelike_loop_periodicity_mul`, `godel_closed_timelike_loop_periodicity` (`𝔍𝔚₂`)
- `peebles_isotropy_no_preferred_rotation`, `peebles_isotropy_finset_sum_two_nsmul_zero` (`𝔍𝔚₃`)
- `heisenberg_godel_commutator_undecidability_bridge` (`𝔍𝔚₄`)
- `einstein_brainwashing_quarantine_tragedy`, `classical_einstein_godel_commutative_collapse` (`𝔍𝔚₅`–`𝔍𝔚₆`)
- `wheeler_how_come_quantum_iff_how_come_existence`, `wheeler_godel_quantum_existence_master_synthesis` (`𝔍𝔚₇`)

## iii. Table of contents
- Nodes `𝔍𝔚₁`–`𝔍𝔚₃`: Machian translation invariance, CTC periodicity, and Peebles parity cancellation
- Nodes `𝔍𝔚₄`–`𝔍𝔚₆`: Heisenberg–Gödel commutator–undecidability bridge and quarantine collapse
- Node `𝔍𝔚₇`: Equivalence of cross-boundary Peirce transport and diagonal idempotence defect

## iv. References
- John Archibald Wheeler, *Web of Stories*, Segment 93/130 (*Thoughts on Gödel, Part 2*)
- Kurt Gödel, *An Example of a New Type of Cosmological Solutions of Einstein's Field Equations of Gravitation* (1949)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `mach_relational_translation_invariance`
- `godel_closed_timelike_loop_periodicity_mul`, `godel_closed_timelike_loop_periodicity`
- `peebles_isotropy_no_preferred_rotation`, `peebles_isotropy_finset_sum_two_nsmul_zero`
- `heisenberg_godel_commutator_undecidability_bridge`
- `einstein_brainwashing_quarantine_tragedy`
- `classical_einstein_godel_commutative_collapse`
- `wheeler_how_come_quantum_iff_how_come_existence`
- `wheeler_godel_quantum_existence_master_synthesis`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `godel_closed_timelike_loop_periodicity` (conditional on closed loop `step^[L] x0 = x0`)
- `peebles_isotropy_no_preferred_rotation` and `peebles_isotropy_finset_sum_two_nsmul_zero`
  (conditional on parity inversion `∀ g, spin (σ g) = -spin g`)
- `einstein_brainwashing_quarantine_tragedy` (conditional on `conePlus P Q * coneMinus P Q = 0`
  and `coneMinus P Q * conePlus P Q = 0`)
- `classical_einstein_godel_commutative_collapse` (conditional on `P * Q = Q * P`)

#### BUCKET 3: OPEN CLOSURE DEBT
- Empirical galaxy spin survey statistics, full pseudo-Riemannian Lorentzian manifold metrics
  for Gödel's rotating dust cosmology, and first-order Gödel numbering of `ZFC` remain external
  context, not claimed as consequences of these algebraic ring and group theorems.
-/

namespace InfoGeometry.Canonical.WheelerGodelQuantumExistencePoset

open BigOperators InfoGeometry.OperatorAlgebra.PeirceSpine

/--
**Theorem 1 (`𝔍𝔚₁` — `mach_relational_translation_invariance`):**
In any additive commutative group `G`, shifting every coordinate by a global background translation
`c : G` cancels out of all relative displacements `(x + c) - (y + c) = x - y`, and relative
displacements compose additively (`((x + c) - (y + c)) + ((y + c) - (z + c)) = x - z`).
-/
theorem mach_relational_translation_invariance
    {G : Type*} [AddCommGroup G] (x y z c : G) :
    (x + c) - (y + c) = x - y ∧
    ((x + c) - (y + c)) + ((y + c) - (z + c)) = x - z := by
  refine ⟨by abel, by abel⟩

/-- Inductive multi-winding periodicity along a closed timelike loop `step^[L] x0 = x0`. -/
lemma godel_closed_timelike_loop_periodicity_mul
    {X : Type*} (step : X → X) (x0 : X) (L : ℕ)
    (h_ctc : (step^[L] x0) = x0) :
    ∀ (k m : ℕ), (step^[m + k * L] x0) = (step^[m] x0)
  | 0, m => by simp
  | k + 1, m => by
      have h_split : m + (k + 1) * L = (m + k * L) + L := by
        rw [Nat.succ_mul, ← Nat.add_assoc]
      rw [h_split, Function.iterate_add_apply, h_ctc]
      exact godel_closed_timelike_loop_periodicity_mul step x0 L h_ctc k m

/--
**Theorem 2 (`𝔍𝔚₂` — `godel_closed_timelike_loop_periodicity`):**
If a discrete worldline transition `step : X → X` admits a closed timelike loop of period `L`
at `x0` (`step^[L] x0 = x0`), then the trajectory repeats with period `L` (`step^[m + L] x0 = step^[m] x0`)
and across all integer windings `k : ℕ` (`step^[m + k * L] x0 = step^[m] x0`).
-/
theorem godel_closed_timelike_loop_periodicity
    {X : Type*} (step : X → X) (x0 : X) (L : ℕ)
    (h_ctc : (step^[L] x0) = x0) (m k : ℕ) :
    (step^[m + L] x0) = (step^[m] x0) ∧
    (step^[m + k * L] x0) = (step^[m] x0) := by
  have h1 : (step^[m + L] x0) = (step^[m] x0) := by
    rw [Function.iterate_add_apply, h_ctc]
  exact ⟨h1, godel_closed_timelike_loop_periodicity_mul step x0 L h_ctc k m⟩

/--
**Theorem 3A (`𝔍𝔚₃` — `peebles_isotropy_no_preferred_rotation`):**
If a parity involution `σ : G → G` reverses rotational spin (`spin (σ g) = -spin g`),
every pair `(g, σ g)` sums to zero net angular momentum (`spin g + spin (σ g) = 0`).
-/
theorem peebles_isotropy_no_preferred_rotation
    {G R : Type*} [AddCommGroup R]
    (σ : G → G) (spin : G → R)
    (h_parity : ∀ g : G, spin (σ g) = -spin g) (g : G) :
    spin g + spin (σ g) = 0 := by
  rw [h_parity g, add_neg_cancel]

/--
**Theorem 3B (`𝔍𝔚₃` — `peebles_isotropy_finset_sum_two_nsmul_zero`):**
On any finite galaxy catalog `[Fintype G]` equipped with a parity equivalence `σ : G ≃ G`
satisfying `∀ g, spin (σ g) = -spin g`, twice the total rotational spin vanishes:
`2 • (∑ g : G, spin g) = 0`.
-/
theorem peebles_isotropy_finset_sum_two_nsmul_zero
    {G R : Type*} [AddCommGroup R] [Fintype G]
    (σ : G ≃ G) (spin : G → R)
    (h_parity : ∀ g : G, spin (σ g) = -spin g) :
    2 • (∑ g : G, spin g) = 0 := by
  have h_sum_eq : (∑ g : G, spin (σ g)) = ∑ g : G, spin g :=
    Equiv.sum_comp σ spin
  have h_sum_neg : (∑ g : G, spin (σ g)) = -(∑ g : G, spin g) := by
    calc
      (∑ g : G, spin (σ g)) = ∑ g : G, (-spin g) :=
        Finset.sum_congr rfl (fun g _ => h_parity g)
      _ = -(∑ g : G, spin g) := by rw [Finset.sum_neg_distrib]
  calc
    2 • (∑ g : G, spin g) = (∑ g : G, spin g) + (∑ g : G, spin g) :=
      two_nsmul (∑ g : G, spin g)
    _ = (∑ g : G, spin g) + (∑ g : G, spin (σ g)) := by rw [h_sum_eq]
    _ = (∑ g : G, spin g) + (-(∑ g : G, spin g)) := by rw [h_sum_neg]
    _ = 0 := add_neg_cancel (∑ g : G, spin g)

section NoncommutativeQuantumPeirceAlgebra
variable {B : Type*} [Ring B]

/-- Right-associated idempotent absorption `P * (P * Z) = P * Z`. -/
lemma P_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

/-- Core Peirce diagonal idempotence defects and even-grade commutator vanishing for two
idempotents `P * P = P` and `Q * Q = Q`. -/
lemma peirce_idempotent_corner_excursion_defects
    (P Q : B) (hP : P * P = P) (hQ : Q * Q = Q) :
    peirce11 P Q - peirce11 P Q * peirce11 P Q = conePlus P Q * coneMinus P Q ∧
    peirce00 P Q - peirce00 P Q * peirce00 P Q = coneMinus P Q * conePlus P Q ∧
    OperatorAlgebra.PeirceSpine.comm P (evenGrade P Q) = 0 := by
  have h_11 : peirce11 P Q - peirce11 P Q * peirce11 P Q = conePlus P Q * coneMinus P Q := by
    dsimp only [peirce11, conePlus, coneMinus]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, P_idem hP, P_idem hQ]
    abel
  have h_00 : peirce00 P Q - peirce00 P Q * peirce00 P Q = coneMinus P Q * conePlus P Q := by
    dsimp only [peirce00, conePlus, coneMinus]
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, P_idem hP, hQ, P_idem hQ]
    abel
  have h_comm_even : OperatorAlgebra.PeirceSpine.comm P (evenGrade P Q) = 0 := by
    peirce_nf hP
  exact ⟨h_11, h_00, h_comm_even⟩

/--
**Theorem 4 (`𝔍𝔚₅` — `heisenberg_godel_commutator_undecidability_bridge`):**
For any two idempotents `P * P = P` and `Q * Q = Q` in an associative ring `[Ring B]`:
1. The Heisenberg commutator `[P, Q]` equals `genJ P Q Q = conePlus P Q - coneMinus P Q`,
2. Its square is negative-definite relative to the Operator Fisher Metric:
   `[P, Q]² = -genV P Q Q` (equivalently `[P, Q]² + genV P Q Q = 0`),
3. The inner and outer Peirce idempotency defects equal the two corner excursion products:
   `peirce11 P Q - (peirce11 P Q)² = conePlus P Q * coneMinus P Q` and
   `peirce00 P Q - (peirce00 P Q)² = coneMinus P Q * conePlus P Q`,
4. Their sum and difference recover `genV P Q Q` and `genSig P Q Q`, and
   `evenGrade P Q - (evenGrade P Q)² = genV P Q Q`.
-/
theorem heisenberg_godel_commutator_undecidability_bridge
    (P Q : B) (hP : P * P = P) (hQ : Q * Q = Q) :
    OperatorAlgebra.PeirceSpine.comm P Q = genJ P Q Q ∧
    OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = -genV P Q Q ∧
    OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q + genV P Q Q = 0 ∧
    peirce11 P Q - peirce11 P Q * peirce11 P Q = conePlus P Q * coneMinus P Q ∧
    peirce00 P Q - peirce00 P Q * peirce00 P Q = coneMinus P Q * conePlus P Q ∧
    (peirce11 P Q - peirce11 P Q * peirce11 P Q) +
      (peirce00 P Q - peirce00 P Q * peirce00 P Q) = genV P Q Q ∧
    (peirce11 P Q - peirce11 P Q * peirce11 P Q) -
      (peirce00 P Q - peirce00 P Q * peirce00 P Q) = genSig P Q Q ∧
    evenGrade P Q - evenGrade P Q * evenGrade P Q = genV P Q Q := by
  have h_comm : OperatorAlgebra.PeirceSpine.comm P Q = genJ P Q Q := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, genJ, conePlus, coneMinus]
    noncomm_ring
  have h_sq : OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = -genV P Q Q := by
    rw [h_comm]
    peirce_nf hP
  have h_sum_zero : OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q + genV P Q Q = 0 := by
    rw [h_sq, neg_add_cancel]
  rcases peirce_idempotent_corner_excursion_defects P Q hP hQ with ⟨h_11, h_00, _⟩
  have h_V : (peirce11 P Q - peirce11 P Q * peirce11 P Q) +
      (peirce00 P Q - peirce00 P Q * peirce00 P Q) = genV P Q Q := by
    rw [h_11, h_00]
    rfl
  have h_Sig : (peirce11 P Q - peirce11 P Q * peirce11 P Q) -
      (peirce00 P Q - peirce00 P Q * peirce00 P Q) = genSig P Q Q := by
    rw [h_11, h_00]
    rfl
  have h_even_split :
      evenGrade P Q - evenGrade P Q * evenGrade P Q =
        (peirce11 P Q - peirce11 P Q * peirce11 P Q) +
          (peirce00 P Q - peirce00 P Q * peirce00 P Q) := by
    peirce_nf hP
  have h_even : evenGrade P Q - evenGrade P Q * evenGrade P Q = genV P Q Q :=
    h_even_split.trans h_V
  exact ⟨h_comm, h_sq, h_sum_zero, h_11, h_00, h_V, h_Sig, h_even⟩

/--
**Theorem 5 (`𝔍𝔚₆` — `einstein_brainwashing_quarantine_tragedy`):**
If the off-diagonal Peirce transition products are suppressed (`conePlus P Q * coneMinus P Q = 0`
and `coneMinus P Q * conePlus P Q = 0`), then `genV P Q Q = 0`, `genSig P Q Q = 0`,
`[P, Q]² = 0`, and `peirce11 P Q`, `peirce00 P Q`, and `evenGrade P Q` all collapse to
classical idempotents.
-/
theorem einstein_brainwashing_quarantine_tragedy
    (P Q : B) (hP : P * P = P) (hQ : Q * Q = Q)
    (h_no_up : conePlus P Q * coneMinus P Q = 0)
    (h_no_dn : coneMinus P Q * conePlus P Q = 0) :
    genV P Q Q = 0 ∧
    genSig P Q Q = 0 ∧
    OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = 0 ∧
    peirce11 P Q * peirce11 P Q = peirce11 P Q ∧
    peirce00 P Q * peirce00 P Q = peirce00 P Q ∧
    evenGrade P Q * evenGrade P Q = evenGrade P Q := by
  rcases peirce_idempotent_corner_excursion_defects P Q hP hQ with ⟨h_11_def, h_00_def, _⟩
  have hV : genV P Q Q = 0 := by
    dsimp [genV, anticomm]; rw [h_no_up, h_no_dn, add_zero]
  have hSig : genSig P Q Q = 0 := by
    dsimp [genSig, OperatorAlgebra.PeirceSpine.comm]; rw [h_no_up, h_no_dn, sub_zero]
  have h_comm : OperatorAlgebra.PeirceSpine.comm P Q = genJ P Q Q := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, genJ, conePlus, coneMinus]
    noncomm_ring
  have h_sq : OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = -genV P Q Q := by
    rw [h_comm]
    peirce_nf hP
  have hCommSq : OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = 0 := by
    rw [h_sq, hV, neg_zero]
  have h11 : peirce11 P Q * peirce11 P Q = peirce11 P Q := by
    rw [h_no_up] at h_11_def
    exact (sub_eq_zero.mp h_11_def).symm
  have h00 : peirce00 P Q * peirce00 P Q = peirce00 P Q := by
    rw [h_no_dn] at h_00_def
    exact (sub_eq_zero.mp h_00_def).symm
  have h_even_split :
      evenGrade P Q - evenGrade P Q * evenGrade P Q =
        (peirce11 P Q - peirce11 P Q * peirce11 P Q) +
          (peirce00 P Q - peirce00 P Q * peirce00 P Q) := by
    peirce_nf hP
  have hEven : evenGrade P Q * evenGrade P Q = evenGrade P Q := by
    rw [h11, h00, sub_self, sub_self, add_zero] at h_even_split
    exact (sub_eq_zero.mp h_even_split).symm
  exact ⟨hV, hSig, hCommSq, h11, h00, hEven⟩

/--
**Theorem 6 (`𝔍𝔚₄` — `classical_einstein_godel_commutative_collapse`):**
When two idempotent observables `P * P = P` and `Q * Q = Q` commute (`P * Q = Q * P`),
both off-diagonal Peirce transition corners vanish (`conePlus P Q = 0`, `coneMinus P Q = 0`),
the solder form `genPhi P Q Q`, complex generator `genJ P Q Q`, Fisher metric `genV P Q Q`,
and symplectic curvature `genSig P Q Q` all collapse to `0`, and both diagonal compressions
`peirce11 P Q` and `peirce00 P Q` are exact idempotents.
-/
theorem classical_einstein_godel_commutative_collapse
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q) (hComm : P * Q = Q * P) :
    conePlus P Q = 0 ∧
    coneMinus P Q = 0 ∧
    genPhi P Q Q = 0 ∧
    genJ P Q Q = 0 ∧
    genV P Q Q = 0 ∧
    genSig P Q Q = 0 ∧
    peirce11 P Q * peirce11 P Q = peirce11 P Q ∧
    peirce00 P Q * peirce00 P Q = peirce00 P Q := by
  rcases peirce_idempotent_corner_excursion_defects P Q hP hQ with ⟨h_11_def, h_00_def, _⟩
  have hCp : conePlus P Q = 0 := by
    calc
      conePlus P Q = (P * Q) * (1 - P) := rfl
      _ = (Q * P) * (1 - P) := by rw [hComm]
      _ = Q * P - Q * (P * P) := by noncomm_ring
      _ = Q * P - Q * P := by rw [hP]
      _ = 0 := sub_self (Q * P)
  have hCm : coneMinus P Q = 0 := by
    calc
      coneMinus P Q = (1 - P) * (Q * P) := by dsimp [coneMinus]; noncomm_ring
      _ = (1 - P) * (P * Q) := by rw [← hComm]
      _ = P * Q - (P * P) * Q := by noncomm_ring
      _ = P * Q - P * Q := by rw [hP]
      _ = 0 := sub_self (P * Q)
  have hPhi : genPhi P Q Q = 0 := by
    dsimp [genPhi]; rw [hCp, hCm, add_zero]
  have hJ : genJ P Q Q = 0 := by
    dsimp [genJ]; rw [hCp, hCm, sub_zero]
  have h_no_up : conePlus P Q * coneMinus P Q = 0 := by rw [hCp, zero_mul]
  have h_no_dn : coneMinus P Q * conePlus P Q = 0 := by rw [hCm, zero_mul]
  have hV : genV P Q Q = 0 := by
    dsimp [genV, anticomm]; rw [h_no_up, h_no_dn, add_zero]
  have hSig : genSig P Q Q = 0 := by
    dsimp [genSig, OperatorAlgebra.PeirceSpine.comm]; rw [h_no_up, h_no_dn, sub_zero]
  have h11 : peirce11 P Q * peirce11 P Q = peirce11 P Q := by
    rw [h_no_up] at h_11_def
    exact (sub_eq_zero.mp h_11_def).symm
  have h00 : peirce00 P Q * peirce00 P Q = peirce00 P Q := by
    rw [h_no_dn] at h_00_def
    exact (sub_eq_zero.mp h_00_def).symm
  exact ⟨hCp, hCm, hPhi, hJ, hV, hSig, h11, h00⟩

/--
**Theorem 7 (`𝔍𝔚₇` — `wheeler_how_come_quantum_iff_how_come_existence`):**
For any two idempotents `P * P = P` and `Q * Q = Q`, non-vanishing of the off-diagonal quantum
Peirce excursion products (`conePlus P Q * coneMinus P Q ≠ 0 ∨ coneMinus P Q * conePlus P Q ≠ 0`)
is constructively equivalent to non-idempotence of the diagonal Peirce compressions
(`peirce11 P Q * peirce11 P Q ≠ peirce11 P Q ∨ peirce00 P Q * peirce00 P Q ≠ peirce00 P Q`),
proved with zero `Classical.choice`.
-/
theorem wheeler_how_come_quantum_iff_how_come_existence
    (P Q : B) (hP : P * P = P) (hQ : Q * Q = Q) :
    ((conePlus P Q * coneMinus P Q ≠ 0 ∨ coneMinus P Q * conePlus P Q ≠ 0) ↔
     (peirce11 P Q * peirce11 P Q ≠ peirce11 P Q ∨ peirce00 P Q * peirce00 P Q ≠ peirce00 P Q)) ∧
    ((conePlus P Q * coneMinus P Q = 0 ∧ coneMinus P Q * conePlus P Q = 0) ↔
     (peirce11 P Q * peirce11 P Q = peirce11 P Q ∧ peirce00 P Q * peirce00 P Q = peirce00 P Q)) ∧
    (conePlus P Q * coneMinus P Q ≠ 0 ↔ peirce11 P Q * peirce11 P Q ≠ peirce11 P Q) ∧
    (coneMinus P Q * conePlus P Q ≠ 0 ↔ peirce00 P Q * peirce00 P Q ≠ peirce00 P Q) := by
  rcases peirce_idempotent_corner_excursion_defects P Q hP hQ with ⟨h_11_def, h_00_def, _⟩
  have h_up_eq : conePlus P Q * coneMinus P Q = 0 ↔ peirce11 P Q * peirce11 P Q = peirce11 P Q := by
    rw [← h_11_def, sub_eq_zero, eq_comm]
  have h_dn_eq : coneMinus P Q * conePlus P Q = 0 ↔ peirce00 P Q * peirce00 P Q = peirce00 P Q := by
    rw [← h_00_def, sub_eq_zero, eq_comm]
  have h_up_ne : conePlus P Q * coneMinus P Q ≠ 0 ↔ peirce11 P Q * peirce11 P Q ≠ peirce11 P Q :=
    not_congr h_up_eq
  have h_dn_ne : coneMinus P Q * conePlus P Q ≠ 0 ↔ peirce00 P Q * peirce00 P Q ≠ peirce00 P Q :=
    not_congr h_dn_eq
  exact ⟨or_congr h_up_ne h_dn_ne, and_congr h_up_eq h_dn_eq, h_up_ne, h_dn_ne⟩

end NoncommutativeQuantumPeirceAlgebra

/--
**Master Synthesis (`wheeler_godel_quantum_existence_master_synthesis`):**
Unites all seven stages `𝔍𝔚₁`–`𝔍𝔚₇` in one kernel-checked theorem:
1. `𝔍𝔚₁`: Mach relational translation invariance (`(x + c) - (y + c) = x - y`),
2. `𝔍𝔚₂`: Gödel closed timelike loop periodicity (`step^[m + k * L] x0 = step^[m] x0`),
3. `𝔍𝔚₃`: Peebles parity cancellation (`spin g + spin (σ g) = 0` and `2 • ∑ g, spin g = 0`),
4. `𝔍𝔚₄`: Commutative collapse (`P * Q = Q * P → genV P Q Q = 0 ∧ genSig P Q Q = 0`),
5. `𝔍𝔚₅`: Heisenberg–Gödel commutator square (`[P, Q]² = -genV P Q Q`) and diagonal Peirce defects,
6. `𝔍𝔚₆`: Quarantine collapse when corner excursions vanish,
7. `𝔍𝔚₇`: Constructive equivalence between non-vanishing quantum corner excursions and
   diagonal Peirce non-idempotence.
-/
theorem wheeler_godel_quantum_existence_master_synthesis
    {G : Type*} [AddCommGroup G] (x y z c : G)
    {X : Type*} (step : X → X) (x0 : X) (L : ℕ) (h_ctc : (step^[L] x0) = x0) (m k : ℕ)
    {Cat R : Type*} [AddCommGroup R] [Fintype Cat]
    (σ : Cat ≃ Cat) (spin : Cat → R) (h_parity : ∀ g : Cat, spin (σ g) = -spin g) (g0 : Cat)
    {B : Type*} [Ring B] (P Q : B) (hP : P * P = P) (hQ : Q * Q = Q) :
    ((x + c) - (y + c) = x - y ∧
     ((x + c) - (y + c)) + ((y + c) - (z + c)) = x - z) ∧
    ((step^[m + L] x0) = (step^[m] x0) ∧
     (step^[m + k * L] x0) = (step^[m] x0)) ∧
    (spin g0 + spin (σ g0) = 0 ∧
     2 • (∑ g : Cat, spin g) = 0) ∧
    (P * Q = Q * P → genV P Q Q = 0 ∧ genSig P Q Q = 0) ∧
    (OperatorAlgebra.PeirceSpine.comm P (evenGrade P Q) = 0 ∧
     OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = -genV P Q Q ∧
     peirce11 P Q - peirce11 P Q * peirce11 P Q = conePlus P Q * coneMinus P Q ∧
     peirce00 P Q - peirce00 P Q * peirce00 P Q = coneMinus P Q * conePlus P Q ∧
     evenGrade P Q - evenGrade P Q * evenGrade P Q = genV P Q Q) ∧
    (conePlus P Q * coneMinus P Q = 0 → coneMinus P Q * conePlus P Q = 0 →
      genV P Q Q = 0 ∧
      OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = 0 ∧
      peirce11 P Q * peirce11 P Q = peirce11 P Q ∧
      peirce00 P Q * peirce00 P Q = peirce00 P Q) ∧
    ((conePlus P Q * coneMinus P Q ≠ 0 ∨ coneMinus P Q * conePlus P Q ≠ 0) ↔
     (peirce11 P Q * peirce11 P Q ≠ peirce11 P Q ∨ peirce00 P Q * peirce00 P Q ≠ peirce00 P Q)) := by
  rcases peirce_idempotent_corner_excursion_defects P Q hP hQ with ⟨h_11_def, h_00_def, h_comm_even⟩
  have h_comm : OperatorAlgebra.PeirceSpine.comm P Q = genJ P Q Q := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, genJ, conePlus, coneMinus]
    noncomm_ring
  have h_sq : OperatorAlgebra.PeirceSpine.comm P Q * OperatorAlgebra.PeirceSpine.comm P Q = -genV P Q Q := by
    rw [h_comm]
    peirce_nf hP
  have h_even_split :
      evenGrade P Q - evenGrade P Q * evenGrade P Q =
        (peirce11 P Q - peirce11 P Q * peirce11 P Q) +
          (peirce00 P Q - peirce00 P Q * peirce00 P Q) := by
    peirce_nf hP
  have h_even_def : evenGrade P Q - evenGrade P Q * evenGrade P Q = genV P Q Q := by
    rw [h_even_split, h_11_def, h_00_def]
    rfl
  have h_sum_eq : (∑ g : Cat, spin (σ g)) = ∑ g : Cat, spin g :=
    Equiv.sum_comp σ spin
  have h_sum_neg : (∑ g : Cat, spin (σ g)) = -(∑ g : Cat, spin g) := by
    calc
      (∑ g : Cat, spin (σ g)) = ∑ g : Cat, (-spin g) :=
        Finset.sum_congr rfl (fun g _ => h_parity g)
      _ = -(∑ g : Cat, spin g) := by rw [Finset.sum_neg_distrib]
  have h_two_sum : 2 • (∑ g : Cat, spin g) = 0 := by
    calc
      2 • (∑ g : Cat, spin g) = (∑ g : Cat, spin g) + (∑ g : Cat, spin g) :=
        two_nsmul (∑ g : Cat, spin g)
      _ = (∑ g : Cat, spin g) + (∑ g : Cat, spin (σ g)) := by rw [h_sum_eq]
      _ = (∑ g : Cat, spin g) + (-(∑ g : Cat, spin g)) := by rw [h_sum_neg]
      _ = 0 := add_neg_cancel (∑ g : Cat, spin g)
  have h_up_ne : conePlus P Q * coneMinus P Q ≠ 0 ↔ peirce11 P Q * peirce11 P Q ≠ peirce11 P Q := by
    refine not_congr ?_
    rw [← h_11_def, sub_eq_zero, eq_comm]
  have h_dn_ne : coneMinus P Q * conePlus P Q ≠ 0 ↔ peirce00 P Q * peirce00 P Q ≠ peirce00 P Q := by
    refine not_congr ?_
    rw [← h_00_def, sub_eq_zero, eq_comm]
  refine ⟨⟨by abel, by abel⟩,
          ⟨by rw [Function.iterate_add_apply, h_ctc],
           godel_closed_timelike_loop_periodicity_mul step x0 L h_ctc k m⟩,
          ⟨by rw [h_parity g0, add_neg_cancel], h_two_sum⟩,
          fun hComm => by
            have hCp : conePlus P Q = 0 := by
              calc
                conePlus P Q = (P * Q) * (1 - P) := rfl
                _ = (Q * P) * (1 - P) := by rw [hComm]
                _ = Q * P - Q * (P * P) := by noncomm_ring
                _ = Q * P - Q * P := by rw [hP]
                _ = 0 := sub_self (Q * P)
            have hCm : coneMinus P Q = 0 := by
              calc
                coneMinus P Q = (1 - P) * (Q * P) := by dsimp [coneMinus]; noncomm_ring
                _ = (1 - P) * (P * Q) := by rw [← hComm]
                _ = P * Q - (P * P) * Q := by noncomm_ring
                _ = P * Q - P * Q := by rw [hP]
                _ = 0 := sub_self (P * Q)
            exact ⟨by dsimp [genV, anticomm]; rw [hCp, hCm, zero_mul, add_zero],
                   by dsimp [genSig, OperatorAlgebra.PeirceSpine.comm]; rw [hCp, hCm, zero_mul, sub_zero]⟩,
          ⟨h_comm_even, h_sq, h_11_def, h_00_def, h_even_def⟩,
          fun h_up h_dn => by
            have hV : genV P Q Q = 0 := by
              dsimp [genV, anticomm]; rw [h_up, h_dn, add_zero]
            have h11 : peirce11 P Q * peirce11 P Q = peirce11 P Q := by
              have h_d := h_11_def; rw [h_up] at h_d; exact (sub_eq_zero.mp h_d).symm
            have h00 : peirce00 P Q * peirce00 P Q = peirce00 P Q := by
              have h_d := h_00_def; rw [h_dn] at h_d; exact (sub_eq_zero.mp h_d).symm
            exact ⟨hV, by rw [h_sq, hV, neg_zero], h11, h00⟩,
          or_congr h_up_ne h_dn_ne⟩

end InfoGeometry.Canonical.WheelerGodelQuantumExistencePoset
