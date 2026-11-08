/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Doubled Plabic Graphs, Twisted KLT Double Copy & Amplituhedron Foam (`𝔓𝔄₁`–`𝔓𝔄₇`)

## i. Overview
Formalizes bicolored plabic turn duality, rules-of-the-road trip cycles, square-move spurious-pole
cancellation, single-sheet nilpotency vs. doubled Peirce handles, twisted KLT double-copy foam
defects, and graded Leibniz boundary cuts over associative rings.

## ii. Key results
- `plabic_bicolored_turn_duality`, `plabic_trip_dictionary_cycle` (`𝔓𝔄₁`)
- `plabic_square_move_spurious_pole_cancellation` (`𝔓𝔄₂`)
- `single_plabic_sheet_nilpotent_vs_doubled_handle` (`𝔓𝔄₃`)
- `peirce_grading_twist_identities`, `klt_twisted_double_copy_foam_defect` (`𝔓𝔄₄`)
- `amplituhedron_boundary_leibniz_and_unitarity_cut` (`𝔓𝔄₅`)
- `popper_surprise_and_survival_of_twisted_klt_foam` (`𝔓𝔄₆`)
- `doubled_plabic_twisted_amplituhedron_master_synthesis` (`𝔓𝔄₇`)

## iii. Table of contents
- Nodes `𝔓𝔄₁`–`𝔓𝔄₂`: Plabic turn involution, trip cycles, and square-move pole cancellation
- Nodes `𝔓𝔄₃`–`𝔓𝔄₄`: Single-sheet nilpotency vs. doubled twisted KLT handle
- Nodes `𝔓𝔄₅`–`𝔓𝔄₇`: Boundary Leibniz rule, Popper survival, and master synthesis

## iv. References
- Alexander Postnikov, *Total Positivity, Grassmannians, and Networks* (2006)
- Nima Arkani-Hamed and Jaroslav Trnka, *The Amplituhedron* (2014)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `plabic_bicolored_turn_duality`, `plabic_trip_dictionary_cycle`
- `plabic_square_move_spurious_pole_cancellation`
- `single_plabic_sheet_nilpotent_vs_doubled_handle`
- `peirce_grading_twist_identities`, `klt_twisted_double_copy_foam_defect`
- `amplituhedron_boundary_leibniz_and_unitarity_cut`
- `popper_surprise_and_survival_of_twisted_klt_foam`
- `doubled_plabic_twisted_amplituhedron_master_synthesis`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `klt_twisted_double_copy_foam_defect` and `popper_surprise_and_survival_of_twisted_klt_foam`
  (conditional on `P * P = P` and `P * Theta = Theta * P`)

#### BUCKET 3: OPEN CLOSURE DEBT
- Full positive Grassmannian cell decompositions `Gr₊(k, n)`, loop-level momentum-twistor
  canonical differential forms `Ω(𝒜)`, and continuum path-integral graviton scattering amplitudes
  remain external geometric and physical context.
-/

namespace InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam

open InfoGeometry.OperatorAlgebra.PeirceSpine

/--
**Theorem 1A (`𝔓𝔄₁` — `plabic_bicolored_turn_duality`):**
Bicolored vertex involution on `Bool`: flipping color twice is the identity (`!(!c) = c`),
the signed turn weight `cond c 1 (-1) : ℤ` negates under color reversal, and opposite-colored
vertices cancel (`cond c 1 (-1) + cond (!c) 1 (-1) = 0`).
-/
theorem plabic_bicolored_turn_duality (c : Bool) :
    (!(!c)) = c ∧
    cond (!c) (1 : ℤ) (-1) = - cond c (1 : ℤ) (-1) ∧
    cond c (1 : ℤ) (-1) + cond (!c) (1 : ℤ) (-1) = 0 := by
  cases c <;> decide

/--
**Theorem 1B (`𝔓𝔄₁` — `plabic_trip_dictionary_cycle`):**
By Fintype pigeonhole, any plabic rules-of-the-road trip map `trip : Fin n → Fin n` on `n`
ports enters a closed cycle within `n + 1` steps from any initial port `p0 : Fin n`.
-/
theorem plabic_trip_dictionary_cycle
    {n : ℕ} (trip : Fin n → Fin n) (p0 : Fin n) :
    ∃ (i j : Fin (n + 1)), i ≠ j ∧ (trip^[i.val] p0) = (trip^[j.val] p0) := by
  have h_card : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp only [Fintype.card_fin, Nat.lt_succ_self]
  exact Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (n + 1) => trip^[k.val] p0) h_card

/--
**Theorem 2 (`𝔓𝔄₂` — `plabic_square_move_spurious_pole_cancellation`):**
Adjacent BCFW / plabic square-move channels `(A + S_spurious) + (B - S_spurious)` and
`(A + T_spurious) + (B - T_spurious)` cancel their internal spurious boundary terms identically
to yield the same invariant sum `A + B`.
-/
theorem plabic_square_move_spurious_pole_cancellation
    {R : Type*} [Ring R] (A B S_spurious T_spurious : R) :
    (A + S_spurious) + (B - S_spurious) = A + B ∧
    (A + T_spurious) + (B - T_spurious) = A + B ∧
    (A + S_spurious) + (B - S_spurious) = (A + T_spurious) + (B - T_spurious) := by
  have hS : (A + S_spurious) + (B - S_spurious) = A + B := by abel
  have hT : (A + T_spurious) + (B - T_spurious) = A + B := by abel
  exact ⟨hS, hT, hS.trans hT.symm⟩

/--
**Theorem 3 (`𝔓𝔄₃` — `single_plabic_sheet_nilpotent_vs_doubled_handle`):**
For any idempotent cut `P * P = P` and operator `g : B`:
1. Single chiral Peirce sheets are square-zero (`conePlus P g * conePlus P g = 0` and
   `coneMinus P g * coneMinus P g = 0`) and have zero inner projection `peirce11 P`,
2. Doubling both sheets into `genPhi P g g = conePlus P g + coneMinus P g` generates the
   quadratic handle `genPhi P g g * genPhi P g g = genV P g g`.
-/
theorem single_plabic_sheet_nilpotent_vs_doubled_handle
    {B : Type*} [Ring B] (P g : B) (hP : P * P = P) :
    conePlus P g * conePlus P g = 0 ∧
    coneMinus P g * coneMinus P g = 0 ∧
    peirce11 P (conePlus P g) = 0 ∧
    peirce11 P (coneMinus P g) = 0 ∧
    genPhi P g g * genPhi P g g = genV P g g := by
  have h_up : conePlus P g * conePlus P g = 0 := by peirce_nf hP
  have h_dn : coneMinus P g * coneMinus P g = 0 := by peirce_nf hP
  have h_11_up : peirce11 P (conePlus P g) = 0 := by peirce_nf hP
  have h_11_dn : peirce11 P (coneMinus P g) = 0 := by peirce_nf hP
  have h_phi : genPhi P g g * genPhi P g g = genV P g g := by peirce_nf hP
  exact ⟨h_up, h_dn, h_11_up, h_11_dn, h_phi⟩

/--
**Theorem 4A (`𝔓𝔄₄` — `peirce_grading_twist_identities`):**
For any idempotent `P * P = P` and `g : B`, the Peirce grading involution `invS P = 2 • P - 1`
satisfies `invS P * invS P = 1`, twists `genPhi P g g` into the commutator
`invS P * genPhi P g g = comm P g = genJ P g g`, anticommutes with `genPhi P g g`, and squares
on `genPhi P g g` to `-genV P g g`.
-/
theorem peirce_grading_twist_identities
    {B : Type*} [Ring B] (P g : B) (hP : P * P = P) :
    invS P * invS P = 1 ∧
    invS P * genPhi P g g = OperatorAlgebra.PeirceSpine.comm P g ∧
    OperatorAlgebra.PeirceSpine.comm P g = genJ P g g ∧
    invS P * genPhi P g g + genPhi P g g * invS P = 0 ∧
    (invS P * genPhi P g g) * (invS P * genPhi P g g) + genV P g g = 0 := by
  have h_inv : invS P * invS P = 1 := by peirce_nf hP
  have h_comm : OperatorAlgebra.PeirceSpine.comm P g = genJ P g g := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, genJ, conePlus, coneMinus]
    noncomm_ring
  have h_twist_J : invS P * genPhi P g g = genJ P g g := by peirce_nf hP
  have h_twist : invS P * genPhi P g g = OperatorAlgebra.PeirceSpine.comm P g :=
    h_twist_J.trans h_comm.symm
  have h_anti : invS P * genPhi P g g + genPhi P g g * invS P = 0 := by peirce_nf hP
  have h_sq : (invS P * genPhi P g g) * (invS P * genPhi P g g) + genV P g g = 0 := by peirce_nf hP
  exact ⟨h_inv, h_twist, h_comm, h_anti, h_sq⟩

/--
**Theorem 4B (`𝔓𝔄₄` — `klt_twisted_double_copy_foam_defect`):**
For any idempotent `P * P = P`, operator `g : B`, and `P`-commuting twist kernel `Theta : B`
(`P * Theta = Theta * P`), the twisted quadratic compression defect equals the `Theta`-twisted
off-diagonal handle product:
`peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g = conePlus P g * Theta * coneMinus P g`.
-/
theorem klt_twisted_double_copy_foam_defect
    {B : Type*} [Ring B] (P g Theta : B) (hP : P * P = P) (hTheta : P * Theta = Theta * P) :
    peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g =
      conePlus P g * Theta * coneMinus P g := by
  have h_1P_theta : (1 - P) * Theta * (1 - P) = (1 - P) * Theta := by
    calc
      (1 - P) * Theta * (1 - P) = Theta - P * Theta - (Theta * P) + P * (Theta * P) := by
        noncomm_ring
      _ = Theta - P * Theta - (P * Theta) + P * (P * Theta) := by rw [← hTheta]
      _ = Theta - P * Theta - P * Theta + (P * P) * Theta := by noncomm_ring
      _ = Theta - P * Theta - P * Theta + P * Theta := by rw [hP]
      _ = (1 - P) * Theta := by noncomm_ring
  have h_P_theta : P * Theta * P = P * Theta := by
    calc
      P * Theta * P = P * (Theta * P) := by noncomm_ring
      _ = P * (P * Theta) := by rw [← hTheta]
      _ = (P * P) * Theta := by noncomm_ring
      _ = P * Theta := by rw [hP]
  have h1 : P * (g * Theta * g) * P - P * g * (P * Theta * P) * g * P =
      P * g * ((1 - P) * Theta) * g * P := by
    rw [h_P_theta]
    noncomm_ring
  have h2 : conePlus P g * Theta * coneMinus P g =
      P * g * ((1 - P) * Theta * (1 - P)) * g * P := by
    dsimp [conePlus, coneMinus]
    noncomm_ring
  dsimp [peirce11]
  calc
    P * (g * Theta * g) * P - P * g * P * Theta * (P * g * P)
      = P * (g * Theta * g) * P - P * g * (P * Theta * P) * g * P := by noncomm_ring
    _ = P * g * ((1 - P) * Theta) * g * P := h1
    _ = conePlus P g * Theta * coneMinus P g := by rw [h2, h_1P_theta]

/--
**Theorem 5 (`𝔓𝔄₅` — `amplituhedron_boundary_leibniz_and_unitarity_cut`):**
For any idempotent `P * P = P` and operators `X, Y, g : B`:
1. `comm P` satisfies the Leibniz derivation rule `comm P (X * Y) = comm P X * Y + X * comm P Y`,
2. The inner projection of the squared boundary commutator `comm P g * comm P g` cancels the
   quadratic handle `conePlus P g * coneMinus P g`:
   `peirce11 P (comm P g * comm P g) + conePlus P g * coneMinus P g = 0`.
-/
theorem amplituhedron_boundary_leibniz_and_unitarity_cut
    {B : Type*} [Ring B] (P X Y g : B) (hP : P * P = P) :
    OperatorAlgebra.PeirceSpine.comm P (X * Y) =
      OperatorAlgebra.PeirceSpine.comm P X * Y + X * OperatorAlgebra.PeirceSpine.comm P Y ∧
    peirce11 P (OperatorAlgebra.PeirceSpine.comm P g * OperatorAlgebra.PeirceSpine.comm P g) +
      conePlus P g * coneMinus P g = 0 := by
  have h_leib :
      OperatorAlgebra.PeirceSpine.comm P (X * Y) =
        OperatorAlgebra.PeirceSpine.comm P X * Y + X * OperatorAlgebra.PeirceSpine.comm P Y := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have h_comm : OperatorAlgebra.PeirceSpine.comm P g = genJ P g g :=
    (peirce_grading_twist_identities P g hP).2.2.1
  have h_cut_J : peirce11 P (genJ P g g * genJ P g g) + conePlus P g * coneMinus P g = 0 := by
    peirce_nf hP
  have h_cut :
      peirce11 P (OperatorAlgebra.PeirceSpine.comm P g * OperatorAlgebra.PeirceSpine.comm P g) +
        conePlus P g * coneMinus P g = 0 := by
    rw [h_comm]
    exact h_cut_J
  exact ⟨h_leib, h_cut⟩

/--
**Theorem 6 (`𝔓𝔄₆` — `popper_surprise_and_survival_of_twisted_klt_foam`):**
Whenever the `Theta`-twisted compression defect `peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g`
is non-zero, both off-diagonal Peirce channels `conePlus P g` and `coneMinus P g` as well as the
twist kernel `Theta` must be simultaneously non-zero.
-/
theorem popper_surprise_and_survival_of_twisted_klt_foam
    {B : Type*} [Ring B] (P g Theta : B) (hP : P * P = P) (hTheta : P * Theta = Theta * P)
    (h_surv : peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g ≠ 0) :
    conePlus P g ≠ 0 ∧ Theta ≠ 0 ∧ coneMinus P g ≠ 0 := by
  have h_prod : conePlus P g * Theta * coneMinus P g ≠ 0 := by
    rw [← klt_twisted_double_copy_foam_defect P g Theta hP hTheta]
    exact h_surv
  have h_up : conePlus P g ≠ 0 := by
    intro h0
    apply h_prod
    rw [h0, zero_mul, zero_mul]
  have h_th : Theta ≠ 0 := by
    intro h0
    apply h_prod
    rw [h0, mul_zero, zero_mul]
  have h_dn : coneMinus P g ≠ 0 := by
    intro h0
    apply h_prod
    rw [h0, mul_zero]
  exact ⟨h_up, h_th, h_dn⟩

/--
**Theorem 6B (`𝔓𝔄₆` — `peirce_bruhat_positroid_idempotent_and_annihilator`):**
For any idempotent `P * P = P` and `A, C : B`, the degree-3 Bruhat positroid projector
`dressedPeirceProjector P A C = (1 - conePlus P A) * (P + coneMinus P C) * (1 + conePlus P A)`
is an exact idempotent (`dressedPeirceProjector P A C * dressedPeirceProjector P A C = dressedPeirceProjector P A C`)
and is mutually orthogonal to its complementary positroid cell `1 - dressedPeirceProjector P A C`:
`dressedPeirceProjector P A C * (1 - dressedPeirceProjector P A C) = 0` and
`(1 - dressedPeirceProjector P A C) * dressedPeirceProjector P A C = 0`.
-/
theorem peirce_bruhat_positroid_idempotent_and_annihilator
    {B : Type*} [Ring B] (P A C : B) (hP : P * P = P) :
    dressedPeirceProjector P A C * dressedPeirceProjector P A C =
      dressedPeirceProjector P A C ∧
    dressedPeirceProjector P A C * (1 - dressedPeirceProjector P A C) = 0 ∧
    (1 - dressedPeirceProjector P A C) * dressedPeirceProjector P A C = 0 := by
  have h_idem := dressedPeirceProjector_idempotent hP A C
  have h_ann_r : dressedPeirceProjector P A C * (1 - dressedPeirceProjector P A C) = 0 := by
    rw [mul_sub, mul_one, h_idem, sub_self]
  have h_ann_l : (1 - dressedPeirceProjector P A C) * dressedPeirceProjector P A C = 0 := by
    rw [sub_mul, one_mul, h_idem, sub_self]
  exact ⟨h_idem, h_ann_r, h_ann_l⟩

/--
**Theorem 7 (`𝔓𝔄₇` — `doubled_plabic_twisted_amplituhedron_master_synthesis`):**
Master synthesis uniting linear wave cancellation, quadratic doubled-plabic handle ignition,
Peirce grading twist, `Theta`-twisted KLT double-copy defect, and boundary commutator cut.
-/
theorem doubled_plabic_twisted_amplituhedron_master_synthesis
    {B : Type*} [Ring B] (P g Theta : B) (hP : P * P = P) (hTheta : P * Theta = Theta * P) :
    peirce11 P (genPhi P g g) = 0 ∧
    genPhi P g g * genPhi P g g = genV P g g ∧
    invS P * genPhi P g g = OperatorAlgebra.PeirceSpine.comm P g ∧
    peirce11 P (g * Theta * g) - peirce11 P g * Theta * peirce11 P g =
      conePlus P g * Theta * coneMinus P g ∧
    peirce11 P (OperatorAlgebra.PeirceSpine.comm P g * OperatorAlgebra.PeirceSpine.comm P g) =
      - (conePlus P g * coneMinus P g) := by
  have h_lin : peirce11 P (genPhi P g g) = 0 := by peirce_nf hP
  have h_quad : genPhi P g g * genPhi P g g = genV P g g := by peirce_nf hP
  have h_twist_all := peirce_grading_twist_identities P g hP
  have h_klt := klt_twisted_double_copy_foam_defect P g Theta hP hTheta
  have h_cut_J :
      peirce11 P (genJ P g g * genJ P g g) = - (conePlus P g * coneMinus P g) := by
    peirce_nf hP
  have h_cut :
      peirce11 P (OperatorAlgebra.PeirceSpine.comm P g * OperatorAlgebra.PeirceSpine.comm P g) =
        - (conePlus P g * coneMinus P g) := by
    rw [h_twist_all.2.2.1]
    exact h_cut_J
  exact ⟨h_lin, h_quad, h_twist_all.2.1, h_klt, h_cut⟩

end InfoGeometry.Canonical.DoubledPlabicTwistedAmplituhedronFoam
