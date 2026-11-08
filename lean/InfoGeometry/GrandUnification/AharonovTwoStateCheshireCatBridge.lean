/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.ModularTomitaTwoStateKleinBridge
import InfoGeometry.QuantumContext.AharonovTwoStateSphereTime
import InfoGeometry.GrandUnification.ModularPhaseSeparation
import InfoGeometry.GrandUnification.ModularHamiltonian

/-!
# Aharonov Two-State Vector Formalism, Quantum Cheshire Cat & Counter-Particle Modular Bridge

This module formalizes the exact operator-algebraic core of Yakir Aharonov's Two-State Vector
Formalism (TSVF / ABL theory), weak values, the **Quantum Cheshire Cat** (separation of a
particle's position from its spin in a two-arm interferometer), **Quantum Counter-Particles**
(negative weak occupation in the 3-box / two-slit setup with conserved total particle number),
and the **Heisenberg–Weyl non-local modular shift equation of motion**, connected directly to
the repository's Tomita–Takesaki / Krein twin-sheet modular architecture.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.ModularTomitaTwoStateKlein`: `J_swap`, `J_sq`,
    `J_swaps_Peirce_plus`, `J_swaps_Peirce_minus`, `J_inverts_eta`, `TwoStateVector`,
    `tsvfTransition`, `tsvfOverlap`.
  * `InfoGeometry.QuantumContext.AharonovTime`: `SlitState2D`, `two_state_weak_partition`,
    `standard_qm_slit1_nonneg`.
  * `InfoGeometry.GrandUnification.ModularPhaseSeparation`:
    `IsKreinSymmetry`, `IsOddOperator`, `clifford_bivector_square_eq_neg_one`.
  * `InfoGeometry.GrandUnification.Dynamics`:
    `modular_hamiltonian_twin_sheet_time_reversal`, `time_requires_horizon_trace_capacitance`.
- BUCKET 2 (Deconfabulation):
  * Separates historical and interpretive prose from exact finite-dimensional matrix and
    module identities over any commutative ring `R`.
  * Proves that in single-vector quantum mechanics ($\Phi = \Psi$), vanishing right-arm
    amplitude $\Pi_R \psi = 0$ forces vanishing right-arm spin $(\Pi_R \Sigma_z) \psi = 0$
    (`single_state_no_cheshire_cat_separation`), whereas in the Two-State Vector Formalism
    ($\langle\Phi| \ne \langle\Psi|$), the particle resides exclusively in the Left arm
    ($\langle\Phi|\Pi_L|\Psi\rangle = \langle\Phi|\Psi\rangle = 2$,
    $\langle\Phi|\Pi_R|\Psi\rangle = 0$) while its spin polarization resides exclusively in
    the Right arm ($\langle\Phi|\Pi_L\Sigma_z|\Psi\rangle = 0$,
    $\langle\Phi|\Pi_R\Sigma_z|\Psi\rangle = \langle\Phi|\Psi\rangle = 2$).
  * Proves the 3-box Quantum Counter-Particle theorem (`three_box_counter_particle_theorem`)
    and the Heisenberg–Weyl modular shift eigenstate translation law
    (`heisenberg_modular_shift_weyl_commutation`).
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `sum_fin_4`
  * `cheshirePathLeft_mul_cheshireArmSwap_ne`
  * `cheshire_projectors_and_spin_algebra`
  * `single_state_no_cheshire_cat_separation`
  * `quantum_cheshire_cat_separation_theorem`
  * `three_box_counter_particle_theorem`
  * `heisenberg_modular_shift_weyl_commutation`
  * `aharonov_two_state_grand_unification_synthesis`
-/

namespace InfoGeometry.GrandUnification.AharonovTwoStateCheshireCatBridge

open Matrix
open scoped Matrix BigOperators
open InfoGeometry.Canonical.KreinDoubledCartanPeirce
open InfoGeometry.Canonical.ModularTomitaTwoStateKlein
open InfoGeometry.GrandUnification.ModularPhaseSeparation
open InfoGeometry.GrandUnification.Dynamics

variable {R : Type*} [CommRing R]

/-! ## Section 1: Four-State Interferometer $\mathcal{H}_{\mathrm{path}} \otimes \mathcal{H}_{\mathrm{spin}} \cong R^4$ -/

/-- Explicit four-term expansion of a sum over `Fin 4`. -/
lemma sum_fin_4 {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) :
    ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_four]

/-- Left-arm path projector $\Pi_L = P_L \otimes I_2 = \operatorname{diag}(1, 1, 0, 0)$
on basis $(|L,\uparrow\rangle, |L,\downarrow\rangle, |R,\uparrow\rangle, |R,\downarrow\rangle)$. -/
def cheshirePathLeft : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- Right-arm path projector $\Pi_R = P_R \otimes I_2 = \operatorname{diag}(0, 0, 1, 1)$. -/
def cheshirePathRight : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Spin-polarization operator $\Sigma_z = I_2 \otimes \sigma_z
  = \operatorname{diag}(1, -1, 1, -1)$. -/
def cheshireSpinZ : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- Interferometer arm-exchange operator $X_{\mathrm{path}} \otimes I_2$ swapping $|L\rangle \leftrightarrow |R\rangle$. -/
def cheshireArmSwap : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Non-commutativity witness on `Matrix (Fin 4) (Fin 4) R`: the Left-arm path projector
`cheshirePathLeft` does not commute with the interferometer arm-swap operator
`cheshireArmSwap` over any nontrivial ring `R`. -/
theorem cheshirePathLeft_mul_cheshireArmSwap_ne [Nontrivial R] :
    cheshirePathLeft (R := R) * cheshireArmSwap (R := R) ≠
      cheshireArmSwap (R := R) * cheshirePathLeft (R := R) := by
  intro h
  have h02 :
      (cheshirePathLeft (R := R) * cheshireArmSwap (R := R)) 0 2 =
        (cheshireArmSwap (R := R) * cheshirePathLeft (R := R)) 0 2 :=
    congrFun (congrFun h 0) 2
  rw [mul_apply, mul_apply, sum_fin_4, sum_fin_4] at h02
  change (1 : R) * 1 + 0 * 0 + 0 * 0 + 0 * 0 =
    (0 : R) * 0 + 0 * 0 + 1 * 0 + 0 * 0 at h02
  simp only [mul_one, mul_zero, add_zero] at h02
  exact one_ne_zero h02

/-- Complete algebraic package for the interferometer path projectors and spin operator:
1. $\Pi_L^2 = \Pi_L$ and $\Pi_R^2 = \Pi_R$,
2. $\Pi_L \Pi_R = 0$ and $\Pi_R \Pi_L = 0$,
3. $\Pi_L + \Pi_R = 1$,
4. $\Sigma_z^2 = 1$, and
5. $\Pi_L \Sigma_z = \Sigma_z \Pi_L$ and $\Pi_R \Sigma_z = \Sigma_z \Pi_R$. -/
theorem cheshire_projectors_and_spin_algebra :
    cheshirePathLeft (R := R) * cheshirePathLeft = cheshirePathLeft ∧
    cheshirePathRight (R := R) * cheshirePathRight = cheshirePathRight ∧
    cheshirePathLeft (R := R) * cheshirePathRight = 0 ∧
    cheshirePathRight (R := R) * cheshirePathLeft = 0 ∧
    cheshirePathLeft (R := R) + cheshirePathRight = 1 ∧
    cheshireSpinZ (R := R) * cheshireSpinZ = 1 ∧
    cheshirePathLeft (R := R) * cheshireSpinZ = cheshireSpinZ * cheshirePathLeft ∧
    cheshirePathRight (R := R) * cheshireSpinZ = cheshireSpinZ * cheshirePathRight := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathLeft, mul_apply, sum_fin_4]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathRight, mul_apply, sum_fin_4]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathLeft, cheshirePathRight, mul_apply, sum_fin_4]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathLeft, cheshirePathRight, mul_apply, sum_fin_4]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathLeft, cheshirePathRight, one_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshireSpinZ, mul_apply, sum_fin_4, one_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathLeft, cheshireSpinZ, mul_apply, sum_fin_4]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [cheshirePathRight, cheshireSpinZ, mul_apply, sum_fin_4]

/-! ## Section 2: The Quantum Cheshire Cat Separation Theorem -/

/-- Two-state bilinear pairing $\langle \Phi | M | \Psi \rangle = \Phi \cdot (M *ᵥ \Psi)$
on the 4-dimensional path-spin space `Fin 4 → R`. -/
def twoStatePairing4 (Φ : Fin 4 → R) (M : Matrix (Fin 4) (Fin 4) R) (Ψ : Fin 4 → R) : R :=
  Φ 0 * (M *ᵥ Ψ) 0 + Φ 1 * (M *ᵥ Ψ) 1 + Φ 2 * (M *ᵥ Ψ) 2 + Φ 3 * (M *ᵥ Ψ) 3

/-- Two-state overlap $\langle \Phi | \Psi \rangle$ on `Fin 4 → R`. -/
def twoStateOverlap4 (Φ Ψ : Fin 4 → R) : R :=
  Φ 0 * Ψ 0 + Φ 1 * Ψ 1 + Φ 2 * Ψ 2 + Φ 3 * Ψ 3

/-- **Single-State No-Go Theorem (`single_state_no_cheshire_cat_separation`):**
If a pre-selected state $\Psi$ has zero amplitude in the Right arm ($\Pi_R *ᵥ \Psi = 0$),
then the Right-arm spin operator $\Pi_R \Sigma_z = \Sigma_z \Pi_R$ also annihilates $\Psi$:
$(\Pi_R \Sigma_z) *ᵥ \Psi = 0$,
  for every $\Phi$, $\langle \Phi | \Pi_R \Sigma_z | \Psi \rangle
  = 0$.
In particular, in 1-vector QM ($\Phi = \Psi$), if the particle is absent from the Right arm
($\Pi_R *ᵥ \Psi = 0$), its spin in the Right arm is identically zero. -/
theorem single_state_no_cheshire_cat_separation
    (Φ Ψ : Fin 4 → R)
    (hR_zero : cheshirePathRight (R := R) *ᵥ Ψ = 0) :
    (cheshirePathRight (R := R) * cheshireSpinZ) *ᵥ Ψ = 0 ∧
    twoStatePairing4 Φ (cheshirePathRight (R := R) * cheshireSpinZ) Ψ = 0 := by
  have hcomm : cheshirePathRight (R := R) * cheshireSpinZ =
      cheshireSpinZ * cheshirePathRight :=
    cheshire_projectors_and_spin_algebra.2.2.2.2.2.2.2
  have hvec : (cheshirePathRight (R := R) * cheshireSpinZ) *ᵥ Ψ = 0 := by
    rw [hcomm, ← mulVec_mulVec, hR_zero, mulVec_zero]
  refine ⟨hvec, ?_⟩
  unfold twoStatePairing4
  rw [hvec]
  simp

/-- Aharonov–Popescu pre-selected Cheshire Cat state
$|\Psi_{\mathrm{CC}}\rangle = (1, 1, 1, -1)^T
  = |L\rangle(|{\uparrow}\rangle + |{\downarrow}\rangle) + |R\rangle(|{\uparrow}\rangle - |{\downarrow}\rangle)$. -/
def cheshirePreState : Fin 4 → R :=
  ![1, 1, 1, -1]

/-- Aharonov–Popescu post-selected Cheshire Cat state
$\langle\Phi_{\mathrm{CC}}| = (1, 1, 1, 1)
  = (\langle L| + \langle R|)(\langle\uparrow| + \langle\downarrow|)$. -/
def cheshirePostState : Fin 4 → R :=
  ![1, 1, 1, 1]

/-- **The Quantum Cheshire Cat Theorem (`quantum_cheshire_cat_separation_theorem`):**
For the pre-selected state $|\Psi_{\mathrm{CC}}\rangle = (1, 1, 1, -1)$ and post-selected state
$\langle\Phi_{\mathrm{CC}}| = (1, 1, 1, 1)$ over any commutative ring `R`:
1. **Non-vanishing overlap:** $\langle\Phi_{\mathrm{CC}} | \Psi_{\mathrm{CC}}\rangle = 2$;
2. **The Cat (particle presence) is 100% in the Left arm:**
   $\langle\Phi_{\mathrm{CC}} | \Pi_L | \Psi_{\mathrm{CC}}\rangle = 2
  = \langle\Phi_{\mathrm{CC}} | \Psi_{\mathrm{CC}}\rangle$
   and $\langle\Phi_{\mathrm{CC}} | \Pi_R | \Psi_{\mathrm{CC}}\rangle = 0$;
3. **The Grin (spin polarization $\Sigma_z$) is 100% in the Right arm:**
   $\langle\Phi_{\mathrm{CC}} | \Pi_L \Sigma_z | \Psi_{\mathrm{CC}}\rangle = 0$

  $\langle\Phi_{\mathrm{CC}} | \Pi_R \Sigma_z | \Psi_{\mathrm{CC}}\rangle = 2
  = \langle\Phi_{\mathrm{CC}} | \Psi_{\mathrm{CC}}\rangle$;
4. **Weak Partition Conservation:**
   $\langle\Phi_{\mathrm{CC}} | \Pi_L | \Psi_{\mathrm{CC}}\rangle + \langle\Phi_{\mathrm{CC}} | \Pi_R | \Psi_{\mathrm{CC}}\rangle = \langle\Phi_{\mathrm{CC}} | \Psi_{\mathrm{CC}}\rangle$
   and
   $\langle\Phi_{\mathrm{CC}} | \Pi_L \Sigma_z | \Psi_{\mathrm{CC}}\rangle + \langle\Phi_{\mathrm{CC}} | \Pi_R \Sigma_z | \Psi_{\mathrm{CC}}\rangle = \langle\Phi_{\mathrm{CC}} | \Sigma_z | \Psi_{\mathrm{CC}}\rangle = 2$. -/
theorem quantum_cheshire_cat_separation_theorem :
    twoStateOverlap4 (cheshirePostState (R := R)) (cheshirePreState (R := R)) = 2 ∧
    twoStatePairing4 (cheshirePostState (R := R)) cheshirePathLeft (cheshirePreState (R := R)) = 2 ∧
    twoStatePairing4 (cheshirePostState (R := R)) cheshirePathRight (cheshirePreState (R
  := R)) = 0 ∧
    twoStatePairing4 (cheshirePostState (R := R))
      (cheshirePathLeft * cheshireSpinZ) (cheshirePreState (R := R)) = 0 ∧
    twoStatePairing4 (cheshirePostState (R := R))
      (cheshirePathRight * cheshireSpinZ) (cheshirePreState (R := R)) = 2 ∧
    twoStatePairing4 (cheshirePostState (R := R)) cheshireSpinZ (cheshirePreState (R := R)) = 2 ∧
    twoStatePairing4 (cheshirePostState (R := R)) cheshirePathLeft (cheshirePreState (R := R)) +
      twoStatePairing4 (cheshirePostState (R := R)) cheshirePathRight (cheshirePreState (R := R)) =
      twoStateOverlap4 (cheshirePostState (R := R)) (cheshirePreState (R := R)) ∧
    twoStatePairing4 (cheshirePostState (R := R))
      (cheshirePathLeft * cheshireSpinZ) (cheshirePreState (R := R)) +
      twoStatePairing4 (cheshirePostState (R := R))
      (cheshirePathRight * cheshireSpinZ) (cheshirePreState (R := R)) =
      twoStatePairing4 (cheshirePostState (R := R)) cheshireSpinZ (cheshirePreState (R := R)) := by
  have h1 : twoStateOverlap4 (cheshirePostState (R := R)) (cheshirePreState (R := R)) = 2 := by
    unfold twoStateOverlap4 cheshirePostState cheshirePreState
    change (1 : R) * 1 + 1 * 1 + 1 * 1 + 1 * (-1) = 2
    ring
  have hL_vec : cheshirePathLeft (R := R) *ᵥ cheshirePreState (R := R) = ![1, 1, 0, 0] := by
    ext i; fin_cases i <;>
      simp [cheshirePathLeft, cheshirePreState, mulVec, dotProduct, sum_fin_4]
  have hR_vec : cheshirePathRight (R := R) *ᵥ cheshirePreState (R := R) = ![0, 0, 1, -1] := by
    ext i; fin_cases i <;>
      simp [cheshirePathRight, cheshirePreState, mulVec, dotProduct, sum_fin_4]
  have hS_vec : cheshireSpinZ (R := R) *ᵥ cheshirePreState (R := R) = ![1, -1, 1, 1] := by
    ext i; fin_cases i <;>
      simp [cheshireSpinZ, cheshirePreState, mulVec, dotProduct, sum_fin_4]
  have hLS_vec :
      (cheshirePathLeft (R := R) * cheshireSpinZ) *ᵥ cheshirePreState (R := R) = ![1, -1, 0, 0]
  := by
    rw [← mulVec_mulVec, hS_vec]
    ext i; fin_cases i <;>
      simp [cheshirePathLeft, mulVec, dotProduct, sum_fin_4]
  have hRS_vec :
      (cheshirePathRight (R := R) * cheshireSpinZ) *ᵥ cheshirePreState (R := R) = ![0, 0, 1, 1]
  := by
    rw [← mulVec_mulVec, hS_vec]
    ext i; fin_cases i <;>
      simp [cheshirePathRight, mulVec, dotProduct, sum_fin_4]
  have h2 : twoStatePairing4 (cheshirePostState (R := R)) cheshirePathLeft (cheshirePreState (R
  := R)) = 2 := by
    unfold twoStatePairing4
    rw [hL_vec]
    unfold cheshirePostState
    change (1 : R) * 1 + 1 * 1 + 1 * 0 + 1 * 0 = 2
    ring
  have h3 : twoStatePairing4 (cheshirePostState (R := R)) cheshirePathRight (cheshirePreState (R
  := R)) = 0 := by
    unfold twoStatePairing4
    rw [hR_vec]
    unfold cheshirePostState
    change (1 : R) * 0 + 1 * 0 + 1 * 1 + 1 * (-1) = 0
    ring
  have h4 : twoStatePairing4 (cheshirePostState (R := R))
      (cheshirePathLeft * cheshireSpinZ) (cheshirePreState (R := R)) = 0 := by
    unfold twoStatePairing4
    rw [hLS_vec]
    unfold cheshirePostState
    change (1 : R) * 1 + 1 * (-1) + 1 * 0 + 1 * 0 = 0
    ring
  have h5 : twoStatePairing4 (cheshirePostState (R := R))
      (cheshirePathRight * cheshireSpinZ) (cheshirePreState (R := R)) = 2 := by
    unfold twoStatePairing4
    rw [hRS_vec]
    unfold cheshirePostState
    change (1 : R) * 0 + 1 * 0 + 1 * 1 + 1 * 1 = 2
    ring
  have h6 : twoStatePairing4 (cheshirePostState (R := R)) cheshireSpinZ (cheshirePreState (R
  := R)) = 2 := by
    unfold twoStatePairing4
    rw [hS_vec]
    unfold cheshirePostState
    change (1 : R) * 1 + 1 * (-1) + 1 * 1 + 1 * 1 = 2
    ring
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_⟩
  · rw [h2, h3, h1, add_zero]
  · rw [h4, h5, h6, zero_add]

/-! ## Section 3: The 3-Box Paradox & Quantum Counter-Particles (`(N_2)_w = -1`) -/

/-- Three-box two-state overlap $\langle \Phi | \Psi \rangle$ on `Fin 3 → R`. -/
def threeBoxOverlap (Φ Ψ : Fin 3 → R) : R :=
  Φ 0 * Ψ 0 + Φ 1 * Ψ 1 + Φ 2 * Ψ 2

/-- Weak box-occupation numerator $\langle \Phi | P_k | \Psi \rangle
  = \Phi_k \Psi_k$ for box $k \in \mathrm{Fin}\,3$. -/
def boxWeakNumerator (k : Fin 3) (Φ Ψ : Fin 3 → R) : R :=
  Φ k * Ψ k

/-- Pre-selected 3-box state $|\Psi_{\mathrm{box}}\rangle = (1, 1, 1)^T$. -/
def threeBoxPreState : Fin 3 → R :=
  ![1, 1, 1]

/-- Post-selected 3-box state $\langle\Phi_{\mathrm{box}}| = (1, 1, -1)$. -/
def threeBoxPostState : Fin 3 → R :=
  ![1, 1, -1]

/-- **Aharonov 3-Box Quantum Counter-Particle Theorem (`three_box_counter_particle_theorem`):**
For $|\Psi_{\mathrm{box}}\rangle = (1, 1, 1)$ and $\langle\Phi_{\mathrm{box}}| = (1, 1, -1)$:
1. Unit overlap: $\langle\Phi_{\mathrm{box}} | \Psi_{\mathrm{box}}\rangle
  = 1$ (so weak values equal their numerators);
2. Box 0 has weak particle number $+1$;
3. Box 1 has weak particle number $+1$;
4. Box 2 hosts a **Quantum Counter-Particle** with negative weak occupation $-1$;
5. Total weak particle number across all three boxes is strictly conserved:
   $1 + 1 + (-1) = 1 = \langle\Phi_{\mathrm{box}} | \Psi_{\mathrm{box}}\rangle$. -/
theorem three_box_counter_particle_theorem :
    threeBoxOverlap (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = 1 ∧
    boxWeakNumerator 0 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = 1 ∧
    boxWeakNumerator 1 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = 1 ∧
    boxWeakNumerator 2 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = -1 ∧
    boxWeakNumerator 0 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) +
      boxWeakNumerator 1 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) +
      boxWeakNumerator 2 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) =
      threeBoxOverlap (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold threeBoxOverlap threeBoxPostState threeBoxPreState
    change (1 : R) * 1 + 1 * 1 + (-1) * 1 = 1
    noncomm_ring
  · unfold boxWeakNumerator threeBoxPostState threeBoxPreState
    change (1 : R) * 1 = 1
    noncomm_ring
  · unfold boxWeakNumerator threeBoxPostState threeBoxPreState
    change (1 : R) * 1 = 1
    noncomm_ring
  · unfold boxWeakNumerator threeBoxPostState threeBoxPreState
    change (-1 : R) * 1 = -1
    noncomm_ring
  · unfold boxWeakNumerator threeBoxOverlap threeBoxPostState threeBoxPreState
    change (1 : R) * 1 + 1 * 1 + (-1) * 1 = 1 * 1 + 1 * 1 + (-1) * 1
    noncomm_ring

/-! ## Section 4: Heisenberg Non-Local Modular Shift Equation & Uncertainty Protection -/

/-- **Heisenberg–Weyl Modular Shift Eigenstate Translation (`heisenberg_modular_shift_weyl_commutation`):**
Let $X, T_L \in \mathrm{End}_R(M)$ satisfy the non-local Heisenberg–Weyl slit-shift commutation
relation $X T_L - T_L X = L \cdot T_L$ (modeling position $X$ and the modular momentum translation
operator $T_L = e^{i p L/\hbar}$ across slit separation $L$).
Then:
1. $X T_L = T_L X + L \cdot T_L$;
2. For any slit-localized eigenstate $v \in M$ with $X v = x_0 \cdot v$, the modular-shifted
   state $T_L v$ is an eigenstate of $X$ at the translated slit position $x_0 + L$:
   $X (T_L v) = (x_0 + L) \cdot (T_L v)$. -/
theorem heisenberg_modular_shift_weyl_commutation
    {M : Type*} [AddCommGroup M] [Module R M]
    (X T_L : Module.End R M) (L x₀ : R) (v : M)
    (h_weyl : X * T_L - T_L * X = L • T_L)
    (h_slit : X v = x₀ • v) :
    X * T_L = T_L * X + L • T_L ∧
    X (T_L v) = (x₀ + L) • (T_L v) := by
  have hXT : X * T_L = T_L * X + L • T_L :=
    sub_eq_iff_eq_add'.mp h_weyl
  refine ⟨hXT, ?_⟩
  have h_eval : (X * T_L) v = (T_L * X + L • T_L) v :=
    congrArg (fun F : Module.End R M => F v) hXT
  calc
    X (T_L v) = (X * T_L) v := by rw [Module.End.mul_apply]
    _ = (T_L * X + L • T_L) v := h_eval
    _ = T_L (X v) + L • (T_L v) := by
      rw [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply]
    _ = T_L (x₀ • v) + L • (T_L v) := by rw [h_slit]
    _ = x₀ • (T_L v) + L • (T_L v) := by rw [LinearMap.map_smul]
    _ = (x₀ + L) • (T_L v) := (add_smul x₀ L (T_L v)).symm

/-! ## Section 5: Master Synthesis — Aharonov Two-State Vector Formalism & Modular Horizon -/

/-- **Aharonov Two-State, Quantum Cheshire Cat, Counter-Particle & Modular Horizon Synthesis
(`aharonov_two_state_grand_unification_synthesis`):**
Unifies in one kernel-checked theorem:
1. **Tomita–Takesaki / Klein-Bottle Two-State Time Inversion:**
   $J_{\mathrm{swap}}^2 = 1$, $J_{\mathrm{swap}} P_+ J_{\mathrm{swap}} = P_-$, and
   $J_{\mathrm{swap}} \eta J_{\mathrm{swap}} = -\eta$ (forward sheet $\mathcal{H}_+$ and backward
   sheet $\mathcal{H}_-$ exchanged by modular conjugation);
2. **Boundary $\mathrm{Cl}(1,1)$ Majorana Bivector:**
   $J_\Delta \mathcal{T} J_\Delta = -\mathcal{T}$, $\mathcal{T} J_\Delta \mathcal{T} = -J_\Delta$,
   and $(J_\Delta \mathcal{T})^2 = -1$ on the modular phase-separation boundary;
3. **Quantum Cheshire Cat Separation:**
   $\langle\Phi_{\mathrm{CC}}|\Pi_L|\Psi_{\mathrm{CC}}\rangle = 2$,
   $\langle\Phi_{\mathrm{CC}}|\Pi_R|\Psi_{\mathrm{CC}}\rangle = 0$ (cat in Left arm) and
   $\langle\Phi_{\mathrm{CC}}|\Pi_L\Sigma_z|\Psi_{\mathrm{CC}}\rangle = 0$,
   $\langle\Phi_{\mathrm{CC}}|\Pi_R\Sigma_z|\Psi_{\mathrm{CC}}\rangle = 2$ (grin in Right arm);
4. **3-Box Quantum Counter-Particle:**
   weak box occupations $(+1, +1,
  -1)$ summing to $\langle\Phi_{\mathrm{box}}|\Psi_{\mathrm{box}}\rangle = 1$;
5. **Heisenberg–Weyl Modular Shift Translation:**
   $X v = x_0 v \implies X(T_L v) = (x_0 + L)(T_L v)$. -/
theorem aharonov_two_state_grand_unification_synthesis
    {M : Type*} [AddCommGroup M] [Module R M]
    (J_Δ 𝒯 X T_L : Module.End R M)
    (hJ : IsKreinSymmetry J_Δ) (hT : IsKreinSymmetry 𝒯) (hJT : IsOddOperator J_Δ 𝒯)
    (L x₀ : R) (v : M)
    (h_weyl : X * T_L - T_L * X = L • T_L)
    (h_slit : X v = x₀ • v) :
    (J_swap (R := R) * J_swap = 1 ∧
      J_swap (R := R) * P_plus * J_swap = P_minus ∧
      J_swap (R := R) * eta * J_swap = -eta) ∧
    (J_Δ * 𝒯 * J_Δ = - 𝒯 ∧
      𝒯 * J_Δ * 𝒯 = - J_Δ ∧
      (J_Δ * 𝒯) * (J_Δ * 𝒯) = -1) ∧
    (twoStateOverlap4 (cheshirePostState (R := R)) (cheshirePreState (R := R)) = 2 ∧
      twoStatePairing4 (cheshirePostState (R := R)) cheshirePathLeft (cheshirePreState (R
  := R)) = 2 ∧
      twoStatePairing4 (cheshirePostState (R := R)) cheshirePathRight (cheshirePreState (R
  := R)) = 0 ∧
      twoStatePairing4 (cheshirePostState (R := R))
        (cheshirePathLeft * cheshireSpinZ) (cheshirePreState (R := R)) = 0 ∧
      twoStatePairing4 (cheshirePostState (R := R))
        (cheshirePathRight * cheshireSpinZ) (cheshirePreState (R := R)) = 2) ∧
    (threeBoxOverlap (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = 1 ∧
      boxWeakNumerator 0 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = 1 ∧
      boxWeakNumerator 1 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = 1 ∧
      boxWeakNumerator 2 (threeBoxPostState (R := R)) (threeBoxPreState (R := R)) = -1) ∧
    (X * T_L = T_L * X + L • T_L ∧
      X (T_L v) = (x₀ + L) • (T_L v)) := by
  have hCC := quantum_cheshire_cat_separation_theorem (R := R)
  have hBox := three_box_counter_particle_theorem (R := R)
  exact ⟨⟨J_sq, J_swaps_Peirce_plus, J_inverts_eta⟩,
    clifford_bivector_square_eq_neg_one J_Δ 𝒯 hJ hT hJT,
    ⟨hCC.1, hCC.2.1, hCC.2.2.1, hCC.2.2.2.1, hCC.2.2.2.2.1⟩,
    ⟨hBox.1, hBox.2.1, hBox.2.2.1, hBox.2.2.2.1⟩,
    heisenberg_modular_shift_weyl_commutation X T_L L x₀ v h_weyl h_slit⟩

end InfoGeometry.GrandUnification.AharonovTwoStateCheshireCatBridge
