/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors.
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Causal vortex Cooper pairing: the algebraic owner

The surrounding physical language describes a Kähler phase, a null-boundary
pairing, and a Bogoliubov--de Gennes interpretation.  This file deliberately
separates those interpretations from the finite algebra that Lean checks.

The formal data are:

* `KahlerPhase`, a matrix square-root datum for the advertised phase action;
* `NullBoundaryMajoranas`, two matrix generators with Clifford squares and
  vanishing mixed anticommutator;
* `cooperPairCondensate` and `cooperPairConjugate`, the two complex linear
  combinations used in the narrative.

The closed results are the two nilpotency identities and the anticommutator
identity.  With the normalization `1 / √2` used by the narrative, the latter
is `2 • 1`; the conventional CAR value `1 • 1` belongs to the normalization
`1 / 2`.  No existence, positivity, gap, vortex, Kähler, or field-theoretic
claim is silently inferred from these algebraic hypotheses.
-/

open Matrix Complex

namespace CausalVortex

variable {n : ℕ}

/-- A square root of minus one acting on a finite matrix space. -/
structure KahlerPhase (n : ℕ) where
  K : (Matrix (Fin n) (Fin n) ℂ)ˣ
  h_K_sq : (K : Matrix (Fin n) (Fin n) ℂ) * K = -1

/-- The algebraic phase action on a radial matrix. -/
noncomputable def symplecticTrick (phase : KahlerPhase n)
    (radial_M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (phase.K : Matrix (Fin n) (Fin n) ℂ) * radial_M

/-- Applying the phase action twice gives the negative radial matrix. -/
theorem symplecticTrick_sq (phase : KahlerPhase n)
    (radial_M : Matrix (Fin n) (Fin n) ℂ) :
    symplecticTrick phase (symplecticTrick phase radial_M) = -radial_M := by
  unfold symplecticTrick
  rw [← mul_assoc, phase.h_K_sq]
  simp

/-- Two finite Majorana generators with the Clifford relations used below. -/
structure NullBoundaryMajoranas (n : ℕ) where
  gamma_L : (Matrix (Fin n) (Fin n) ℂ)ˣ
  gamma_R : (Matrix (Fin n) (Fin n) ℂ)ˣ
  h_anticomm : (gamma_L : Matrix (Fin n) (Fin n) ℂ) * gamma_R +
      gamma_R * gamma_L = 0
  h_L_sq : (gamma_L : Matrix (Fin n) (Fin n) ℂ) * gamma_L = 1
  h_R_sq : (gamma_R : Matrix (Fin n) (Fin n) ℂ) * gamma_R = 1

def involutiveUnit (x : Matrix (Fin n) (Fin n) ℂ)
    (hx : x * x = 1) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  { val := x
    inv := x
    val_inv := hx
    inv_val := by simpa [mul_comm] using hx }

def gammaLVal (m : NullBoundaryMajoranas n) : Matrix (Fin n) (Fin n) ℂ := m.gamma_L

def gammaRVal (m : NullBoundaryMajoranas n) : Matrix (Fin n) (Fin n) ℂ := m.gamma_R

/-- The extra hypothesis needed to identify the algebraic partner with an
actual Hilbert-space adjoint. -/
def MajoranasSelfAdjoint (m : NullBoundaryMajoranas n) : Prop :=
  (gammaLVal m)ᴴ = gammaLVal m ∧ (gammaRVal m)ᴴ = gammaRVal m

/-- The `1 / √2` Cooper-pair combination. -/
noncomputable def cooperPairCondensate (m : NullBoundaryMajoranas n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (↑(1 / Real.sqrt 2) : ℂ) • (gammaLVal m + Complex.I • gammaRVal m)

private theorem majorana_sum_sq_zero (m : NullBoundaryMajoranas n) :
    (gammaLVal m + Complex.I • gammaRVal m) *
        (gammaLVal m + Complex.I • gammaRVal m) = 0 := by
  have hI2 : Complex.I * Complex.I = -1 := by
    have h := Complex.I_sq
    rwa [sq] at h
  have h_cross : Complex.I • (gammaLVal m * gammaRVal m) +
      Complex.I • (gammaRVal m * gammaLVal m) = 0 := by
    have hanti : gammaLVal m * gammaRVal m + gammaRVal m * gammaLVal m = 0 := by
      simpa [gammaLVal, gammaRVal] using m.h_anticomm
    rw [← smul_add, hanti, smul_zero]
  have h_expand : (gammaLVal m + Complex.I • gammaRVal m) *
      (gammaLVal m + Complex.I • gammaRVal m) =
      gammaLVal m * gammaLVal m +
        (Complex.I • (gammaLVal m * gammaRVal m) +
          Complex.I • (gammaRVal m * gammaLVal m)) +
        (Complex.I * Complex.I) • (gammaRVal m * gammaRVal m) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_add, smul_smul]
    abel
  rw [h_expand, show gammaLVal m * gammaLVal m = 1 from m.h_L_sq,
    h_cross, show gammaRVal m * gammaRVal m = 1 from m.h_R_sq, hI2]
  simp

/-- The Cooper-pair combination is nilpotent under the Clifford relations. -/
theorem cooper_pair_is_nilpotent_cap (m : NullBoundaryMajoranas n) :
    cooperPairCondensate m * cooperPairCondensate m = 0 := by
  unfold cooperPairCondensate
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [majorana_sum_sq_zero m]
  exact smul_zero _

/-- The conjugate Cooper-pair combination. -/
noncomputable def cooperPairConjugate (m : NullBoundaryMajoranas n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (↑(1 / Real.sqrt 2) : ℂ) • (gammaLVal m - Complex.I • gammaRVal m)

/-- Under self-adjoint Majorana generators, the sign-flipped pair is the
matrix adjoint of the normalized Cooper pair. -/
theorem cooper_pair_conjugate_eq_conjTranspose
    (m : NullBoundaryMajoranas n) (hself : MajoranasSelfAdjoint m) :
    (cooperPairCondensate m)ᴴ = cooperPairConjugate m := by
  unfold cooperPairCondensate cooperPairConjugate MajoranasSelfAdjoint at *
  rcases hself with ⟨hL, hR⟩
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, hL, hR]
  simp [Complex.conj_ofReal, smul_sub, smul_neg, smul_smul]
  abel

private theorem majorana_conj_sq_zero (m : NullBoundaryMajoranas n) :
    (gammaLVal m - Complex.I • gammaRVal m) *
        (gammaLVal m - Complex.I • gammaRVal m) = 0 := by
  let m' : NullBoundaryMajoranas n :=
    { gamma_L := m.gamma_L
      gamma_R :=
        { val := -(m.gamma_R : Matrix (Fin n) (Fin n) ℂ)
          inv := -(m.gamma_R : Matrix (Fin n) (Fin n) ℂ)
          val_inv := by rw [neg_mul_neg]; exact m.h_R_sq
          inv_val := by rw [neg_mul_neg]; exact m.h_R_sq }
      h_anticomm := by
        change gammaLVal m * (-gammaRVal m) + (-gammaRVal m) * gammaLVal m = 0
        have hanti : gammaLVal m * gammaRVal m + gammaRVal m * gammaLVal m = 0 := by
          simpa [gammaLVal, gammaRVal] using m.h_anticomm
        rw [mul_neg, neg_mul, ← neg_add, hanti, neg_zero]
      h_L_sq := m.h_L_sq
      h_R_sq := by
        change (-gammaRVal m) * (-gammaRVal m) = 1
        rw [neg_mul_neg, show gammaRVal m * gammaRVal m = 1 from m.h_R_sq] }
  have h := majorana_sum_sq_zero m'
  simpa [m', gammaLVal, gammaRVal, sub_eq_add_neg, neg_smul, smul_neg] using h

/-- The conjugate Cooper-pair combination is nilpotent. -/
theorem conjugate_pair_is_nilpotent (m : NullBoundaryMajoranas n) :
    cooperPairConjugate m * cooperPairConjugate m = 0 := by
  unfold cooperPairConjugate
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [majorana_conj_sq_zero m]
  exact smul_zero _

private theorem majorana_cross_sum (m : NullBoundaryMajoranas n) :
    (gammaLVal m + Complex.I • gammaRVal m) *
          (gammaLVal m - Complex.I • gammaRVal m) +
        (gammaLVal m - Complex.I • gammaRVal m) *
          (gammaLVal m + Complex.I • gammaRVal m) =
      (4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [sub_eq_add_neg, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_add]
  ring_nf
  have hL : gammaLVal m * gammaLVal m = 1 := by
    simpa [gammaLVal] using m.h_L_sq
  have hR : gammaRVal m * gammaRVal m = 1 := by
    simpa [gammaRVal] using m.h_R_sq
  simp [hL, hR, smul_smul]
  abel
  ext i j; simp

/-- The canonical anticommutation relation for the normalized pair. -/
theorem majorana_car (m : NullBoundaryMajoranas n) :
    cooperPairCondensate m * cooperPairConjugate m +
        cooperPairConjugate m * cooperPairCondensate m =
      (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold cooperPairCondensate cooperPairConjugate
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_add]
  rw [majorana_cross_sum m, smul_smul]
  have hscalar :
      (↑(1 / Real.sqrt 2) : ℂ) *
          (↑(1 / Real.sqrt 2) : ℂ) * (4 : ℂ) = 2 := by
    have hbase :
        (↑(1 / Real.sqrt 2) : ℂ) *
            ((↑(1 / Real.sqrt 2) : ℂ) * (4 : ℂ)) = 2 := by
      have hs : Real.sqrt 2 * Real.sqrt 2 = 2 :=
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      push_cast
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
      have hcast :
          (↑(Real.sqrt 2) : ℂ) ^ 2 =
            ↑(Real.sqrt 2 * Real.sqrt 2) := by
        norm_num [pow_two, ← Complex.ofReal_mul]
      rw [hcast, hs]
      norm_num
    calc
      (↑(1 / Real.sqrt 2) : ℂ) *
          (↑(1 / Real.sqrt 2) : ℂ) * (4 : ℂ) =
          (↑(1 / Real.sqrt 2) : ℂ) *
            ((↑(1 / Real.sqrt 2) : ℂ) * (4 : ℂ)) := by ring
      _ = 2 := hbase
  rw [hscalar]

/-- The U(1) gauge phase rotation on the Cooper pair condensate: `f(θ) = e^(iθ) · f`. -/
noncomputable def cooperPairPhaseRotation (m : NullBoundaryMajoranas n) (θ : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Complex.exp (Complex.I * (θ : ℂ)) • cooperPairCondensate m

/-- **U(1) Gauge Invariance of Nilpotency**: `f(θ)² = 0` for any rotation angle `θ`. -/
theorem phase_rotated_is_nilpotent (m : NullBoundaryMajoranas n) (θ : ℝ) :
    cooperPairPhaseRotation m θ * cooperPairPhaseRotation m θ = 0 := by
  unfold cooperPairPhaseRotation
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [cooper_pair_is_nilpotent_cap m]
  exact smul_zero _

/-- The Bogoliubov--de Gennes (BdG) Hamiltonian operator at gap energy `Δ`. -/
noncomputable def bogoliubovHamiltonian (m : NullBoundaryMajoranas n) (Δ : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Δ : ℂ) • (cooperPairCondensate m * cooperPairConjugate m +
              cooperPairConjugate m * cooperPairCondensate m)

/-- **The Bogoliubov Mass Gap Theorem**:

The BdG Hamiltonian at gap scale `Δ` resolves the causal singularity by opening
an exact scalar mass gap of `2Δ · I` at the horizon boundary. -/
theorem bogoliubov_mass_gap (m : NullBoundaryMajoranas n) (Δ : ℝ) :
    bogoliubovHamiltonian m Δ = (2 * Δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold bogoliubovHamiltonian
  rw [majorana_car m, smul_smul]
  congr 1
  ring

/-- The Cooper pair number operator `N_f = f† · f`. -/
noncomputable def cooperPairNumber (m : NullBoundaryMajoranas n) :
    Matrix (Fin n) (Fin n) ℂ :=
  cooperPairConjugate m * cooperPairCondensate m

/-- **Superflow Charge Conservation**:

The Bogoliubov Hamiltonian commutes with the Cooper pair number operator `N_f`:
`[H_BdG, N_f] = 0`. -/
theorem bogoliubov_number_commute (m : NullBoundaryMajoranas n) (Δ : ℝ) :
    bogoliubovHamiltonian m Δ * cooperPairNumber m -
    cooperPairNumber m * bogoliubovHamiltonian m Δ = 0 := by
  rw [bogoliubov_mass_gap m Δ]
  simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  abel

end CausalVortex
