/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
import InfoGeometry.Canonical.TimeAsWindingMonodromy3D

/-!
# Chiral Lightcone Matrix Units and Unipotent Shear Readouts

This module proves finite matrix identities for the $3+1\mathrm{D}$ chiral
lightcone matrix `chiralMatrix`, nilpotent ladder modes `Splus`/`Sminus`, and
unipotent shear readout. It imports the projective logarithmic connection and
integer pole-winding owners for their definitions. Those owners remain separate;
this file does not prove a braid representation or identify it with the chiral
matrix action.

## Main Theorems

1. **Section 1 — Chiral Lightcone $2 \times 2$ Matrix-Unit / CAR Relations & Jordan Nilpotent Identification**:
   - `chiral_ladder_ne_comm`: explicit $2 \times 2$ non-commutativity witness `Splus * Sminus ≠ Sminus * Splus` (`T16`).
   - `Splus_eq_jordanNilpotent`: identifies the chiral lightcone upper nilpotent generator `Splus`
     with the native rank-two LCFT Jordan generator `jordanNilpotent`.
   - `chiral_ladder_matrix_unit_resolution`: proves nilpotency $S_+^2 = S_-^2 = 0$, the finite matrix
     relation $S_+ S_- + S_- S_+ = I_2$, idempotency and mutual orthogonality of the Peirce
     projectors $P_+ = S_+ S_-$ and $P_- = S_- S_+$, and trace/determinant identities
     $\operatorname{Tr}(chiralMatrix(X)) = 2 t$, $\det(chiralMatrix(X)) = Q(X)$.
2. **Section 2 — Unipotent Chiral Shear $I_2 + p S_+$ & Lightcone Determinant Preservation**:
   - Defines `unipotentChiralShear (p : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := 1 + p • Splus`.
   - Proves `unipotentChiralShear_mul_and_det`: additive unipotent group law
     `(1 + p • Splus) * (1 + q • Splus) = 1 + (p + q) • Splus`, unit determinant
     $\det(I_2 + p S_+) = 1$, lightcone determinant preservation
     $\det((I_2 + p S_+) \cdot \mathrm{chiralMatrix}(X)) = Q(X)$, and compatibility with
     `unipotentResidueReadout (rankTwoLogResidue h) p`.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped Matrix BigOperators

namespace InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Canonical.ChiralCausalConeFlow
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D

/-!
## Section 1: Chiral Lightcone $2 \times 2$ Matrix-Unit / CAR Relations & Jordan Nilpotent Identification
-/

/-- Forward chiral ladder generator $S_+ := E_{01}$ on `Matrix (Fin 2) (Fin 2) ℂ`. -/
def chiralLadderPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  Splus

/-- Backward chiral ladder generator $S_- := E_{10}$ on `Matrix (Fin 2) (Fin 2) ℂ`. -/
def chiralLadderMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  Sminus

/-- Explicit $2 \times 2$ non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ` (`T16`):
the chiral ladder generators $S_+$ and $S_-$ do not commute ($S_+ S_- \neq S_- S_+$). -/
theorem chiral_ladder_ne_comm :
    chiralLadderPlus * chiralLadderMinus ≠ chiralLadderMinus * chiralLadderPlus := by
  intro h
  have h00 : (chiralLadderPlus * chiralLadderMinus) 0 0 = (chiralLadderMinus * chiralLadderPlus) 0 0 :=
    congrFun (congrFun h 0) 0
  norm_num [chiralLadderPlus, chiralLadderMinus, Splus, Sminus, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The chiral lightcone nilpotent generator `Splus` in `TimeAsWindingMonodromy3D` is identically
the native rank-two LCFT Jordan nilpotent `jordanNilpotent` in `LogCftMonodromy`. -/
theorem Splus_eq_jordanNilpotent :
    Splus = jordanNilpotent := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Forward chiral Peirce projector $P_+^{\mathrm{chiral}} := S_+ S_- = \operatorname{diag}(1, 0)$. -/
def chiralPeircePlus : Matrix (Fin 2) (Fin 2) ℂ :=
  Splus * Sminus

/-- Backward chiral Peirce projector $P_-^{\mathrm{chiral}} := S_- S_+ = \operatorname{diag}(0, 1)$. -/
def chiralPeirceMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  Sminus * Splus

/-- **Theorem 1.1 (Chiral Lightcone $2 \times 2$ Matrix-Unit Resolution & Trace-Determinant Identities)**:
1. Nilpotency: $S_+^2 = 0$ and $S_-^2 = 0$.
2. Partition of unity: $P_+^{\mathrm{chiral}} + P_-^{\mathrm{chiral}} = S_+ S_- + S_- S_+ = I_2$.
3. Idempotency and orthogonality: $(P_\pm^{\mathrm{chiral}})^2 = P_\pm^{\mathrm{chiral}}$ and
   $P_+^{\mathrm{chiral}} P_-^{\mathrm{chiral}} = P_-^{\mathrm{chiral}} P_+^{\mathrm{chiral}} = 0$.
4. For any $X \in \mathrm{Chiral3}$, $\operatorname{Tr}(\mathrm{chiralMatrix}(X)) = 2 X.t$ and
   $\det(\mathrm{chiralMatrix}(X)) = Q(X)$. -/
theorem chiral_ladder_matrix_unit_resolution (X : Chiral3) :
    (Splus * Splus = 0 ∧ Sminus * Sminus = 0) ∧
    (chiralPeircePlus + chiralPeirceMinus = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (chiralPeircePlus * chiralPeircePlus = chiralPeircePlus ∧
     chiralPeirceMinus * chiralPeirceMinus = chiralPeirceMinus ∧
     chiralPeircePlus * chiralPeirceMinus = 0 ∧
     chiralPeirceMinus * chiralPeircePlus = 0) ∧
    (Matrix.trace (chiralMatrix X) = 2 * (X.t : ℂ) ∧
     Matrix.det (chiralMatrix X) = (lightconePotential X : ℂ)) := by
  refine ⟨⟨Splus_sqr_eq_zero, Sminus_sqr_eq_zero⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, chiralMatrix_det X⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralPeircePlus, chiralPeirceMinus, Splus, Sminus]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralPeircePlus, Splus, Sminus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralPeirceMinus, Splus, Sminus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralPeircePlus, chiralPeirceMinus, Splus, Sminus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralPeircePlus, chiralPeirceMinus, Splus, Sminus, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [chiralMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    ring

/-!
## Section 2: Unipotent Chiral Shear $I_2 + p S_+$ & Lightcone Determinant Preservation
-/

/-- The $2 \times 2$ unipotent shear matrix $U(p) := I_2 + p S_+$. -/
def unipotentChiralShear (p : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + p • Splus

/-- **Theorem 2.1 (Unipotent Chiral Shear Group Law, Unit Determinant, Lightcone Preservation & Rank-Two Readout)**:
For any shear parameters $p, q \in \mathbb{C}$, conformal weight $h \in \mathbb{C}$, chiral state
$X \in \mathrm{Chiral3}$, and rank-two fiber vector $v \in \mathrm{RankTwoFiber}$:
1. Additive unipotent group law: `unipotentChiralShear p * unipotentChiralShear q = unipotentChiralShear (p + q)`.
2. Unit determinant: `Matrix.det (unipotentChiralShear p) = 1`.
3. Lightcone quadratic preservation: `Matrix.det (unipotentChiralShear p * chiralMatrix X) = (lightconePotential X : ℂ)`.
4. Exact match with `unipotentResidueReadout (rankTwoLogResidue h) p`:
   `unipotentResidueReadout (rankTwoLogResidue h) p v = (unipotentChiralShear p).mulVec v`. -/
theorem unipotentChiralShear_mul_and_det
    (p q h : ℂ) (X : Chiral3) (v : RankTwoFiber) :
    (unipotentChiralShear p * unipotentChiralShear q = unipotentChiralShear (p + q)) ∧
    (Matrix.det (unipotentChiralShear p) = 1) ∧
    (Matrix.det (unipotentChiralShear p * chiralMatrix X) = (lightconePotential X : ℂ)) ∧
    (unipotentResidueReadout (rankTwoLogResidue h) p v = (unipotentChiralShear p).mulVec v) := by
  have h_det : Matrix.det (unipotentChiralShear p) = 1 := by
    simp [unipotentChiralShear, Splus, Matrix.det_fin_two]
  refine ⟨?_, h_det, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentChiralShear, Splus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · rw [Matrix.det_mul, h_det, one_mul, chiralMatrix_det]
  · ext i
    fin_cases i <;>
      simp [unipotentResidueReadout, rankTwoLogResidue, nativeNilpotentEnd,
        unipotentChiralShear, Splus, jordanNilpotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For any nonzero shear parameter `p ≠ 0`, the double action of `unipotentChiralShear p`
equals `unipotentChiralShear (2 * p)` and is strictly non-identity (`≠ 1`). -/
theorem unipotentChiralShear_double_ne_one (p : ℂ) (hp : p ≠ 0) :
    unipotentChiralShear p * unipotentChiralShear p = unipotentChiralShear (2 * p) ∧
    unipotentChiralShear p * unipotentChiralShear p ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h_double : unipotentChiralShear p * unipotentChiralShear p = unipotentChiralShear (2 * p) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentChiralShear, Splus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨h_double, ?_⟩
  intro h_id
  rw [h_double] at h_id
  have h01 : unipotentChiralShear (2 * p) 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 :=
    congrFun (congrFun h_id 0) 1
  have h2p : (2 * p : ℂ) = 0 := by
    simpa [unipotentChiralShear, Splus] using h01
  exact mul_ne_zero (by norm_num) hp h2p

/-- For any conformal weight `h : ℂ` and nonzero shear parameter `p ≠ 0`, the double action
of the rank-two unipotent residue readout `unipotentResidueReadout (rankTwoLogResidue h) p`
is strictly non-identity (`≠ LinearMap.id`). -/
theorem rankTwo_unipotentResidueReadout_double_ne_id (h p : ℂ) (hp : p ≠ 0) :
    (unipotentResidueReadout (rankTwoLogResidue h) p).comp
      (unipotentResidueReadout (rankTwoLogResidue h) p) ≠ LinearMap.id := by
  rw [unipotentResidueReadout_comp]
  intro h_id
  have heval : unipotentResidueReadout (rankTwoLogResidue h) (p + p) ![0, 1] 0 =
      (LinearMap.id : RankTwoFiber →ₗ[ℂ] RankTwoFiber) ![0, 1] 0 :=
    congrFun (LinearMap.congr_fun h_id ![0, 1]) 0
  have hpp : p + p = 0 := by
    simpa [unipotentResidueReadout, rankTwoLogResidue, nativeNilpotentEnd,
      jordanNilpotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using heval
  have h2p : (2 * p : ℂ) = 0 := by
    calc (2 * p : ℂ) = p + p := two_mul p
    _ = 0 := hpp
  exact mul_ne_zero (by norm_num) hp h2p

/-!
The imported projective owner retains its own braid statement, conditional on a
`LogResidueBraidFrame`, and the winding owner retains its integer pole-winding
readout. The Rindler and Milne results live in other owners and are not used
here. This file does not combine these separate facts into a KMS or spacetime
equivalence.
-/

end InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

