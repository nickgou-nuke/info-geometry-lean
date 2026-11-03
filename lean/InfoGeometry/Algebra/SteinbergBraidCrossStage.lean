/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.SteinbergBraidDefectSpine

/-!
# Steinberg braid cross-stage and tetraktys sandwich covariances

The cross-stage of the Steinberg braid spine: the packaged `A17` dual braid
decomposition strand, the `A18` cross-product defect chain forms, and the `A20`
tetraktys sandwich covariance block.  Every statement was certified against the
exact word model of `proofs/steinberg_braid_defect_spine.py` (106 strict checks,
zero failures) before transcription; the `Mat₃(ℚ)`-over-`ℂ` witness
`P₃ = E₁₁`, `A₃ = E₁₂ + 2E₁₃`, `C₃ = E₂₁ + E₃₁` makes the cross defect real
(`B₊ B₋' - 1` has `6` at the `(0, 0)` entry, its dual the sign mirror).

## Ground-truth arbitration recorded here

* The stream's draft factored cross-product form
  `B₊ B₋' - 1 = (1 - V) Φ + ((1 - V)² - (1 - V)) V` (and its dual) is **refuted**
  by the exact word model.  The verified transcriptions are the 11-chain forms
  `braid_cross_dualInv_defect` / `braidDual_cross_inv_defect` below.
* All nine tetraktys sandwich covariances hold exactly off-shell:
  `J V (-J) = V²`, `(-J) V J = V²`, `Φ V Φ = V²`, `J J (-J) = V J`,
  `Φ J Φ = -V J`, `J Φ (-J) = -V Φ`, `Φ Φ Φ = V Φ`, `J Σ (-J) = -V Σ`,
  `Φ Σ Φ = -V Σ`.  The `Σ` two were previously reachable only as large package
  conjuncts; they are exposed here as named lemmas.

All definitions are owned by `PureNonCommutativeOperatorSpine`
(`SteinbergBraidDefectSpine.lean`); this file only adds verified stages.
-/

namespace SteinbergBraidCrossStage

open PureNonCommutativeOperatorSpine

variable {B : Type*} [Ring B]

/-! ### A17 (packaged): the dual braid decomposition strand -/

/-- The complete dual braid decomposition strand: the packaged `A17`
conjunction (both sheer decompositions, both residual forms, and both
Yang-Baxter defects `(1 - V) Φ`). -/
theorem archetype_A17_dual_braid_package {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A ∧
    steinbergBraidDual P A C = weylJ P A C - (1 - genV P A C) * coneMinus P C ∧
    steinbergBraid P A C - steinbergBraidDual P A C
      = (1 - genV P A C) * genPhi P A C ∧
    steinbergBraidInv P A C = weylJInv P A C - (1 - genV P A C) * conePlus P A ∧
    steinbergBraidDualInv P A C = weylJInv P A C + (1 - genV P A C) * coneMinus P C ∧
    steinbergBraidDualInv P A C - steinbergBraidInv P A C
      = (1 - genV P A C) * genPhi P A C := by
  exact ⟨braid_eq_weyl hP A C, braidDual_eq_weyl hP A C, braid_defect hP A C,
    braidInv_eq_weylPartner hP A C, braidDualInv_eq_weylPartner hP A C,
    braidDualInv_defect hP A C⟩

/-! ### A18 (cross-product stage): verified 11-chain forms -/

/-- **Corrected A18 cross-product** (positive braid times dual inverse):
`B₊ B₋' - 1` is exactly the following 11-chain form.  The stream's factored
draft `(1 - V) Φ + ((1 - V)² - (1 - V)) V` was refuted by the exact word model. -/
theorem braid_cross_dualInv_defect {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraid P A C * steinbergBraidDualInv P A C - 1
      = conePlus P A + coneMinus P C
        + (2 : ℤ) • (conePlus P A * coneMinus P C)
        - coneMinus P C * conePlus P A
        - (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A)
        - (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)
        - (3 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A * coneMinus P C)
        + coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
        + conePlus P A * coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
        + coneMinus P C * conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
        + conePlus P A * coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
            * coneMinus P C := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [steinbergBraid, steinbergBraidDualInv]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- **Corrected dual A18 cross-product**: the mirrored defect with the upper and
lower cones exchanged (the model's sign-mirrored 11-chain form). -/
theorem braidDual_cross_inv_defect {P : B} (hP : P * P = P) (A C : B) :
    steinbergBraidDual P A C * steinbergBraidInv P A C - 1
      = -(conePlus P A) - coneMinus P C
        - conePlus P A * coneMinus P C
        + (2 : ℤ) • (coneMinus P C * conePlus P A)
        + (2 : ℤ) • (conePlus P A * coneMinus P C * conePlus P A)
        + (2 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C)
        + conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
        - (3 : ℤ) • (coneMinus P C * conePlus P A * coneMinus P C * conePlus P A)
        - conePlus P A * coneMinus P C * conePlus P A * coneMinus P C * conePlus P A
        - coneMinus P C * conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
        + coneMinus P C * conePlus P A * coneMinus P C * conePlus P A * coneMinus P C
            * conePlus P A := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [steinbergBraidDual, steinbergBraidInv]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-! ### A20: tetraktys sandwich covariance block (nine lemmas plus package) -/

/-- `J V (-J) = V²`. -/
theorem genJ_sandwich_V {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genV P A C * -(genJ P A C) = genV P A C * genV P A C := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [genJ, genV, anticomm, add_mul, mul_add, sub_mul]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `(-J) V J = V²` (reverse-J variant of the `V` covariance). -/
theorem genJRev_sandwich_V {P : B} (hP : P * P = P) (A C : B) :
    -(genJ P A C) * genV P A C * genJ P A C = genV P A C * genV P A C := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [genJ, genV, anticomm, add_mul, mul_add]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `Φ V Φ = V²`. -/
theorem genPhi_sandwich_V {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genV P A C * genPhi P A C = genV P A C * genV P A C := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [genPhi, genV, anticomm, add_mul, mul_add]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `J J (-J) = V J` (the `J` self-sandwich, via `J² = -V`). -/
theorem genJ_sq_sandwich {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genJ P A C * -(genJ P A C) = genV P A C * genJ P A C := by
  rw [genJ_sq hP A C, neg_mul, mul_neg, neg_neg]

/-- `Φ J Φ = -V J`. -/
theorem genPhi_sandwich_J {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genJ P A C * genPhi P A C = -(genV P A C * genJ P A C) := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [genPhi, genJ, genV, anticomm, add_mul, mul_add]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `J Φ (-J) = -V Φ`. -/
theorem genJ_sandwich_Phi {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genPhi P A C * -(genJ P A C) = -(genV P A C * genPhi P A C) := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [genPhi, genJ, genV, anticomm, add_mul, mul_add, sub_mul]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `Φ Φ Φ = V Φ` (the `Φ` self-sandwich, via `Φ² = V`). -/
theorem genPhi_sq_sandwich {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C := by
  rw [genPhi_sq hP A C]

/-- `J Σ (-J) = -V Σ` (the spin covariance, previously only a package conjunct). -/
theorem genJ_sandwich_sig {P : B} (hP : P * P = P) (A C : B) :
    genJ P A C * genSig P A C * -(genJ P A C) = -(genV P A C * genSig P A C) := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [PureNonCommutativeOperatorSpine.comm, genJ, genSig, genV, anticomm,
    add_mul, sub_mul]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- `Φ Σ Φ = -V Σ` (the mirrored spin covariance). -/
theorem genPhi_sandwich_sig {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genSig P A C * genPhi P A C = -(genV P A C * genSig P A C) := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [PureNonCommutativeOperatorSpine.comm, genPhi, genSig, genV, anticomm,
    add_mul]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- The packaged `A20` tetraktys sandwich covariance conjunction (all nine
model-verified covariances of the tetraktys generators under the `J` and `Φ`
braid reflections). -/
theorem archetype_A20_tetraktys_sandwich_covariance {P : B} (hP : P * P = P)
    (A C : B) :
    genJ P A C * genV P A C * -(genJ P A C) = genV P A C * genV P A C ∧
    -(genJ P A C) * genV P A C * genJ P A C = genV P A C * genV P A C ∧
    genPhi P A C * genV P A C * genPhi P A C = genV P A C * genV P A C ∧
    genJ P A C * genJ P A C * -(genJ P A C) = genV P A C * genJ P A C ∧
    genPhi P A C * genJ P A C * genPhi P A C = -(genV P A C * genJ P A C) ∧
    genJ P A C * genPhi P A C * -(genJ P A C) = -(genV P A C * genPhi P A C) ∧
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genSig P A C * -(genJ P A C) = -(genV P A C * genSig P A C) ∧
    genPhi P A C * genSig P A C * genPhi P A C = -(genV P A C * genSig P A C) := by
  exact ⟨genJ_sandwich_V hP A C, genJRev_sandwich_V hP A C, genPhi_sandwich_V hP A C,
    genJ_sq_sandwich hP A C, genPhi_sandwich_J hP A C, genJ_sandwich_Phi hP A C,
    genPhi_sq_sandwich hP A C, genJ_sandwich_sig hP A C,
    genPhi_sandwich_sig hP A C⟩

/-! ### A20 (center commutant): the mass center commutes with the principal axes -/

/-- **Center preservation**: the mass center `V` commutes with `J`
(the block-swap axis). -/
theorem genJ_commutes_V {P : B} (hP : P * P = P) (A C : B) :
    PureNonCommutativeOperatorSpine.comm (genJ P A C) (genV P A C) = 0 := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [PureNonCommutativeOperatorSpine.comm, genJ, genV, anticomm, add_mul,
    mul_add, sub_mul]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- **Center preservation**: the mass center `V` commutes with `Φ`. -/
theorem genPhi_commutes_V {P : B} (hP : P * P = P) (A C : B) :
    PureNonCommutativeOperatorSpine.comm (genPhi P A C) (genV P A C) = 0 := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [PureNonCommutativeOperatorSpine.comm, genPhi, genV, anticomm, add_mul,
    mul_add]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- **Center preservation**: the mass center `V` commutes with `Σ`
(the spin axis) — `V` spans the commutant of the tetraktys principal axes. -/
theorem genSig_commutes_V {P : B} (hP : P * P = P) (A C : B) :
    PureNonCommutativeOperatorSpine.comm (genSig P A C) (genV P A C) = 0 := by
  have hu := conePlus_sq_zero hP A
  have hv := coneMinus_sq_zero hP C
  simp only [PureNonCommutativeOperatorSpine.comm, genSig, genV, anticomm, add_mul,
    mul_add, sub_mul]
  noncomm_ring [hu, hv, sq_zero_left_mul hu, sq_zero_left_mul hv]

/-- The packaged center-commutant conjunction: `V` commutes with all three
principal axes `J`, `Φ`, `Σ` (the tetraktys center is preserved). -/
theorem archetype_A20_tetraktys_center_commutant {P : B} (hP : P * P = P)
    (A C : B) :
    PureNonCommutativeOperatorSpine.comm (genJ P A C) (genV P A C) = 0 ∧
    PureNonCommutativeOperatorSpine.comm (genPhi P A C) (genV P A C) = 0 ∧
    PureNonCommutativeOperatorSpine.comm (genSig P A C) (genV P A C) = 0 := by
  exact ⟨genJ_commutes_V hP A C, genPhi_commutes_V hP A C,
    genSig_commutes_V hP A C⟩

/-! ### `Mat₃(ℚ)`-over-`ℂ` witness: the cross defect is real -/

section Witness

open InfoGeometry.Algebra.FiniteSpin

/-- The cross-product defect is real on the witness: the `(0, 0)` entry of
`B₊ B₋' - 1` equals `6` (the full value is `[[6, 4, 8], [4, 2, 4], [4, 2, 4]]`). -/
theorem witness_braid_cross_dualInv_defect_ne_zero :
    steinbergBraid wP wA wC * steinbergBraidDualInv wP wA wC - 1 ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have h7 : (steinbergBraid wP wA wC * steinbergBraidDualInv wP wA wC) 0 0 = 7 := by
    have hadd (M : Mat3C) (i j : Fin 3) : ((1 : Mat3C) + M) i j = (1 : Mat3C) i j + M i j := rfl
    have hsub (M : Mat3C) (i j : Fin 3) : ((1 : Mat3C) - M) i j = (1 : Mat3C) i j - M i j := rfl
    have hone (i j : Fin 3) : (1 : Mat3C) i j = if i = j then 1 else 0 := rfl
    rw [steinbergBraid, steinbergBraidDualInv, wNp_eq, wNm_eq]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, hadd, hsub, hone]
    norm_num [wA, wC]
  rw [h, Matrix.one_apply_eq] at h7
  norm_num at h7

/-- The mirrored cross-product defect is real on the witness too: the `(0, 0)`
entry of `B₋ B₊' - 1` equals `6` (full value `[[6, -4, -8], [-4, 2, 4], [-4, 2, 4]]`). -/
theorem witness_braidDual_cross_inv_defect_ne_zero :
    steinbergBraidDual wP wA wC * steinbergBraidInv wP wA wC - 1 ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have h7 : (steinbergBraidDual wP wA wC * steinbergBraidInv wP wA wC) 0 0 = 7 := by
    have hadd (M : Mat3C) (i j : Fin 3) : ((1 : Mat3C) + M) i j = (1 : Mat3C) i j + M i j := rfl
    have hsub (M : Mat3C) (i j : Fin 3) : ((1 : Mat3C) - M) i j = (1 : Mat3C) i j - M i j := rfl
    have hone (i j : Fin 3) : (1 : Mat3C) i j = if i = j then 1 else 0 := rfl
    rw [steinbergBraidDual, steinbergBraidInv, wNp_eq, wNm_eq]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, hadd, hsub, hone]
    norm_num [wA, wC]
  rw [h, Matrix.one_apply_eq] at h7
  norm_num at h7

end Witness

end SteinbergBraidCrossStage
