/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.RealPauliPfaffianKernel
import InfoGeometry.Algebra.AssociativeNambuOperators
import Mathlib.Data.Matrix.Block

/-!
# Real Dirac spin generators and doubled finite Casimirs

The spatial Clifford generators below are the three spatial unit vectors of
the existing real Dirac family. Their ordered bivectors give rotation and
boost matrices, with all signs tied to the existing real phase axis.

On the native sum of two four-dimensional real carriers, the phase is shared
and the boosts have opposite signs. The two resulting spin triples have
disjoint diagonal supports. Their matrix identities record the support,
commutation, mirror exchange, and finite Casimir values. The real phase
continues to supply a complex structure; these identities do not assert a
decomposition of the real Lorentz Lie algebra into two compact Lie algebras.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDiracSpinCasimir

open scoped Matrix BigOperators
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge
open InfoGeometry.Canonical.RealPauliPfaffianKernel
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.AssociativeNambuOperators

/-- The three spatial generators of the existing real Dirac vector. -/
def spatialGamma : Fin 3 → Matrix4 :=
  ![diracVector 0 1 0 0, diracVector 0 0 1 0, diracVector 0 0 0 1]

/-- Cyclic spatial bivectors, with the rotation sign fixed by `[J₀,J₁]=J₂`. -/
def spinJ (i : Fin 3) : Matrix4 :=
  -(1 / 2 : ℝ) • (spatialGamma (i + 1) * spatialGamma (i + 2))

/-- Timelike-spacelike bivectors on the same real carrier. -/
def boostK (i : Fin 3) : Matrix4 :=
  (1 / 2 : ℝ) • (timeGamma * spatialGamma i)

/-- A proved coordinate view of the existing spatial Dirac unit vectors. -/
private theorem spatialGamma_explicit (i : Fin 3) :
    spatialGamma i =
      ![!![-1, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, -1],
        !![0, 1, 0, 0;
           1, 0, 0, 0;
           0, 0, 0, 1;
           0, 0, 1, 0],
        !![0, 0, 1, 0;
           0, 0, 0, -1;
           1, 0, 0, 0;
           0, -1, 0, 0]] i := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spatialGamma, diracVector, pauli_explicit, timeGamma,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Compute the existing rotation bivectors once before their constant identities. -/
private theorem spinJ_explicit (i : Fin 3) :
    spinJ i = (1 / 2 : ℝ) •
      ![!![0, 0, 0, 1;
           0, 0, -1, 0;
           0, 1, 0, 0;
           -1, 0, 0, 0],
        !![0, 0, -1, 0;
           0, 0, 0, -1;
           1, 0, 0, 0;
           0, 1, 0, 0],
        !![0, 1, 0, 0;
           -1, 0, 0, 0;
           0, 0, 0, -1;
           0, 0, 1, 0]] i := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ, spatialGamma_explicit, Matrix.mul_apply, Fin.sum_univ_four]

/-- Compute the existing boost bivectors using the same spatial coordinate view. -/
private theorem boostK_explicit (i : Fin 3) :
    boostK i = (1 / 2 : ℝ) •
      ![!![0, 0, 1, 0;
           0, 0, 0, 1;
           1, 0, 0, 0;
           0, 1, 0, 0],
        !![0, 0, 0, 1;
           0, 0, -1, 0;
           0, -1, 0, 0;
           1, 0, 0, 0],
        !![1, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, -1, 0;
           0, 0, 0, -1]] i := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [boostK, spatialGamma_explicit, timeGamma,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem spinJ_cyclic_comm (i : Fin 3) :
    spinJ i * spinJ (i + 1) - spinJ (i + 1) * spinJ i = spinJ (i + 2) := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, Matrix.mul_apply, Fin.sum_univ_four]

theorem boostK_cyclic_comm (i : Fin 3) :
    boostK i * boostK (i + 1) - boostK (i + 1) * boostK i = -spinJ (i + 2) := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, boostK_explicit, Matrix.mul_apply, Fin.sum_univ_four]

theorem spinJ_boostK_cyclic_comm (i : Fin 3) :
    spinJ i * boostK (i + 1) - boostK (i + 1) * spinJ i = boostK (i + 2) := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, boostK_explicit, Matrix.mul_apply, Fin.sum_univ_four]

/-- The reverse cyclic order supplies the other three mixed rotation-boost brackets. -/
theorem spinJ_boostK_reverse_cyclic_comm (i : Fin 3) :
    spinJ i * boostK (i + 2) - boostK (i + 2) * spinJ i = -boostK (i + 1) := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, boostK_explicit, Matrix.mul_apply, Fin.sum_univ_four]

theorem spinJ_boostK_same_comm (i : Fin 3) :
    spinJ i * boostK i - boostK i * spinJ i = 0 := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, boostK_explicit, Matrix.mul_apply, Fin.sum_univ_four]

/-- Multiplication by the real Clifford volume sends each boost to `-Jᵢ`. -/
theorem phase_mul_boostK (i : Fin 3) :
    realPhaseAxis * boostK i = -spinJ i := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, boostK_explicit, realPhaseAxis,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem spinJ_sq (i : Fin 3) :
    spinJ i * spinJ i = (-1 / 4 : ℝ) • (1 : Matrix4) := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, Matrix.mul_apply, Fin.sum_univ_four]

theorem boostK_sq (i : Fin 3) :
    boostK i * boostK i = (1 / 4 : ℝ) • (1 : Matrix4) := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [boostK_explicit, Matrix.mul_apply, Fin.sum_univ_four]

theorem spinJ_mul_boostK (i : Fin 3) :
    spinJ i * boostK i = (-1 / 4 : ℝ) • realPhaseAxis := by
  fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
    norm_num [spinJ_explicit, boostK_explicit, realPhaseAxis,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem spinJ_casimir :
    (∑ i : Fin 3, spinJ i * spinJ i) = (-3 / 4 : ℝ) • (1 : Matrix4) := by
  rw [Fin.sum_univ_three, spinJ_sq, spinJ_sq, spinJ_sq, ← add_smul, ← add_smul]
  norm_num

theorem boostK_casimir :
    (∑ i : Fin 3, boostK i * boostK i) = (3 / 4 : ℝ) • (1 : Matrix4) := by
  rw [Fin.sum_univ_three, boostK_sq, boostK_sq, boostK_sq, ← add_smul, ← add_smul]
  norm_num

theorem lorentz_first_casimir :
    (∑ i : Fin 3, spinJ i * spinJ i) - (∑ i : Fin 3, boostK i * boostK i) =
      (-3 / 2 : ℝ) • (1 : Matrix4) := by
  rw [spinJ_casimir, boostK_casimir, ← sub_smul]
  norm_num

theorem lorentz_second_casimir :
    (∑ i : Fin 3, spinJ i * boostK i) = (-3 / 4 : ℝ) • realPhaseAxis := by
  rw [Fin.sum_univ_three, spinJ_mul_boostK, spinJ_mul_boostK, spinJ_mul_boostK, ← add_smul,
    ← add_smul]
  norm_num

/-- The rotation triple retains genuine noncommutativity on its actual carrier. -/
theorem spinJ_cyclic_not_commute (i : Fin 3) :
    spinJ i * spinJ (i + 1) ≠ spinJ (i + 1) * spinJ i := by
  intro h
  have hz : spinJ (i + 2) = 0 := by
    have hc := spinJ_cyclic_comm i
    rw [h, sub_self] at hc
    exact hc.symm
  have hs := spinJ_sq (i + 2)
  rw [hz, zero_mul] at hs
  have h00 := congrFun (congrFun hs (0 : Fin 4)) (0 : Fin 4)
  norm_num at h00

/-! ## The native doubled real carrier -/

abbrev DoubledMatrix := Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ

/-- The same real phase on both four-dimensional summands. -/
def doubledPhase : DoubledMatrix :=
  Matrix.fromBlocks realPhaseAxis 0 0 realPhaseAxis

/-- The sign distinguishing the two summands. -/
def doubledCut : DoubledMatrix :=
  Matrix.fromBlocks (1 : Matrix4) 0 0 (-1)

/-- The involution exchanging the two summands. -/
def doubledMirror : DoubledMatrix :=
  Matrix.fromBlocks (0 : Matrix4) 1 1 0

def totalJ (i : Fin 3) : DoubledMatrix :=
  Matrix.fromBlocks (spinJ i) 0 0 (spinJ i)

def totalK (i : Fin 3) : DoubledMatrix :=
  Matrix.fromBlocks (boostK i) 0 0 (-boostK i)

def chiralA (i : Fin 3) : DoubledMatrix :=
  (1 / 2 : ℝ) • (totalJ i + doubledPhase * totalK i)

def chiralB (i : Fin 3) : DoubledMatrix :=
  (1 / 2 : ℝ) • (totalJ i - doubledPhase * totalK i)

theorem doubledPhase_sq : doubledPhase * doubledPhase = -(1 : DoubledMatrix) := by
  have h : doubledPhase * doubledPhase =
      -Matrix.fromBlocks (1 : Matrix4) 0 0 (1 : Matrix4) := by
    simp only [doubledPhase, Matrix.fromBlocks_multiply, zero_mul, mul_zero,
      zero_add, add_zero, realPhaseAxis_sq, Matrix.fromBlocks_neg, neg_zero]
  simpa only [Matrix.fromBlocks_one] using h

theorem doubledCut_sq : doubledCut * doubledCut = (1 : DoubledMatrix) := by
  simp [doubledCut, Matrix.fromBlocks_multiply]

theorem doubledMirror_sq : doubledMirror * doubledMirror = (1 : DoubledMatrix) := by
  simp [doubledMirror, Matrix.fromBlocks_multiply]

/-- The supported lower block follows from `phase_mul_boostK`, for every axis. -/
theorem chiralA_support (i : Fin 3) :
    chiralA i = Matrix.fromBlocks (0 : Matrix4) 0 0 (spinJ i) := by
  simp only [chiralA, totalJ, totalK, doubledPhase, Matrix.fromBlocks_multiply,
    zero_mul, mul_zero, zero_add, add_zero, mul_neg, phase_mul_boostK,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul, add_neg_cancel, smul_zero]
  congr 1
  module

/-- The supported upper block follows from the same ordered volume relation. -/
theorem chiralB_support (i : Fin 3) :
    chiralB i = Matrix.fromBlocks (spinJ i) 0 0 (0 : Matrix4) := by
  simp only [chiralB, totalJ, totalK, doubledPhase, Matrix.fromBlocks_multiply,
    zero_mul, mul_zero, zero_add, add_zero, mul_neg, phase_mul_boostK,
    sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add,
    Matrix.fromBlocks_smul, neg_zero, neg_neg, add_neg_cancel, smul_zero]
  congr 1
  module

theorem chiralA_mul_chiralB (i j : Fin 3) : chiralA i * chiralB j = 0 := by
  simp [chiralA_support, chiralB_support, Matrix.fromBlocks_multiply]

theorem chiralB_mul_chiralA (i j : Fin 3) : chiralB i * chiralA j = 0 := by
  simp [chiralA_support, chiralB_support, Matrix.fromBlocks_multiply]

/-- Every pair of generators from the two supported families commutes. -/
theorem chiral_mixed_comm (i j : Fin 3) :
    chiralA i * chiralB j - chiralB j * chiralA i = 0 := by
  rw [chiralA_mul_chiralB, chiralB_mul_chiralA, sub_self]

theorem chiralA_cyclic_comm (i : Fin 3) :
    chiralA i * chiralA (i + 1) - chiralA (i + 1) * chiralA i =
      chiralA (i + 2) := by
  simpa only [chiralA_support, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, zero_mul, mul_zero,
    zero_add, add_zero, neg_zero] using
      congrArg (fun M : Matrix4 => Matrix.fromBlocks (0 : Matrix4) 0 0 M)
        (spinJ_cyclic_comm i)

theorem chiralB_cyclic_comm (i : Fin 3) :
    chiralB i * chiralB (i + 1) - chiralB (i + 1) * chiralB i =
      chiralB (i + 2) := by
  simpa only [chiralB_support, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, zero_mul, mul_zero,
    zero_add, add_zero, neg_zero] using
      congrArg (fun M : Matrix4 => Matrix.fromBlocks M 0 0 (0 : Matrix4))
        (spinJ_cyclic_comm i)

theorem mirror_chiralA (i : Fin 3) :
    doubledMirror * chiralA i * doubledMirror = chiralB i := by
  simp [doubledMirror, chiralA_support, chiralB_support, Matrix.fromBlocks_multiply]

theorem mirror_chiralB (i : Fin 3) :
    doubledMirror * chiralB i * doubledMirror = chiralA i := by
  simp [doubledMirror, chiralA_support, chiralB_support, Matrix.fromBlocks_multiply]

/-- The first supported rotation Casimir occupies the lower summand. -/
theorem chiralA_casimir :
    (∑ i : Fin 3, chiralA i * chiralA i) =
      (-3 / 4 : ℝ) • Matrix.fromBlocks (0 : Matrix4) 0 0 (1 : Matrix4) := by
  simpa only [Fin.sum_univ_three, chiralA_support, Matrix.fromBlocks_multiply,
    zero_mul, mul_zero, zero_add, add_zero, Matrix.fromBlocks_add,
    Matrix.fromBlocks_smul, smul_zero] using
      congrArg (fun M : Matrix4 => Matrix.fromBlocks (0 : Matrix4) 0 0 M) spinJ_casimir

/-- The second supported rotation Casimir occupies the upper summand. -/
theorem chiralB_casimir :
    (∑ i : Fin 3, chiralB i * chiralB i) =
      (-3 / 4 : ℝ) • Matrix.fromBlocks (1 : Matrix4) 0 0 (0 : Matrix4) := by
  simpa only [Fin.sum_univ_three, chiralB_support, Matrix.fromBlocks_multiply,
    zero_mul, mul_zero, zero_add, add_zero, Matrix.fromBlocks_add,
    Matrix.fromBlocks_smul, smul_zero] using
      congrArg (fun M : Matrix4 => Matrix.fromBlocks M 0 0 (0 : Matrix4)) spinJ_casimir

/-- The mirror exchanges the lower supported Casimir with the upper one. -/
theorem mirror_chiralA_casimir :
    doubledMirror * (∑ i : Fin 3, chiralA i * chiralA i) * doubledMirror =
      ∑ i : Fin 3, chiralB i * chiralB i := by
  rw [chiralA_casimir, chiralB_casimir]
  simp [doubledMirror, Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]

/-- The reverse mirror exchange holds on the actual finite Casimir sums. -/
theorem mirror_chiralB_casimir :
    doubledMirror * (∑ i : Fin 3, chiralB i * chiralB i) * doubledMirror =
      ∑ i : Fin 3, chiralA i * chiralA i := by
  rw [chiralA_casimir, chiralB_casimir]
  simp [doubledMirror, Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]

/-- Restricted centrality of the lower supported Casimir with every rotation. -/
theorem chiralA_casimir_commutes_totalJ (i : Fin 3) :
    Commute (∑ j : Fin 3, chiralA j * chiralA j) (totalJ i) := by
  rw [commute_iff_eq, chiralA_casimir]
  simp [totalJ, Matrix.fromBlocks_multiply]

/-- Restricted centrality of the lower supported Casimir with every boost. -/
theorem chiralA_casimir_commutes_totalK (i : Fin 3) :
    Commute (∑ j : Fin 3, chiralA j * chiralA j) (totalK i) := by
  rw [commute_iff_eq, chiralA_casimir]
  simp [totalK, Matrix.fromBlocks_multiply]

/-- Restricted centrality of the upper supported Casimir with every rotation. -/
theorem chiralB_casimir_commutes_totalJ (i : Fin 3) :
    Commute (∑ j : Fin 3, chiralB j * chiralB j) (totalJ i) := by
  rw [commute_iff_eq, chiralB_casimir]
  simp [totalJ, Matrix.fromBlocks_multiply]

/-- Restricted centrality of the upper supported Casimir with every boost. -/
theorem chiralB_casimir_commutes_totalK (i : Fin 3) :
    Commute (∑ j : Fin 3, chiralB j * chiralB j) (totalK i) := by
  rw [commute_iff_eq, chiralB_casimir]
  simp [totalK, Matrix.fromBlocks_multiply]

theorem totalJ_casimir :
    (∑ i : Fin 3, totalJ i * totalJ i) = (-3 / 4 : ℝ) • (1 : DoubledMatrix) := by
  have h : (∑ i : Fin 3, totalJ i * totalJ i) =
      (-3 / 4 : ℝ) • Matrix.fromBlocks (1 : Matrix4) 0 0 (1 : Matrix4) := by
    simpa only [Fin.sum_univ_three, totalJ, Matrix.fromBlocks_multiply,
      zero_mul, mul_zero, zero_add, add_zero, Matrix.fromBlocks_add,
      Matrix.fromBlocks_smul, smul_zero] using
        congrArg (fun M : Matrix4 => Matrix.fromBlocks M 0 0 M) spinJ_casimir
  simpa only [Matrix.fromBlocks_one] using h

theorem totalK_casimir :
    (∑ i : Fin 3, totalK i * totalK i) = (3 / 4 : ℝ) • (1 : DoubledMatrix) := by
  have h : (∑ i : Fin 3, totalK i * totalK i) =
      (3 / 4 : ℝ) • Matrix.fromBlocks (1 : Matrix4) 0 0 (1 : Matrix4) := by
    simpa only [Fin.sum_univ_three, totalK, Matrix.fromBlocks_multiply,
      zero_mul, mul_zero, zero_add, add_zero, neg_mul_neg, Matrix.fromBlocks_add,
      Matrix.fromBlocks_smul, smul_zero] using
        congrArg (fun M : Matrix4 => Matrix.fromBlocks M 0 0 M) boostK_casimir
  simpa only [Matrix.fromBlocks_one] using h

theorem doubled_lorentz_first_casimir :
    (∑ i : Fin 3, totalJ i * totalJ i) - (∑ i : Fin 3, totalK i * totalK i) =
      (-3 / 2 : ℝ) • (1 : DoubledMatrix) := by
  rw [totalJ_casimir, totalK_casimir, ← sub_smul]
  norm_num

/-- The two supported rotation Casimirs reconstruct the first doubled Lorentz Casimir. -/
theorem doubled_lorentz_first_casimir_reconstruction :
    (∑ i : Fin 3, totalJ i * totalJ i) - (∑ i : Fin 3, totalK i * totalK i) =
      (2 : ℝ) • ((∑ i : Fin 3, chiralA i * chiralA i) +
        (∑ i : Fin 3, chiralB i * chiralB i)) := by
  rw [doubled_lorentz_first_casimir, chiralA_casimir, chiralB_casimir, ← smul_add]
  norm_num [Matrix.fromBlocks_add, smul_smul]

/-- The parity-flipped boosts give the negative mixed-Casimir sign. -/
theorem doubled_lorentz_second_casimir :
    (∑ i : Fin 3, totalJ i * totalK i) =
      (-3 / 4 : ℝ) • (doubledCut * doubledPhase) := by
  simpa only [Fin.sum_univ_three, totalJ, totalK, doubledCut, doubledPhase,
    Matrix.fromBlocks_multiply, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_neg, neg_mul, neg_add, neg_zero, Matrix.fromBlocks_add,
    Matrix.fromBlocks_smul, smul_zero, smul_neg] using
      congrArg (fun M : Matrix4 => Matrix.fromBlocks M 0 0 (-M))
        lorentz_second_casimir

/-! ## The existing alternating cubic evaluated on the spin triples -/

theorem spinJ_alternatingProduct3 :
    alternatingProduct3 (spinJ 0) (spinJ 1) (spinJ 2) =
      (-3 / 4 : ℝ) • (1 : Matrix4) := by
  calc
    _ = spinJ 0 * spinJ 0 + spinJ 1 * spinJ 1 + spinJ 2 * spinJ 2 :=
      alternatingProduct3_eq_casimir _ _ _
        (by simpa [PeirceSpine.comm] using spinJ_cyclic_comm (0 : Fin 3))
        (by simpa [PeirceSpine.comm] using spinJ_cyclic_comm (1 : Fin 3))
        (by simpa [PeirceSpine.comm] using spinJ_cyclic_comm (2 : Fin 3))
    _ = (-3 / 4 : ℝ) • (1 : Matrix4) := by
      simpa only [Fin.sum_univ_three] using spinJ_casimir

theorem chiralA_alternatingProduct3 :
    alternatingProduct3 (chiralA 0) (chiralA 1) (chiralA 2) =
      (-3 / 4 : ℝ) • Matrix.fromBlocks (0 : Matrix4) 0 0 (1 : Matrix4) := by
  calc
    _ = chiralA 0 * chiralA 0 + chiralA 1 * chiralA 1 + chiralA 2 * chiralA 2 :=
      alternatingProduct3_eq_casimir _ _ _
        (by simpa [PeirceSpine.comm] using chiralA_cyclic_comm (0 : Fin 3))
        (by simpa [PeirceSpine.comm] using chiralA_cyclic_comm (1 : Fin 3))
        (by simpa [PeirceSpine.comm] using chiralA_cyclic_comm (2 : Fin 3))
    _ = (-3 / 4 : ℝ) • Matrix.fromBlocks (0 : Matrix4) 0 0 (1 : Matrix4) := by
      simpa only [Fin.sum_univ_three] using chiralA_casimir

theorem chiralB_alternatingProduct3 :
    alternatingProduct3 (chiralB 0) (chiralB 1) (chiralB 2) =
      (-3 / 4 : ℝ) • Matrix.fromBlocks (1 : Matrix4) 0 0 (0 : Matrix4) := by
  calc
    _ = chiralB 0 * chiralB 0 + chiralB 1 * chiralB 1 + chiralB 2 * chiralB 2 :=
      alternatingProduct3_eq_casimir _ _ _
        (by simpa [PeirceSpine.comm] using chiralB_cyclic_comm (0 : Fin 3))
        (by simpa [PeirceSpine.comm] using chiralB_cyclic_comm (1 : Fin 3))
        (by simpa [PeirceSpine.comm] using chiralB_cyclic_comm (2 : Fin 3))
    _ = (-3 / 4 : ℝ) • Matrix.fromBlocks (1 : Matrix4) 0 0 (0 : Matrix4) := by
      simpa only [Fin.sum_univ_three] using chiralB_casimir

end InfoGeometry.Canonical.RealDiracSpinCasimir
