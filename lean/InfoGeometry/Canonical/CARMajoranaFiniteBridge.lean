/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Quantum.MajoranaPfaffianNaturalClosure
import InfoGeometry.Canonical.MajoranaPfaffian4
import InfoGeometry.Canonical.MajoranaLinearKernel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# An explicit CAR-to-chain-to-Pfaffian bridge

The doubled-real carrier adapter is in CARMajoranaOwnerAdapters. This core
uses the existing concrete CAR and Majorana matrices, including the parity
string. The four-mode Pfaffian is the existing signed matching polynomial.
-/
namespace InfoGeometry.Canonical.CARMajoranaFiniteBridge

open scoped BigOperators Kronecker
open InfoGeometry.MajoranaPfaffianNaturalClosure
open MajoranaLinearKernel
open MajoranaPfaffian4 ProjectivePfaffianDeterminantCounts

noncomputable section

/-- The first Majorana is the complexified sum of the existing CAR units. -/
theorem majorana1_from_car :
    majorana1 = annihilationR.map (algebraMap ℝ ℂ) +
      creationR.map (algebraMap ℝ ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana1, splitPos, annihilationR, creationR]

/-- The negative real split generator needs an explicit imaginary factor. -/
theorem majorana2_from_car :
    majorana2 = (-Complex.I) •
      (annihilationR.map (algebraMap ℝ ℂ) - creationR.map (algebraMap ℝ ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana2, splitNeg, annihilationR, creationR]

/-- Parity of the same concrete CAR pair. -/
def parityMatrix : M2C :=
  (annihilationR * creationR - creationR * annihilationR).map (algebraMap ℝ ℂ)

abbrev ChainOp := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Two-site Jordan-Wigner family on the full complex spin space. -/
def twoSiteMajorana : Fin 4 → ChainOp :=
  ![majorana1 ⊗ₖ (1 : M2C), majorana2 ⊗ₖ (1 : M2C),
    parityMatrix ⊗ₖ majorana1, parityMatrix ⊗ₖ majorana2]

/-- Full cross-site CAR, not merely the single-site square identities. -/
theorem twoSiteMajorana_car (a b : Fin 4) :
    twoSiteMajorana a * twoSiteMajorana b + twoSiteMajorana b * twoSiteMajorana a =
      if a = b then 2 else 0 := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  fin_cases a <;> fin_cases b <;>
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [twoSiteMajorana, parityMatrix, majorana1, majorana2,
      splitPos, splitNeg, annihilationR, creationR, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem twoSiteMajorana_selfAdjoint (i : Fin 4) :
    (twoSiteMajorana i).conjTranspose = twoSiteMajorana i := by
  ext a b
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  fin_cases i <;> fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    norm_num [twoSiteMajorana, parityMatrix, majorana1, majorana2,
      splitPos, splitNeg, annihilationR, creationR, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem twoSiteMajorana_ne_zero (i : Fin 4) : twoSiteMajorana i ≠ 0 := by
  intro hz
  have hfield : field twoSiteMajorana (Pi.single i 1) = 0 := by
    simpa only [field_single] using hz
  have hs := (field_eq_zero_iff twoSiteMajorana_car _).mp hfield
  have he := congrFun hs i
  simpa using he

/-- Instantiate the existing Pfaffian carrier from the proved matching law. -/
def matchingKernel (a b c d e f : ℝ) : PfaffianKernel (Fin 4) where
  omega := skewMatrix4 a b c d e f
  skew := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M j i)
      (skewMatrix4_transpose a b c d e f)
    simpa using h
  pfaffian := pfaffian4 a b c d e f
  pf_sq_eq_det := by
    simpa only [pow_two] using skewMatrix4_pfaffian_sq_eq_det a b c d e f

/-- No assumed Majorana family or square-law witness remains in this instance. -/
theorem fourMode_pfaffian_iff_conserved_field (a b c d e f : ℝ) :
    pfaffian4 a b c d e f = 0 ↔ ∃ v : Fin 4 → ℝ,
      field twoSiteMajorana v ≠ 0 ∧
      quadratic twoSiteMajorana (skewMatrix4 a b c d e f) * field twoSiteMajorana v -
        field twoSiteMajorana v * quadratic twoSiteMajorana (skewMatrix4 a b c d e f) = 0 :=
  pfaffian_zero_iff_conserved_majorana twoSiteMajorana_car (matchingKernel a b c d e f)

/-- The open sweet-spot matrix couples only the middle Majorana pair. -/
def sweetSpotKernel (t : ℝ) : PfaffianKernel (Fin 4) :=
  matchingKernel 0 0 0 (2 * t) 0 0

theorem sweetSpot_endpoint_kernel (t : ℝ) :
    (sweetSpotKernel t).omega.mulVec (Pi.single (0 : Fin 4) 1) = 0 ∧
    (sweetSpotKernel t).omega.mulVec (Pi.single (3 : Fin 4) 1) = 0 := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [sweetSpotKernel, matchingKernel, skewMatrix4,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply]

theorem sweetSpot_pfaffian_zero (t : ℝ) : (sweetSpotKernel t).pfaffian = 0 := by
  simp [sweetSpotKernel, matchingKernel, pfaffian4]

/-- Two-site skew generator. The owner adapter identifies the existing chain sum. -/
def twoSiteGenerator (t : ℝ) : ChainOp :=
  t • (twoSiteMajorana 1 * twoSiteMajorana 2)

/-- Exact coefficient/operator normalization. -/
theorem sweetSpot_quadratic_eq_chain (t : ℝ) :
    quadratic twoSiteMajorana (sweetSpotKernel t).omega = twoSiteGenerator t := by
  have hanti : twoSiteMajorana 2 * twoSiteMajorana 1 =
      -(twoSiteMajorana 1 * twoSiteMajorana 2) := by
    have h := twoSiteMajorana_car (2 : Fin 4) (1 : Fin 4)
    simp only [Fin.isValue, show (2 : Fin 4) ≠ 1 by decide, if_false] at h
    exact eq_neg_of_add_eq_zero_left h
  simp [quadratic, sweetSpotKernel, matchingKernel, skewMatrix4,
    Fin.sum_univ_succ, twoSiteGenerator, hanti]
  module

/-- Actual nonzero endpoint operators and the same chain's Pfaffian. -/
theorem car_to_chain_to_pfaffian (t : ℝ) :
    let H := twoSiteGenerator t
    twoSiteMajorana 0 ≠ 0 ∧ twoSiteMajorana 3 ≠ 0 ∧
    H * twoSiteMajorana 0 - twoSiteMajorana 0 * H = 0 ∧
    H * twoSiteMajorana 3 - twoSiteMajorana 3 * H = 0 ∧
    (sweetSpotKernel t).pfaffian = 0 := by
  dsimp only
  obtain ⟨h0, h3⟩ := sweetSpot_endpoint_kernel t
  have c0 := (comm_field_zero_iff twoSiteMajorana_car
    (sweetSpotKernel t).omega (sweetSpotKernel t).skew (Pi.single 0 1)).mpr h0
  have c3 := (comm_field_zero_iff twoSiteMajorana_car
    (sweetSpotKernel t).omega (sweetSpotKernel t).skew (Pi.single 3 1)).mpr h3
  simp only [field_single, sweetSpot_quadratic_eq_chain] at c0 c3
  exact ⟨twoSiteMajorana_ne_zero 0, twoSiteMajorana_ne_zero 3,
    c0, c3, sweetSpot_pfaffian_zero t⟩

end
end InfoGeometry.Canonical.CARMajoranaFiniteBridge
