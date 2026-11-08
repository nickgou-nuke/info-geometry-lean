/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl33BivectorLoxodromicBridge
import InfoGeometry.Clifford.Cl55SpinorChirality

/-!
# Cl(3,3) volume and matrix chirality projectors

This module records the exact ordered Clifford volume on the repository's
recursive `Cl_split 3` carrier and its 8 × 8 spinor readout.  The generator
order is positive coordinates first, followed by negative coordinates.  No
claim about a 4-dimensional half-spinor carrier is made here.

This module compares the positive-first ordered volume with the recursive
paired-generator grading tensor and records the orientation sign in the
8 × 8 real spinor representation. It proves matrix-level volume involution
and complementary orthogonal projectors. It does not assert the Clifford
volume square, projector ranks, a four-dimensional half-spinor carrier, or a
full matrix-algebra representation theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl33SpinorChirality

open InfoGeometry.Clifford.Cl33BivectorLoxodromicBridge
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.Cl55SpinorChirality

abbrev Cl33 := InfoGeometry.Clifford.SpinorRep.Cl_split 3
abbrev SpinorMatrix33 := Matrix (Fin 8) (Fin 8) ℝ

/-- The second negative coordinate vector in the recursive split carrier. -/
def f₂ : Carrier := ((0, 0), ((0, 1), 0))

/-- The third negative coordinate vector in the recursive split carrier. -/
def f₃ : Carrier := ((0, 0), ((0, 0), ((0, 1), 0)))

/-- The ordered recursive Witt pairs used by the spinor tower. -/
def pairedBasis33 : List Carrier := [e₁, f₁, e₂, f₂, e₃, f₃]

/-- The same volume written in the recursive tower's paired order. -/
def pairedVolumeClifford33 : Cl33 := (pairedBasis33.map γ).prod

/-- The ordered six-vector volume element for the convention
`e₁,e₂,e₃,f₁,f₂,f₃` on the repository's `Cl_split 3`. -/
def volumeClifford33 : Cl33 :=
  (((((γ e₁ * γ e₂) * γ e₃) * γ f₁) * γ f₂) * γ f₃)

/-- The spinor representation readout of the ordered Clifford volume. -/
def volumeMatrix33 : SpinorMatrix33 :=
  spinorRepresentation 3 volumeClifford33

/-- Matrix readout of the recursive paired volume. -/
def pairedVolumeMatrix33 : SpinorMatrix33 :=
  spinorRepresentation 3 pairedVolumeClifford33

/-- The recursive grading matrix at the `Cl(3,3)` spinor stage. -/
def gradingMatrix33 : SpinorMatrix33 :=
  tensorMatrixEquivFinPowTwo 3 (gradingTensor 3)

theorem gradingMatrix33_sq :
    gradingMatrix33 * gradingMatrix33 = (1 : SpinorMatrix33) := by
  rw [gradingMatrix33, ← map_mul, gradingTensor_sq, map_one]

private theorem f₁_e₂_ortho : Q33.IsOrtho f₁ e₂ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [f₁, e₂, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem f₁_e₃_ortho : Q33.IsOrtho f₁ e₃ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [f₁, e₃, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem f₂_e₃_ortho : Q33.IsOrtho f₂ e₃ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [f₂, e₃, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem gamma_anticomm_of_isOrtho (v w : Carrier)
    (h : Q33.IsOrtho v w) : γ v * γ w = -(γ w * γ v) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h

private theorem gamma_f₁_e₂_anticommute :
    γ f₁ * γ e₂ = -(γ e₂ * γ f₁) :=
  gamma_anticomm_of_isOrtho f₁ e₂ f₁_e₂_ortho

private theorem gamma_f₁_e₃_anticommute :
    γ f₁ * γ e₃ = -(γ e₃ * γ f₁) :=
  gamma_anticomm_of_isOrtho f₁ e₃ f₁_e₃_ortho

private theorem gamma_f₂_e₃_anticommute :
    γ f₂ * γ e₃ = -(γ e₃ * γ f₂) :=
  gamma_anticomm_of_isOrtho f₂ e₃ f₂_e₃_ortho

private theorem pairedBasis33_eq_pairedSplitVectors :
    pairedBasis33 = pairedSplitVectors 3 := by
  rfl

private lemma algHom_map_foldl_mul
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (L : List A) (a : A) :
    f (L.foldl (· * ·) a) = (L.map f).foldl (· * ·) (f a) := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, map_mul]

private lemma foldl_mul_one_eq_prod {M : Type*} [Monoid M] (L : List M) :
    L.foldl (· * ·) 1 = L.prod := by
  have h (a : M) : L.foldl (· * ·) a = a * L.prod := by
    induction L generalizing a with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.prod_cons, ih]
        rw [mul_assoc]
  have h1 := h 1
  rw [one_mul] at h1
  exact h1

private theorem pairedVolumeClifford33_leftAssociated :
    pairedVolumeClifford33 =
      (((((γ e₁ * γ f₁) * γ e₂) * γ f₂) * γ e₃) * γ f₃) := by
  rw [pairedVolumeClifford33, pairedBasis33, ← foldl_mul_one_eq_prod]
  simp only [List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, one_mul]

/-- Moving from the standard all-positive-then-all-negative orientation to
the recursive positive/negative pair order makes three swaps. -/
theorem orderedVolume_eq_neg_pairedVolume :
    volumeClifford33 = -pairedVolumeClifford33 := by
  rw [volumeClifford33, pairedVolumeClifford33_leftAssociated]
  let a := γ e₁
  let b := γ e₂
  let c := γ e₃
  let d := γ f₁
  let e := γ f₂
  let f := γ f₃
  have hcd : c * d = -(d * c) := by
    calc
      c * d = -(-(c * d)) := by simp
      _ = -(d * c) := by
        rw [← gamma_f₁_e₃_anticommute]
  have hbd : b * d = -(d * b) := by
    calc
      b * d = -(-(b * d)) := by simp
      _ = -(d * b) := by
        rw [← gamma_f₁_e₂_anticommute]
  have hce : c * e = -(e * c) := by
    calc
      c * e = -(-(c * e)) := by simp
      _ = -(e * c) := by
        rw [← gamma_f₂_e₃_anticommute]
  change (((((a * b) * c) * d) * e) * f) =
    -(((((a * d) * b) * e) * c) * f)
  calc
    (((((a * b) * c) * d) * e) * f) =
        -(((((a * b) * d) * c) * e) * f) := by
          have h := congrArg (fun z : Cl33 => ((((a * b) * z) * e) * f)) hcd
          simpa only [mul_assoc, mul_neg, neg_mul] using h
    _ = (((((a * d) * b) * c) * e) * f) := by
          have h := congrArg (fun z : Cl33 => ((((a * z) * c) * e) * f)) hbd
          have hn := congrArg Neg.neg h
          simpa only [neg_neg, mul_assoc, mul_neg, neg_mul] using hn
    _ = -(((((a * d) * b) * e) * c) * f) := by
          have h := congrArg (fun z : Cl33 => ((((a * d) * b) * z) * f)) hce
          simpa only [mul_assoc, mul_neg, neg_mul] using h

/-- The spinor representation sends the paired Clifford volume to the
recursive grading tensor. -/
theorem pairedVolumeMatrix33_eq_gradingMatrix33 :
    pairedVolumeMatrix33 = gradingMatrix33 := by
  rw [pairedVolumeMatrix33, pairedVolumeClifford33,
    pairedBasis33_eq_pairedSplitVectors]
  rw [← foldl_mul_one_eq_prod]
  rw [algHom_map_foldl_mul (f := spinorRepresentation 3)]
  simp only [map_one, List.map_map]
  have hpoint (v : Carrier) :
      spinorRepresentation 3 (γ v) =
        tensorMatrixEquivFinPowTwo 3 (recursiveGammaTensor 3 v) := by
    rw [γ, spinorRepresentation_ι]
    rfl
  have hlist :
      (pairedSplitVectors 3).map ((spinorRepresentation 3) ∘ γ) =
        (pairedSplitVectors 3).map
          ((tensorMatrixEquivFinPowTwo 3) ∘ recursiveGammaTensor 3) := by
    apply List.map_congr_left
    intro v _
    exact hpoint v
  rw [hlist]
  have hone : tensorMatrixEquivFinPowTwo 3
      (1 : InfoGeometry.Clifford.GammaMatrices.SplitGammaMatrix 3) =
      (1 : SpinorMatrix33) := map_one (tensorMatrixEquivFinPowTwo 3)
  rw [← hone]
  have hmap := algHom_map_foldl_mul
    (f := (tensorMatrixEquivFinPowTwo 3).toAlgHom)
    ((pairedSplitVectors 3).map (recursiveGammaTensor 3))
    (1 : InfoGeometry.Clifford.GammaMatrices.SplitGammaMatrix 3)
  change ((((pairedSplitVectors 3).map (recursiveGammaTensor 3)).map
    (tensorMatrixEquivFinPowTwo 3).toAlgHom).foldl (· * ·)
      ((tensorMatrixEquivFinPowTwo 3).toAlgHom
        (1 : InfoGeometry.Clifford.GammaMatrices.SplitGammaMatrix 3))) =
    gradingMatrix33
  rw [← hmap]
  rw [← pairedGammaProduct_fold, pairedGammaProduct_eq_gradingTensor]
  rfl

/-- Correct orientation sign for the ordered positive-first volume readout. -/
theorem volumeMatrix33_eq_neg_gradingMatrix33 :
    volumeMatrix33 = -gradingMatrix33 := by
  rw [volumeMatrix33, orderedVolume_eq_neg_pairedVolume,
    map_neg, ← pairedVolumeMatrix33, pairedVolumeMatrix33_eq_gradingMatrix33]

/-- The ordered Cl(3,3) volume squares to `+1` in the actual 8 × 8
spinor representation. -/
theorem volumeMatrix33_sq :
    volumeMatrix33 * volumeMatrix33 = (1 : SpinorMatrix33) := by
  rw [volumeMatrix33_eq_neg_gradingMatrix33, neg_mul_neg, gradingMatrix33_sq]

/-- Positive eigensheet projector for the recursive grading matrix. -/
def gradingPlusProjector33 : SpinorMatrix33 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix33) + gradingMatrix33)

/-- Negative eigensheet projector for the recursive grading matrix. -/
def gradingMinusProjector33 : SpinorMatrix33 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix33) - gradingMatrix33)

theorem gradingPlusProjector33_idempotent :
    gradingPlusProjector33 * gradingPlusProjector33 = gradingPlusProjector33 := by
  rw [gradingPlusProjector33, smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [add_mul, mul_add, one_mul, mul_one, gradingMatrix33_sq]
  module

theorem gradingMinusProjector33_idempotent :
    gradingMinusProjector33 * gradingMinusProjector33 = gradingMinusProjector33 := by
  rw [gradingMinusProjector33, smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [sub_mul, mul_sub, one_mul, mul_one, gradingMatrix33_sq]
  module

theorem gradingProjectors33_complementary :
    gradingPlusProjector33 + gradingMinusProjector33 = (1 : SpinorMatrix33) := by
  rw [gradingPlusProjector33, gradingMinusProjector33]
  module

theorem gradingProjectors33_orthogonal :
    gradingPlusProjector33 * gradingMinusProjector33 = 0 := by
  rw [gradingPlusProjector33, gradingMinusProjector33, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [add_mul, mul_sub, one_mul, mul_one, gradingMatrix33_sq]
  module

theorem gradingProjectors33_orthogonal_rev :
    gradingMinusProjector33 * gradingPlusProjector33 = 0 := by
  rw [gradingPlusProjector33, gradingMinusProjector33, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [sub_mul, mul_add, one_mul, mul_one, gradingMatrix33_sq]
  module

/-- Positive eigensheet projector for the standard ordered Clifford volume. -/
def volumePlusProjector33 : SpinorMatrix33 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix33) + volumeMatrix33)

/-- Negative eigensheet projector for the standard ordered Clifford volume. -/
def volumeMinusProjector33 : SpinorMatrix33 :=
  (1 / 2 : ℝ) • ((1 : SpinorMatrix33) - volumeMatrix33)

theorem volumePlusProjector33_idempotent :
    volumePlusProjector33 * volumePlusProjector33 = volumePlusProjector33 := by
  rw [volumePlusProjector33, smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [add_mul, mul_add, one_mul, mul_one, volumeMatrix33_sq]
  module

theorem volumeMinusProjector33_idempotent :
    volumeMinusProjector33 * volumeMinusProjector33 = volumeMinusProjector33 := by
  rw [volumeMinusProjector33, smul_mul_assoc, Algebra.mul_smul_comm]
  simp only [sub_mul, mul_sub, one_mul, mul_one, volumeMatrix33_sq]
  module

theorem volumeProjectors33_complementary :
    volumePlusProjector33 + volumeMinusProjector33 = (1 : SpinorMatrix33) := by
  rw [volumePlusProjector33, volumeMinusProjector33]
  module

theorem volumeProjectors33_orthogonal :
    volumePlusProjector33 * volumeMinusProjector33 = 0 := by
  rw [volumePlusProjector33, volumeMinusProjector33, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [add_mul, mul_sub, one_mul, mul_one, volumeMatrix33_sq]
  module

theorem volumeProjectors33_orthogonal_rev :
    volumeMinusProjector33 * volumePlusProjector33 = 0 := by
  rw [volumePlusProjector33, volumeMinusProjector33, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [sub_mul, mul_add, one_mul, mul_one, volumeMatrix33_sq]
  module

/-- The all-positive-then-all-negative orientation exchanges the grading
eigensheet labels, as dictated by the three-swap sign. -/
theorem volumePlusProjector33_eq_gradingMinusProjector33 :
    volumePlusProjector33 = gradingMinusProjector33 := by
  rw [volumePlusProjector33, gradingMinusProjector33,
    volumeMatrix33_eq_neg_gradingMatrix33]
  module

theorem volumeMinusProjector33_eq_gradingPlusProjector33 :
    volumeMinusProjector33 = gradingPlusProjector33 := by
  rw [volumeMinusProjector33, gradingPlusProjector33,
    volumeMatrix33_eq_neg_gradingMatrix33]
  module

end InfoGeometry.Clifford.Cl33SpinorChirality
