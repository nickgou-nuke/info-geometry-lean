/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55ContactGradeDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Orthogonal.O55ContactLie
import InfoGeometry.Orthogonal.O55ContactGrading

/-! Native two-boundary matrix-coefficient readouts. -/

noncomputable section
namespace InfoGeometry.Orthogonal.O55Contact

structure BoundaryPair55 where
  ket : Vector55
  bra : Module.Dual ℝ Vector55
  overlap_ne : bra ket ≠ 0

namespace BoundaryPair55

def overlap (B : BoundaryPair55) : ℝ := B.bra B.ket

def numerator (B : BoundaryPair55) (A : End55) : ℝ := B.bra (A B.ket)

def readout (B : BoundaryPair55) (A : End55) : ℝ :=
  B.numerator A / B.overlap

@[simp] theorem overlap_ne_zero (B : BoundaryPair55) : B.overlap ≠ 0 :=
  B.overlap_ne

@[simp] theorem numerator_zero (B : BoundaryPair55) : B.numerator 0 = 0 := by
  simp [numerator]

@[simp] theorem numerator_add (B : BoundaryPair55) (A C : End55) :
    B.numerator (A + C) = B.numerator A + B.numerator C := by
  simp [numerator]

@[simp] theorem numerator_smul (B : BoundaryPair55) (c : ℝ) (A : End55) :
    B.numerator (c • A) = c * B.numerator A := by
  simp [numerator]

@[simp] theorem readout_zero (B : BoundaryPair55) : B.readout 0 = 0 := by
  simp [readout]

@[simp] theorem readout_one (B : BoundaryPair55) : B.readout 1 = 1 := by
  simp [readout, numerator, overlap, B.overlap_ne]

@[simp] theorem readout_add (B : BoundaryPair55) (A C : End55) :
    B.readout (A + C) = B.readout A + B.readout C := by
  simp [readout, add_div]

@[simp] theorem readout_smul (B : BoundaryPair55) (c : ℝ) (A : End55) :
    B.readout (c • A) = c * B.readout A := by
  simp [readout]
  ring

def readoutLinear (B : BoundaryPair55) : End55 →ₗ[ℝ] ℝ where
  toFun := B.readout
  map_add' := B.readout_add
  map_smul' c A := by
    simpa only [smul_eq_mul, RingHom.id_apply] using B.readout_smul c A

def idempotent (B : BoundaryPair55) : End55 where
  toFun x := (B.bra x / B.overlap) • B.ket
  map_add' x y := by
    simp [map_add, add_div, add_smul]
  map_smul' c x := by
    simp [map_smul, mul_div_assoc, smul_smul]

@[simp] theorem idempotent_apply (B : BoundaryPair55) (x : Vector55) :
    B.idempotent x = (B.bra x / B.overlap) • B.ket := rfl

theorem idempotent_sq (B : BoundaryPair55) :
    B.idempotent * B.idempotent = B.idempotent := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, idempotent_apply, overlap, B.overlap_ne]

theorem idempotent_sandwich (B : BoundaryPair55) (A : End55) :
    B.idempotent * A * B.idempotent = B.readout A • B.idempotent := by
  apply LinearMap.ext
  intro x
  simp [Module.End.mul_apply, idempotent_apply, readout,
    numerator, overlap, div_eq_mul_inv, smul_smul]
  field_simp [B.overlap_ne]

def rescale (B : BoundaryPair55) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) : BoundaryPair55 where
  ket := a • B.ket
  bra := b • B.bra
  overlap_ne := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact mul_ne_zero ha (mul_ne_zero hb B.overlap_ne)

theorem readout_rescale (B : BoundaryPair55) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (A : End55) :
    (B.rescale a b ha hb).readout A = B.readout A := by
  unfold readout numerator overlap rescale
  simp only [LinearMap.smul_apply, map_smul, LinearMap.map_smul,
    smul_eq_mul]
  field_simp [ha, hb, B.overlap_ne]

end BoundaryPair55

def IsKetWeight (a : ℤ) (v : Vector55) : Prop :=
  contactEulerEnd v = (a : ℝ) • v

def IsBraWeight (b : ℤ) (f : Module.Dual ℝ Vector55) : Prop :=
  ∀ x, f (contactEulerEnd x) = (b : ℝ) * f x

theorem homogeneous_matrix_coefficient_balance
    {a b k : ℤ} {v : Vector55} {f : Module.Dual ℝ Vector55}
    {A : O55Lie}
    (hv : IsKetWeight a v)
    (hf : IsBraWeight b f)
    (hA : A ∈ realContactGradeSpace k) :
    ((b : ℝ) - (a : ℝ) - (k : ℝ)) * f ((A : End55) v) = 0 := by
  unfold IsKetWeight at hv
  unfold IsBraWeight at hf
  unfold realContactGradeSpace IsContactGrade at hA
  have hpoint := LinearMap.congr_fun hA v
  change contactEulerEnd ((A : End55) v) -
      (A : End55) (contactEulerEnd v) =
    (k : ℝ) • (A : End55) v at hpoint
  have hscalar := congrArg f hpoint
  simp only [map_sub, map_smul] at hscalar
  rw [hf, hv, map_smul] at hscalar
  simp only [LinearMap.map_smul, smul_eq_mul] at hscalar
  linear_combination hscalar

theorem homogeneous_numerator_eq_zero_of_weight_mismatch
    {a b k : ℤ} {v : Vector55} {f : Module.Dual ℝ Vector55}
    {A : O55Lie}
    (hv : IsKetWeight a v)
    (hf : IsBraWeight b f)
    (hA : A ∈ realContactGradeSpace k)
    (hmismatch : b - a ≠ k) :
    f ((A : End55) v) = 0 := by
  have hbalance := homogeneous_matrix_coefficient_balance hv hf hA
  have hcoeffInt : b - a - k ≠ 0 := by omega
  have hcoeff : ((b : ℝ) - (a : ℝ) - (k : ℝ)) ≠ 0 := by
    exact_mod_cast hcoeffInt
  exact (mul_eq_zero.mp hbalance).resolve_left hcoeff

theorem homogeneous_readout_eq_zero_of_weight_mismatch
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket)
    (hf : IsBraWeight b B.bra)
    (hA : A ∈ realContactGradeSpace k)
    (hmismatch : b - a ≠ k) :
    B.readout (A : End55) = 0 := by
  unfold BoundaryPair55.readout BoundaryPair55.numerator
  rw [homogeneous_numerator_eq_zero_of_weight_mismatch hv hf hA hmismatch]
  simp

theorem contact_degree_of_nonzero_readout
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket)
    (hf : IsBraWeight b B.bra)
    (hA : A ∈ realContactGradeSpace k)
    (hnonzero : B.readout (A : End55) ≠ 0) :
    b - a = k := by
  by_contra h
  exact hnonzero
    (homogeneous_readout_eq_zero_of_weight_mismatch B hv hf hA h)


theorem block_numerator_eq_zero_of_weight_mismatch
    (d : BlockDegree) (A : End55)
    {a b : ℤ} {v : Vector55} {f : Module.Dual ℝ Vector55}
    (hv : IsKetWeight a v) (hf : IsBraWeight b f)
    (hmismatch : b - a ≠ d.contact) :
    f (blockComponent d A v) = 0 := by
  have hgrade := blockComponent_grade d A
  have hpoint := LinearMap.congr_fun hgrade v
  change contactEulerEnd (blockComponent d A v) -
      blockComponent d A (contactEulerEnd v) =
    (d.contact : ℝ) • blockComponent d A v at hpoint
  have hscalar := congrArg f hpoint
  simp only [map_sub, map_smul] at hscalar
  rw [hf, hv] at hscalar
  simp only [LinearMap.map_smul, smul_eq_mul] at hscalar
  have hbalance :
      ((b : ℝ) - (a : ℝ) - (d.contact : ℝ)) * f (blockComponent d A v) = 0 := by
    linear_combination hscalar
  have hcoeffInt : b - a - d.contact ≠ 0 := by omega
  have hcoeff : ((b : ℝ) - (a : ℝ) - (d.contact : ℝ)) ≠ 0 := by exact_mod_cast hcoeffInt
  exact (mul_eq_zero.mp hbalance).resolve_left hcoeff

/-- Crosscap transform of both boundary representatives. -/
def BoundaryPair55.crosscap (B : BoundaryPair55) : BoundaryPair55 where
  ket := crosscapEnd B.ket
  bra := B.bra.comp crosscapEnd
  overlap_ne := by
    change B.bra (crosscapEnd (crosscapEnd B.ket)) ≠ 0
    rw [crosscapEnd_apply_twice]
    exact B.overlap_ne

@[simp] theorem BoundaryPair55.crosscap_overlap (B : BoundaryPair55) :
    B.crosscap.overlap = B.overlap := by
  unfold BoundaryPair55.crosscap BoundaryPair55.overlap
  change B.bra (crosscapEnd (crosscapEnd B.ket)) = B.bra B.ket
  rw [crosscapEnd_apply_twice]

theorem BoundaryPair55.crosscap_readout (B : BoundaryPair55) (A : O55Lie) :
    B.crosscap.readout (crosscapConjugation A : End55) = B.readout (A : End55) := by
  unfold BoundaryPair55.readout BoundaryPair55.numerator
  rw [B.crosscap_overlap]
  congr 1
  change B.bra (crosscapEnd
      (crosscapEnd ((A : End55) (crosscapEnd (crosscapEnd B.ket))))) =
    B.bra ((A : End55) B.ket)
  simp

theorem crosscap_ket_weight {a : ℤ} {v : Vector55} (hv : IsKetWeight a v) :
    IsKetWeight (-a) (crosscapEnd v) := by
  unfold IsKetWeight at hv ⊢
  have hanti := LinearMap.congr_fun crosscap_anticommutes_euler v
  change contactEulerEnd (crosscapEnd v) = -(crosscapEnd (contactEulerEnd v)) at hanti
  rw [hanti, hv, map_smul]
  simp

theorem crosscap_bra_weight {b : ℤ} {f : Module.Dual ℝ Vector55}
    (hf : IsBraWeight b f) : IsBraWeight (-b) (f.comp crosscapEnd) := by
  intro x
  change f (crosscapEnd (contactEulerEnd x)) = ((-b : ℤ) : ℝ) * f (crosscapEnd x)
  have hanti : crosscapEnd (contactEulerEnd x) = -(contactEulerEnd (crosscapEnd x)) := by
    funext i
    simp [crosscapEnd_apply, contactEulerEnd_apply, contactWeightR_dualIndex]
  rw [hanti, map_neg, hf]
  simp

theorem crosscap_selection_packet
    {a b k : ℤ} (B : BoundaryPair55) {A : O55Lie}
    (hv : IsKetWeight a B.ket) (hf : IsBraWeight b B.bra)
    (hA : A ∈ realContactGradeSpace k) :
    IsKetWeight (-a) B.crosscap.ket ∧ IsBraWeight (-b) B.crosscap.bra ∧
      crosscapConjugation A ∈ realContactGradeSpace (-k) ∧
      B.crosscap.readout (crosscapConjugation A : End55) = B.readout (A : End55) := by
  exact ⟨crosscap_ket_weight hv, crosscap_bra_weight hf,
    crosscap_reverses_grade hA, B.crosscap_readout A⟩

end InfoGeometry.Orthogonal.O55Contact
