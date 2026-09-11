/-
Zorn `ell` representation into the existing real-linear modular chiral mirror.

This file is an adapter only.  It does not identify the split-octonion carrier
with a Hilbert-space operator algebra; it proves the consequences once a
linear representation sends `1` to the identity and `ell` to the existing
chiral grading.
-/

import InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ModularChiralMirror

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitOctonionChiralMirrorBridge

open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost
open InfoGeometry.OperatorAlgebra.ModularChiralMirror

abbrev CZ := InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.CZ

abbrev EndR (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  H →L[ℝ] H

def leftProjector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H) : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H + M.chi)

def rightProjector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H) : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H - M.chi)

theorem ell_representation_flips_under_mirror
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H)
    (ρ : CZ →ₗ[ℝ] EndR H)
    (hρ_ell : ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = M.chi) :
    M.J.comp (ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) =
      -(ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit).comp M.J := by
  rw [hρ_ell]
  exact M.J_flips_chi

theorem ell_representation_chiral_plus_eq_left_projector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H)
    (ρ : CZ →ₗ[ℝ] EndR H)
    (hρ_one : ρ 1 = ContinuousLinearMap.id ℝ H)
    (hρ_ell : ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = M.chi) :
    ρ (chiralNull ⟨0, by decide⟩ 1) = leftProjector M := by
  rw [scalar_chiralNull_plus_idempotent]
  simp only [map_smul, map_add, hρ_one]
  rw [hρ_ell]
  rfl

theorem ell_representation_chiral_minus_eq_right_projector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H)
    (ρ : CZ →ₗ[ℝ] EndR H)
    (hρ_one : ρ 1 = ContinuousLinearMap.id ℝ H)
    (hρ_ell : ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = M.chi) :
    ρ (chiralNull ⟨0, by decide⟩ (-1)) = rightProjector M := by
  rw [scalar_chiralNull_minus_idempotent]
  simp only [map_smul, map_sub, hρ_one]
  rw [hρ_ell]
  rfl

theorem ell_representation_chiral_plus_mirror
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H)
    (ρ : CZ →ₗ[ℝ] EndR H)
    (hρ_one : ρ 1 = ContinuousLinearMap.id ℝ H)
    (hρ_ell : ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = M.chi) :
    M.J.comp (ρ (chiralNull ⟨0, by decide⟩ 1)) =
      (ρ (chiralNull ⟨0, by decide⟩ (-1))).comp M.J := by
  rw [ell_representation_chiral_plus_eq_left_projector M ρ hρ_one hρ_ell,
    ell_representation_chiral_minus_eq_right_projector M ρ hρ_one hρ_ell]
  ext x
  simp [leftProjector, rightProjector, ContinuousLinearMap.comp_apply,
    M.J_flips_chi]
  module

theorem ell_representation_boost_mirror
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : RealLinear.ModularChiralMirrorDatum H)
    (ρ : CZ →ₗ[ℝ] EndR H)
    (hρ_one : ρ 1 = ContinuousLinearMap.id ℝ H)
    (hρ_ell : ρ InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = M.chi)
    (η : ℝ) :
    M.J.comp (ρ (splitOctonionBoost η)) =
      (ρ (splitOctonionBoost (-η))).comp M.J := by
  rw [splitOctonionBoost, splitOctonionBoost]
  simp only [map_add, map_smul, map_neg, hρ_one, Real.cosh_neg,
    Real.sinh_neg, neg_smul]
  rw [hρ_ell]
  ext x
  simp only [ContinuousLinearMap.comp_apply, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [M.J_chi_apply]
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    Pi.neg_apply]
  simp

end InfoGeometry.OperatorAlgebra.SplitOctonionChiralMirrorBridge
