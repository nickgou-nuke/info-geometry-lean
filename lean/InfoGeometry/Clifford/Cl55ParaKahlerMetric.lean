/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ParaKahlerGeneralizedMetric
import InfoGeometry.Clifford.Cl55PureSpinorParaGrassmannianBridge
import InfoGeometry.Clifford.ParaKahler55SUSYClosure
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Native (5,5) para-Kähler and positive-metric transport

All forms live on the existing carriers. The metric of the para-Grassmannian
is minus the polar of Q55, not the positive generalized metric. The selected
duality supplies the latter, and transports its complex phase to (-y,x).
No Pin action, geometric holonomy or global supergeometry is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ParaKahlerMetric

open scoped BigOperators
open Clifford55 NeutralPhaseSpaceCore PhaseSpaceGeneralizedMetric
open PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open Cl55NeutralHyperbolicIsometry (dualToV5 neutralToV55 dualToV5_apply_mul_sum
  q55_neutralToV55)
open ParaKahler55SUSYClosure

/-- The native basis-dual identification is the Euclidean dot pairing. -/
theorem dualToV5_symm_apply (x y : Fin 5 → ℝ) :
    dualToV5.symm x y = ∑ i, y i * x i := by
  simpa using (dualToV5_apply_mul_sum y (dualToV5.symm x)).symm

/-- An actual inhabitant of the existing metric-data owner, not an assumed metric. -/
def euclideanMetric : MetricDatum (Fin 5 → ℝ) where
  gFlat := dualToV5.symm
  symmetric x y := by
    simp only [dualToV5_symm_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem euclideanMetric_pos (x : Fin 5 → ℝ) (hx : x ≠ 0) :
    0 < euclideanMetric.gFlat x x := by
  change 0 < dualToV5.symm x x
  rw [dualToV5_symm_apply]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_self_nonneg (x i))).mpr
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- The neutral para grading becomes the existing five-slot swap. -/
theorem neutralToV55_para (X : PhaseSpaceCarrier (Fin 5 → ℝ)) :
    neutralToV55 (neutralParaInvolution X) = paraKahlerK (neutralToV55 X) := by
  apply Prod.ext <;> funext i <;>
    simp [Cl55NeutralHyperbolicIsometry.neutralToV55, paraKahlerK, fst55, snd55,
      sub_eq_add_neg]

/-- The generalized-metric polarization becomes the diagonal sign involution. -/
theorem neutralToV55_polarization (X : PhaseSpaceCarrier (Fin 5 → ℝ)) :
    neutralToV55 ((ofMetric euclideanMetric).polarization X) =
      ((neutralToV55 X).1, -(neutralToV55 X).2) := by
  rw [ofMetric_polarization]
  apply Prod.ext <;> funext i <;>
    simp [basePolarization, ofMetric, euclideanMetric,
      Cl55NeutralHyperbolicIsometry.neutralToV55] <;> ring

/-- The phase is the native real complex rotation, with the same selected duality. -/
theorem neutralToV55_phase (X : PhaseSpaceCarrier (Fin 5 → ℝ)) :
    neutralToV55 (ParaKahlerGeneralizedMetric.phase euclideanMetric X) =
      (-(neutralToV55 X).2, (neutralToV55 X).1) := by
  rw [ParaKahlerGeneralizedMetric.phase_apply]
  apply Prod.ext <;> funext i <;>
    simp [euclideanMetric, Cl55NeutralHyperbolicIsometry.neutralToV55] <;> ring

/-- Polarization fixes the factor of two in the diagonal/neutral identification. -/
theorem polar_neutralToV55 (X Y : PhaseSpaceCarrier (Fin 5 → ℝ)) :
    Q55.polarBilin (neutralToV55 X) (neutralToV55 Y) = canonicalNeutralBilin X Y := by
  change QuadraticMap.polar Q55 (neutralToV55 X) (neutralToV55 Y) = _
  rw [QuadraticMap.polar, ← map_add, q55_neutralToV55, q55_neutralToV55,
    q55_neutralToV55]
  exact canonicalNeutralFormUnscaled_polar X Y

/-- Transport of the actual nondegenerate skew form. -/
def diagonalOmega : LinearMap.BilinForm ℝ V55 :=
  LinearMap.BilinForm.congr neutralToV55 (neutralOmega (E := Fin 5 → ℝ))

/-- Positive generalized metric, distinct from the indefinite para metric. -/
def positiveMetric : LinearMap.BilinForm ℝ V55 :=
  LinearMap.BilinForm.congr neutralToV55 (ofMetric euclideanMetric).generalizedMetricForm

@[simp] theorem diagonalOmega_transport (X Y : PhaseSpaceCarrier (Fin 5 → ℝ)) :
    diagonalOmega (neutralToV55 X) (neutralToV55 Y) = neutralOmega X Y := by
  simp [diagonalOmega, LinearMap.BilinForm.congr_apply]

@[simp] theorem positiveMetric_transport (X Y : PhaseSpaceCarrier (Fin 5 → ℝ)) :
    positiveMetric (neutralToV55 X) (neutralToV55 Y) =
      (ofMetric euclideanMetric).generalizedMetricForm X Y := by
  simp [positiveMetric, LinearMap.BilinForm.congr_apply]

theorem diagonalOmega_nondegenerate : diagonalOmega.Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.congr neutralToV55 neutralOmega_nondegenerate

theorem diagonalOmega_skew (u v : V55) : diagonalOmega u v = -diagonalOmega v u :=
  neutralOmega_skew _ _

/-- Exact compatibility with the existing para-Grassmannian convention g = -B. -/
theorem diagonalOmega_eq_neg_polar_para (u v : V55) :
    diagonalOmega u v = -Q55.polarBilin u (paraKahlerK v) := by
  obtain ⟨X, rfl⟩ := neutralToV55.surjective u
  obtain ⟨Y, rfl⟩ := neutralToV55.surjective v
  rw [← neutralToV55_para, polar_neutralToV55, diagonalOmega_transport]
  simp [neutralOmega_apply, canonicalNeutralBilin_apply, sub_eq_add_neg]

theorem positiveMetric_symm (u v : V55) : positiveMetric u v = positiveMetric v u :=
  (ofMetric euclideanMetric).generalizedMetricForm_symm _ _

theorem positiveMetric_pos (v : V55) (hv : v ≠ 0) : 0 < positiveMetric v v := by
  apply ParaKahlerGeneralizedMetric.generalizedMetricForm_pos euclideanMetric
    euclideanMetric_pos
  exact fun h => hv (neutralToV55.symm.injective (by simpa using h))

theorem positiveMetric_nondegenerate : positiveMetric.Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.congr neutralToV55
    (ParaKahlerGeneralizedMetric.generalizedMetricForm_nondegenerate
      euclideanMetric euclideanMetric_pos)

/-- The fundamental sign operator, rather than K, converts the polar to positivity. -/
theorem positiveMetric_eq_polar_sign (u v : V55) :
    positiveMetric u v = Q55.polarBilin u (v.1, -v.2) := by
  obtain ⟨X, rfl⟩ := neutralToV55.surjective u
  obtain ⟨Y, rfl⟩ := neutralToV55.surjective v
  rw [← neutralToV55_polarization, polar_neutralToV55, positiveMetric_transport]
  rfl

/-- Explicit normalization of the native polar form. -/
theorem polar_apply (u v : V55) :
    Q55.polarBilin u v =
      2 * ((∑ i, u.1 i * v.1 i) - ∑ i, u.2 i * v.2 i) := by
  change Q55 (u + v) - Q55 u - Q55 v = _
  simp [Q55_apply, Fin.sum_univ_succ]
  ring

@[simp] theorem diagonalOmega_e_pos (i : Fin 5) (v : V55) :
    diagonalOmega (e_pos i) v = -2 * v.2 i := by
  rw [diagonalOmega_eq_neg_polar_para, polar_apply]
  simp [e_pos, paraKahlerK, fst55, snd55]

@[simp] theorem positiveMetric_e_pos (i : Fin 5) (v : V55) :
    positiveMetric (e_pos i) v = 2 * v.1 i := by
  rw [positiveMetric_eq_polar_sign, polar_apply]
  simp [e_pos]

/-- The indefinite polar cannot be used as a positive dissipative pairing. -/
theorem polar_negative_direction : Q55.polarBilin (f_neg 0) (f_neg 0) = -2 := by
  change QuadraticMap.polar Q55 (f_neg 0) (f_neg 0) = -2
  norm_num [QuadraticMap.polar, Q55_apply, f_neg, Fin.sum_univ_succ]

end InfoGeometry.Clifford.Cl55ParaKahlerMetric
