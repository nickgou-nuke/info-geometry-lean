/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Clifford.Clifford55

/-!
# A generator-calibrated Clifford map into the existing Witt matrix stage

The five matrix CAR pairs determine a linear map from native `V55`. Its
positive coordinate maps to `cᵢ+aᵢ` and its negative coordinate to `aᵢ-cᵢ`.
Consequently the native half-null generators have precisely the matrix
creation/annihilation normalization. The Clifford square law is derived
from the owner's CAR relations, independently of Fock coordinate ordering.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55WittCalibratedGamma

open scoped BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR

/-- Contribution of one native positive/negative coordinate pair. -/
def gammaSite (v : V55) (i : Fin 5) : MatStage 5 :=
  (v.1 i - v.2 i) • creation i + (v.1 i + v.2 i) • annihilation i

theorem gammaSite_add (v w : V55) (i : Fin 5) :
    gammaSite (v + w) i = gammaSite v i + gammaSite w i := by
  dsimp [gammaSite]
  module

theorem gammaSite_smul (r : ℝ) (v : V55) (i : Fin 5) :
    gammaSite (r • v) i = r • gammaSite v i := by
  simp [gammaSite, smul_add, smul_smul, mul_add, mul_sub]

theorem gammaSite_square (v : V55) (i : Fin 5) :
    gammaSite v i * gammaSite v i =
      (v.1 i ^ 2 - v.2 i ^ 2) • (1 : MatStage 5) := by
  let α := v.1 i - v.2 i
  let β := v.1 i + v.2 i
  change (α • creation i + β • annihilation i) *
      (α • creation i + β • annihilation i) = _
  calc
    _ = (α * α) • (creation i * creation i) +
        (α * β) • (creation i * annihilation i + annihilation i * creation i) +
        (β * β) • (annihilation i * annihilation i) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_smul, smul_add]
      module
    _ = (α * β) • (1 : MatStage 5) := by
      rw [creation_same_site_sq, annihilation_same_site_sq,
        creation_annihilation_same_site]
      simp
    _ = (v.1 i ^ 2 - v.2 i ^ 2) • (1 : MatStage 5) := by
      congr 1
      dsimp [α, β]
      ring

theorem gammaSite_anticommute (v : V55) (i j : Fin 5) (hij : i ≠ j) :
    gammaSite v i * gammaSite v j + gammaSite v j * gammaSite v i = 0 := by
  let α := v.1 i - v.2 i
  let β := v.1 i + v.2 i
  let γ := v.1 j - v.2 j
  let δ := v.1 j + v.2 j
  change (α • creation i + β • annihilation i) *
      (γ • creation j + δ • annihilation j) +
    (γ • creation j + δ • annihilation j) *
      (α • creation i + β • annihilation i) = 0
  calc
    _ = (α * γ) • (creation i * creation j + creation j * creation i) +
        (α * δ) • (creation i * annihilation j + annihilation j * creation i) +
        (β * γ) • (annihilation i * creation j + creation j * annihilation i) +
        (β * δ) • (annihilation i * annihilation j + annihilation j * annihilation i) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_smul, smul_add]
      module
    _ = 0 := by
      rw [creation_cross_anticommute hij, creation_annihilation_cross_anticommute hij,
        annihilation_creation_cross_anticommute hij, annihilation_cross_anticommute hij]
      simp

/-- The square of a finite partial sum is the corresponding quadratic sum. -/
theorem gamma_sum_square (v : V55) (s : Finset (Fin 5)) :
    (∑ i ∈ s, gammaSite v i) * (∑ i ∈ s, gammaSite v i) =
      (∑ i ∈ s, (v.1 i ^ 2 - v.2 i ^ 2)) • (1 : MatStage 5) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hcross : gammaSite v i * (∑ j ∈ s, gammaSite v j) +
        (∑ j ∈ s, gammaSite v j) * gammaSite v i = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro j hj
      apply gammaSite_anticommute
      intro hij
      exact hi (hij.symm ▸ hj)
    simp only [Finset.sum_insert hi]
    calc
      _ = gammaSite v i * gammaSite v i +
          (∑ j ∈ s, gammaSite v j) * (∑ j ∈ s, gammaSite v j) +
          (gammaSite v i * (∑ j ∈ s, gammaSite v j) +
            (∑ j ∈ s, gammaSite v j) * gammaSite v i) := by noncomm_ring
      _ = ((v.1 i ^ 2 - v.2 i ^ 2) +
          ∑ j ∈ s, (v.1 j ^ 2 - v.2 j ^ 2)) • (1 : MatStage 5) := by
        rw [gammaSite_square, ih, hcross, add_zero, add_smul]

/-- Native coordinates are mapped to the already owned Jordan–Wigner matrices. -/
def wittGamma : V55 →ₗ[ℝ] MatStage 5 where
  toFun v := ∑ i : Fin 5, gammaSite v i
  map_add' v w := by simp only [gammaSite_add, Finset.sum_add_distrib]
  map_smul' r v := by simp only [gammaSite_smul, Finset.smul_sum, RingHom.id_apply]

theorem wittGamma_square (v : V55) :
    wittGamma v * wittGamma v = algebraMap ℝ (MatStage 5) (Q55 v) := by
  change (∑ i : Fin 5, gammaSite v i) * (∑ i : Fin 5, gammaSite v i) = _
  rw [gamma_sum_square]
  simp [Q55_apply, Finset.sum_sub_distrib, Algebra.algebraMap_eq_smul_one]

@[simp] theorem wittGamma_e_pos (i : Fin 5) :
    wittGamma (e_pos i) = creation i + annihilation i := by
  classical
  change (∑ j : Fin 5, gammaSite (e_pos i) j) = _
  rw [Finset.sum_eq_single i]
  · simp [gammaSite, e_pos]
  · intro j _ hji
    simp [gammaSite, e_pos, hji]
  · simp

@[simp] theorem wittGamma_f_neg (i : Fin 5) :
    wittGamma (f_neg i) = -creation i + annihilation i := by
  classical
  change (∑ j : Fin 5, gammaSite (f_neg i) j) = _
  rw [Finset.sum_eq_single i]
  · simp [gammaSite, f_neg]
  · intro j _ hji
    simp [gammaSite, f_neg, hji]
  · simp

end InfoGeometry.Clifford.Cl55WittCalibratedGamma
