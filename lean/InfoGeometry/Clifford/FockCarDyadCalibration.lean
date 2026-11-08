import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A finite, explicit calibration of the top exterior dyad.

This is deliberately a coordinate model: it records the empty-to-full rank-one
operator and the distinction between total occupation and a two-mode contact
Euler operator.  It does not identify either operator with a physical state.
-/

namespace InfoGeometry.FockCarDyadCalibration

noncomputable section

open Finset

abbrev FockSpace := Finset (Fin 5) → ℝ

def vac : FockSpace := fun t => if t = ∅ then 1 else 0
def fullState : FockSpace := fun t => if t = univ then 1 else 0

@[simp] theorem vac_empty : vac ∅ = 1 := by simp [vac]
@[simp] theorem vac_univ : vac univ = 0 := by
  have h : (univ : Finset (Fin 5)) ≠ ∅ := by
    intro h'
    have hc := congrArg Finset.card h'
    simp at hc
  simp [vac, h]

@[simp] theorem full_univ : fullState (univ : Finset (Fin 5)) = 1 := by simp [fullState]
@[simp] theorem full_empty : fullState (∅ : Finset (Fin 5)) = 0 := by
  have h : (∅ : Finset (Fin 5)) ≠ univ := by
    intro h'
    have hc := congrArg Finset.card h'
    simp at hc
  simp [fullState, h]

def topDyad : FockSpace →ₗ[ℝ] FockSpace where
  toFun x := fun t => if t = univ then x ∅ else 0
  map_add' x y := by
    ext t
    by_cases h : t = univ <;> simp [h]
  map_smul' c x := by
    ext t
    by_cases h : t = univ <;> simp [h]

@[simp] theorem topDyad_vac : topDyad vac = fullState := by
  ext t
  simp [topDyad, vac, fullState]

theorem topDyad_sq : topDyad.comp topDyad = 0 := by
  ext x t
  by_cases ht : t = (univ : Finset (Fin 5))
  · subst t
    have h : (∅ : Finset (Fin 5)) ≠ univ := by
      intro h'
      have hc := congrArg Finset.card h'
      simp at hc
    simp [topDyad, h]
  · simp [topDyad, ht]

theorem topDyad_ne_zero : topDyad ≠ 0 := by
  intro h
  have hv := LinearMap.congr_fun h vac
  have hu := congr_fun hv (univ : Finset (Fin 5))
  simpa [topDyad, vac_empty] using hu

def totalNumber : FockSpace →ₗ[ℝ] FockSpace where
  toFun x := fun t => (t.card : ℝ) * x t
  map_add' x y := by ext t; simp; ring
  map_smul' c x := by ext t; simp; ring

def totalEuler : FockSpace →ₗ[ℝ] FockSpace :=
  totalNumber - (5 / 2 : ℝ) • LinearMap.id

def contactEuler : FockSpace →ₗ[ℝ] FockSpace where
  toFun x := fun t =>
    (((if 0 ∈ t then 1 else 0) : ℝ) +
      ((if 1 ∈ t then 1 else 0) : ℝ) - 1) * x t
  map_add' x y := by ext t; simp; ring
  map_smul' c x := by ext t; simp; ring

theorem commutator_total :
    totalNumber.comp topDyad - topDyad.comp totalNumber = (5 : ℝ) • topDyad := by
  ext x t
  by_cases ht : t = (univ : Finset (Fin 5))
  · subst t
    simp [totalNumber, topDyad, Finset.card_univ]
  · simp [totalNumber, topDyad, ht]

theorem commutator_totalEuler :
    totalEuler.comp topDyad - topDyad.comp totalEuler = (5 : ℝ) • topDyad := by
  ext x t
  by_cases ht : t = (univ : Finset (Fin 5))
  · subst t
    simp [totalEuler, totalNumber, topDyad, Finset.card_univ]
  · simp [totalEuler, totalNumber, topDyad, ht]

theorem commutator_contact :
    contactEuler.comp topDyad - topDyad.comp contactEuler = (2 : ℝ) • topDyad := by
  ext x t
  by_cases ht : t = (univ : Finset (Fin 5)) <;>
    simp [contactEuler, topDyad, ht] <;> ring

theorem total_grade_not_le_two (k : ℤ) (hk : k ≤ 2) :
    totalEuler.comp topDyad - topDyad.comp totalEuler ≠ (k : ℝ) • topDyad := by
  rw [commutator_totalEuler]
  intro h
  have hv := congr_fun (LinearMap.congr_fun (sub_eq_zero.mp (sub_eq_zero.mpr h)) vac) univ
  have h5 : (5 : ℝ) = k := by simpa [topDyad, vac_empty] using hv
  have : (5 : ℤ) = k := by exact_mod_cast h5
  omega

def postFunctional (x : FockSpace) : ℝ := x ∅ + x univ

theorem boundary_readout_top :
    postFunctional (topDyad vac) / postFunctional vac = 1 := by
  have h0 : (∅ : Finset (Fin 5)) ≠ univ := by
    intro h
    have hc : (∅ : Finset (Fin 5)).card = (univ : Finset (Fin 5)).card :=
      congrArg Finset.card h
    norm_num at hc
  simp [postFunctional, topDyad, vac, h0, h0.symm]

theorem boundary_readout_top_sq :
    postFunctional ((topDyad.comp topDyad) vac) / postFunctional vac = 0 := by
  rw [topDyad_sq]
  have h0 : (∅ : Finset (Fin 5)) ≠ univ := by
    intro h
    have hc := congrArg Finset.card h
    simp at hc
  simp [postFunctional, vac, h0, h0.symm]

/-! The boundary matrix coefficient is not multiplicative on the top dyad.

This is the operator-algebraic distinction between a normalized two-boundary
readout and a character: the dyad is nonzero and nilpotent, so its readout is
one while the readout of its square is zero.
 -/
theorem boundary_readout_not_character :
    postFunctional ((topDyad.comp topDyad) vac) / postFunctional vac ≠
      (postFunctional (topDyad vac) / postFunctional vac) ^ 2 := by
  rw [boundary_readout_top, boundary_readout_top_sq]
  norm_num

end
