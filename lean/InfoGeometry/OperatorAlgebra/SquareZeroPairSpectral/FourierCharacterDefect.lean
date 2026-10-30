/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.KleinHadamard

/-!
# Fourier sandwich comparison and its exact defects

For a square-zero pair in an associative algebra, compare the four
`V²`-weighted sandwiches against the homogenized Lie projectors. The sum and
difference channels agree exactly on the centralizer of `V²`; the spin and
mass channels retain their own explicit second-order defects. This corrects
the transcript's overstrong claim that the two projector families agree on
the entire algebra.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

open InfoGeometry.OperatorAlgebra.LieJordan

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {u v : A}

def fourierSandwichId (x : A) : A :=
  (u * v + v * u) * (u * v + v * u) * x

def fourierSandwichSum (x : A) : A :=
  (u * v + v * u) * ((u + v) * x * (u + v))

def fourierSandwichDifference (x : A) : A :=
  -((u * v + v * u) * ((u - v) * x * (u - v)))

def fourierSandwichSpin (x : A) : A :=
  (u * v - v * u) * x * (u * v - v * u)

def fourierProjMass (x : A) : A :=
  (2 : ℕ) • (fourierSandwichId (u := u) (v := v) x +
    fourierSandwichSum (u := u) (v := v) x + fourierSandwichDifference (u := u) (v := v) x + fourierSandwichSpin (u := u) (v := v) x)

def fourierProjSum (x : A) : A :=
  (2 : ℕ) • (fourierSandwichId (u := u) (v := v) x +
    fourierSandwichSum (u := u) (v := v) x - fourierSandwichDifference (u := u) (v := v) x - fourierSandwichSpin (u := u) (v := v) x)

def fourierProjDifference (x : A) : A :=
  (2 : ℕ) • (fourierSandwichId (u := u) (v := v) x -
    fourierSandwichSum (u := u) (v := v) x + fourierSandwichDifference (u := u) (v := v) x - fourierSandwichSpin (u := u) (v := v) x)

def fourierProjSpin (x : A) : A :=
  (2 : ℕ) • (fourierSandwichId (u := u) (v := v) x -
    fourierSandwichSum (u := u) (v := v) x - fourierSandwichDifference (u := u) (v := v) x + fourierSandwichSpin (u := u) (v := v) x)

theorem projSum_fourierProjSum_defect (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projSum R u v x - fourierProjSum (u := u) (v := v) x =
      x * ((u * v + v * u) * (u * v + v * u)) -
        ((u * v + v * u) * (u * v + v * u)) * x := by
  rw [projSum_apply, phiLaplacian_apply, jLaplacian_apply, spinLaplacian_apply]
  simp only [fourierProjSum, fourierSandwichId, fourierSandwichSum,
    fourierSandwichDifference, fourierSandwichSpin, lieOp_apply, two_nsmul,
    mul_neg]
  have hUU : ∀ z : A, u * (u * z) = 0 := fun z => mul_mul_eq_zero_of_sq hu z
  have hVV : ∀ z : A, v * (v * z) = 0 := fun z => mul_mul_eq_zero_of_sq hv z
  noncomm_ring [hu, hv, hUU x, hUU v, hUU (u * x), hUU (v * x), hVV x, hVV u, hVV (u * x), hVV (v * x)]

theorem projDifference_fourierProjDifference_defect
    (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projDifference R u v x - fourierProjDifference (u := u) (v := v) x =
      x * ((u * v + v * u) * (u * v + v * u)) -
        ((u * v + v * u) * (u * v + v * u)) * x := by
  rw [projDifference_apply, phiLaplacian_apply, jLaplacian_apply, spinLaplacian_apply]
  simp only [fourierProjDifference, fourierSandwichId, fourierSandwichSum,
    fourierSandwichDifference, fourierSandwichSpin, lieOp_apply, two_nsmul,
    mul_neg]
  have hUU : ∀ z : A, u * (u * z) = 0 := fun z => mul_mul_eq_zero_of_sq hu z
  have hVV : ∀ z : A, v * (v * z) = 0 := fun z => mul_mul_eq_zero_of_sq hv z
  noncomm_ring [hu, hv, hUU x, hUU v, hUU (u * x), hUU (v * x), hVV x, hVV u, hVV (u * x), hVV (v * x)]

/-- The sum-channel Fourier identity holds exactly on the centralizer of `V²`. -/
theorem projSum_fourierProjSum_eq_iff_commute_mass_sq
    (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projSum R u v x = fourierProjSum (u := u) (v := v) x ↔
      Commute x ((u * v + v * u) * (u * v + v * u)) := by
  constructor
  · intro h
    have hzero : projSum R u v x - fourierProjSum (u := u) (v := v) x = 0 :=
      sub_eq_zero.mpr h
    rw [projSum_fourierProjSum_defect hu hv x] at hzero
    exact sub_eq_zero.mp hzero
  · intro h
    apply sub_eq_zero.mp
    rw [projSum_fourierProjSum_defect hu hv x]
    exact sub_eq_zero.mpr h.eq

/-- The difference-channel Fourier identity has the same exact centralizer
condition as the sum channel. -/
theorem projDifference_fourierProjDifference_eq_iff_commute_mass_sq
    (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projDifference R u v x = fourierProjDifference (u := u) (v := v) x ↔
      Commute x ((u * v + v * u) * (u * v + v * u)) := by
  constructor
  · intro h
    have hzero : projDifference R u v x - fourierProjDifference (u := u) (v := v) x = 0 :=
      sub_eq_zero.mpr h
    rw [projDifference_fourierProjDifference_defect hu hv x] at hzero
    exact sub_eq_zero.mp hzero
  · intro h
    apply sub_eq_zero.mp
    rw [projDifference_fourierProjDifference_defect hu hv x]
    exact sub_eq_zero.mpr h.eq

theorem projSpin_fourierProjSpin_defect (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projSpin R u v x - fourierProjSpin (u := u) (v := v) x =
      (2 : ℕ) • ((u * v + v * u) * x * (u * v + v * u)) -
        ((u * v + v * u) * (u * v + v * u)) * x -
          x * ((u * v + v * u) * (u * v + v * u)) := by
  rw [projSpin_apply, phiLaplacian_apply, jLaplacian_apply, spinLaplacian_apply]
  simp only [fourierProjSpin, fourierSandwichId, fourierSandwichSum,
    fourierSandwichDifference, fourierSandwichSpin, lieOp_apply, two_nsmul,
    mul_neg]
  have hUU : ∀ z : A, u * (u * z) = 0 := fun z => mul_mul_eq_zero_of_sq hu z
  have hVV : ∀ z : A, v * (v * z) = 0 := fun z => mul_mul_eq_zero_of_sq hv z
  noncomm_ring [hu, hv, hUU x, hUU v, hUU (u * x), hUU (v * x), hVV x, hVV u, hVV (u * x), hVV (v * x)]

theorem projMass_fourierProjMass_defect (hu : u * u = 0) (hv : v * v = 0) (x : A) :
    projMass R u v x - fourierProjMass (u := u) (v := v) x =
      (3 : ℕ) • (((u * v + v * u) * (u * v + v * u)) * x) -
        (2 : ℕ) • ((u * v + v * u) * x * (u * v + v * u)) -
          x * ((u * v + v * u) * (u * v + v * u)) := by
  rw [projMass_apply, phiLaplacian_apply, jLaplacian_apply, spinLaplacian_apply]
  simp only [fourierProjMass, fourierSandwichId, fourierSandwichSum,
    fourierSandwichDifference, fourierSandwichSpin, lieOp_apply, two_nsmul,
    mul_neg]
  have hUU : ∀ z : A, u * (u * z) = 0 := fun z => mul_mul_eq_zero_of_sq hu z
  have hVV : ∀ z : A, v * (v * z) = 0 := fun z => mul_mul_eq_zero_of_sq hv z
  noncomm_ring [hu, hv, hUU x, hUU v, hUU (u * x), hUU (v * x), hVV x, hVV u, hVV (u * x), hVV (v * x)]

/-- All four Lie/Fourier channels agree on the centralizer of the mass.
This is a sufficient centralizer statement; the exact defects above retain
the weaker channel-specific conditions. -/
theorem all_fourier_channels_agree_of_commute_mass
    (hu : u * u = 0) (hv : v * v = 0) (x : A)
    (hV : Commute (u * v + v * u) x) :
    projMass R u v x = fourierProjMass (u := u) (v := v) x ∧
    projSum R u v x = fourierProjSum (u := u) (v := v) x ∧
    projDifference R u v x = fourierProjDifference (u := u) (v := v) x ∧
    projSpin R u v x = fourierProjSpin (u := u) (v := v) x := by
  have hV2 :
      (u * v + v * u) * (u * v + v * u) * x =
        x * (u * v + v * u) * (u * v + v * u) := by
    calc
      _ = (u * v + v * u) * ((u * v + v * u) * x) := by rw [mul_assoc]
      _ = (u * v + v * u) * (x * (u * v + v * u)) := by rw [hV.eq]
      _ = ((u * v + v * u) * x) * (u * v + v * u) := by rw [← mul_assoc]
      _ = (x * (u * v + v * u)) * (u * v + v * u) := by rw [hV.eq]
      _ = x * (u * v + v * u) * (u * v + v * u) := by rw [mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sub_eq_zero.mp
    rw [projMass_fourierProjMass_defect hu hv x, hV2, hV.eq]
    simp only [mul_assoc]
    abel
  · apply sub_eq_zero.mp
    rw [projSum_fourierProjSum_defect hu hv x, hV2]
    simp [mul_assoc]
  · apply sub_eq_zero.mp
    rw [projDifference_fourierProjDifference_defect hu hv x, hV2]
    simp [mul_assoc]
  · apply sub_eq_zero.mp
    rw [projSpin_fourierProjSpin_defect hu hv x, hV2, hV.eq]
    simp only [mul_assoc]
    abel

/-- The four Lie/Fourier channels agree on each of the four elements generated
by a square-zero pair: its mass, sum, difference, and commutator spin. -/
theorem all_fourier_channels_agree_on_tetraktys
    (hu : u * u = 0) (hv : v * v = 0) (x : A)
    (hx : x = u * v + v * u ∨ x = u + v ∨ x = u - v ∨
      x = u * v - v * u) :
    projMass R u v x = fourierProjMass (u := u) (v := v) x ∧
    projSum R u v x = fourierProjSum (u := u) (v := v) x ∧
    projDifference R u v x = fourierProjDifference (u := u) (v := v) x ∧
    projSpin R u v x = fourierProjSpin (u := u) (v := v) x := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact all_fourier_channels_agree_of_commute_mass hu hv _ (Commute.refl _)
  · exact all_fourier_channels_agree_of_commute_mass hu hv _ (mass_commute_sum hu hv)
  · exact all_fourier_channels_agree_of_commute_mass hu hv _ (mass_commute_difference hu hv)
  · exact all_fourier_channels_agree_of_commute_mass hu hv _ (mass_commute_spin hu hv)

end InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral
