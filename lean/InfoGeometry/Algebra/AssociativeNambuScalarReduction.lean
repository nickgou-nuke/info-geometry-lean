/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeZornNambuAssociator
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar sectors of the associative Nambu polynomial

This file reuses the ordered `nambu` and `comm` operations of
`NoncommutativeZornNambu`. It first proves associative-ring and scalar-sector
identities, then a signed quartic obstruction with an operator `J` over the
real scalars. The generators themselves need not commute.

The centralizer result assumes the scalar-commutant property explicitly:
irreducibility over the real numbers does not supply that property. The
quartic reduction assumes a nonzero real scalar sector, cyclic commutator
relations, and a specified Casimir value. It is not a classification of all
matrix representations. No Filippov identity for an arbitrary associative
ring is asserted.

Source motivation: C. Sochichiu, *On Nambu-Lie 3-algebra representations*,
arXiv:0806.3520v2, equations (2.13)--(2.21). The formal coefficient carrier
for the quartic result is real; `J` is an operator with square `-1`.
-/

namespace InfoGeometry.Algebra.AssociativeNambuScalarReduction

open NoncommutativeZornNambu

section Ring

variable {B : Type*} [Ring B]

/-- First-slot expansion retaining all noncommuting factors. -/
theorem nambu_noncommutative_first_slot (M A C : B) :
    nambu ⟨M, A, C⟩ =
      M * comm A C + comm A C * M - A * M * C + C * M * A := by
  rw [nambu_eq_alternating_cubic]
  dsimp [NoncommutativeZornNambu.comm]
  noncomm_ring

end Ring

section Scalars

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

/-- A scalar in the first slot scales the ordinary commutator. -/
theorem nambu_scalar_first_slot (t : K) (A C : B) :
    nambu ⟨t • (1 : B), A, C⟩ = t • comm A C := by
  rw [nambu_eq_cyclic_commutator]
  simp [NoncommutativeZornNambu.comm]

/-- A scalar in the third slot scales the ordinary commutator. -/
theorem nambu_scalar_third_slot (t : K) (A C : B) :
    nambu ⟨A, C, t • (1 : B)⟩ = t • comm A C := by
  rw [nambu_eq_cyclic_commutator]
  simp [NoncommutativeZornNambu.comm]

/-- A nonzero scalar sector reduces Nambu centrality to ordinary commutation. -/
theorem nambu_scalar_first_slot_eq_zero_iff
    (t : K) (ht : t ≠ 0) (A X : B) :
    nambu ⟨t • (1 : B), A, X⟩ = 0 ↔ comm A X = 0 := by
  rw [nambu_scalar_first_slot, smul_eq_zero]
  simp [ht]

/-- A noncommuting pair has no nonzero scalar Nambu-central element. -/
theorem nambu_scalar_third_slot_eq_zero_iff
    (t : K) (A C : B) (hAC : comm A C ≠ 0) :
    nambu ⟨A, C, t • (1 : B)⟩ = 0 ↔ t = 0 := by
  rw [nambu_scalar_third_slot, smul_eq_zero]
  simp [hAC]

/-- The scalar-commutant hypothesis and one noncommuting pair suffice to
annihilate a Nambu-central element. No irreducibility implication is assumed. -/
theorem nambu_center_eq_zero_of_scalar_commutant
    {ι : Type*} (T : ι → B) (t : K) (ht : t ≠ 0)
    (hScalar : ∀ X : B, (∀ i, comm (T i) X = 0) →
      ∃ a : K, X = a • (1 : B))
    (i j : ι) (hNoncomm : comm (T i) (T j) ≠ 0)
    (X : B)
    (hSector : ∀ k, nambu ⟨t • (1 : B), T k, X⟩ = 0)
    (hPairs : ∀ k l, nambu ⟨T k, T l, X⟩ = 0) :
    X = 0 := by
  have hComm : ∀ k, comm (T k) X = 0 := fun k =>
    (nambu_scalar_first_slot_eq_zero_iff t ht (T k) X).mp (hSector k)
  obtain ⟨a, ha⟩ := hScalar X hComm
  have hPair : nambu ⟨T i, T j, a • (1 : B)⟩ = 0 := by
    rw [← ha]
    exact hPairs i j
  have ha0 : a = 0 :=
    (nambu_scalar_third_slot_eq_zero_iff a (T i) (T j) hNoncomm).mp hPair
  simpa [ha0] using ha

/-- Three cyclic commutators with a common commuting operator give a
Casimir expression for the ordered Nambu polynomial. -/
theorem nambu_eq_phase_casimir
    (J T₁ T₂ T₃ : B) (a : K)
    (hJ₁ : J * T₁ = T₁ * J)
    (hJ₂ : J * T₂ = T₂ * J)
    (hJ₃ : J * T₃ = T₃ * J)
    (h₂₃ : comm T₂ T₃ = a • (J * T₁))
    (h₃₁ : comm T₃ T₁ = a • (J * T₂))
    (h₁₂ : comm T₁ T₂ = a • (J * T₃)) :
    nambu ⟨T₁, T₂, T₃⟩ =
      a • (J * (T₁ * T₁ + T₂ * T₂ + T₃ * T₃)) := by
  rw [nambu_eq_cyclic_commutator]
  dsimp only
  rw [h₂₃, h₃₁, h₁₂]
  simp only [Algebra.mul_smul_comm, ← smul_add]
  congr 1
  simp only [← mul_assoc, ← hJ₁, ← hJ₂, ← hJ₃]
  noncomm_ring

/-- A scalar Casimir turns the common-phase formula into a scalar multiple
of that operator. The Casimir equality is an explicit premise. -/
theorem nambu_eq_scaled_phase
    (J T₁ T₂ T₃ : B) (a q : K)
    (hJ₁ : J * T₁ = T₁ * J)
    (hJ₂ : J * T₂ = T₂ * J)
    (hJ₃ : J * T₃ = T₃ * J)
    (h₂₃ : comm T₂ T₃ = a • (J * T₁))
    (h₃₁ : comm T₃ T₁ = a • (J * T₂))
    (h₁₂ : comm T₁ T₂ = a • (J * T₃))
    (hCas : T₁ * T₁ + T₂ * T₂ + T₃ * T₃ = q • (1 : B)) :
    nambu ⟨T₁, T₂, T₃⟩ = (a * q) • J := by
  rw [nambu_eq_phase_casimir J T₁ T₂ T₃ a hJ₁ hJ₂ hJ₃ h₂₃ h₃₁ h₁₂,
    hCas, Algebra.mul_smul_comm, mul_one, smul_smul]

end Scalars

section RealQuartic

variable {B : Type*} [Ring B] [Algebra ℝ B] [Nontrivial B]

/-- The sign in the remaining Nambu equation determines the quartic scalar
constraint. All operator products retain their original order. -/
theorem real_phase_scalar_sector_quartic
    (J T₁ T₂ T₃ : B) (t c k : ℝ) (ht : t ≠ 0)
    (hJ_sq : J * J = -(1 : B))
    (hJ₁ : J * T₁ = T₁ * J)
    (hJ₂ : J * T₂ = T₂ * J)
    (hJ₃ : J * T₃ = T₃ * J)
    (h₂₃ : comm T₂ T₃ = (-t⁻¹) • (J * T₁))
    (h₃₁ : comm T₃ T₁ = (-t⁻¹) • (J * T₂))
    (h₁₂ : comm T₁ T₂ = (-t⁻¹) • (J * T₃))
    (hCas : T₁ * T₁ + T₂ * T₂ + T₃ * T₃ =
      (t⁻¹ ^ 2 * c) • (1 : B))
    (hN : nambu ⟨T₁, T₂, T₃⟩ = (k * t) • J) :
    k * t ^ 4 = -c := by
  have hJ_ne : J ≠ 0 := by
    intro hZero
    simp [hZero] at hJ_sq
  have hReduction : nambu ⟨T₁, T₂, T₃⟩ = (-(t⁻¹ ^ 3 * c)) • J := by
    rw [nambu_eq_scaled_phase J T₁ T₂ T₃ (-t⁻¹) (t⁻¹ ^ 2 * c)
      hJ₁ hJ₂ hJ₃ h₂₃ h₃₁ h₁₂ hCas]
    congr 1
    ring
  have hScalar : -(t⁻¹ ^ 3 * c) = k * t := by
    have hDifference : (-(t⁻¹ ^ 3 * c) - k * t) • J = 0 := by
      rw [sub_smul, ← hReduction, hN, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hDifference).resolve_right hJ_ne)
  calc
    k * t ^ 4 = (k * t) * t ^ 3 := by ring
    _ = (-(t⁻¹ ^ 3 * c)) * t ^ 3 := by rw [hScalar]
    _ = -c := by field_simp [ht]

/-- The Euclidean sign gives the negative quartic constraint. -/
theorem real_phase_scalar_sector_euclidean_quartic
    (J T₁ T₂ T₃ : B) (t c : ℝ) (ht : t ≠ 0)
    (hJ_sq : J * J = -(1 : B))
    (hJ₁ : J * T₁ = T₁ * J)
    (hJ₂ : J * T₂ = T₂ * J)
    (hJ₃ : J * T₃ = T₃ * J)
    (h₂₃ : comm T₂ T₃ = (-t⁻¹) • (J * T₁))
    (h₃₁ : comm T₃ T₁ = (-t⁻¹) • (J * T₂))
    (h₁₂ : comm T₁ T₂ = (-t⁻¹) • (J * T₃))
    (hCas : T₁ * T₁ + T₂ * T₂ + T₃ * T₃ =
      (t⁻¹ ^ 2 * c) • (1 : B))
    (hN : nambu ⟨T₁, T₂, T₃⟩ = t • J) :
    t ^ 4 = -c := by
  have hSigned : nambu ⟨T₁, T₂, T₃⟩ = (1 * t) • J := by simpa using hN
  simpa only [one_mul] using
    real_phase_scalar_sector_quartic J T₁ T₂ T₃ t c 1 ht hJ_sq
      hJ₁ hJ₂ hJ₃ h₂₃ h₃₁ h₁₂ hCas hSigned

/-- Reversing the remaining Nambu sign gives the positive quartic constraint. -/
theorem real_phase_scalar_sector_sign_flip_quartic
    (J T₁ T₂ T₃ : B) (t c : ℝ) (ht : t ≠ 0)
    (hJ_sq : J * J = -(1 : B))
    (hJ₁ : J * T₁ = T₁ * J)
    (hJ₂ : J * T₂ = T₂ * J)
    (hJ₃ : J * T₃ = T₃ * J)
    (h₂₃ : comm T₂ T₃ = (-t⁻¹) • (J * T₁))
    (h₃₁ : comm T₃ T₁ = (-t⁻¹) • (J * T₂))
    (h₁₂ : comm T₁ T₂ = (-t⁻¹) • (J * T₃))
    (hCas : T₁ * T₁ + T₂ * T₂ + T₃ * T₃ =
      (t⁻¹ ^ 2 * c) • (1 : B))
    (hN : nambu ⟨T₁, T₂, T₃⟩ = (-t) • J) :
    t ^ 4 = c := by
  have hSigned : nambu ⟨T₁, T₂, T₃⟩ = ((-1) * t) • J := by simpa using hN
  have h := real_phase_scalar_sector_quartic J T₁ T₂ T₃ t c (-1) ht hJ_sq
    hJ₁ hJ₂ hJ₃ h₂₃ h₃₁ h₁₂ hCas hSigned
  linarith

/-- A fourth power of a real scalar cannot be strictly negative. -/
theorem real_fourth_power_ne_neg (t c : ℝ) (hc : 0 < c) :
    t ^ 4 ≠ -c := by
  nlinarith [sq_nonneg (t ^ 2)]

/-- Positive Casimir and the Euclidean remaining sign exclude the specified
nonzero real scalar sector. This is a no-go theorem for these hypotheses. -/
theorem no_positive_casimir_real_scalar_sector
    (J T₁ T₂ T₃ : B) (t c : ℝ) (ht : t ≠ 0) (hc : 0 < c)
    (hJ_sq : J * J = -(1 : B))
    (hJ₁ : J * T₁ = T₁ * J)
    (hJ₂ : J * T₂ = T₂ * J)
    (hJ₃ : J * T₃ = T₃ * J)
    (h₂₃ : comm T₂ T₃ = (-t⁻¹) • (J * T₁))
    (h₃₁ : comm T₃ T₁ = (-t⁻¹) • (J * T₂))
    (h₁₂ : comm T₁ T₂ = (-t⁻¹) • (J * T₃))
    (hCas : T₁ * T₁ + T₂ * T₂ + T₃ * T₃ =
      (t⁻¹ ^ 2 * c) • (1 : B)) :
    nambu ⟨T₁, T₂, T₃⟩ ≠ t • J := by
  intro hN
  exact real_fourth_power_ne_neg t c hc
    (real_phase_scalar_sector_euclidean_quartic J T₁ T₂ T₃ t c ht hJ_sq
      hJ₁ hJ₂ hJ₃ h₂₃ h₃₁ h₁₂ hCas hN)

end RealQuartic

end InfoGeometry.Algebra.AssociativeNambuScalarReduction
