/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.NCG.NonCommutativeFredholmIndex

/-! # Coupling arbitrary opposite Peirce corners

All statements concern the full matrix algebra. The two input matrices are
independent and need not commute. No division by two or star structure is used.
-/

namespace InfoGeometry.NCG.OppositePeirceCoupling

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open NonCommutativeFredholmIndex

variable {n R : Type*} [Fintype n] [DecidableEq n] [Ring R]
variable {P : Matrix n n R} (hP : IsIdempotentElem P) (A B : Matrix n n R)

local notation "X" => component10 P A
local notation "Y" => component01 P B

include hP

/-- Each same-direction product vanishes; the mixed products remain. -/
theorem sum_sq : (X + Y) * (X + Y) = anticommutator X Y := by
  have hx := peirce10_mul_peirce10_eq_zero P hP.eq (component10_mem P A)
    (component10_mem P A)
  have hy := peirce01_mul_peirce01_eq_zero P hP.eq (component01_mem P B)
    (component01_mem P B)
  dsimp [anticommutator]
  noncomm_ring [hx, hy]

theorem sum_mem_odd : X + Y ∈ LinearMap.range (odd P) := by
  rw [mem_odd_iff hP]
  simp only [component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

theorem conjugate_sum : reflection P * (X + Y) * reflection P = -(X + Y) := by
  have h := odd_anticommutes_reflection hP (sum_mem_odd hP A B)
  rw [eq_neg_of_add_eq_zero_left h, neg_mul, mul_assoc, reflection_sq hP, mul_one]

/-- Products of the independent corners have even parity. -/
theorem anticommutator_mem_even : anticommutator X Y ∈ LinearMap.range (even P) := by
  rw [← sum_sq hP A B]
  exact odd_mul_odd hP (sum_mem_odd hP A B) (sum_mem_odd hP A B)

theorem commutator_mem_even : commutator X Y ∈ LinearMap.range (even P) := by
  rw [mem_even_iff hP]
  simp only [NonCommutativeFredholmIndex.commutator,
    component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

/-- The reflection exchanges the symmetric and antisymmetric products. -/
theorem commutator_eq_reflection_mul :
    commutator X Y = reflection P * anticommutator X Y := by
  simp only [NonCommutativeFredholmIndex.commutator, anticommutator, reflection,
    component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

theorem anticommutator_eq_reflection_mul :
    anticommutator X Y = reflection P * commutator X Y := by
  rw [commutator_eq_reflection_mul hP A B, ← mul_assoc, reflection_sq hP, one_mul]

theorem anticommutator_eq_zero_iff_commutator :
    anticommutator X Y = 0 ↔ commutator X Y = 0 := by
  constructor
  · intro h
    rw [commutator_eq_reflection_mul hP A B, h, mul_zero]
  · intro h
    rw [anticommutator_eq_reflection_mul hP A B, h, mul_zero]

theorem component11_anticommutator : component11 P (anticommutator X Y) = X * Y := by
  simp only [component11, anticommutator, component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

theorem component00_anticommutator : component00 P (anticommutator X Y) = Y * X := by
  simp only [component00, anticommutator, component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

theorem component11_commutator : component11 P (commutator X Y) = X * Y := by
  simp only [component11, NonCommutativeFredholmIndex.commutator,
    component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

theorem component00_commutator : component00 P (commutator X Y) = -(Y * X) := by
  simp only [component00, NonCommutativeFredholmIndex.commutator,
    component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

/-- Complementary supports prohibit cancellation, in every characteristic. -/
theorem anticommutator_eq_zero_iff_products :
    anticommutator X Y = 0 ↔ X * Y = 0 ∧ Y * X = 0 := by
  constructor
  · intro h
    constructor
    · rw [← component11_anticommutator hP A B, h]
      simp [component11]
    · rw [← component00_anticommutator hP A B, h]
      simp [component00]
  · rintro ⟨hxy, hyx⟩
    simp [anticommutator, hxy, hyx]

theorem conjugate_anticommutator :
    reflection P * anticommutator X Y * reflection P = anticommutator X Y := by
  rw [(even_commutes_reflection hP (anticommutator_mem_even hP A B)).eq,
    mul_assoc, reflection_sq hP, mul_one]

theorem conjugate_commutator :
    reflection P * commutator X Y * reflection P = commutator X Y := by
  rw [(even_commutes_reflection hP (commutator_mem_even hP A B)).eq,
    mul_assoc, reflection_sq hP, mul_one]

end InfoGeometry.NCG.OppositePeirceCoupling
