/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAssociatorGram
import InfoGeometry.LinearAlgebra.RegularDyadCompression

/-!
# The energy-compressed full Zorn associator Gram form

The carrier, nonassociative products, positive coefficient pairing, and full
64-channel Gram form are the existing native Zorn constructions. The energy
projection is the complement of the existing normalized rank-one dyad, using
the positive coefficient pairing. At the zero energy vector it is the identity.

The compressed bilinear form vanishes exactly when the projected argument is
scalar. Equivalently, a vector has the form `a • h + b • 1` with
`b * (h.a + h.b) = 0`. This identifies the full radical, including zero energy
and trace-zero energy. No positive definiteness of the split norm is used.

This owner constructs a bilinear form and its exact radical. It does not yet
identify a representing Hilbert-space endomorphism, construct a Poisson
bracket or an evolution, or establish a heat/entropy exchange law.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Algebra.ZornProjectedAssociatorGram

open ZornPinorReconstruction ZornCARAdjoint ZornAssociatorGram
open InfoGeometry.LinearAlgebra.RegularDyadCompression

/-- Orthogonal removal of the energy line in the positive coefficient pairing,
using the existing normalized dyad. The total inverse also covers `h = 0`. -/
def energyProjection (h : Z) : Module.End ℝ Z :=
  1 - normalizedDyad h (coefficientPairing h)

@[simp] theorem energyProjection_apply (h x : Z) :
    energyProjection h x =
      x - (coefficientPairing h x / coefficientPairing h h) • h := by
  change x - normalizedDyad h (coefficientPairing h) x = _
  rw [normalizedDyad_apply]

@[simp] theorem energyProjection_zero : energyProjection (0 : Z) = 1 := by
  apply LinearMap.ext
  intro x
  change energyProjection 0 x = x
  rw [energyProjection_apply, smul_zero, sub_zero]

/-- The energy vector is annihilated, including when it is zero. -/
@[simp] theorem energyProjection_self (h : Z) : energyProjection h h = 0 := by
  by_cases hh : h = 0
  · subst h
    exact map_zero (energyProjection 0)
  · have hnorm : coefficientPairing h h ≠ 0 :=
      fun hz => hh ((coefficientPairing_zero_iff h).mp hz)
    rw [energyProjection_apply, div_self hnorm, one_smul, sub_self]

/-- Every projected vector is perpendicular to the energy in the positive form. -/
theorem energyProjection_orthogonal (h x : Z) :
    coefficientPairing h (energyProjection h x) = 0 := by
  by_cases hh : h = 0
  · subst h
    simp only [map_zero, LinearMap.zero_apply]
  · have hnorm : coefficientPairing h h ≠ 0 :=
      fun hz => hh ((coefficientPairing_zero_iff h).mp hz)
    rw [energyProjection_apply, map_sub, map_smul, smul_eq_mul,
      div_mul_cancel₀ _ hnorm, sub_self]

theorem energyProjection_fixed_of_orthogonal (h x : Z)
    (hx : coefficientPairing h x = 0) : energyProjection h x = x := by
  rw [energyProjection_apply, hx, zero_div, zero_smul, sub_zero]

theorem energyProjection_idempotent (h : Z) :
    energyProjection h * energyProjection h = energyProjection h := by
  apply LinearMap.ext
  intro x
  change energyProjection h (energyProjection h x) = energyProjection h x
  exact energyProjection_fixed_of_orthogonal h _ (energyProjection_orthogonal h x)

/-- The positive pairing with the actual Zorn unit is the scalar trace. -/
@[simp] theorem coefficientPairing_one (h : Z) :
    coefficientPairing h (ZornVectorMatrix.one : Z) = h.a + h.b := by
  simp [coefficientPairing, ZornVectorMatrix.one, ZornVec3.dot]

/-- A scalar projected vector has an energy-plus-scalar decomposition whose
scalar coefficient satisfies the exact positive-orthogonality condition. -/
theorem energyProjection_scalar_iff (h x : Z) :
    (∃ b : ℝ, energyProjection h x = b • (ZornVectorMatrix.one : Z)) ↔
      ∃ a b : ℝ, x = a • h + b • (ZornVectorMatrix.one : Z) ∧
        b * (h.a + h.b) = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨coefficientPairing h x / coefficientPairing h h, b, ?_, ?_⟩
    · calc
        x = (coefficientPairing h x / coefficientPairing h h) • h +
            energyProjection h x := by
          rw [energyProjection_apply]
          abel
        _ = (coefficientPairing h x / coefficientPairing h h) • h +
            b • (ZornVectorMatrix.one : Z) := by rw [hb]
    · have horth := energyProjection_orthogonal h x
      rw [hb, map_smul, smul_eq_mul, coefficientPairing_one] at horth
      exact horth
  · rintro ⟨a, b, rfl, hb⟩
    refine ⟨b, ?_⟩
    have horth : coefficientPairing h (b • (ZornVectorMatrix.one : Z)) = 0 := by
      rw [map_smul, smul_eq_mul, coefficientPairing_one]
      exact hb
    calc
      energyProjection h (a • h + b • (ZornVectorMatrix.one : Z)) =
          a • energyProjection h h +
            energyProjection h (b • (ZornVectorMatrix.one : Z)) := by
        rw [map_add, map_smul]
      _ = b • (ZornVectorMatrix.one : Z) := by
        rw [energyProjection_self, smul_zero, zero_add,
          energyProjection_fixed_of_orthogonal h _ horth]

/-- Compress the existing full associator Gram form in both ordered arguments. -/
def projectedGram (h : Z) : LinearMap.BilinForm ℝ Z :=
  associatorGram.compl₁₂ (energyProjection h) (energyProjection h)

@[simp] theorem projectedGram_apply (h x y : Z) :
    projectedGram h x y =
      associatorGram (energyProjection h x) (energyProjection h y) := rfl

theorem projectedGram_symm (h x y : Z) :
    projectedGram h x y = projectedGram h y x :=
  associatorGram_symm _ _

theorem projectedGram_nonneg (h x : Z) : 0 ≤ projectedGram h x x :=
  associatorGram_nonneg _

@[simp] theorem projectedGram_energy_left (h x : Z) : projectedGram h h x = 0 := by
  simp only [projectedGram_apply, energyProjection_self, map_zero, LinearMap.zero_apply]

@[simp] theorem projectedGram_energy_right (h x : Z) : projectedGram h x h = 0 := by
  simp only [projectedGram_apply, energyProjection_self, map_zero]

/-- The exact quadratic zero set after energy compression. No nonzero-energy
or nonzero-trace hypothesis is needed. -/
theorem projectedGram_zero_iff (h x : Z) :
    projectedGram h x x = 0 ↔
      ∃ a b : ℝ, x = a • h + b • (ZornVectorMatrix.one : Z) ∧
        b * (h.a + h.b) = 0 :=
  (associatorGram_zero_iff_scalar (energyProjection h x)).trans
    (energyProjection_scalar_iff h x)

/-- The bilinear left radical has the same exact energy-plus-scalar criterion. -/
theorem projectedGram_left_kernel_iff (h x : Z) :
    (∀ y : Z, projectedGram h x y = 0) ↔
      ∃ a b : ℝ, x = a • h + b • (ZornVectorMatrix.one : Z) ∧
        b * (h.a + h.b) = 0 := by
  constructor
  · intro hx
    exact (projectedGram_zero_iff h x).mp (hx x)
  · intro hx y
    exact ((associatorGram_left_kernel_iff_scalar (energyProjection h x)).mpr
      ((energyProjection_scalar_iff h x).mpr hx)) (energyProjection h y)

/-- Nonzero scalar trace leaves exactly the energy line as the quadratic zero set. -/
theorem projectedGram_zero_iff_of_trace_ne_zero (h x : Z)
    (htrace : h.a + h.b ≠ 0) :
    projectedGram h x x = 0 ↔ ∃ a : ℝ, x = a • h := by
  rw [projectedGram_zero_iff]
  constructor
  · rintro ⟨a, b, hx, hb⟩
    have hbzero : b = 0 := (mul_eq_zero.mp hb).resolve_right htrace
    refine ⟨a, ?_⟩
    simpa only [hbzero, zero_smul, add_zero] using hx
  · rintro ⟨a, hx⟩
    refine ⟨a, 0, ?_, zero_mul _⟩
    simpa only [zero_smul, add_zero] using hx

/-- At trace-zero energy, the full scalar line remains in the radical as well. -/
theorem projectedGram_zero_iff_of_trace_eq_zero (h x : Z)
    (htrace : h.a + h.b = 0) :
    projectedGram h x x = 0 ↔
      ∃ a b : ℝ, x = a • h + b • (ZornVectorMatrix.one : Z) := by
  simpa only [htrace, mul_zero, and_true] using projectedGram_zero_iff h x

theorem projectedGram_left_kernel_iff_of_trace_ne_zero (h x : Z)
    (htrace : h.a + h.b ≠ 0) :
    (∀ y : Z, projectedGram h x y = 0) ↔ ∃ a : ℝ, x = a • h :=
  (projectedGram_left_kernel_iff h x).trans
    ((projectedGram_zero_iff h x).symm.trans
      (projectedGram_zero_iff_of_trace_ne_zero h x htrace))

theorem projectedGram_left_kernel_iff_of_trace_eq_zero (h x : Z)
    (htrace : h.a + h.b = 0) :
    (∀ y : Z, projectedGram h x y = 0) ↔
      ∃ a b : ℝ, x = a • h + b • (ZornVectorMatrix.one : Z) :=
  (projectedGram_left_kernel_iff h x).trans
    ((projectedGram_zero_iff h x).symm.trans
      (projectedGram_zero_iff_of_trace_eq_zero h x htrace))

end InfoGeometry.Algebra.ZornProjectedAssociatorGram
