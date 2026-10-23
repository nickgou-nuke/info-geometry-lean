/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.MDPASJMGlobalQuantization

/-!
# Exact potentials and circulation on the oriented triangle

Contract: on the existing `TriangleOneForm` carrier, circulation is the
complete obstruction to a vertex potential, not merely a necessary condition.
Fixing the potential at vertex zero removes precisely the constant ambiguity.
Subtracting the mean circulation produces an exact cochain, uniquely.
These are finite cochain statements; no smooth or continuum claim is made.
-/

namespace InfoGeometry.Physics.MDPASJMGlobalQuantization

/-- Integrate along the spanning path `0 → 1 → 2`. -/
def trianglePotential (A : TriangleOneForm) : Vec3 :=
  ![0, A.e01, A.e01 + A.e12]

/-- Vanishing circulation suffices: the spanning-path potential also closes
the final edge. -/
theorem isExact_iff_cycleIntegral_eq_zero (A : TriangleOneForm) :
    IsExact A ↔ cycleIntegral A = 0 := by
  constructor
  · exact cycleIntegral_eq_zero_of_exact A
  · intro hA
    refine ⟨trianglePotential A, ?_, ?_, ?_⟩
    · simp [trianglePotential]
    · simp [trianglePotential]
    · simp only [cycleIntegral] at hA
      simp [trianglePotential]
      linarith

/-- The potential is unique after fixing its additive constant at vertex zero. -/
theorem existsUnique_normalized_trianglePotential (A : TriangleOneForm)
    (hA : cycleIntegral A = 0) :
    ∃! φ : Vec3, φ 0 = 0 ∧ A.e01 = φ 1 - φ 0 ∧
      A.e12 = φ 2 - φ 1 ∧ A.e20 = φ 0 - φ 2 := by
  have hclose : A.e20 = -(A.e01 + A.e12) := by
    unfold cycleIntegral at hA
    linarith
  refine ⟨trianglePotential A, ?_, ?_⟩
  · simp [trianglePotential, hclose]
  · intro φ hφ
    have h1 : φ 1 = A.e01 := by linarith [hφ.1, hφ.2.1]
    have h2 : φ 2 = A.e01 + A.e12 := by linarith [hφ.2.2.1]
    funext i
    fin_cases i <;> simp [trianglePotential, hφ.1, h1, h2]

/-- Remove a constant oriented circulation from the three edges. -/
def subtractCirculation (A : TriangleOneForm) (c : ℚ) : TriangleOneForm :=
  ⟨A.e01 - c, A.e12 - c, A.e20 - c⟩

theorem cycleIntegral_subtractCirculation (A : TriangleOneForm) (c : ℚ) :
    cycleIntegral (subtractCirculation A c) = cycleIntegral A - 3 * c := by
  unfold cycleIntegral subtractCirculation
  ring

/-- Every triangle cochain splits uniquely into an exact cochain and a
constant circulation. The constant is its mean circulation. -/
theorem existsUnique_exact_subtractCirculation (A : TriangleOneForm) :
    ∃! c : ℚ, IsExact (subtractCirculation A c) := by
  refine ⟨cycleIntegral A / 3, ?_, ?_⟩
  · change IsExact (subtractCirculation A (cycleIntegral A / 3))
    rw [isExact_iff_cycleIntegral_eq_zero, cycleIntegral_subtractCirculation]
    ring
  · intro c hc
    rw [isExact_iff_cycleIntegral_eq_zero, cycleIntegral_subtractCirculation] at hc
    linarith

end InfoGeometry.Physics.MDPASJMGlobalQuantization
