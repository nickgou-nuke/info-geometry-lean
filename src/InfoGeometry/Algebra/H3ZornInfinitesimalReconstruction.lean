/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornCubicReconstruction
import InfoGeometry.Algebra.TrilinearStabilizer

/-!
# Infinitesimal reconstruction of the split Albert product

An endomorphism which annihilates the distinguished unit and infinitesimally
preserves the full polarized cubic norm is a derivation of the actual split
Albert Jordan product.  The proof reconstructs, in order, infinitesimal trace
preservation, skew-adjointness for the trace pairing, the cross-product
Leibniz rule, and the normalized Jordan-product Leibniz rule.

The resulting statement is a genuine inclusion of native Lie subalgebras in
the noncommutative algebra `Module.End ℝ (H3Zorn ℝ)`.  The cubic stabilizer and
the unit annihilator are intersected using the existing lattice operation.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn TrilinearStabilizer

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Endomorphisms annihilating the distinguished split-Albert unit form a
native Lie subalgebra for the composition commutator. -/
def h3zornUnitAnnihilator : LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ)) where
  carrier := {D | D 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro D E hD hE
    change D 1 + E 1 = 0
    change D 1 = 0 at hD
    change E 1 = 0 at hE
    rw [hD, hE, add_zero]
  smul_mem' := by
    intro r D hD
    change r • D 1 = 0
    change D 1 = 0 at hD
    rw [hD, smul_zero]
  lie_mem' := by
    intro D E hD hE
    change D (E 1) - E (D 1) = 0
    change D 1 = 0 at hD
    change E 1 = 0 at hE
    rw [hD, hE, map_zero, map_zero, sub_self]

@[simp] theorem mem_h3zornUnitAnnihilator (D : Module.End ℝ (H3Zorn ℝ)) :
    D ∈ h3zornUnitAnnihilator ↔ D 1 = 0 := Iff.rfl

/-- The cubic slot equation evaluated at two units forces the image of the
endomorphism to have zero linear trace. -/
theorem h3zorn_linearTrace_apply_eq_zero_of_cubic_unit
    (D : Module.End ℝ (H3Zorn ℝ))
    (hC : D ∈ trilinearStabilizer h3zornNormTrilin)
    (h1 : D 1 = 0) (x : H3Zorn ℝ) : linearTrace (D x) = 0 := by
  have h := hC x 1 1
  simp only [h1, map_zero, LinearMap.zero_apply, add_zero] at h
  rw [← h3zornNormTrilin_one_one (D x), h, mul_zero]

/-- The cubic slot equation at one unit recovers infinitesimal preservation
of the entire split trace pairing. -/
theorem h3zorn_traceBilin_infinitesimal_of_cubic_unit
    (D : Module.End ℝ (H3Zorn ℝ))
    (hC : D ∈ trilinearStabilizer h3zornNormTrilin)
    (h1 : D 1 = 0) (x y : H3Zorn ℝ) :
    traceBilin (D x) y + traceBilin x (D y) = 0 := by
  have h := hC x y 1
  simp only [h1, map_zero, add_zero] at h
  have hx := h3zornNormTrilin_one_right (D x) y
  have hy := h3zornNormTrilin_one_right x (D y)
  rw [h3zorn_linearTrace_apply_eq_zero_of_cubic_unit D hC h1 x] at hx
  rw [h3zorn_linearTrace_apply_eq_zero_of_cubic_unit D hC h1 y] at hy
  linear_combination hx + hy - 6 * h

/-- Nondegeneracy converts cubic slot invariance and trace-pairing
skew-adjointness into the Leibniz rule for the full Albert cross product. -/
theorem h3zorn_crossProduct_leibniz_of_cubic_unit
    (D : Module.End ℝ (H3Zorn ℝ))
    (hC : D ∈ trilinearStabilizer h3zornNormTrilin)
    (h1 : D 1 = 0) (x y : H3Zorn ℝ) :
    D (crossProduct x y) = crossProduct (D x) y + crossProduct x (D y) := by
  apply eq_of_traceBilin_right_eq
  intro z
  have hb := h3zorn_traceBilin_infinitesimal_of_cubic_unit D hC h1 z
    (crossProduct x y)
  have hc := hC z x y
  simp only [h3zornNormTrilin_apply] at hc
  rw [traceBilin_add_right]
  linear_combination hb - 6 * hc

/-- The differentiated reconstruction formula proves the Leibniz rule for
the installed normalized Jordan product, without assuming that rule. -/
theorem h3zorn_jordanDerivation_of_cubic_unit
    (D : Module.End ℝ (H3Zorn ℝ))
    (hC : D ∈ trilinearStabilizer h3zornNormTrilin)
    (h1 : D 1 = 0) : H3ZornJordanDerivation D := by
  intro x y
  have ht (z : H3Zorn ℝ) : linearTrace (D z) = 0 :=
    h3zorn_linearTrace_apply_eq_zero_of_cubic_unit D hC h1 z
  have hc := h3zorn_crossProduct_leibniz_of_cubic_unit D hC h1 x y
  have htc : linearTrace (crossProduct (D x) y) =
      -linearTrace (crossProduct x (D y)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← linearTrace_add, ← hc]
    exact ht (crossProduct x y)
  change D (candidateJordanMul x y) =
    candidateJordanMul (D x) y + candidateJordanMul x (D y)
  simp only [candidateJordanMul_trace_formula, map_smul, map_add, map_sub,
    h1, ht, hc, smul_zero, zero_smul, zero_add, add_zero, sub_zero]
  rw [htc]
  module

/-- The intersection of the actual cubic stabilizer with the unit annihilator
is contained in the existing split-Albert derivation Lie subalgebra. -/
theorem h3zorn_cubic_unit_stabilizer_le_F4 :
    trilinearStabilizer h3zornNormTrilin ⊓ h3zornUnitAnnihilator ≤
      H3ZornF4Derivations := by
  intro D hD
  exact h3zorn_jordanDerivation_of_cubic_unit D hD.1 hD.2

/-- The existing theorem that every Jordan derivation annihilates the unit
gives a second inclusion in the same native operator-subalgebra poset. -/
theorem h3zornF4Derivations_le_unitAnnihilator :
    H3ZornF4Derivations ≤ h3zornUnitAnnihilator := by
  intro D hD
  exact h3Zorn_derivation_apply_one_eq_zero
    (⟨D, hD⟩ : NonAssocDerivation.derivations ℝ (H3Zorn ℝ))

end InfoGeometry.Algebra
