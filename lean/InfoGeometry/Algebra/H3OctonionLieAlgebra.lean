/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3OctonionStructureGroup
import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Algebra.TrilinearStabilizer
import InfoGeometry.Algebra.H3ZornF4DimensionClosure
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Compact Lie Algebras `𝔣₄(-52) = Der(H₃(𝕆))`, `𝔢₆(-26) = str₀(H₃(𝕆))`,
  `str(H₃(𝕆))` (52D, 78D, 79D), and Real-Form Signature Separation

Directly on the compact 27-dimensional Albert Jordan algebra `H3Octonion ℝ`, this module proves:

1. `H3OctonionF4Derivations : LieSubalgebra ℝ (Module.End ℝ (H3Octonion ℝ))` (`𝔣₄(-52)`):
   unconditional 52-dimensional closure `Module.finrank ℝ H3OctonionF4Derivations = 52`,
   via 24D Peirce shifts (`octPeirceShiftEv` / `octPeirceShiftSection`) and 28D triality inner
   derivations (`so(8)` + `CompactOctonion.pureImaginary_left_nucleus_eq_zero`).
2. `h3OctonionCubicStabilizer := trilinearStabilizer h3OctonionNormTrilin` (`𝔢₆(-26)`):
   exact decomposition `H3OctonionF4Derivations.toSubmodule ⊕ h3OctonionLmulTraceZeroSubmodule`
   with `Module.finrank ℝ h3OctonionCubicStabilizer = 78`, and 79D `h3OctonionStructureLieSubalgebra`.
3. **Cartan Involution & Real-Form Signature Separation**:
   * Every `D ∈ H3OctonionF4Derivations` is skew-adjoint for positive-definite `traceBilin`,
     giving negative-definiteness `LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0`
     (with equality iff `D = 0`) on 52D compact `𝔣₄(-52)`.
   * Every `jordanLmul a` is self-adjoint for `traceBilin`, giving positive-definiteness
     `0 ≤ LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul a * jordanLmul a)` (with equality iff `a = 0`)
     on 26D `L(H₃(𝕆)⁰)` and 27D `L(H₃(𝕆))`.
   * Explicit split witness `splitF4TracePosWitness ∈ H3ZornF4Derivations` with
     `LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 > 0`,
     separating compact `𝔣₄(-52)` from split `𝔣₄(4)`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Octonion
open CompactOctonion (trace conj mul finrank_compactOctonion trace_add trace_zero)

attribute [local instance 100] LieRing.ofAssociativeRing

private instance : Module.Finite ℝ (H3Octonion ℝ) :=
  Module.Finite.of_basis h3OctonionBasis

private instance : Module.Finite ℝ (CompactOctonion ℝ) :=
  Module.Finite.of_basis CompactOctonion.compactOctonionBasis

private instance : Module.Finite ℝ (H3Zorn ℝ) :=
  Module.Finite.of_basis InfoGeometry.Algebra.h3ZornBasis

section PeirceSetupAndDerivations

abbrev EndH3O := Module.End ℝ (H3Octonion ℝ)

/-- Derivation Lie subalgebra `𝔣₄(-52) = Der(H₃(𝕆))` inside `End(H₃(𝕆))`. -/
def H3OctonionF4Derivations : LieSubalgebra ℝ EndH3O :=
  NonAssocDerivation.derivations ℝ (H3Octonion ℝ)

/-- Inner Jordan derivation `[L_a, L_b]` bundled inside `H3OctonionF4Derivations`. -/
def h3OctonionJordanInnerDerivation (a b : H3Octonion ℝ) : H3OctonionF4Derivations :=
  jordanInnerDerivationBundled (R := ℝ) (A := H3Octonion ℝ) a b

@[simp] theorem h3OctonionJordanInnerDerivation_apply (a b x : H3Octonion ℝ) :
    (h3OctonionJordanInnerDerivation a b : EndH3O) x = a * (b * x) - b * (a * x) := rfl

theorem h3Octonion_derivation_apply_one_eq_zero (D : H3OctonionF4Derivations) :
    (D : EndH3O) 1 = 0 := by
  have h := D.property (1 : H3Octonion ℝ) (1 : H3Octonion ℝ)
  rw [one_mul_h3Octonion, _root_.mul_comm ((D : EndH3O) 1) 1, one_mul_h3Octonion] at h
  have h0 := congrArg (fun w => w - (D : EndH3O) 1) h
  rw [sub_self, add_sub_cancel_right] at h0
  exact h0.symm

private theorem ext_h3_mul_diag1 (x : H3Octonion ℝ) :
    diagCartan 1 0 0 * x = ⟨x.α₁, 0, 0, (1 / 2 : ℝ) • x.a, 0, (1 / 2 : ℝ) • x.c⟩ := by
  rw [mul_trace_formula]
  have hlt : linearTrace (diagCartan (1 : ℝ) 0 0) = 1 := by simp [linearTrace, diagCartan]
  have hcr : H3Octonion.crossProduct (diagCartan (1 : ℝ) 0 0) x =
      ⟨0, x.α₃, x.α₂, 0, -x.b, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, diagCartan]
  rw [hlt, hcr]
  apply ext_h3
  · simp [diagCartan, linearTrace]; ring
  · simp [diagCartan, linearTrace]
  · simp [diagCartan, linearTrace]
  · simp [diagCartan]
  · simp [diagCartan]
  · simp [diagCartan]

private theorem ext_h3_mul_diag2 (x : H3Octonion ℝ) :
    diagCartan 0 1 0 * x = ⟨0, x.α₂, 0, (1 / 2 : ℝ) • x.a, (1 / 2 : ℝ) • x.b, 0⟩ := by
  rw [mul_trace_formula]
  have hlt : linearTrace (diagCartan (0 : ℝ) 1 0) = 1 := by simp [linearTrace, diagCartan]
  have hcr : H3Octonion.crossProduct (diagCartan (0 : ℝ) 1 0) x =
      ⟨x.α₃, 0, x.α₁, 0, 0, -x.c⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, diagCartan]
  rw [hlt, hcr]
  apply ext_h3
  · simp [diagCartan, linearTrace]
  · simp [diagCartan, linearTrace]; ring
  · simp [diagCartan, linearTrace]
  · simp [diagCartan]
  · simp [diagCartan]
  · simp [diagCartan]

private theorem ext_h3_mul_diag3 (x : H3Octonion ℝ) :
    diagCartan 0 0 1 * x = ⟨0, 0, x.α₃, 0, (1 / 2 : ℝ) • x.b, (1 / 2 : ℝ) • x.c⟩ := by
  rw [mul_trace_formula]
  have hlt : linearTrace (diagCartan (0 : ℝ) 0 1) = 1 := by simp [linearTrace, diagCartan]
  have hcr : H3Octonion.crossProduct (diagCartan (0 : ℝ) 0 1) x =
      ⟨x.α₂, x.α₁, 0, -x.a, 0, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, diagCartan]
  rw [hlt, hcr]
  apply ext_h3
  · simp [diagCartan, linearTrace]
  · simp [diagCartan, linearTrace]
  · simp [diagCartan, linearTrace]; ring
  · simp [diagCartan]
  · simp [diagCartan]
  · simp [diagCartan]

private def h3o_diag1 : H3Octonion ℝ := diagCartan 1 0 0
private def h3o_diag2 : H3Octonion ℝ := diagCartan 0 1 0
private def h3o_diag3 : H3Octonion ℝ := diagCartan 0 0 1

private theorem h3o_diag1_mul_diag1 : h3o_diag1 * h3o_diag1 = h3o_diag1 := by
  rw [h3o_diag1, ext_h3_mul_diag1]; apply ext_h3 <;> simp [diagCartan]
private theorem h3o_diag2_mul_diag2 : h3o_diag2 * h3o_diag2 = h3o_diag2 := by
  rw [h3o_diag2, ext_h3_mul_diag2]; apply ext_h3 <;> simp [diagCartan]
private theorem h3o_diag3_mul_diag3 : h3o_diag3 * h3o_diag3 = h3o_diag3 := by
  rw [h3o_diag3, ext_h3_mul_diag3]; apply ext_h3 <;> simp [diagCartan]
private theorem h3o_diag1_mul_diag2 : h3o_diag1 * h3o_diag2 = 0 := by
  rw [h3o_diag1, ext_h3_mul_diag1]; apply ext_h3 <;> simp [h3o_diag2, diagCartan]
private theorem h3o_diag1_mul_diag3 : h3o_diag1 * h3o_diag3 = 0 := by
  rw [h3o_diag1, ext_h3_mul_diag1]; apply ext_h3 <;> simp [h3o_diag3, diagCartan]
private theorem h3o_diag2_mul_diag3 : h3o_diag2 * h3o_diag3 = 0 := by
  rw [h3o_diag2, ext_h3_mul_diag2]; apply ext_h3 <;> simp [h3o_diag3, diagCartan]

private theorem h3o_diag1_mul_embedJ12 (x : CompactOctonion ℝ) :
    h3o_diag1 * embedJ12 x = (1 / 2 : ℝ) • embedJ12 x := by
  rw [h3o_diag1, ext_h3_mul_diag1]; apply ext_h3 <;> simp [embedJ12]
private theorem h3o_diag2_mul_embedJ12 (x : CompactOctonion ℝ) :
    h3o_diag2 * embedJ12 x = (1 / 2 : ℝ) • embedJ12 x := by
  rw [h3o_diag2, ext_h3_mul_diag2]; apply ext_h3 <;> simp [embedJ12]
private theorem h3o_diag3_mul_embedJ12 (x : CompactOctonion ℝ) :
    h3o_diag3 * embedJ12 x = 0 := by
  rw [h3o_diag3, ext_h3_mul_diag3]; apply ext_h3 <;> simp [embedJ12]

private theorem h3o_diag1_mul_embedJ23 (x : CompactOctonion ℝ) :
    h3o_diag1 * H3Octonion.embedJ23 x = 0 := by
  rw [h3o_diag1, ext_h3_mul_diag1]; apply ext_h3 <;> simp [H3Octonion.embedJ23]
private theorem h3o_diag2_mul_embedJ23 (x : CompactOctonion ℝ) :
    h3o_diag2 * H3Octonion.embedJ23 x = (1 / 2 : ℝ) • H3Octonion.embedJ23 x := by
  rw [h3o_diag2, ext_h3_mul_diag2]; apply ext_h3 <;> simp [H3Octonion.embedJ23]
private theorem h3o_diag3_mul_embedJ23 (x : CompactOctonion ℝ) :
    h3o_diag3 * H3Octonion.embedJ23 x = (1 / 2 : ℝ) • H3Octonion.embedJ23 x := by
  rw [h3o_diag3, ext_h3_mul_diag3]; apply ext_h3 <;> simp [H3Octonion.embedJ23]

private theorem h3o_diag1_mul_embedJ31 (x : CompactOctonion ℝ) :
    h3o_diag1 * H3Octonion.embedJ31 x = (1 / 2 : ℝ) • H3Octonion.embedJ31 x := by
  rw [h3o_diag1, ext_h3_mul_diag1]; apply ext_h3 <;> simp [H3Octonion.embedJ31]
private theorem h3o_diag2_mul_embedJ31 (x : CompactOctonion ℝ) :
    h3o_diag2 * H3Octonion.embedJ31 x = 0 := by
  rw [h3o_diag2, ext_h3_mul_diag2]; apply ext_h3 <;> simp [H3Octonion.embedJ31]
private theorem h3o_diag3_mul_embedJ31 (x : CompactOctonion ℝ) :
    h3o_diag3 * H3Octonion.embedJ31 x = (1 / 2 : ℝ) • H3Octonion.embedJ31 x := by
  rw [h3o_diag3, ext_h3_mul_diag3]; apply ext_h3 <;> simp [H3Octonion.embedJ31]

theorem oct_embedJ12_mul_embedJ12 (x y : CompactOctonion ℝ) :
    embedJ12 x * embedJ12 y =
      ((1 / 2 : ℝ) * CompactOctonion.bilin x y) • (h3o_diag1 + h3o_diag2) := by
  rw [mul_trace_formula]
  have h1 : linearTrace (embedJ12 x) = 0 := by simp [linearTrace, embedJ12]
  have h2 : linearTrace (embedJ12 y) = 0 := by simp [linearTrace, embedJ12]
  have hc : H3Octonion.crossProduct (embedJ12 x) (embedJ12 y) =
      ⟨0, 0, -CompactOctonion.bilin x y, 0, 0, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, embedJ12, CompactOctonion.bilin]
  rw [h1, h2, hc]
  apply ext_h3
  · simp [linearTrace, h3o_diag1, h3o_diag2, diagCartan]
  · simp [linearTrace, h3o_diag1, h3o_diag2, diagCartan]
  · simp [linearTrace, h3o_diag1, h3o_diag2, diagCartan]
  · simp [h3o_diag1, h3o_diag2, diagCartan]
  · simp [h3o_diag1, h3o_diag2, diagCartan]
  · simp [h3o_diag1, h3o_diag2, diagCartan]

theorem oct_embedJ23_mul_embedJ23 (x y : CompactOctonion ℝ) :
    H3Octonion.embedJ23 x * H3Octonion.embedJ23 y =
      ((1 / 2 : ℝ) * CompactOctonion.bilin x y) • (h3o_diag2 + h3o_diag3) := by
  rw [mul_trace_formula]
  have h1 : linearTrace (H3Octonion.embedJ23 x) = 0 := by simp [linearTrace, H3Octonion.embedJ23]
  have h2 : linearTrace (H3Octonion.embedJ23 y) = 0 := by simp [linearTrace, H3Octonion.embedJ23]
  have hc : H3Octonion.crossProduct (H3Octonion.embedJ23 x) (H3Octonion.embedJ23 y) =
      ⟨-CompactOctonion.bilin x y, 0, 0, 0, 0, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, H3Octonion.embedJ23, CompactOctonion.bilin]
  rw [h1, h2, hc]
  apply ext_h3
  · simp [linearTrace, h3o_diag2, h3o_diag3, diagCartan]
  · simp [linearTrace, h3o_diag2, h3o_diag3, diagCartan]
  · simp [linearTrace, h3o_diag2, h3o_diag3, diagCartan]
  · simp [h3o_diag2, h3o_diag3, diagCartan]
  · simp [h3o_diag2, h3o_diag3, diagCartan]
  · simp [h3o_diag2, h3o_diag3, diagCartan]

theorem oct_embedJ31_mul_embedJ31 (x y : CompactOctonion ℝ) :
    H3Octonion.embedJ31 x * H3Octonion.embedJ31 y =
      ((1 / 2 : ℝ) * CompactOctonion.bilin x y) • (h3o_diag3 + h3o_diag1) := by
  rw [mul_trace_formula]
  have h1 : linearTrace (H3Octonion.embedJ31 x) = 0 := by simp [linearTrace, H3Octonion.embedJ31]
  have h2 : linearTrace (H3Octonion.embedJ31 y) = 0 := by simp [linearTrace, H3Octonion.embedJ31]
  have hc : H3Octonion.crossProduct (H3Octonion.embedJ31 x) (H3Octonion.embedJ31 y) =
      ⟨0, -CompactOctonion.bilin x y, 0, 0, 0, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, H3Octonion.embedJ31, CompactOctonion.bilin]
  rw [h1, h2, hc]
  apply ext_h3
  · simp [linearTrace, h3o_diag3, h3o_diag1, diagCartan]
  · simp [linearTrace, h3o_diag3, h3o_diag1, diagCartan]
  · simp [linearTrace, h3o_diag3, h3o_diag1, diagCartan]
  · simp [h3o_diag3, h3o_diag1, diagCartan]
  · simp [h3o_diag3, h3o_diag1, diagCartan]
  · simp [h3o_diag3, h3o_diag1, diagCartan]

theorem oct_embedJ12_mul_embedJ23 (x y : CompactOctonion ℝ) :
    embedJ12 x * H3Octonion.embedJ23 y =
      (1 / 2 : ℝ) • H3Octonion.embedJ31 (CompactOctonion.mul (CompactOctonion.conj y) (CompactOctonion.conj x)) := by
  rw [mul_trace_formula]
  have h1 : linearTrace (embedJ12 x) = 0 := by simp [linearTrace, embedJ12]
  have h2 : linearTrace (H3Octonion.embedJ23 y) = 0 := by simp [linearTrace, H3Octonion.embedJ23]
  have hc : H3Octonion.crossProduct (embedJ12 x) (H3Octonion.embedJ23 y) =
      H3Octonion.embedJ31 (CompactOctonion.mul (CompactOctonion.conj y) (CompactOctonion.conj x)) := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, embedJ12, H3Octonion.embedJ23, H3Octonion.embedJ31]
  rw [h1, h2, hc]
  simp [linearTrace, H3Octonion.embedJ31]

theorem oct_embedJ23_mul_embedJ31 (y z : CompactOctonion ℝ) :
    H3Octonion.embedJ23 y * H3Octonion.embedJ31 z =
      (1 / 2 : ℝ) • embedJ12 (CompactOctonion.mul (CompactOctonion.conj z) (CompactOctonion.conj y)) := by
  rw [mul_trace_formula]
  have h1 : linearTrace (H3Octonion.embedJ23 y) = 0 := by simp [linearTrace, H3Octonion.embedJ23]
  have h2 : linearTrace (H3Octonion.embedJ31 z) = 0 := by simp [linearTrace, H3Octonion.embedJ31]
  have hc : H3Octonion.crossProduct (H3Octonion.embedJ23 y) (H3Octonion.embedJ31 z) =
      embedJ12 (CompactOctonion.mul (CompactOctonion.conj z) (CompactOctonion.conj y)) := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, H3Octonion.embedJ23, H3Octonion.embedJ31, embedJ12]
  rw [h1, h2, hc]
  simp [linearTrace, embedJ12]

theorem oct_embedJ31_mul_embedJ12 (z x : CompactOctonion ℝ) :
    H3Octonion.embedJ31 z * embedJ12 x =
      (1 / 2 : ℝ) • H3Octonion.embedJ23 (CompactOctonion.mul (CompactOctonion.conj x) (CompactOctonion.conj z)) := by
  rw [mul_trace_formula]
  have h1 : linearTrace (H3Octonion.embedJ31 z) = 0 := by simp [linearTrace, H3Octonion.embedJ31]
  have h2 : linearTrace (embedJ12 x) = 0 := by simp [linearTrace, embedJ12]
  have hc : H3Octonion.crossProduct (H3Octonion.embedJ31 z) (embedJ12 x) =
      H3Octonion.embedJ23 (CompactOctonion.mul (CompactOctonion.conj x) (CompactOctonion.conj z)) := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, H3Octonion.embedJ31, embedJ12, H3Octonion.embedJ23]
  rw [h1, h2, hc]
  simp [linearTrace, H3Octonion.embedJ23]

private theorem h3Octonion_decomp (x : H3Octonion ℝ) :
    x = x.α₁ • h3o_diag1 + x.α₂ • h3o_diag2 + x.α₃ • h3o_diag3 +
      embedJ12 x.a + H3Octonion.embedJ23 x.b + H3Octonion.embedJ31 x.c := by
  apply ext_h3 <;> simp [h3o_diag1, h3o_diag2, h3o_diag3, diagCartan, embedJ12, H3Octonion.embedJ23, H3Octonion.embedJ31]

theorem h3Octonion_traceBilin_jordanLmul_assoc (a x y : H3Octonion ℝ) :
    traceBilin (a * x) y = traceBilin x (a * y) := by
  simp only [mul_trace_formula, traceBilin_smul_left, traceBilin_smul_right,
    traceBilin_add_left, traceBilin_add_right, traceBilin_sub_left, traceBilin_sub_right]
  rw [traceBilin_one, traceBilin_one_left, mccrimmon_identity_16 a x, mccrimmon_identity_16 a y,
    traceBilin_symm x a, traceBilin_symm x (H3Octonion.crossProduct a y),
    mccrimmon_identity_15 a x y, mccrimmon_identity_15 a y x, crossProduct_symm y x]
  ring

private theorem half_oct_eq_zero_of_eq_zero {u : CompactOctonion ℝ}
    (h : (1 / 2 : ℝ) • u = 0) : u = 0 :=
  (smul_eq_zero.mp h).resolve_left (by norm_num)

private theorem deriv_diag_kill_off (D : H3OctonionF4Derivations) :
    ((D : EndH3O) h3o_diag1).α₁ = 0 ∧ ((D : EndH3O) h3o_diag1).α₂ = 0 ∧
      ((D : EndH3O) h3o_diag1).α₃ = 0 ∧ ((D : EndH3O) h3o_diag1).b = 0 ∧
    ((D : EndH3O) h3o_diag2).α₁ = 0 ∧ ((D : EndH3O) h3o_diag2).α₂ = 0 ∧
      ((D : EndH3O) h3o_diag2).α₃ = 0 ∧ ((D : EndH3O) h3o_diag2).c = 0 ∧
    ((D : EndH3O) h3o_diag3).α₁ = 0 ∧ ((D : EndH3O) h3o_diag3).α₂ = 0 ∧
      ((D : EndH3O) h3o_diag3).α₃ = 0 ∧ ((D : EndH3O) h3o_diag3).a = 0 := by
  have hd1 := D.2 h3o_diag1 h3o_diag1
  rw [h3o_diag1_mul_diag1, _root_.mul_comm ((D : EndH3O) h3o_diag1) h3o_diag1, ← two_smul ℝ] at hd1
  change _ = (2 : ℝ) • (h3o_diag1 * (D : EndH3O) h3o_diag1) at hd1
  rw [h3o_diag1, ext_h3_mul_diag1, ← h3o_diag1] at hd1
  have hd2 := D.2 h3o_diag2 h3o_diag2
  rw [h3o_diag2_mul_diag2, _root_.mul_comm ((D : EndH3O) h3o_diag2) h3o_diag2, ← two_smul ℝ] at hd2
  change _ = (2 : ℝ) • (h3o_diag2 * (D : EndH3O) h3o_diag2) at hd2
  rw [h3o_diag2, ext_h3_mul_diag2, ← h3o_diag2] at hd2
  have hd3 := D.2 h3o_diag3 h3o_diag3
  rw [h3o_diag3_mul_diag3, _root_.mul_comm ((D : EndH3O) h3o_diag3) h3o_diag3, ← two_smul ℝ] at hd3
  change _ = (2 : ℝ) • (h3o_diag3 * (D : EndH3O) h3o_diag3) at hd3
  rw [h3o_diag3, ext_h3_mul_diag3, ← h3o_diag3] at hd3
  refine ⟨by have := congrArg H3Octonion.α₁ hd1; simp at this; linarith,
    by have := congrArg H3Octonion.α₂ hd1; simp at this; exact this,
    by have := congrArg H3Octonion.α₃ hd1; simp at this; exact this,
    by have := congrArg H3Octonion.b hd1; simp at this; exact this,
    by have := congrArg H3Octonion.α₁ hd2; simp at this; exact this,
    by have := congrArg H3Octonion.α₂ hd2; simp at this; linarith,
    by have := congrArg H3Octonion.α₃ hd2; simp at this; exact this,
    by have := congrArg H3Octonion.c hd2; simp at this; exact this,
    by have := congrArg H3Octonion.α₁ hd3; simp at this; exact this,
    by have := congrArg H3Octonion.α₂ hd3; simp at this; exact this,
    by have := congrArg H3Octonion.α₃ hd3; simp at this; linarith,
    by have := congrArg H3Octonion.a hd3; simp at this; exact this⟩

private theorem mul_embed_trace_diag (y : H3Octonion ℝ) :
    ∀ u : CompactOctonion ℝ,
      (y * embedJ12 u).α₁ = (1 / 2 : ℝ) * trace (mul y.a (conj u)) ∧
      (y * embedJ12 u).α₂ = (1 / 2 : ℝ) * trace (mul y.a (conj u)) ∧
      (y * embedJ12 u).α₃ = 0 := by
  intro u
  rw [mul_trace_formula]
  have hc : (H3Octonion.crossProduct y (embedJ12 u)).α₃ = y.α₁ * 0 + 0 * y.α₂ - trace (mul y.a (conj u)) := rfl
  have hc1 : (H3Octonion.crossProduct y (embedJ12 u)).α₁ = 0 := by simp [H3Octonion.crossProduct, embedJ12]
  have hc2 : (H3Octonion.crossProduct y (embedJ12 u)).α₂ = 0 := by simp [H3Octonion.crossProduct, embedJ12]
  have htr : linearTrace (embedJ12 u) = 0 := by simp [linearTrace, embedJ12]
  have hlt_cr : linearTrace (H3Octonion.crossProduct y (embedJ12 u)) =
      -trace (mul y.a (conj u)) := by
    rw [linearTrace, hc, hc1, hc2]; ring
  rw [htr, hlt_cr]
  refine ⟨?_, ?_, ?_⟩
  · change (1 / 2 : ℝ) * (y.linearTrace * (embedJ12 u).α₁ + 0 * y.α₁ -
        (-trace (mul y.a (conj u))) * (1 : H3Octonion ℝ).α₁ +
        (H3Octonion.crossProduct y (embedJ12 u)).α₁) = _
    rw [hc1]; dsimp [embedJ12, H3Octonion.one]; ring
  · change (1 / 2 : ℝ) * (y.linearTrace * (embedJ12 u).α₂ + 0 * y.α₂ -
        (-trace (mul y.a (conj u))) * (1 : H3Octonion ℝ).α₂ +
        (H3Octonion.crossProduct y (embedJ12 u)).α₂) = _
    rw [hc2]; dsimp [embedJ12, H3Octonion.one]; ring
  · change (1 / 2 : ℝ) * (y.linearTrace * (embedJ12 u).α₃ + 0 * y.α₃ -
        (-trace (mul y.a (conj u))) * (1 : H3Octonion ℝ).α₃ +
        (H3Octonion.crossProduct y (embedJ12 u)).α₃) = _
    rw [hc]; dsimp [embedJ12, H3Octonion.one]; ring

private theorem deriv_off12_linearTrace_zero (D : H3OctonionF4Derivations) (u : CompactOctonion ℝ) :
    linearTrace ((D : EndH3O) (embedJ12 u)) = 0 := by
  have hk := deriv_diag_kill_off D
  have h1sum : h3o_diag1 + h3o_diag2 + h3o_diag3 = (1 : H3Octonion ℝ) := by
    apply ext_h3 <;> simp [h3o_diag1, h3o_diag2, h3o_diag3, diagCartan]
  have hD1 : (D : EndH3O) h3o_diag1 + (D : EndH3O) h3o_diag2 + (D : EndH3O) h3o_diag3 = 0 := by
    rw [← map_add, ← map_add, h1sum, h3Octonion_derivation_apply_one_eq_zero]
  have ha_sum : ((D : EndH3O) h3o_diag1).a + ((D : EndH3O) h3o_diag2).a = 0 := by
    have h := congrArg H3Octonion.a hD1
    simpa [hk.2.2.2.2.2.2.2.2.2.2.2] using h
  have hd1 := D.2 h3o_diag1 (embedJ12 u)
  rw [h3o_diag1_mul_embedJ12, map_smul] at hd1
  have hd2 := D.2 h3o_diag2 (embedJ12 u)
  rw [h3o_diag2_mul_embedJ12, map_smul] at hd2
  have hd3 := D.2 h3o_diag3 (embedJ12 u)
  rw [h3o_diag3_mul_embedJ12, map_zero] at hd3
  have hα3 : ((D : EndH3O) (embedJ12 u)).α₃ = 0 := by
    have h := congrArg H3Octonion.α₃ hd3
    change (0 : ℝ) = (((D : EndH3O) h3o_diag3 * embedJ12 u).α₃) +
      ((h3o_diag3 * (D : EndH3O) (embedJ12 u)).α₃) at h
    rw [h3o_diag3, ext_h3_mul_diag3, (mul_embed_trace_diag _ u).2.2, zero_add] at h
    exact h.symm
  have hα2 : (1 / 2 : ℝ) * ((D : EndH3O) (embedJ12 u)).α₂ =
      (1 / 2 : ℝ) * trace (mul ((D : EndH3O) h3o_diag1).a (conj u)) := by
    have h := congrArg H3Octonion.α₂ hd1
    change (1 / 2 : ℝ) * ((D : EndH3O) (embedJ12 u)).α₂ =
      (((D : EndH3O) h3o_diag1 * embedJ12 u).α₂) +
        ((h3o_diag1 * (D : EndH3O) (embedJ12 u)).α₂) at h
    rw [h3o_diag1, ext_h3_mul_diag1, (mul_embed_trace_diag _ u).2.1, add_zero] at h
    exact h
  have hα1 : (1 / 2 : ℝ) * ((D : EndH3O) (embedJ12 u)).α₁ =
      (1 / 2 : ℝ) * trace (mul ((D : EndH3O) h3o_diag2).a (conj u)) := by
    have h := congrArg H3Octonion.α₁ hd2
    change (1 / 2 : ℝ) * ((D : EndH3O) (embedJ12 u)).α₁ =
      (((D : EndH3O) h3o_diag2 * embedJ12 u).α₁) +
        ((h3o_diag2 * (D : EndH3O) (embedJ12 u)).α₁) at h
    rw [h3o_diag2, ext_h3_mul_diag2, (mul_embed_trace_diag _ u).1, add_zero] at h
    exact h
  have hsum12 : (1 / 2 : ℝ) * (((D : EndH3O) (embedJ12 u)).α₁ +
      ((D : EndH3O) (embedJ12 u)).α₂) = 0 := by
    rw [mul_add, hα1, hα2, ← mul_add, ← trace_add, ← CompactOctonion.add_mul, add_comm ((D : EndH3O) h3o_diag2).a,
      ha_sum, CompactOctonion.zero_mul, trace_zero, mul_zero]
  have h12 : ((D : EndH3O) (embedJ12 u)).α₁ + ((D : EndH3O) (embedJ12 u)).α₂ = 0 :=
    (mul_eq_zero.mp hsum12).resolve_left (by norm_num)
  dsimp [linearTrace]
  linarith

private theorem mul_embed23_trace_diag (y : H3Octonion ℝ) (u : CompactOctonion ℝ) :
    (y * H3Octonion.embedJ23 u).α₁ = 0 ∧
    (y * H3Octonion.embedJ23 u).α₂ = (1 / 2 : ℝ) * trace (mul y.b (conj u)) ∧
    (y * H3Octonion.embedJ23 u).α₃ = (1 / 2 : ℝ) * trace (mul y.b (conj u)) := by
  rw [mul_trace_formula]
  have hc : (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)).α₁ = -trace (mul y.b (conj u)) := by
    simp [H3Octonion.crossProduct, H3Octonion.embedJ23]
  have hc2 : (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)).α₂ = 0 := by simp [H3Octonion.crossProduct, H3Octonion.embedJ23]
  have hc3 : (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)).α₃ = 0 := by simp [H3Octonion.crossProduct, H3Octonion.embedJ23]
  have htr : linearTrace (H3Octonion.embedJ23 u) = 0 := by simp [linearTrace, H3Octonion.embedJ23]
  have hlt_cr : linearTrace (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)) =
      -trace (mul y.b (conj u)) := by
    rw [linearTrace, hc, hc2, hc3]; ring
  rw [htr, hlt_cr]
  refine ⟨?_, ?_, ?_⟩
  · change (1 / 2 : ℝ) * (y.linearTrace * (H3Octonion.embedJ23 u).α₁ + 0 * y.α₁ -
        (-trace (mul y.b (conj u))) * (1 : H3Octonion ℝ).α₁ +
        (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)).α₁) = _
    rw [hc]; dsimp [H3Octonion.embedJ23, H3Octonion.one]; ring
  · change (1 / 2 : ℝ) * (y.linearTrace * (H3Octonion.embedJ23 u).α₂ + 0 * y.α₂ -
        (-trace (mul y.b (conj u))) * (1 : H3Octonion ℝ).α₂ +
        (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)).α₂) = _
    rw [hc2]; dsimp [H3Octonion.embedJ23, H3Octonion.one]; ring
  · change (1 / 2 : ℝ) * (y.linearTrace * (H3Octonion.embedJ23 u).α₃ + 0 * y.α₃ -
        (-trace (mul y.b (conj u))) * (1 : H3Octonion ℝ).α₃ +
        (H3Octonion.crossProduct y (H3Octonion.embedJ23 u)).α₃) = _
    rw [hc3]; dsimp [H3Octonion.embedJ23, H3Octonion.one]; ring

private theorem deriv_off23_linearTrace_zero (D : H3OctonionF4Derivations) (u : CompactOctonion ℝ) :
    linearTrace ((D : EndH3O) (H3Octonion.embedJ23 u)) = 0 := by
  have hk := deriv_diag_kill_off D
  have h1sum : h3o_diag1 + h3o_diag2 + h3o_diag3 = (1 : H3Octonion ℝ) := by
    apply ext_h3 <;> simp [h3o_diag1, h3o_diag2, h3o_diag3, diagCartan]
  have hD1 : (D : EndH3O) h3o_diag1 + (D : EndH3O) h3o_diag2 + (D : EndH3O) h3o_diag3 = 0 := by
    rw [← map_add, ← map_add, h1sum, h3Octonion_derivation_apply_one_eq_zero]
  have hb_sum : ((D : EndH3O) h3o_diag2).b + ((D : EndH3O) h3o_diag3).b = 0 := by
    have h := congrArg H3Octonion.b hD1
    simpa [hk.2.2.2.1] using h
  have hd1 := D.2 h3o_diag1 (H3Octonion.embedJ23 u)
  rw [h3o_diag1_mul_embedJ23, map_zero] at hd1
  have hd2 := D.2 h3o_diag2 (H3Octonion.embedJ23 u)
  rw [h3o_diag2_mul_embedJ23, map_smul] at hd2
  have hd3 := D.2 h3o_diag3 (H3Octonion.embedJ23 u)
  rw [h3o_diag3_mul_embedJ23, map_smul] at hd3
  have hα1 : ((D : EndH3O) (H3Octonion.embedJ23 u)).α₁ = 0 := by
    have h := congrArg H3Octonion.α₁ hd1
    change (0 : ℝ) = (((D : EndH3O) h3o_diag1 * H3Octonion.embedJ23 u).α₁) +
      ((h3o_diag1 * (D : EndH3O) (H3Octonion.embedJ23 u)).α₁) at h
    rw [h3o_diag1, ext_h3_mul_diag1, (mul_embed23_trace_diag _ u).1, zero_add] at h
    exact h.symm
  have hα3 : (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ23 u)).α₃ =
      (1 / 2 : ℝ) * trace (mul ((D : EndH3O) h3o_diag2).b (conj u)) := by
    have h := congrArg H3Octonion.α₃ hd2
    change (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ23 u)).α₃ =
      (((D : EndH3O) h3o_diag2 * H3Octonion.embedJ23 u).α₃) +
        ((h3o_diag2 * (D : EndH3O) (H3Octonion.embedJ23 u)).α₃) at h
    rw [h3o_diag2, ext_h3_mul_diag2, (mul_embed23_trace_diag _ u).2.2, add_zero] at h
    exact h
  have hα2 : (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ23 u)).α₂ =
      (1 / 2 : ℝ) * trace (mul ((D : EndH3O) h3o_diag3).b (conj u)) := by
    have h := congrArg H3Octonion.α₂ hd3
    change (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ23 u)).α₂ =
      (((D : EndH3O) h3o_diag3 * H3Octonion.embedJ23 u).α₂) +
        ((h3o_diag3 * (D : EndH3O) (H3Octonion.embedJ23 u)).α₂) at h
    rw [h3o_diag3, ext_h3_mul_diag3, (mul_embed23_trace_diag _ u).2.1, add_zero] at h
    exact h
  have hsum23 : (1 / 2 : ℝ) * (((D : EndH3O) (H3Octonion.embedJ23 u)).α₂ +
      ((D : EndH3O) (H3Octonion.embedJ23 u)).α₃) = 0 := by
    rw [mul_add, hα2, hα3, ← mul_add, ← trace_add, ← CompactOctonion.add_mul,
      add_comm ((D : EndH3O) h3o_diag3).b, hb_sum, CompactOctonion.zero_mul, trace_zero, mul_zero]
  have h23 : ((D : EndH3O) (H3Octonion.embedJ23 u)).α₂ + ((D : EndH3O) (H3Octonion.embedJ23 u)).α₃ = 0 :=
    (mul_eq_zero.mp hsum23).resolve_left (by norm_num)
  dsimp [linearTrace]; linarith

private theorem mul_embed31_trace_diag (y : H3Octonion ℝ) (u : CompactOctonion ℝ) :
    (y * H3Octonion.embedJ31 u).α₁ = (1 / 2 : ℝ) * trace (mul y.c (conj u)) ∧
    (y * H3Octonion.embedJ31 u).α₂ = 0 ∧
    (y * H3Octonion.embedJ31 u).α₃ = (1 / 2 : ℝ) * trace (mul y.c (conj u)) := by
  rw [mul_trace_formula]
  have hc1 : (crossProduct y (H3Octonion.embedJ31 u)).α₁ = 0 := by simp [H3Octonion.crossProduct, H3Octonion.embedJ31]
  have hc2 : (crossProduct y (H3Octonion.embedJ31 u)).α₂ = -trace (mul y.c (conj u)) := by
    simp [H3Octonion.crossProduct, H3Octonion.embedJ31]
  have hc3 : (crossProduct y (H3Octonion.embedJ31 u)).α₃ = 0 := by simp [H3Octonion.crossProduct, H3Octonion.embedJ31]
  have htr : linearTrace (H3Octonion.embedJ31 u) = 0 := by simp [linearTrace, H3Octonion.embedJ31]
  have hlt_cr : linearTrace (H3Octonion.crossProduct y (H3Octonion.embedJ31 u)) =
      -trace (mul y.c (conj u)) := by
    rw [linearTrace, hc1, hc2, hc3]; ring
  rw [htr, hlt_cr]
  refine ⟨?_, ?_, ?_⟩
  · change (1 / 2 : ℝ) * (y.linearTrace * (H3Octonion.embedJ31 u).α₁ + 0 * y.α₁ -
        (-trace (mul y.c (conj u))) * (1 : H3Octonion ℝ).α₁ +
        (H3Octonion.crossProduct y (H3Octonion.embedJ31 u)).α₁) = _
    rw [hc1]; dsimp [H3Octonion.embedJ31, H3Octonion.one]; ring
  · change (1 / 2 : ℝ) * (y.linearTrace * (H3Octonion.embedJ31 u).α₂ + 0 * y.α₂ -
        (-trace (mul y.c (conj u))) * (1 : H3Octonion ℝ).α₂ +
        (H3Octonion.crossProduct y (H3Octonion.embedJ31 u)).α₂) = _
    rw [hc2]; dsimp [H3Octonion.embedJ31, H3Octonion.one]; ring
  · change (1 / 2 : ℝ) * (y.linearTrace * (H3Octonion.embedJ31 u).α₃ + 0 * y.α₃ -
        (-trace (mul y.c (conj u))) * (1 : H3Octonion ℝ).α₃ +
        (H3Octonion.crossProduct y (H3Octonion.embedJ31 u)).α₃) = _
    rw [hc3]; dsimp [H3Octonion.embedJ31, H3Octonion.one]; ring

private theorem deriv_off31_linearTrace_zero (D : H3OctonionF4Derivations) (u : CompactOctonion ℝ) :
    linearTrace ((D : EndH3O) (H3Octonion.embedJ31 u)) = 0 := by
  have hk := deriv_diag_kill_off D
  have h1sum : h3o_diag1 + h3o_diag2 + h3o_diag3 = (1 : H3Octonion ℝ) := by
    apply ext_h3 <;> simp [h3o_diag1, h3o_diag2, h3o_diag3, diagCartan]
  have hD1 : (D : EndH3O) h3o_diag1 + (D : EndH3O) h3o_diag2 + (D : EndH3O) h3o_diag3 = 0 := by
    rw [← map_add, ← map_add, h1sum, h3Octonion_derivation_apply_one_eq_zero]
  have hc_sum : ((D : EndH3O) h3o_diag3).c + ((D : EndH3O) h3o_diag1).c = 0 := by
    have h := congrArg H3Octonion.c hD1
    simpa [hk.2.2.2.2.2.2.2.1, add_comm] using h
  have hd2 := D.2 h3o_diag2 (H3Octonion.embedJ31 u)
  rw [h3o_diag2_mul_embedJ31, map_zero] at hd2
  have hd3 := D.2 h3o_diag3 (H3Octonion.embedJ31 u)
  rw [h3o_diag3_mul_embedJ31, map_smul] at hd3
  have hd1 := D.2 h3o_diag1 (H3Octonion.embedJ31 u)
  rw [h3o_diag1_mul_embedJ31, map_smul] at hd1
  have hα2 : ((D : EndH3O) (H3Octonion.embedJ31 u)).α₂ = 0 := by
    have h := congrArg H3Octonion.α₂ hd2
    change (0 : ℝ) = (((D : EndH3O) h3o_diag2 * H3Octonion.embedJ31 u).α₂) +
      ((h3o_diag2 * (D : EndH3O) (H3Octonion.embedJ31 u)).α₂) at h
    rw [h3o_diag2, ext_h3_mul_diag2, (mul_embed31_trace_diag _ u).2.1, zero_add] at h
    exact h.symm
  have hα1 : (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ31 u)).α₁ =
      (1 / 2 : ℝ) * trace (mul ((D : EndH3O) h3o_diag3).c (conj u)) := by
    have h := congrArg H3Octonion.α₁ hd3
    change (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ31 u)).α₁ =
      (((D : EndH3O) h3o_diag3 * H3Octonion.embedJ31 u).α₁) +
        ((h3o_diag3 * (D : EndH3O) (H3Octonion.embedJ31 u)).α₁) at h
    rw [h3o_diag3, ext_h3_mul_diag3, (mul_embed31_trace_diag _ u).1, add_zero] at h
    exact h
  have hα3 : (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ31 u)).α₃ =
      (1 / 2 : ℝ) * trace (mul ((D : EndH3O) h3o_diag1).c (conj u)) := by
    have h := congrArg H3Octonion.α₃ hd1
    change (1 / 2 : ℝ) * ((D : EndH3O) (H3Octonion.embedJ31 u)).α₃ =
      (((D : EndH3O) h3o_diag1 * H3Octonion.embedJ31 u).α₃) +
        ((h3o_diag1 * (D : EndH3O) (H3Octonion.embedJ31 u)).α₃) at h
    rw [h3o_diag1, ext_h3_mul_diag1, (mul_embed31_trace_diag _ u).2.2, add_zero] at h
    exact h
  have hsum31 : (1 / 2 : ℝ) * (((D : EndH3O) (H3Octonion.embedJ31 u)).α₃ +
      ((D : EndH3O) (H3Octonion.embedJ31 u)).α₁) = 0 := by
    rw [mul_add, hα3, hα1, ← mul_add, ← trace_add, ← CompactOctonion.add_mul,
      add_comm ((D : EndH3O) h3o_diag1).c, hc_sum, CompactOctonion.zero_mul, trace_zero, mul_zero]
  have h31 : ((D : EndH3O) (H3Octonion.embedJ31 u)).α₃ + ((D : EndH3O) (H3Octonion.embedJ31 u)).α₁ = 0 :=
    (mul_eq_zero.mp hsum31).resolve_left (by norm_num)
  dsimp [linearTrace]; linarith

theorem h3Octonion_derivation_linearTrace_zero (D : H3OctonionF4Derivations) (x : H3Octonion ℝ) :
    linearTrace ((D : EndH3O) x) = 0 := by
  conv_lhs => rw [h3Octonion_decomp x]
  simp only [map_add, map_smul, linearTrace_add, linearTrace_smul]
  have hk := deriv_diag_kill_off D
  have hl1 : linearTrace ((D : EndH3O) h3o_diag1) = 0 := by
    dsimp [linearTrace]; linarith [hk.1, hk.2.1, hk.2.2.1]
  have hl2 : linearTrace ((D : EndH3O) h3o_diag2) = 0 := by
    dsimp [linearTrace]; linarith [hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1]
  have hl3 : linearTrace ((D : EndH3O) h3o_diag3) = 0 := by
    dsimp [linearTrace]
    linarith [hk.2.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.2.2.1]
  rw [hl1, hl2, hl3, deriv_off12_linearTrace_zero, deriv_off23_linearTrace_zero,
    deriv_off31_linearTrace_zero]
  ring

theorem h3Octonion_derivation_traceBilin_skew (D : H3OctonionF4Derivations) (x y : H3Octonion ℝ) :
    traceBilin ((D : EndH3O) x) y + traceBilin x ((D : EndH3O) y) = 0 := by
  rw [← linearTrace_jordanMul, ← linearTrace_jordanMul, ← linearTrace_add, ← D.2 x y]
  exact h3Octonion_derivation_linearTrace_zero D (x * y)

theorem h3Octonion_derivation_adjointQuad (D : H3OctonionF4Derivations) (x : H3Octonion ℝ) :
    (D : EndH3O) (adjointQuad x) = crossProduct x ((D : EndH3O) x) := by
  have h1 : (D : EndH3O) 1 = 0 := h3Octonion_derivation_apply_one_eq_zero D
  have htr : linearTrace ((D : EndH3O) x) = 0 := h3Octonion_derivation_linearTrace_zero D x
  have hbil : traceBilin x ((D : EndH3O) x) = 0 := by
    have hs := h3Octonion_derivation_traceBilin_skew D x x
    rw [traceBilin_symm ((D : EndH3O) x) x] at hs
    linarith
  have hsq : (D : EndH3O) (x * x) = linearTrace x • (D : EndH3O) x + (D : EndH3O) (adjointQuad x) := by
    conv_lhs => rw [h3octonion_mul_self_eq_adjoint x]
    simp only [map_add, map_sub, map_smul, h1, smul_zero, sub_zero]
  have hleib : (D : EndH3O) (x * x) = linearTrace x • (D : EndH3O) x + crossProduct x ((D : EndH3O) x) := by
    rw [D.2 x x, _root_.mul_comm ((D : EndH3O) x) x, ← two_smul ℝ (x * (D : EndH3O) x), mul_trace_formula,
      mccrimmon_identity_16, htr, hbil]
    simp only [mul_zero, sub_zero, zero_smul, add_zero]
    module
  exact add_left_cancel (hsq.symm.trans hleib)

end PeirceSetupAndDerivations

section CompactF4DimensionClosure

abbrev OctTriple := CompactOctonion ℝ × CompactOctonion ℝ × CompactOctonion ℝ

private theorem finrank_octTriple : Module.finrank ℝ OctTriple = 24 := by
  simp [OctTriple, Module.finrank_prod, finrank_compactOctonion]

private def octEmbedJ12LM : CompactOctonion ℝ →ₗ[ℝ] H3Octonion ℝ where
  toFun := embedJ12
  map_add' _ _ := by apply ext_h3 <;> simp [embedJ12]
  map_smul' _ _ := by apply ext_h3 <;> simp [embedJ12]

private def octEmbedJ23LM : CompactOctonion ℝ →ₗ[ℝ] H3Octonion ℝ where
  toFun := H3Octonion.embedJ23
  map_add' _ _ := by apply ext_h3 <;> simp [H3Octonion.embedJ23]
  map_smul' _ _ := by apply ext_h3 <;> simp [H3Octonion.embedJ23]

private def octEmbedJ31LM : CompactOctonion ℝ →ₗ[ℝ] H3Octonion ℝ where
  toFun := H3Octonion.embedJ31
  map_add' _ _ := by apply ext_h3 <;> simp [H3Octonion.embedJ31]
  map_smul' _ _ := by apply ext_h3 <;> simp [H3Octonion.embedJ31]

private def octPeirceShiftEv : H3OctonionF4Derivations →ₗ[ℝ] OctTriple where
  toFun D := (((D : EndH3O) h3o_diag1).a, ((D : EndH3O) h3o_diag2).b, ((D : EndH3O) h3o_diag3).c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def octPeirceShiftSection : OctTriple →ₗ[ℝ] H3OctonionF4Derivations where
  toFun p :=
    (-4 : ℝ) • h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 p.1) +
    (-4 : ℝ) • h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 p.2.1) +
    (-4 : ℝ) • h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 p.2.2)
  map_add' p q := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    have hj12 : embedJ12 (p.1 + q.1) = embedJ12 p.1 + embedJ12 q.1 := octEmbedJ12LM.map_add p.1 q.1
    have hj23 : H3Octonion.embedJ23 (p.2.1 + q.2.1) =
        H3Octonion.embedJ23 p.2.1 + H3Octonion.embedJ23 q.2.1 := octEmbedJ23LM.map_add p.2.1 q.2.1
    have hj31 : H3Octonion.embedJ31 (p.2.2 + q.2.2) =
        H3Octonion.embedJ31 p.2.2 + H3Octonion.embedJ31 q.2.2 := octEmbedJ31LM.map_add p.2.2 q.2.2
    have hcoe_add : ∀ A B : H3OctonionF4Derivations,
        ((A + B : H3OctonionF4Derivations) : EndH3O) = (A : EndH3O) + (B : EndH3O) := fun _ _ => rfl
    have hcoe_smul : ∀ (c : ℝ) (A : H3OctonionF4Derivations),
        ((c • A : H3OctonionF4Derivations) : EndH3O) = c • (A : EndH3O) := fun _ _ => rfl
    simp only [Prod.fst_add, Prod.snd_add, hj12, hj23, hj31]
    simp only [hcoe_add, hcoe_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h3OctonionJordanInnerDerivation_apply, mul_add, add_mul, smul_add, smul_sub]
    module
  map_smul' r p := by
    apply Subtype.ext; apply LinearMap.ext; intro x
    have hj12 : embedJ12 (r • p.1) = r • embedJ12 p.1 := octEmbedJ12LM.map_smul r p.1
    have hj23 : H3Octonion.embedJ23 (r • p.2.1) = r • H3Octonion.embedJ23 p.2.1 := octEmbedJ23LM.map_smul r p.2.1
    have hj31 : H3Octonion.embedJ31 (r • p.2.2) = r • H3Octonion.embedJ31 p.2.2 := octEmbedJ31LM.map_smul r p.2.2
    have hcoe_add : ∀ A B : H3OctonionF4Derivations,
        ((A + B : H3OctonionF4Derivations) : EndH3O) = (A : EndH3O) + (B : EndH3O) := fun _ _ => rfl
    have hcoe_smul : ∀ (c : ℝ) (A : H3OctonionF4Derivations),
        ((c • A : H3OctonionF4Derivations) : EndH3O) = c • (A : EndH3O) := fun _ _ => rfl
    simp only [Prod.smul_fst, Prod.smul_snd, hj12, hj23, hj31]
    simp only [hcoe_add, hcoe_smul, LinearMap.add_apply, LinearMap.smul_apply, RingHom.id_apply,
      h3OctonionJordanInnerDerivation_apply, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add,
      smul_smul]
    module

private theorem octPeirceShiftEv_section (p : OctTriple) : octPeirceShiftEv (octPeirceShiftSection p) = p := by
  rcases p with ⟨x, y, z⟩
  have h1a : ((h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 x) : EndH3O) h3o_diag1).a =
      (-1 / 4 : ℝ) • x := by
    rw [h3OctonionJordanInnerDerivation_apply, h3o_diag1_mul_diag1, _root_.mul_comm (embedJ12 x) h3o_diag1,
      h3o_diag1_mul_embedJ12, mul_smul_comm, h3o_diag1_mul_embedJ12, smul_smul]
    simp [embedJ12]; module
  have h2a : ((h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 y) : EndH3O) h3o_diag1).a = 0 := by
    rw [h3OctonionJordanInnerDerivation_apply, _root_.mul_comm (H3Octonion.embedJ23 y) h3o_diag1,
      h3o_diag1_mul_embedJ23, _root_.mul_comm h3o_diag2 h3o_diag1, h3o_diag1_mul_diag2, mul_zero,
      mul_zero, sub_self]; rfl
  have h3a : ((h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 z) : EndH3O) h3o_diag1).a = 0 := by
    rw [h3OctonionJordanInnerDerivation_apply, _root_.mul_comm (H3Octonion.embedJ31 z) h3o_diag1,
      h3o_diag1_mul_embedJ31, _root_.mul_comm h3o_diag3 h3o_diag1, h3o_diag1_mul_diag3, mul_zero,
      mul_smul_comm, h3o_diag3_mul_embedJ31]
    simp [H3Octonion.embedJ31]
  have h1b : ((h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 x) : EndH3O) h3o_diag2).b = 0 := by
    rw [h3OctonionJordanInnerDerivation_apply, _root_.mul_comm (embedJ12 x) h3o_diag2,
      h3o_diag2_mul_embedJ12, h3o_diag1_mul_diag2, mul_zero, mul_smul_comm, h3o_diag1_mul_embedJ12]
    simp [embedJ12]
  have h2b : ((h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 y) : EndH3O) h3o_diag2).b =
      (-1 / 4 : ℝ) • y := by
    rw [h3OctonionJordanInnerDerivation_apply, h3o_diag2_mul_diag2, _root_.mul_comm (H3Octonion.embedJ23 y) h3o_diag2,
      h3o_diag2_mul_embedJ23, mul_smul_comm, h3o_diag2_mul_embedJ23, smul_smul]
    simp [H3Octonion.embedJ23]; module
  have h3b : ((h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 z) : EndH3O) h3o_diag2).b = 0 := by
    rw [h3OctonionJordanInnerDerivation_apply, _root_.mul_comm (H3Octonion.embedJ31 z) h3o_diag2,
      h3o_diag2_mul_embedJ31, _root_.mul_comm h3o_diag3 h3o_diag2, h3o_diag2_mul_diag3, mul_zero,
      mul_zero, sub_self]; rfl
  have h1c : ((h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 x) : EndH3O) h3o_diag3).c = 0 := by
    rw [h3OctonionJordanInnerDerivation_apply, _root_.mul_comm (embedJ12 x) h3o_diag3,
      h3o_diag3_mul_embedJ12, h3o_diag1_mul_diag3, mul_zero, mul_zero, sub_self]; rfl
  have h2c : ((h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 y) : EndH3O) h3o_diag3).c = 0 := by
    rw [h3OctonionJordanInnerDerivation_apply, _root_.mul_comm (H3Octonion.embedJ23 y) h3o_diag3,
      h3o_diag3_mul_embedJ23, h3o_diag2_mul_diag3, mul_zero, mul_smul_comm, h3o_diag2_mul_embedJ23]
    simp [H3Octonion.embedJ23]
  have h3c : ((h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 z) : EndH3O) h3o_diag3).c =
      (-1 / 4 : ℝ) • z := by
    rw [h3OctonionJordanInnerDerivation_apply, h3o_diag3_mul_diag3, _root_.mul_comm (H3Octonion.embedJ31 z) h3o_diag3,
      h3o_diag3_mul_embedJ31, mul_smul_comm, h3o_diag3_mul_embedJ31, smul_smul]
    simp [H3Octonion.embedJ31]; module
  ext1
  · change (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 x) : EndH3O) h3o_diag1).a +
      (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 y) : EndH3O) h3o_diag1).a +
      (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 z) : EndH3O) h3o_diag1).a = x
    rw [h1a, h2a, h3a]; module
  · ext1
    · change (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 x) : EndH3O) h3o_diag2).b +
        (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 y) : EndH3O) h3o_diag2).b +
        (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 z) : EndH3O) h3o_diag2).b = y
      rw [h1b, h2b, h3b]; module
    · change (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag1 (embedJ12 x) : EndH3O) h3o_diag3).c +
        (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag2 (H3Octonion.embedJ23 y) : EndH3O) h3o_diag3).c +
        (-4 : ℝ) • ((h3OctonionJordanInnerDerivation h3o_diag3 (H3Octonion.embedJ31 z) : EndH3O) h3o_diag3).c = z
      rw [h1c, h2c, h3c]; module

private theorem ker_octPeirceShiftEv_iff_diags_zero (D : H3OctonionF4Derivations) :
    D ∈ LinearMap.ker octPeirceShiftEv ↔
      ((D : EndH3O) h3o_diag1 = 0 ∧ (D : EndH3O) h3o_diag2 = 0 ∧ (D : EndH3O) h3o_diag3 = 0) := by
  constructor
  · intro hmem
    have hpe : octPeirceShiftEv D = 0 := LinearMap.mem_ker.mp hmem
    have ha0 : ((D : EndH3O) h3o_diag1).a = 0 := congrArg Prod.fst hpe
    have hb0 : ((D : EndH3O) h3o_diag2).b = 0 := congrArg (fun p => p.2.1) hpe
    have hc0 : ((D : EndH3O) h3o_diag3).c = 0 := congrArg (fun p => p.2.2) hpe
    have hk := deriv_diag_kill_off D
    have h1sum : h3o_diag1 + h3o_diag2 + h3o_diag3 = (1 : H3Octonion ℝ) := by
      ext <;> simp [h3o_diag1, h3o_diag2, h3o_diag3, diagCartan]
    have hD1 : (D : EndH3O) h3o_diag1 + (D : EndH3O) h3o_diag2 + (D : EndH3O) h3o_diag3 = 0 := by
      rw [← map_add, ← map_add, h1sum, h3Octonion_derivation_apply_one_eq_zero]
    have hc1 : ((D : EndH3O) h3o_diag1).c = 0 := by
      have h := congrArg H3Octonion.c hD1
      simpa [hk.2.2.2.2.2.2.2.1, hc0] using h
    have ha2 : ((D : EndH3O) h3o_diag2).a = 0 := by
      have h := congrArg H3Octonion.a hD1
      simpa [ha0, hk.2.2.2.2.2.2.2.2.2.2.2] using h
    have hb3 : ((D : EndH3O) h3o_diag3).b = 0 := by
      have h := congrArg H3Octonion.b hD1
      simpa [hk.2.2.2.1, hb0] using h
    exact ⟨by apply ext_h3 <;> simp [hk.1, hk.2.1, hk.2.2.1, ha0, hk.2.2.2.1, hc1],
      by apply ext_h3 <;> simp [hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1, ha2, hb0, hk.2.2.2.2.2.2.2.1],
      by apply ext_h3 <;> simp [hk.2.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.2.2.2.1,
        hk.2.2.2.2.2.2.2.2.2.2.2, hb3, hc0]⟩
  · rintro ⟨h1, h2, h3⟩
    rw [LinearMap.mem_ker]
    ext1
    · change ((D : EndH3O) h3o_diag1).a = 0
      rw [h1]; rfl
    · ext1
      · change ((D : EndH3O) h3o_diag2).b = 0
        rw [h2]; rfl
      · change ((D : EndH3O) h3o_diag3).c = 0
        rw [h3]; rfl

private theorem ker_octPeirceShiftEv_preserves_slots (D : LinearMap.ker octPeirceShiftEv) :
    (∀ x, (D.1 : EndH3O) (embedJ12 x) = embedJ12 ((D.1 : EndH3O) (embedJ12 x)).a) ∧
    (∀ y, (D.1 : EndH3O) (H3Octonion.embedJ23 y) = H3Octonion.embedJ23 ((D.1 : EndH3O) (H3Octonion.embedJ23 y)).b) ∧
    (∀ z, (D.1 : EndH3O) (H3Octonion.embedJ31 z) = H3Octonion.embedJ31 ((D.1 : EndH3O) (H3Octonion.embedJ31 z)).c) := by
  have half_scalar_eq_self : ∀ {r : ℝ}, (1 / 2 : ℝ) * r = r → r = 0 := fun {r} h => by
    have h1 : ((1 / 2 : ℝ) - 1) * r = 0 := by rw [_root_.sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
  obtain ⟨hd1, hd2, hd3⟩ := (ker_octPeirceShiftEv_iff_diags_zero D.1).mp D.2
  refine ⟨?_, ?_, ?_⟩
  · intro x
    let Y := (D.1 : EndH3O) (embedJ12 x)
    have h1 := D.1.2 h3o_diag1 (embedJ12 x)
    rw [h3o_diag1_mul_embedJ12, map_smul, hd1, zero_mul, zero_add] at h1
    have h2 := D.1.2 h3o_diag2 (embedJ12 x)
    rw [h3o_diag2_mul_embedJ12, map_smul, hd2, zero_mul, zero_add] at h2
    change (1 / 2 : ℝ) • Y = h3o_diag1 * Y at h1
    change (1 / 2 : ℝ) • Y = h3o_diag2 * Y at h2
    rw [h3o_diag1, ext_h3_mul_diag1] at h1
    rw [h3o_diag2, ext_h3_mul_diag2] at h2
    apply ext_h3
    · have ht := congrArg H3Octonion.α₁ h1; change (1 / 2 : ℝ) * Y.α₁ = Y.α₁ at ht
      exact half_scalar_eq_self ht
    · have ht := congrArg H3Octonion.α₂ h1; change (1 / 2 : ℝ) * Y.α₂ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Octonion.α₃ h1; change (1 / 2 : ℝ) * Y.α₃ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · rfl
    · exact half_oct_eq_zero_of_eq_zero (congrArg H3Octonion.b h1)
    · exact half_oct_eq_zero_of_eq_zero (congrArg H3Octonion.c h2)
  · intro y
    let Y := (D.1 : EndH3O) (H3Octonion.embedJ23 y)
    have h2 := D.1.2 h3o_diag2 (H3Octonion.embedJ23 y)
    rw [h3o_diag2_mul_embedJ23, map_smul, hd2, zero_mul, zero_add] at h2
    have h3 := D.1.2 h3o_diag3 (H3Octonion.embedJ23 y)
    rw [h3o_diag3_mul_embedJ23, map_smul, hd3, zero_mul, zero_add] at h3
    change (1 / 2 : ℝ) • Y = h3o_diag2 * Y at h2
    change (1 / 2 : ℝ) • Y = h3o_diag3 * Y at h3
    rw [h3o_diag2, ext_h3_mul_diag2] at h2
    rw [h3o_diag3, ext_h3_mul_diag3] at h3
    apply ext_h3
    · have ht := congrArg H3Octonion.α₁ h2; change (1 / 2 : ℝ) * Y.α₁ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Octonion.α₂ h2; change (1 / 2 : ℝ) * Y.α₂ = Y.α₂ at ht
      exact half_scalar_eq_self ht
    · have ht := congrArg H3Octonion.α₃ h2; change (1 / 2 : ℝ) * Y.α₃ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · exact half_oct_eq_zero_of_eq_zero (congrArg H3Octonion.a h3)
    · rfl
    · exact half_oct_eq_zero_of_eq_zero (congrArg H3Octonion.c h2)
  · intro z
    let Y := (D.1 : EndH3O) (H3Octonion.embedJ31 z)
    have h3 := D.1.2 h3o_diag3 (H3Octonion.embedJ31 z)
    rw [h3o_diag3_mul_embedJ31, map_smul, hd3, zero_mul, zero_add] at h3
    have h1 := D.1.2 h3o_diag1 (H3Octonion.embedJ31 z)
    rw [h3o_diag1_mul_embedJ31, map_smul, hd1, zero_mul, zero_add] at h1
    change (1 / 2 : ℝ) • Y = h3o_diag3 * Y at h3
    change (1 / 2 : ℝ) • Y = h3o_diag1 * Y at h1
    rw [h3o_diag3, ext_h3_mul_diag3] at h3
    rw [h3o_diag1, ext_h3_mul_diag1] at h1
    apply ext_h3
    · have ht := congrArg H3Octonion.α₁ h3; change (1 / 2 : ℝ) * Y.α₁ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Octonion.α₂ h3; change (1 / 2 : ℝ) * Y.α₂ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Octonion.α₃ h3; change (1 / 2 : ℝ) * Y.α₃ = Y.α₃ at ht
      exact half_scalar_eq_self ht
    · exact half_oct_eq_zero_of_eq_zero (congrArg H3Octonion.a h3)
    · exact half_oct_eq_zero_of_eq_zero (congrArg H3Octonion.b h1)
    · rfl

private def octSkewAdjointSubmodule : Submodule ℝ (Module.End ℝ (CompactOctonion ℝ)) where
  carrier := {T | ∀ x y, CompactOctonion.bilin (T x) y + CompactOctonion.bilin x (T y) = 0}
  zero_mem' x y := by simp [CompactOctonion.bilin]
  add_mem' {A B} hA hB x y := by
    simp only [LinearMap.add_apply]
    have hbx : CompactOctonion.bilin (A x + B x) y =
        CompactOctonion.bilin (A x) y + CompactOctonion.bilin (B x) y := by
      simp [CompactOctonion.bilin, CompactOctonion.add_mul, CompactOctonion.trace_add]
    have hby : CompactOctonion.bilin x (A y + B y) =
        CompactOctonion.bilin x (A y) + CompactOctonion.bilin x (B y) := by
      simp [CompactOctonion.bilin, CompactOctonion.conj_add, CompactOctonion.mul_add,
        CompactOctonion.trace_add]
    rw [hbx, hby, add_add_add_comm, hA x y, hB x y, add_zero]
  smul_mem' r {A} hA x y := by
    simp only [LinearMap.smul_apply]
    have hbx : CompactOctonion.bilin (r • A x) y = r * CompactOctonion.bilin (A x) y := by
      simp [CompactOctonion.bilin, CompactOctonion.smul_mul, CompactOctonion.trace_smul]
    have hby : CompactOctonion.bilin x (r • A y) = r * CompactOctonion.bilin x (A y) := by
      simp [CompactOctonion.bilin, CompactOctonion.conj_smul, CompactOctonion.mul_smul,
        CompactOctonion.trace_smul]
    rw [hbx, hby, ← mul_add, hA x y, mul_zero]

private def octSkewCoordMap : octSkewAdjointSubmodule →ₗ[ℝ] (StrictPair8 → ℝ) where
  toFun T p := CompactOctonion.bilin (T.1 (CompactOctonion.basisVec p.1.1)) (CompactOctonion.basisVec p.1.2)
  map_add' A B := by
    ext p
    simp [CompactOctonion.bilin, CompactOctonion.add_mul, CompactOctonion.trace_add]
  map_smul' r A := by
    ext p
    simp [CompactOctonion.bilin, CompactOctonion.smul_mul, CompactOctonion.trace_smul]

private theorem octSkewCoordMap_injective : Function.Injective octSkewCoordMap := by
  rw [injective_iff_map_eq_zero]
  intro T hT
  apply Subtype.ext; apply LinearMap.ext; intro x
  change T.1 x = 0
  rw [← CompactOctonion.basisVec_decomposition x, map_sum]
  apply Finset.sum_eq_zero; intro i _
  rw [map_smul]
  suffices hzero : T.1 (CompactOctonion.basisVec i) = 0 by rw [hzero, smul_zero]
  apply CompactOctonion.eq_zero_of_bilin_basis
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact congrFun hT ⟨(i, j), hij⟩
  · have h := T.2 (CompactOctonion.basisVec i) (CompactOctonion.basisVec i)
    have hsym : CompactOctonion.bilin (CompactOctonion.basisVec i) (T.1 (CompactOctonion.basisVec i)) =
        CompactOctonion.bilin (T.1 (CompactOctonion.basisVec i)) (CompactOctonion.basisVec i) := by
      simp [CompactOctonion.bilin, CompactOctonion.trace_mul_conj_comm]
    linarith
  · have h := T.2 (CompactOctonion.basisVec i) (CompactOctonion.basisVec j)
    have hsym : CompactOctonion.bilin (CompactOctonion.basisVec i) (T.1 (CompactOctonion.basisVec j)) =
        CompactOctonion.bilin (T.1 (CompactOctonion.basisVec j)) (CompactOctonion.basisVec i) := by
      simp [CompactOctonion.bilin, CompactOctonion.trace_mul_conj_comm]
    have hp : CompactOctonion.bilin (T.1 (CompactOctonion.basisVec j)) (CompactOctonion.basisVec i) = 0 :=
      congrFun hT ⟨(j, i), hij⟩
    linarith

private theorem finrank_octSkewAdjointSubmodule_le :
    Module.finrank ℝ octSkewAdjointSubmodule ≤ 28 := by
  have hf : Module.Finite ℝ (StrictPair8 → ℝ) := inferInstance
  have hle := LinearMap.finrank_le_finrank_of_injective octSkewCoordMap_injective
  rw [Module.finrank_fintype_fun_eq_card, card_strictPair8] at hle
  exact hle

private def octKerPeirceSlotA (D : LinearMap.ker octPeirceShiftEv) : Module.End ℝ (CompactOctonion ℝ) where
  toFun x := ((D.1 : EndH3O) (embedJ12 x)).a
  map_add' x y := by
    change ((D.1 : EndH3O) (octEmbedJ12LM (x + y))).a = _
    rw [octEmbedJ12LM.map_add, map_add]; rfl
  map_smul' r x := by
    change ((D.1 : EndH3O) (octEmbedJ12LM (r • x))).a = _
    rw [octEmbedJ12LM.map_smul, map_smul]; rfl

private def octKerPeirceSlotB (D : LinearMap.ker octPeirceShiftEv) : Module.End ℝ (CompactOctonion ℝ) where
  toFun y := ((D.1 : EndH3O) (H3Octonion.embedJ23 y)).b
  map_add' x y := by
    change ((D.1 : EndH3O) (octEmbedJ23LM (x + y))).b = _
    rw [octEmbedJ23LM.map_add, map_add]; rfl
  map_smul' r x := by
    change ((D.1 : EndH3O) (octEmbedJ23LM (r • x))).b = _
    rw [octEmbedJ23LM.map_smul, map_smul]; rfl

private def octKerPeirceSlotC (D : LinearMap.ker octPeirceShiftEv) : Module.End ℝ (CompactOctonion ℝ) where
  toFun z := ((D.1 : EndH3O) (H3Octonion.embedJ31 z)).c
  map_add' x y := by
    change ((D.1 : EndH3O) (octEmbedJ31LM (x + y))).c = _
    rw [octEmbedJ31LM.map_add, map_add]; rfl
  map_smul' r x := by
    change ((D.1 : EndH3O) (octEmbedJ31LM (r • x))).c = _
    rw [octEmbedJ31LM.map_smul, map_smul]; rfl

private theorem octKerPeirceSlotA_skew (D : LinearMap.ker octPeirceShiftEv) :
    octKerPeirceSlotA D ∈ octSkewAdjointSubmodule := by
  intro x y
  obtain ⟨hd1, hd2, _⟩ := (ker_octPeirceShiftEv_iff_diags_zero D.1).mp D.2
  have hslots := ker_octPeirceShiftEv_preserves_slots D
  have hleib := D.1.2 (embedJ12 x) (embedJ12 y)
  rw [oct_embedJ12_mul_embedJ12, map_smul, map_add, hd1, hd2, add_zero, smul_zero,
    hslots.1 x, hslots.1 y, oct_embedJ12_mul_embedJ12, oct_embedJ12_mul_embedJ12] at hleib
  have hα := congrArg H3Octonion.α₁ hleib.symm
  simp only [add_α₁, smul_α₁, h3o_diag1, h3o_diag2, diagCartan, add_zero, mul_one] at hα
  change (1 / 2 : ℝ) * CompactOctonion.bilin (octKerPeirceSlotA D x) y +
      (1 / 2 : ℝ) * CompactOctonion.bilin x (octKerPeirceSlotA D y) = 0 at hα
  rw [← mul_add] at hα
  exact (mul_eq_zero.mp hα).resolve_left (by norm_num)

private theorem octKerPeirceSlotC_skew (D : LinearMap.ker octPeirceShiftEv) :
    octKerPeirceSlotC D ∈ octSkewAdjointSubmodule := by
  intro x y
  obtain ⟨hd1, _, hd3⟩ := (ker_octPeirceShiftEv_iff_diags_zero D.1).mp D.2
  have hslots := ker_octPeirceShiftEv_preserves_slots D
  have hleib := D.1.2 (H3Octonion.embedJ31 x) (H3Octonion.embedJ31 y)
  rw [oct_embedJ31_mul_embedJ31, map_smul, map_add, hd3, hd1, add_zero, smul_zero,
    hslots.2.2 x, hslots.2.2 y, oct_embedJ31_mul_embedJ31, oct_embedJ31_mul_embedJ31] at hleib
  have hα := congrArg H3Octonion.α₁ hleib.symm
  simp only [add_α₁, smul_α₁, h3o_diag3, h3o_diag1, diagCartan, zero_add, mul_one] at hα
  change (1 / 2 : ℝ) * CompactOctonion.bilin (octKerPeirceSlotC D x) y +
      (1 / 2 : ℝ) * CompactOctonion.bilin x (octKerPeirceSlotC D y) = 0 at hα
  rw [← mul_add] at hα
  exact (mul_eq_zero.mp hα).resolve_left (by norm_num)

private def octKerPeirceResA : LinearMap.ker octPeirceShiftEv →ₗ[ℝ] octSkewAdjointSubmodule where
  toFun D := ⟨octKerPeirceSlotA D, octKerPeirceSlotA_skew D⟩
  map_add' _ _ := by apply Subtype.ext; apply LinearMap.ext; intro _; rfl
  map_smul' _ _ := by apply Subtype.ext; apply LinearMap.ext; intro _; rfl

private theorem octKerPeirceResA_injective : Function.Injective octKerPeirceResA := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  have hA0 : ∀ x, octKerPeirceSlotA D x = 0 := fun x =>
    congrArg (fun f : octSkewAdjointSubmodule => f.1 x) hD
  have hslots := ker_octPeirceShiftEv_preserves_slots D
  have hDA : ∀ x, (D.1 : EndH3O) (embedJ12 x) = 0 := fun x => by
    rw [hslots.1 x]; change embedJ12 (octKerPeirceSlotA D x) = 0; rw [hA0 x]; rfl
  have hleib12_23 : ∀ x y : CompactOctonion ℝ,
      octKerPeirceSlotC D (CompactOctonion.mul (CompactOctonion.conj y) (CompactOctonion.conj x)) =
        CompactOctonion.mul (CompactOctonion.conj (octKerPeirceSlotB D y)) (CompactOctonion.conj x) := by
    intro x y
    have h := D.1.2 (embedJ12 x) (H3Octonion.embedJ23 y)
    rw [oct_embedJ12_mul_embedJ23, map_smul, hslots.2.2, hDA x, zero_mul, zero_add,
      hslots.2.1 y, oct_embedJ12_mul_embedJ23] at h
    have hc' := congrArg H3Octonion.c h
    have hsub : (1 / 2 : ℝ) •
        (octKerPeirceSlotC D (CompactOctonion.mul (CompactOctonion.conj y) (CompactOctonion.conj x)) -
          CompactOctonion.mul (CompactOctonion.conj (octKerPeirceSlotB D y)) (CompactOctonion.conj x)) = 0 := by
      have hc'' : (1 / 2 : ℝ) •
          octKerPeirceSlotC D (CompactOctonion.mul (CompactOctonion.conj y) (CompactOctonion.conj x)) =
          (1 / 2 : ℝ) •
            CompactOctonion.mul (CompactOctonion.conj (octKerPeirceSlotB D y)) (CompactOctonion.conj x) := hc'
      rw [smul_sub, hc'', sub_self]
    exact sub_eq_zero.mp (half_oct_eq_zero_of_eq_zero hsub)
  let u : CompactOctonion ℝ := octKerPeirceSlotC D 1
  have htrace_u : CompactOctonion.trace u = 0 := by
    have hskew := octKerPeirceSlotC_skew D 1 1
    change CompactOctonion.bilin u 1 + CompactOctonion.bilin 1 u = 0 at hskew
    have hzb : CompactOctonion.bilin u 1 = CompactOctonion.trace u := by
      simp [CompactOctonion.bilin]
    have hsym : CompactOctonion.bilin 1 u = CompactOctonion.bilin u 1 := by
      simp [CompactOctonion.bilin]
    rw [hsym, hzb] at hskew
    linarith
  have hDC_mul : ∀ A B : CompactOctonion ℝ,
      octKerPeirceSlotC D (CompactOctonion.mul A B) = CompactOctonion.mul (octKerPeirceSlotC D A) B := by
    intro A B
    have h1 := hleib12_23 1 (CompactOctonion.conj A)
    rw [CompactOctonion.conj_one, CompactOctonion.conj_conj, CompactOctonion.mul_one,
      CompactOctonion.mul_one] at h1
    have h2 := hleib12_23 (CompactOctonion.conj B) (CompactOctonion.conj A)
    rw [CompactOctonion.conj_conj, CompactOctonion.conj_conj, ← h1] at h2
    exact h2
  have hDC_eq_left : ∀ B : CompactOctonion ℝ, octKerPeirceSlotC D B = CompactOctonion.mul u B := by
    intro B
    simpa [u, CompactOctonion.one_mul] using hDC_mul 1 B
  have hassoc_u : ∀ y z : CompactOctonion ℝ,
      CompactOctonion.mul (CompactOctonion.mul u y) z =
        CompactOctonion.mul u (CompactOctonion.mul y z) := by
    intro y z
    rw [← hDC_eq_left y, ← hDC_mul y z, hDC_eq_left (CompactOctonion.mul y z)]
  have hu0 : u = 0 := CompactOctonion.pureImaginary_left_nucleus_eq_zero u htrace_u hassoc_u
  have hC0 : ∀ z, octKerPeirceSlotC D z = 0 := fun z => by
    rw [hDC_eq_left z, hu0, CompactOctonion.zero_mul]
  have hB0 : ∀ y, octKerPeirceSlotB D y = 0 := fun y => by
    have h1 := hleib12_23 1 y
    rw [CompactOctonion.conj_one, CompactOctonion.mul_one, CompactOctonion.mul_one, hC0] at h1
    have h2 := congrArg CompactOctonion.conj h1.symm
    simpa [CompactOctonion.conj_conj, CompactOctonion.conj_zero] using h2
  obtain ⟨hd1, hd2, hd3⟩ := (ker_octPeirceShiftEv_iff_diags_zero D.1).mp D.2
  apply Subtype.ext; apply Subtype.ext; apply LinearMap.ext; intro w
  change (D.1 : EndH3O) w = 0
  rw [h3Octonion_decomp w]
  simp only [map_add, map_smul, hd1, hd2, hd3, smul_zero, add_zero, hDA w.a, zero_add]
  rw [hslots.2.1 w.b, hslots.2.2 w.c]
  change H3Octonion.embedJ23 (octKerPeirceSlotB D w.b) + H3Octonion.embedJ31 (octKerPeirceSlotC D w.c) = 0
  rw [hB0 w.b, hC0 w.c]
  have hj230 : H3Octonion.embedJ23 (0 : CompactOctonion ℝ) = 0 := rfl
  have hj310 : H3Octonion.embedJ31 (0 : CompactOctonion ℝ) = 0 := rfl
  rw [hj230, hj310, add_zero]

private def octDualBasis (i : Fin 8) : CompactOctonion ℝ :=
  (1 / 2 : ℝ) • CompactOctonion.basisVec i

private theorem octBilin_symm (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin x y = CompactOctonion.bilin y x :=
  CompactOctonion.trace_mul_conj_comm x y

private theorem octBilin_add_right (x y₁ y₂ : CompactOctonion ℝ) :
    CompactOctonion.bilin x (y₁ + y₂) =
      CompactOctonion.bilin x y₁ + CompactOctonion.bilin x y₂ := by
  simp [CompactOctonion.bilin, CompactOctonion.conj_add, CompactOctonion.mul_add,
    CompactOctonion.trace_add]

private theorem octBilin_smul_right (r : ℝ) (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin x (r • y) = r * CompactOctonion.bilin x y := by
  simp [CompactOctonion.bilin, CompactOctonion.conj_smul, CompactOctonion.mul_smul,
    CompactOctonion.trace_smul]

private theorem octBilin_basis_dual (i j : Fin 8) :
    CompactOctonion.bilin (CompactOctonion.basisVec i) (octDualBasis j) =
      if i = j then 1 else 0 := by
  dsimp [octDualBasis]
  rw [octBilin_smul_right, CompactOctonion.bilin_basis]
  split_ifs <;> norm_num

private theorem octBilin_dual_basis (i j : Fin 8) :
    CompactOctonion.bilin (octDualBasis i) (CompactOctonion.basisVec j) =
      if i = j then 1 else 0 := by
  rw [octBilin_symm, octBilin_basis_dual]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The 28 inner derivations generating the triality subalgebra `so(8) ≤ 𝔣₄(-52)`. -/
def octTrialityDeriv (k : Fin 28) : H3OctonionF4Derivations :=
  h3OctonionJordanInnerDerivation
    (embedJ12 (CompactOctonion.basisVec (trialityPair k).1))
    (embedJ12 (CompactOctonion.basisVec (trialityPair k).2))

theorem oct_inner12_embedJ12_a (x y z : CompactOctonion ℝ) :
    ((h3OctonionJordanInnerDerivation (embedJ12 x) (embedJ12 y) : EndH3O) (embedJ12 z)).a =
      (1 / 2 : ℝ) • (CompactOctonion.bilin y z • x - CompactOctonion.bilin x z • y) := by
  rw [h3OctonionJordanInnerDerivation_apply, oct_embedJ12_mul_embedJ12, oct_embedJ12_mul_embedJ12]
  simp only [mul_smul_comm, mul_add,
    _root_.mul_comm (embedJ12 x) h3o_diag1, _root_.mul_comm (embedJ12 x) h3o_diag2,
    _root_.mul_comm (embedJ12 y) h3o_diag1, _root_.mul_comm (embedJ12 y) h3o_diag2,
    h3o_diag1_mul_embedJ12, h3o_diag2_mul_embedJ12]
  have hhalf : (1 / 2 : ℝ) • embedJ12 x + (1 / 2 : ℝ) • embedJ12 x = embedJ12 x := by module
  have hhalf' : (1 / 2 : ℝ) • embedJ12 y + (1 / 2 : ℝ) • embedJ12 y = embedJ12 y := by module
  rw [hhalf, hhalf']
  change (1 / 2 * CompactOctonion.bilin y z) • x -
      (1 / 2 * CompactOctonion.bilin x z) • y =
    (1 / 2 : ℝ) • (CompactOctonion.bilin y z • x - CompactOctonion.bilin x z • y)
  rw [mul_smul, mul_smul, ← smul_sub]

private def octTrialitySeparatingCoord (k : Fin 28) : H3OctonionF4Derivations →ₗ[ℝ] ℝ where
  toFun D := CompactOctonion.bilin (octDualBasis (trialityPair k).1)
    (((D : EndH3O) (embedJ12 (octDualBasis (trialityPair k).2))).a)
  map_add' D E := by
    change CompactOctonion.bilin _ (((D : EndH3O) _ + (E : EndH3O) _).a) = _
    exact octBilin_add_right _ _ _
  map_smul' r D := by
    change CompactOctonion.bilin _ ((r • (D : EndH3O) _).a) = _
    exact octBilin_smul_right _ _ _

private theorem oct_bilin_diff_basis (a b c d : Fin 8) :
    CompactOctonion.bilin (octDualBasis c)
      ((1 / 2 : ℝ) • (CompactOctonion.bilin (CompactOctonion.basisVec b) (octDualBasis d) •
          CompactOctonion.basisVec a -
        CompactOctonion.bilin (CompactOctonion.basisVec a) (octDualBasis d) •
          CompactOctonion.basisVec b)) =
      (1 / 2 : ℝ) *
        ((if b = d then (1 : ℝ) else 0) * (if c = a then 1 else 0) -
          (if a = d then (1 : ℝ) else 0) * (if c = b then 1 else 0)) := by
  rw [octBilin_smul_right, show ∀ u v : CompactOctonion ℝ, u - v = u + (-1 : ℝ) • v by
    intro _ _; module, octBilin_add_right, octBilin_smul_right, octBilin_smul_right,
    octBilin_smul_right, octBilin_basis_dual, octBilin_basis_dual,
    octBilin_dual_basis, octBilin_dual_basis]
  ring

theorem octTrialityDeriv_linearIndependent :
    LinearIndependent ℝ octTrialityDeriv := by
  refine linearIndependent_of_separating_coordinate octTrialityDeriv octTrialitySeparatingCoord
    ?_ ?_
  · intro k
    dsimp [octTrialitySeparatingCoord]
    unfold octTrialityDeriv
    rw [oct_inner12_embedJ12_a, oct_bilin_diff_basis]
    have hne : (trialityPair k).1 ≠ (trialityPair k).2 := ne_of_lt (trialityPair_lt k)
    simp [hne]
  · intro k j hkj
    dsimp [octTrialitySeparatingCoord]
    unfold octTrialityDeriv
    rw [oct_inner12_embedJ12_a, oct_bilin_diff_basis]
    have hlt_j := trialityPair_lt j
    have hlt_k := trialityPair_lt k
    have htp_inj : Function.Injective trialityPair := by decide
    have hneq_pair : trialityPair j ≠ trialityPair k :=
      fun h => hkj (htp_inj h.symm)
    have ha0 : (if (trialityPair j).2 = (trialityPair k).2 then (1 : ℝ) else 0) *
        (if (trialityPair k).1 = (trialityPair j).1 then (1 : ℝ) else 0) = 0 := by
      by_cases h2 : (trialityPair j).2 = (trialityPair k).2
      · have h1 : (trialityPair k).1 ≠ (trialityPair j).1 :=
          fun h => hneq_pair (Prod.ext h.symm h2)
        simp [h2, h1]
      · simp [h2]
    have hb0 : (if (trialityPair j).1 = (trialityPair k).2 then (1 : ℝ) else 0) *
        (if (trialityPair k).1 = (trialityPair j).2 then (1 : ℝ) else 0) = 0 := by
      by_cases h12 : (trialityPair j).1 = (trialityPair k).2
      · have h21 : (trialityPair k).1 ≠ (trialityPair j).2 := by omega
        simp [h12, h21]
      · simp [h12]
    rw [ha0, hb0]
    norm_num

private theorem octTrialityDeriv_mem_ker_octPeirceShiftEv (k : Fin 28) :
    octTrialityDeriv k ∈ LinearMap.ker octPeirceShiftEv := by
  rw [ker_octPeirceShiftEv_iff_diags_zero]
  dsimp only [octTrialityDeriv]
  refine ⟨?_, ?_, ?_⟩ <;> rw [h3OctonionJordanInnerDerivation_apply]
  · rw [_root_.mul_comm (embedJ12 (CompactOctonion.basisVec (trialityPair k).2)) h3o_diag1,
      h3o_diag1_mul_embedJ12, mul_smul_comm, oct_embedJ12_mul_embedJ12,
      _root_.mul_comm (embedJ12 (CompactOctonion.basisVec (trialityPair k).1)) h3o_diag1,
      h3o_diag1_mul_embedJ12, mul_smul_comm, oct_embedJ12_mul_embedJ12,
      octBilin_symm (CompactOctonion.basisVec (trialityPair k).1)]
    module
  · rw [_root_.mul_comm (embedJ12 (CompactOctonion.basisVec (trialityPair k).2)) h3o_diag2,
      h3o_diag2_mul_embedJ12, mul_smul_comm, oct_embedJ12_mul_embedJ12,
      _root_.mul_comm (embedJ12 (CompactOctonion.basisVec (trialityPair k).1)) h3o_diag2,
      h3o_diag2_mul_embedJ12, mul_smul_comm, oct_embedJ12_mul_embedJ12,
      octBilin_symm (CompactOctonion.basisVec (trialityPair k).1)]
    module
  · rw [_root_.mul_comm (embedJ12 (CompactOctonion.basisVec (trialityPair k).2)) h3o_diag3,
      h3o_diag3_mul_embedJ12, mul_zero,
      _root_.mul_comm (embedJ12 (CompactOctonion.basisVec (trialityPair k).1)) h3o_diag3,
      h3o_diag3_mul_embedJ12, mul_zero, sub_self]

/-- **Unconditional 52D Dimension of Compact `𝔣₄(-52) = Der(H₃(𝕆))`**:
`Module.finrank ℝ H3OctonionF4Derivations = 52`. -/
theorem finrank_H3OctonionF4Derivations :
    Module.finrank ℝ H3OctonionF4Derivations = 52 := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker octPeirceShiftEv
  have h_range : LinearMap.range octPeirceShiftEv = ⊤ := by
    ext p
    simp only [Submodule.mem_top, iff_true, LinearMap.mem_range]
    exact ⟨octPeirceShiftSection p, octPeirceShiftEv_section p⟩
  rw [h_range, finrank_top, finrank_octTriple] at h_rn
  have hK_le : Module.finrank ℝ (LinearMap.ker octPeirceShiftEv) ≤ 28 :=
    (LinearMap.finrank_le_finrank_of_injective octKerPeirceResA_injective).trans
      finrank_octSkewAdjointSubmodule_le
  have hK_ge : 28 ≤ Module.finrank ℝ (LinearMap.ker octPeirceShiftEv) := by
    let S : Submodule ℝ (LinearMap.ker octPeirceShiftEv) :=
      Submodule.span ℝ (Set.range fun k : Fin 28 =>
        (⟨octTrialityDeriv k, octTrialityDeriv_mem_ker_octPeirceShiftEv k⟩ : LinearMap.ker octPeirceShiftEv))
    have hli : LinearIndependent ℝ (fun k : Fin 28 =>
        (⟨octTrialityDeriv k, octTrialityDeriv_mem_ker_octPeirceShiftEv k⟩ :
          LinearMap.ker octPeirceShiftEv)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hc' : ∑ k : Fin 28, c k • octTrialityDeriv k = 0 := by
        simpa [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using
          congrArg (Subtype.val : LinearMap.ker octPeirceShiftEv → H3OctonionF4Derivations) hc
      exact Fintype.linearIndependent_iff.mp octTrialityDeriv_linearIndependent c hc'
    have hfin := finrank_span_eq_card hli
    rw [Fintype.card_fin] at hfin
    exact hfin.symm.trans_le (Submodule.finrank_le S)
  have hK_eq : Module.finrank ℝ (LinearMap.ker octPeirceShiftEv) = 28 := le_antisymm hK_le hK_ge
  omega

end CompactF4DimensionClosure

section CompactE6AndStructureLieAlgebra

/-- Endomorphisms of `H3Octonion ℝ` annihilating the unit `1`. -/
def h3OctonionUnitAnnihilator : LieSubalgebra ℝ EndH3O where
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

@[simp] theorem mem_h3OctonionUnitAnnihilator (D : EndH3O) :
    D ∈ h3OctonionUnitAnnihilator ↔ D 1 = 0 := Iff.rfl

private theorem h3OctonionNormTrilin_one_one (x : H3Octonion ℝ) :
    h3OctonionNormTrilin x 1 1 = (1 / 3 : ℝ) * linearTrace x := by
  rw [h3OctonionNormTrilin_eq_trace_crossProduct, crossProduct_one]
  rw [traceBilin_sub_left, traceBilin_smul_left, traceBilin_symm 1 1, traceBilin_one_left,
    traceBilin_symm x 1, traceBilin_one_left, linearTrace_one]
  ring

private theorem h3OctonionNormTrilin_one_right (x y : H3Octonion ℝ) :
    6 * h3OctonionNormTrilin x y 1 = linearTrace x * linearTrace y - traceBilin x y := by
  rw [h3OctonionNormTrilin_eq_trace_crossProduct, traceBilin_one, mccrimmon_identity_16]
  ring

theorem h3Octonion_linearTrace_apply_eq_zero_of_cubic_unit
    (D : EndH3O) (hC : D ∈ TrilinearStabilizer.trilinearStabilizer h3OctonionNormTrilin)
    (h1 : D 1 = 0) (x : H3Octonion ℝ) : linearTrace (D x) = 0 := by
  have h := hC x 1 1
  simp only [h1, map_zero, LinearMap.zero_apply, add_zero] at h
  have h3 := h3OctonionNormTrilin_one_one (D x)
  linarith [h, h3]

theorem h3Octonion_traceBilin_infinitesimal_of_cubic_unit
    (D : EndH3O) (hC : D ∈ TrilinearStabilizer.trilinearStabilizer h3OctonionNormTrilin)
    (h1 : D 1 = 0) (x y : H3Octonion ℝ) :
    traceBilin (D x) y + traceBilin x (D y) = 0 := by
  have h := hC x y 1
  simp only [h1, map_zero, add_zero] at h
  have hx := h3OctonionNormTrilin_one_right (D x) y
  have hy := h3OctonionNormTrilin_one_right x (D y)
  rw [h3Octonion_linearTrace_apply_eq_zero_of_cubic_unit D hC h1 x, zero_mul, zero_sub] at hx
  rw [h3Octonion_linearTrace_apply_eq_zero_of_cubic_unit D hC h1 y, mul_zero, zero_sub] at hy
  linarith [h, hx, hy]

theorem h3Octonion_crossProduct_leibniz_of_cubic_unit
    (D : EndH3O) (hC : D ∈ TrilinearStabilizer.trilinearStabilizer h3OctonionNormTrilin)
    (h1 : D 1 = 0) (x y : H3Octonion ℝ) :
    D (crossProduct x y) = crossProduct (D x) y + crossProduct x (D y) := by
  apply eq_of_traceBilin_left_eq
  intro z
  rw [traceBilin_symm (D (H3Octonion.crossProduct x y)) z, traceBilin_symm _ z, traceBilin_add_right]
  have hb := h3Octonion_traceBilin_infinitesimal_of_cubic_unit D hC h1 z (crossProduct x y)
  have hc0 : traceBilin (crossProduct (D z) x) y + traceBilin (crossProduct z (D x)) y +
      traceBilin (crossProduct z x) (D y) = 0 := by
    have h0 := hC z x y
    simp only [h3OctonionNormTrilin_eq_trace_crossProduct] at h0
    linarith [h0]
  rw [mccrimmon_identity_15 (D z) x y, mccrimmon_identity_15 z (D x) y,
    mccrimmon_identity_15 z x (D y)] at hc0
  rw [traceBilin_symm (D z) (crossProduct x y)] at hc0
  rw [traceBilin_symm (D z) (crossProduct x y)] at hb
  linarith [hb, hc0]

theorem h3Octonion_jordanDerivation_of_cubic_unit
    (D : EndH3O) (hC : D ∈ TrilinearStabilizer.trilinearStabilizer h3OctonionNormTrilin)
    (h1 : D 1 = 0) : D ∈ H3OctonionF4Derivations := by
  intro x y
  have ht (z : H3Octonion ℝ) : linearTrace (D z) = 0 :=
    h3Octonion_linearTrace_apply_eq_zero_of_cubic_unit D hC h1 z
  have hc := h3Octonion_crossProduct_leibniz_of_cubic_unit D hC h1 x y
  have htc : linearTrace (crossProduct (D x) y) = -linearTrace (crossProduct x (D y)) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← linearTrace_add, ← hc]
    exact ht (crossProduct x y)
  change D (x * y) = D x * y + x * D y
  simp only [mul_trace_formula, map_smul, map_add, map_sub,
    h1, ht, hc, smul_zero, zero_smul, zero_add, add_zero, sub_zero]
  rw [htc]
  module

/-- Infinitesimal cubic stabilizer `𝔢₆(-26) = str₀(H₃(𝕆))` inside `End(H₃(𝕆))`. -/
def h3OctonionCubicStabilizer : LieSubalgebra ℝ EndH3O :=
  TrilinearStabilizer.trilinearStabilizer h3OctonionNormTrilin

private theorem symmetric_trilinear_eq_zero_oct
    (F : H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] ℝ)
    (h12 : ∀ x y z, F x y z = F y x z)
    (h23 : ∀ x y z, F x y z = F x z y)
    (hdiag : ∀ x, F x x x = 0) (x y z : H3Octonion ℝ) : F x y z = 0 := by
  have h13 (a b c : H3Octonion ℝ) : F a b c = F c b a := by rw [h12, h23, h12]
  have hpol : 6 * F x y z =
      F (x + y + z) (x + y + z) (x + y + z) -
      F (x + y) (x + y) (x + y) - F (x + z) (x + z) (x + z) -
      F (y + z) (y + z) (y + z) + F x x x + F y y y + F z z z := by
    simp only [map_add, LinearMap.add_apply]
    rw [h12 y x x, h23 x x y, h23 y y x, h12 y x y,
      h12 z x x, h23 x x z, h23 z z x, h12 z x z,
      h12 z y y, h23 y y z, h23 z z y, h12 z y z,
      h23 y z x, h12 y x z, h12 z x y, h23 x z y, h13 z y x]
    ring
  rw [hdiag, hdiag, hdiag, hdiag, hdiag, hdiag, hdiag] at hpol
  linarith [hpol]

theorem mem_h3OctonionCubicStabilizer_iff_traceBilin_adjointQuad (T : EndH3O) :
    T ∈ h3OctonionCubicStabilizer ↔
      ∀ x : H3Octonion ℝ, traceBilin (adjointQuad x) (T x) = 0 := by
  change (∀ x y z : H3Octonion ℝ,
      h3OctonionNormTrilin (T x) y z + h3OctonionNormTrilin x (T y) z +
        h3OctonionNormTrilin x y (T z) = 0) ↔
    ∀ x : H3Octonion ℝ, traceBilin (adjointQuad x) (T x) = 0
  let S : H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] ℝ :=
    h3OctonionNormTrilin.comp T +
      { toFun := fun x =>
          { toFun := fun y =>
              { toFun := fun z => h3OctonionNormTrilin x (T y) z + h3OctonionNormTrilin x y (T z)
                map_add' := fun z₁ z₂ => by simp only [map_add, add_add_add_comm]
                map_smul' := fun r z => by simp only [map_smul, smul_eq_mul, RingHom.id_apply, mul_add] }
            map_add' := fun y₁ y₂ => by
              ext z; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]; ring
            map_smul' := fun r y => by
              ext z; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                smul_eq_mul, RingHom.id_apply]; ring }
        map_add' := fun x₁ x₂ => by
          ext y z; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]; ring
        map_smul' := fun r x => by
          ext y z; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
            smul_eq_mul, RingHom.id_apply]; ring }
  have hS_eval (x y z : H3Octonion ℝ) :
      S x y z = h3OctonionNormTrilin (T x) y z + h3OctonionNormTrilin x (T y) z +
        h3OctonionNormTrilin x y (T z) := by
    dsimp [S]; ring
  have hS_diag (x : H3Octonion ℝ) : S x x x = traceBilin (adjointQuad x) (T x) := by
    rw [hS_eval]
    have hs1 : h3OctonionNormTrilin (T x) x x = h3OctonionNormTrilin x x (T x) := by
      rw [h3OctonionNormTrilin_symm_12, h3OctonionNormTrilin_symm_23]
    have hs2 : h3OctonionNormTrilin x (T x) x = h3OctonionNormTrilin x x (T x) :=
      h3OctonionNormTrilin_symm_23 x (T x) x
    rw [hs1, hs2, h3OctonionNormTrilin_eq_trace_crossProduct, crossProduct_self,
      traceBilin_smul_left]
    ring
  have hS_symm12 (x y z : H3Octonion ℝ) : S x y z = S y x z := by
    rw [hS_eval, hS_eval, h3OctonionNormTrilin_symm_12 (T x), h3OctonionNormTrilin_symm_12 x (T y),
      h3OctonionNormTrilin_symm_12 x y]
    ring
  have hS_symm23 (x y z : H3Octonion ℝ) : S x y z = S x z y := by
    rw [hS_eval, hS_eval, h3OctonionNormTrilin_symm_23 (T x), h3OctonionNormTrilin_symm_23 x (T y),
      h3OctonionNormTrilin_symm_23 x y]
    ring
  constructor
  · intro h x; rw [← hS_diag x, hS_eval]; exact h x x x
  · intro h x y z; rw [← hS_eval x y z]
    exact symmetric_trilinear_eq_zero_oct S hS_symm12 hS_symm23 (fun w => by rw [hS_diag, h w]) x y z

theorem H3OctonionF4Derivations_le_h3OctonionCubicStabilizer :
    H3OctonionF4Derivations ≤ h3OctonionCubicStabilizer := by
  intro D hD
  rw [mem_h3OctonionCubicStabilizer_iff_traceBilin_adjointQuad]
  intro x
  let D' : H3OctonionF4Derivations := ⟨D, hD⟩
  have h1 : traceBilin x (D'.1 (adjointQuad x)) = -traceBilin (adjointQuad x) (D'.1 x) := by
    have hs := h3Octonion_derivation_traceBilin_skew D' x (adjointQuad x)
    rw [traceBilin_symm (D'.1 x) (adjointQuad x)] at hs
    linarith [hs]
  have h2 : traceBilin x (D'.1 (adjointQuad x)) = 2 * traceBilin (adjointQuad x) (D'.1 x) := by
    rw [h3Octonion_derivation_adjointQuad D' x, traceBilin_symm, mccrimmon_identity_15,
      crossProduct_symm (D'.1 x) x, ← mccrimmon_identity_15, crossProduct_self,
      traceBilin_smul_left]
  linarith [h1, h2]

theorem h3Octonion_traceBilin_adjointQuad_jordanLmul (a x : H3Octonion ℝ) :
    traceBilin (adjointQuad x) (a * x) = normCubic x * linearTrace a := by
  calc traceBilin (adjointQuad x) (a * x) = traceBilin (x * a) (adjointQuad x) := by
        rw [_root_.mul_comm, traceBilin_symm]
    _ = traceBilin a (x * adjointQuad x) := h3Octonion_traceBilin_jordanLmul_assoc x a (adjointQuad x)
    _ = traceBilin a (normCubic x • (1 : H3Octonion ℝ)) := by
        rw [h3octonion_jordan_mul_adjoint_eq_norm_one x]
    _ = normCubic x * linearTrace a := by
        rw [traceBilin_smul_right, traceBilin_one, _root_.mul_comm]

theorem jordanLmul_mem_h3OctonionCubicStabilizer_iff (a : H3Octonion ℝ) :
    jordanLmul (R := ℝ) a ∈ h3OctonionCubicStabilizer ↔ linearTrace a = 0 := by
  rw [mem_h3OctonionCubicStabilizer_iff_traceBilin_adjointQuad]
  constructor
  · intro h
    have h1 := h 1
    rw [jordanLmul_apply, h3Octonion_traceBilin_adjointQuad_jordanLmul, normCubic_one, one_mul] at h1
    exact h1
  · intro ha x
    rw [jordanLmul_apply, h3Octonion_traceBilin_adjointQuad_jordanLmul, ha, mul_zero]

def h3OctonionLmulLinear : H3Octonion ℝ →ₗ[ℝ] EndH3O where
  toFun a := jordanLmul (R := ℝ) a
  map_add' a b := by apply LinearMap.ext; intro x; simp [jordanLmul_apply, add_mul]
  map_smul' r a := by apply LinearMap.ext; intro x; simp [jordanLmul_apply, smul_mul_assoc]

theorem h3OctonionLmulLinear_injective : Function.Injective h3OctonionLmulLinear := by
  intro a b h
  have h1 := LinearMap.ext_iff.mp h (1 : H3Octonion ℝ)
  simpa [h3OctonionLmulLinear, jordanLmul_apply, h3Octonion_mul_one] using h1

def h3OctonionLinearTraceLinear : H3Octonion ℝ →ₗ[ℝ] ℝ where
  toFun := linearTrace
  map_add' := linearTrace_add
  map_smul' := linearTrace_smul

def h3OctonionTraceZero : Submodule ℝ (H3Octonion ℝ) :=
  LinearMap.ker h3OctonionLinearTraceLinear

@[simp] theorem mem_h3OctonionTraceZero (a : H3Octonion ℝ) :
    a ∈ h3OctonionTraceZero ↔ linearTrace a = 0 := Iff.rfl

theorem finrank_h3OctonionTraceZero :
    Module.finrank ℝ h3OctonionTraceZero = 26 := by
  have hrange : LinearMap.range h3OctonionLinearTraceLinear = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro r
    refine ⟨(r / 3 : ℝ) • (1 : H3Octonion ℝ), ?_⟩
    simp only [h3OctonionLinearTraceLinear, LinearMap.coe_mk, AddHom.coe_mk, linearTrace_smul,
      linearTrace_one]
    ring
  have hrk := LinearMap.finrank_range_add_finrank_ker h3OctonionLinearTraceLinear
  rw [hrange, finrank_top, finrank_h3Octonion, Module.finrank_self] at hrk
  change 1 + Module.finrank ℝ h3OctonionTraceZero = 27 at hrk
  omega

def h3OctonionLmulTraceZeroSubmodule : Submodule ℝ EndH3O :=
  h3OctonionTraceZero.map h3OctonionLmulLinear

def h3OctonionCubicStabilizerDirectSumEquiv :
    (H3OctonionF4Derivations × h3OctonionTraceZero) ≃ₗ[ℝ] h3OctonionCubicStabilizer :=
  LinearEquiv.ofBijective
    { toFun := fun p =>
        ⟨p.1.1 + h3OctonionLmulLinear p.2.1,
          h3OctonionCubicStabilizer.add_mem
            (H3OctonionF4Derivations_le_h3OctonionCubicStabilizer p.1.2)
            ((jordanLmul_mem_h3OctonionCubicStabilizer_iff p.2.1).mpr p.2.2)⟩
      map_add' := fun p q => by
        apply Subtype.ext
        change (p.1.1 + q.1.1) + h3OctonionLmulLinear (p.2.1 + q.2.1) =
          (p.1.1 + h3OctonionLmulLinear p.2.1) + (q.1.1 + h3OctonionLmulLinear q.2.1)
        rw [map_add]; abel
      map_smul' := fun r p => by
        apply Subtype.ext
        change (r • p.1).1 + h3OctonionLmulLinear (r • p.2.1) =
          r • (p.1.1 + h3OctonionLmulLinear p.2.1)
        rw [map_smul, smul_add]; rfl }
    ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨D, a⟩ h
      have h0 : D.1 + h3OctonionLmulLinear a.1 = 0 := congrArg Subtype.val h
      have h1 := LinearMap.ext_iff.mp h0 (1 : H3Octonion ℝ)
      have ha1 : a.1 = 0 := by
        change D.1 1 + a.1 * (1 : H3Octonion ℝ) = 0 at h1
        rw [h3Octonion_derivation_apply_one_eq_zero D, zero_add, h3Octonion_mul_one] at h1
        exact h1
      have ha : a = 0 := Subtype.ext ha1
      have hD : D = 0 := by
        apply Subtype.ext; rw [ha1, map_zero, add_zero] at h0; exact h0
      exact Prod.ext hD ha,
    by
      rintro ⟨T, hT⟩
      let a : H3Octonion ℝ := T 1
      have ha_tr : a ∈ h3OctonionTraceZero := by
        rw [mem_h3OctonionTraceZero]
        have h111 := hT 1 1 1
        have hs1 : h3OctonionNormTrilin 1 a 1 = h3OctonionNormTrilin a 1 1 :=
          h3OctonionNormTrilin_symm_12 1 a 1
        have hs2 : h3OctonionNormTrilin 1 1 a = h3OctonionNormTrilin a 1 1 := by
          rw [h3OctonionNormTrilin_symm_23, h3OctonionNormTrilin_symm_12]
        have h3 : h3OctonionNormTrilin a 1 1 = 0 := by dsimp [a]; linarith [h111, hs1, hs2]
        have h11 := h3OctonionNormTrilin_one_one a
        linarith [h3, h11]
      let D : EndH3O := T - h3OctonionLmulLinear a
      have hD_F4 : D ∈ H3OctonionF4Derivations := by
        apply h3Octonion_jordanDerivation_of_cubic_unit
        · exact h3OctonionCubicStabilizer.sub_mem hT
            ((jordanLmul_mem_h3OctonionCubicStabilizer_iff a).mpr ha_tr)
        · change T 1 - a * (1 : H3Octonion ℝ) = 0
          rw [h3Octonion_mul_one, sub_self]
      refine ⟨(⟨D, hD_F4⟩, ⟨a, ha_tr⟩), ?_⟩
      apply Subtype.ext; dsimp [D]; abel⟩

/-- **Certified 78D Exact Dimension of Compact `𝔢₆(-26) = str₀(H₃(𝕆))`**:
`Module.finrank ℝ h3OctonionCubicStabilizer = 78`. -/
theorem finrank_h3OctonionCubicStabilizer :
    Module.finrank ℝ h3OctonionCubicStabilizer = 78 := by
  rw [← LinearEquiv.finrank_eq h3OctonionCubicStabilizerDirectSumEquiv, Module.finrank_prod,
    finrank_H3OctonionF4Derivations, finrank_h3OctonionTraceZero]

def h3OctonionStructureOperator (D : H3OctonionF4Derivations) (a : H3Octonion ℝ) : EndH3O :=
  D.1 + jordanLmul (R := ℝ) a

private theorem h3OctonionStructureOperator_lie_formula
    (D E : H3OctonionF4Derivations) (a b : H3Octonion ℝ) :
    ⁅h3OctonionStructureOperator D a, h3OctonionStructureOperator E b⁆ =
      (⁅D, E⁆ : H3OctonionF4Derivations).1 +
        (h3OctonionJordanInnerDerivation a b).1 +
        jordanLmul (R := ℝ) (D.1 b - E.1 a) := by
  dsimp [h3OctonionStructureOperator]
  have hDE_add : (D.1 + jordanLmul (R := ℝ) a) * (E.1 + jordanLmul (R := ℝ) b) -
      (E.1 + jordanLmul (R := ℝ) b) * (D.1 + jordanLmul (R := ℝ) a) =
      (D.1 * E.1 - E.1 * D.1) + (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b -
        jordanLmul (R := ℝ) b * jordanLmul (R := ℝ) a) +
      ((D.1 * jordanLmul (R := ℝ) b - jordanLmul (R := ℝ) b * D.1) -
        (E.1 * jordanLmul (R := ℝ) a - jordanLmul (R := ℝ) a * E.1)) := by
    simp only [add_mul, mul_add]; abel
  have hDL : ∀ (K : H3OctonionF4Derivations) (u : H3Octonion ℝ),
      K.1 * jordanLmul (R := ℝ) u - jordanLmul (R := ℝ) u * K.1 =
        jordanLmul (R := ℝ) (K.1 u) := by
    intro K u
    apply LinearMap.ext; intro x
    change K.1 (u * x) - u * K.1 x = K.1 u * x
    rw [K.2 u x]; abel
  change (D.1 + jordanLmul (R := ℝ) a) * (E.1 + jordanLmul (R := ℝ) b) -
      (E.1 + jordanLmul (R := ℝ) b) * (D.1 + jordanLmul (R := ℝ) a) = _
  rw [hDE_add, hDL D b, hDL E a]
  congr 1
  apply LinearMap.ext; intro x
  simp [jordanLmul_apply]
  -- wait: check sign of [D, E] + [L_a, L_b] + L_{Db - Ea}
  -- (L_a * L_b - L_b * L_a) x = a * (b * x) - b * (a * x) = inner a b x
  -- L_{Db} - L_{Ea} = L_{Db - Ea}
  change (h3OctonionLmulLinear (D.1 b)) x - (h3OctonionLmulLinear (E.1 a)) x =
    (h3OctonionLmulLinear (D.1 b - E.1 a)) x
  rw [LinearMap.map_sub, LinearMap.sub_apply]

/-- Full 79-dimensional structure Lie algebra `str(H₃(𝕆)) = 𝔣₄(-52) ⊕ L(H₃(𝕆))`. -/
def h3OctonionStructureLieSubalgebra : LieSubalgebra ℝ EndH3O where
  carrier := {T | ∃ (D : H3OctonionF4Derivations) (a : H3Octonion ℝ),
    T = h3OctonionStructureOperator D a}
  zero_mem' := ⟨0, 0, by
    apply LinearMap.ext; intro x
    simp [h3OctonionStructureOperator, jordanLmul_apply, zero_mul]⟩
  add_mem' := by
    rintro _ _ ⟨D, a, rfl⟩ ⟨E, b, rfl⟩
    refine ⟨D + E, a + b, ?_⟩
    apply LinearMap.ext; intro x
    simp [h3OctonionStructureOperator, jordanLmul_apply, add_mul]; abel
  smul_mem' := by
    rintro r _ ⟨D, a, rfl⟩
    refine ⟨r • D, r • a, ?_⟩
    apply LinearMap.ext; intro x
    simp [h3OctonionStructureOperator, jordanLmul_apply, smul_mul_assoc, smul_add]
  lie_mem' := by
    rintro _ _ ⟨D, a, rfl⟩ ⟨E, b, rfl⟩
    refine ⟨⁅D, E⁆ + h3OctonionJordanInnerDerivation a b, D.1 b - E.1 a, ?_⟩
    rw [h3OctonionStructureOperator_lie_formula]
    rfl

def h3OctonionStructureDirectSumEquiv :
    (H3OctonionF4Derivations × H3Octonion ℝ) ≃ₗ[ℝ] h3OctonionStructureLieSubalgebra :=
  LinearEquiv.ofBijective
    { toFun := fun p =>
        ⟨h3OctonionStructureOperator p.1 p.2, p.1, p.2, rfl⟩
      map_add' := fun p q => by
        apply Subtype.ext; apply LinearMap.ext; intro x
        simp [h3OctonionStructureOperator, jordanLmul_apply, add_mul]; abel
      map_smul' := fun r p => by
        apply Subtype.ext; apply LinearMap.ext; intro x
        simp [h3OctonionStructureOperator, jordanLmul_apply, smul_mul_assoc, smul_add] }
    ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨D, a⟩ h
      have h0 : h3OctonionStructureOperator D a = 0 := congrArg Subtype.val h
      have h1 := LinearMap.ext_iff.mp h0 (1 : H3Octonion ℝ)
      have ha : a = 0 := by
        change D.1 1 + a * (1 : H3Octonion ℝ) = 0 at h1
        rw [h3Octonion_derivation_apply_one_eq_zero D, zero_add, h3Octonion_mul_one] at h1
        exact h1
      have hD : D = 0 := by
        apply Subtype.ext; dsimp [h3OctonionStructureOperator] at h0
        rw [ha] at h0
        have hl0 : jordanLmul (R := ℝ) (0 : H3Octonion ℝ) = 0 := by
          apply LinearMap.ext; intro x; simp [jordanLmul_apply]
        rw [hl0, add_zero] at h0; exact h0
      exact Prod.ext hD ha,
    by
      rintro ⟨T, D, a, rfl⟩
      exact ⟨(D, a), rfl⟩⟩

/-- **Certified 79D Exact Dimension of `str(H₃(𝕆)) = h3OctonionStructureLieSubalgebra`**:
`Module.finrank ℝ h3OctonionStructureLieSubalgebra = 79`. -/
theorem finrank_h3OctonionStructureLieSubalgebra :
    Module.finrank ℝ h3OctonionStructureLieSubalgebra = 79 := by
  rw [← LinearEquiv.finrank_eq h3OctonionStructureDirectSumEquiv, Module.finrank_prod,
    finrank_H3OctonionF4Derivations, finrank_h3Octonion]

end CompactE6AndStructureLieAlgebra

section RealFormTraceSquareSignatures

private def octOpDualWeight (k : Fin 27) : ℝ :=
  if k.val < 3 then 1 else 1 / 2

private def octOpDualVec (k : Fin 27) : H3Octonion ℝ :=
  if k.val < 3 then H3Octonion.basisVec k else (1 / 2 : ℝ) • H3Octonion.basisVec k

private theorem octOpDualWeight_pos (k : Fin 27) : 0 < octOpDualWeight k := by
  dsimp [octOpDualWeight]; split_ifs <;> norm_num

private theorem traceBilin_basisVec_octOpDualVec (j k : Fin 27) :
    traceBilin (H3Octonion.basisVec j) (octOpDualVec k) = if j = k then 1 else 0 := by
  have hbas_diag_zero : ∀ m : Fin 27, ¬m.val < 3 →
      (H3Octonion.basisVec m).α₁ = 0 ∧ (H3Octonion.basisVec m).α₂ = 0 ∧
        (H3Octonion.basisVec m).α₃ = 0 := by
    intro m hm
    have hm0 : m.val ≠ 0 := by omega
    have hm1 : m.val ≠ 1 := by omega
    have hm2 : m.val ≠ 2 := by omega
    dsimp [H3Octonion.basisVec]
    simp only [hm0, hm1, hm2, ↓reduceIte]
    split_ifs <;> refine ⟨rfl, rfl, rfl⟩
  have hsub : ∀ d : H3Octonion ℝ, (d.a = 0 ∧ d.b = 0 ∧ d.c = 0) →
      ∀ m : Fin 27, ¬m.val < 3 → traceBilin d (H3Octonion.basisVec m) = 0 := by
    rintro d ⟨ha, hb, hc⟩ m hm
    obtain ⟨h1, h2, h3⟩ := hbas_diag_zero m hm
    simp [traceBilin, ha, hb, hc, h1, h2, h3]
  have h12_23 (u v : CompactOctonion ℝ) :
      traceBilin (embedJ12 u) (H3Octonion.embedJ23 v) = 0 := by
    change (0 : ℝ) * 0 + 0 * 0 + 0 * 0 + trace (mul u (conj 0)) + trace (mul 0 (conj v)) +
      trace (mul 0 (conj 0)) = 0
    simp only [CompactOctonion.conj_zero, CompactOctonion.mul_zero, CompactOctonion.zero_mul, trace_zero]
    ring
  have h12_31 (u v : CompactOctonion ℝ) :
      traceBilin (embedJ12 u) (H3Octonion.embedJ31 v) = 0 := by
    change (0 : ℝ) * 0 + 0 * 0 + 0 * 0 + trace (mul u (conj 0)) + trace (mul 0 (conj 0)) +
      trace (mul 0 (conj v)) = 0
    simp only [CompactOctonion.conj_zero, CompactOctonion.mul_zero, CompactOctonion.zero_mul, trace_zero]
    ring
  have h23_31 (u v : CompactOctonion ℝ) :
      traceBilin (H3Octonion.embedJ23 u) (H3Octonion.embedJ31 v) = 0 := by
    change (0 : ℝ) * 0 + 0 * 0 + 0 * 0 + trace (mul 0 (conj 0)) + trace (mul u (conj 0)) +
      trace (mul 0 (conj v)) = 0
    simp only [CompactOctonion.conj_zero, CompactOctonion.mul_zero, CompactOctonion.zero_mul, trace_zero]
    ring
  dsimp [octOpDualVec]
  by_cases hj3 : j.val < 3 <;> by_cases hk3 : k.val < 3
  · rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by omega) with hj0 | hj0 | hj0 <;>
      rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with hk0 | hk0 | hk0 <;>
      simp [H3Octonion.basisVec, traceBilin, diagCartan, Fin.ext_iff, hj0, hk0]
  · simp only [hk3, ↓reduceIte, traceBilin_smul_right]
    have hne : j ≠ k := fun h => hk3 (h ▸ hj3)
    simp only [hne, ↓reduceIte]
    have hj0 : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    have h0 : traceBilin (H3Octonion.basisVec j) (H3Octonion.basisVec k) = 0 := by
      rcases hj0 with h0 | h1 | h2
      · have : H3Octonion.basisVec j = diagCartan 1 0 0 := by simp [H3Octonion.basisVec, h0]
        rw [this]; exact hsub _ ⟨rfl, rfl, rfl⟩ k hk3
      · have : H3Octonion.basisVec j = diagCartan 0 1 0 := by simp [H3Octonion.basisVec, h1]
        rw [this]; exact hsub _ ⟨rfl, rfl, rfl⟩ k hk3
      · have : H3Octonion.basisVec j = diagCartan 0 0 1 := by simp [H3Octonion.basisVec, h2]
        rw [this]; exact hsub _ ⟨rfl, rfl, rfl⟩ k hk3
    rw [h0, mul_zero]
  · have hne : j ≠ k := fun h => hj3 (h ▸ hk3)
    simp only [hk3, ↓reduceIte, hne]
    rw [traceBilin_symm]
    have hk0 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
    rcases hk0 with h0 | h1 | h2
    · have : H3Octonion.basisVec k = diagCartan 1 0 0 := by simp [H3Octonion.basisVec, h0]
      rw [this]; exact hsub _ ⟨rfl, rfl, rfl⟩ j hj3
    · have : H3Octonion.basisVec k = diagCartan 0 1 0 := by simp [H3Octonion.basisVec, h1]
      rw [this]; exact hsub _ ⟨rfl, rfl, rfl⟩ j hj3
    · have : H3Octonion.basisVec k = diagCartan 0 0 1 := by simp [H3Octonion.basisVec, h2]
      rw [this]; exact hsub _ ⟨rfl, rfl, rfl⟩ j hj3
  · simp only [hk3, ↓reduceIte, traceBilin_smul_right]
    have hne012 : ∀ (m : Fin 27), ¬m.val < 3 → m.val ≠ 0 ∧ m.val ≠ 1 ∧ m.val ≠ 2 := fun m hm => by omega
    rcases hne012 j hj3 with ⟨hj0, hj1, hj2⟩
    rcases hne012 k hk3 with ⟨hk0, hk1, hk2⟩
    by_cases hj11 : j.val < 11 <;> by_cases hk11 : k.val < 11
    · have hb : H3Octonion.basisVec j = embedJ12 (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩) := by
        simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11]
      have hc : H3Octonion.basisVec k = embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
        simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11]
      rw [hb, hc]
      have htb : traceBilin (embedJ12 (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩))
          (embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩)) =
          CompactOctonion.bilin (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩)
            (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
        simp [traceBilin, embedJ12, CompactOctonion.bilin]
      rw [htb, CompactOctonion.bilin_basis]
      have hij : (⟨j.val - 3, by omega⟩ : Fin 8) = ⟨k.val - 3, by omega⟩ ↔ j = k := by
        constructor
        · intro h; ext; have := congrArg Fin.val h; dsimp at this; omega
        · intro h; subst h; rfl
      by_cases hjk : j = k
      · subst hjk; simp
      · simp only [mt hij.mp hjk, hjk, ↓reduceIte]; norm_num
    · have hjne : j ≠ k := fun h => hk11 (h ▸ hj11)
      simp only [hjne, ↓reduceIte]
      have hb : H3Octonion.basisVec j = embedJ12 (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩) := by
        simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11]
      by_cases hk19 : k.val < 19
      · have hc : H3Octonion.basisVec k = H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
          simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc, h12_23, mul_zero]
      · have hc : H3Octonion.basisVec k = H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
          simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc, h12_31, mul_zero]
    · have hjne : j ≠ k := fun h => hj11 (h ▸ hk11)
      simp only [hjne, ↓reduceIte]
      have hc : H3Octonion.basisVec k = embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
        simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11]
      by_cases hj19 : j.val < 19
      · have hb : H3Octonion.basisVec j = H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩) := by
          simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11, hj19]
        rw [hb, hc, traceBilin_symm, h12_23, mul_zero]
      · have hb : H3Octonion.basisVec j = H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩) := by
          simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11, hj19]
        rw [hb, hc, traceBilin_symm, h12_31, mul_zero]
    · by_cases hj19 : j.val < 19 <;> by_cases hk19 : k.val < 19
      · have hb : H3Octonion.basisVec j = H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩) := by
          simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11, hj19]
        have hc : H3Octonion.basisVec k = H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
          simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc]
        have htb : traceBilin (H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩))
            (H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩)) =
            CompactOctonion.bilin (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩)
              (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
          simp [traceBilin, H3Octonion.embedJ23, CompactOctonion.bilin]
        rw [htb, CompactOctonion.bilin_basis]
        have hij : (⟨j.val - 11, by omega⟩ : Fin 8) = ⟨k.val - 11, by omega⟩ ↔ j = k := by
          constructor
          · intro h; ext; have := congrArg Fin.val h; dsimp at this; omega
          · intro h; subst h; rfl
        by_cases hjk : j = k
        · subst hjk; simp
        · simp only [mt hij.mp hjk, hjk, ↓reduceIte]; norm_num
      · have hjne : j ≠ k := fun h => hk19 (h ▸ hj19)
        simp only [hjne, ↓reduceIte]
        have hb : H3Octonion.basisVec j = H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩) := by
          simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11, hj19]
        have hc : H3Octonion.basisVec k = H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
          simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc, h23_31, mul_zero]
      · have hjne : j ≠ k := fun h => hj19 (h ▸ hk19)
        simp only [hjne, ↓reduceIte]
        have hb : H3Octonion.basisVec j = H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩) := by
          simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11, hj19]
        have hc : H3Octonion.basisVec k = H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
          simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc, traceBilin_symm, h23_31, mul_zero]
      · have hb : H3Octonion.basisVec j = H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩) := by
          simp [H3Octonion.basisVec, hj0, hj1, hj2, hj11, hj19]
        have hc : H3Octonion.basisVec k = H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
          simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc]
        have htb : traceBilin (H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩))
            (H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩)) =
            CompactOctonion.bilin (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩)
              (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
          simp [traceBilin, H3Octonion.embedJ31, CompactOctonion.bilin]
        rw [htb, CompactOctonion.bilin_basis]
        have hij : (⟨j.val - 19, by omega⟩ : Fin 8) = ⟨k.val - 19, by omega⟩ ↔ j = k := by
          constructor
          · intro h; ext; have := congrArg Fin.val h; dsimp at this; omega
          · intro h; subst h; rfl
        by_cases hjk : j = k
        · subst hjk; simp
        · simp only [mt hij.mp hjk, hjk, ↓reduceIte]; norm_num

private theorem h3OctonionBasis_repr_eq_traceBilin (y : H3Octonion ℝ) (k : Fin 27) :
    h3OctonionBasis.repr y k = traceBilin (octOpDualVec k) y := by
  have hcoord : h3OctonionBasis.repr y k = H3Octonion.coordFun y k := rfl
  rw [hcoord]
  conv_rhs => rw [H3Octonion.basisVec_decomposition y]
  have hsum_r : ∀ (s : Finset (Fin 27)) (u : H3Octonion ℝ) (B : Fin 27 → H3Octonion ℝ),
      traceBilin u (∑ j ∈ s, B j) = ∑ j ∈ s, traceBilin u (B j) := by
    intro s u B
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, traceBilin_add_right, ih]
  rw [hsum_r Finset.univ, Finset.sum_eq_single k]
  · rw [traceBilin_smul_right, traceBilin_symm, traceBilin_basisVec_octOpDualVec]
    simp only [↓reduceIte, mul_one]
  · intro j _ hjk
    rw [traceBilin_smul_right, traceBilin_symm, traceBilin_basisVec_octOpDualVec]
    simp only [hjk, ↓reduceIte, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private theorem h3Octonion_operatorTrace_eq_sum (A : EndH3O) :
    LinearMap.trace ℝ (H3Octonion ℝ) A =
      ∑ k : Fin 27, traceBilin (octOpDualVec k) (A (H3Octonion.basisVec k)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ h3OctonionBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, h3OctonionBasis_apply]
  refine Finset.sum_congr rfl fun k _ => h3OctonionBasis_repr_eq_traceBilin _ k

private theorem octOpDualVec_traceBilin_apply (k : Fin 27) (y : H3Octonion ℝ) :
    traceBilin (octOpDualVec k) y = octOpDualWeight k * traceBilin (H3Octonion.basisVec k) y := by
  dsimp [octOpDualVec, octOpDualWeight]
  split_ifs
  · rw [one_mul]
  · rw [traceBilin_smul_left]

/-- **Cartan Involution Signature on Compact `𝔣₄(-52)`**:
`Tr(D²) ≤ 0` for every `D ∈ H3OctonionF4Derivations`, and `Tr(D²) = 0 ↔ D = 0`. -/
theorem compactF4_trace_sq_nonpos (D : H3OctonionF4Derivations) :
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) ≤ 0 := by
  rw [h3Octonion_operatorTrace_eq_sum]
  have hterm : ∀ k : Fin 27,
      traceBilin (octOpDualVec k) ((D.1 * D.1) (H3Octonion.basisVec k)) =
        -(octOpDualWeight k * traceBilin (D.1 (H3Octonion.basisVec k)) (D.1 (H3Octonion.basisVec k))) := by
    intro k
    change traceBilin (octOpDualVec k) (D.1 (D.1 (H3Octonion.basisVec k))) = _
    rw [octOpDualVec_traceBilin_apply]
    have hsk := h3Octonion_derivation_traceBilin_skew D (H3Octonion.basisVec k) (D.1 (H3Octonion.basisVec k))
    have hneg : traceBilin (H3Octonion.basisVec k) (D.1 (D.1 (H3Octonion.basisVec k))) =
        -traceBilin (D.1 (H3Octonion.basisVec k)) (D.1 (H3Octonion.basisVec k)) := by linarith [hsk]
    rw [hneg]; ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_neg_distrib, neg_nonpos]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (octOpDualWeight_pos k).le (traceBilin_self_nonneg _)

theorem compactF4_trace_sq_eq_zero_iff (D : H3OctonionF4Derivations) :
    LinearMap.trace ℝ (H3Octonion ℝ) (D.1 * D.1) = 0 ↔ D = 0 := by
  constructor
  · intro htr
    rw [h3Octonion_operatorTrace_eq_sum] at htr
    have hterm : ∀ k : Fin 27,
        traceBilin (octOpDualVec k) ((D.1 * D.1) (H3Octonion.basisVec k)) =
          -(octOpDualWeight k * traceBilin (D.1 (H3Octonion.basisVec k)) (D.1 (H3Octonion.basisVec k))) := by
      intro k
      change traceBilin (octOpDualVec k) (D.1 (D.1 (H3Octonion.basisVec k))) = _
      rw [octOpDualVec_traceBilin_apply]
      have hsk := h3Octonion_derivation_traceBilin_skew D (H3Octonion.basisVec k) (D.1 (H3Octonion.basisVec k))
      have hneg : traceBilin (H3Octonion.basisVec k) (D.1 (D.1 (H3Octonion.basisVec k))) =
          -traceBilin (D.1 (H3Octonion.basisVec k)) (D.1 (H3Octonion.basisVec k)) := by linarith [hsk]
      rw [hneg]; ring
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_neg_distrib, neg_eq_zero] at htr
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (octOpDualWeight_pos k).le (traceBilin_self_nonneg _)).mp htr
    have hbas : ∀ k : Fin 27, D.1 (H3Octonion.basisVec k) = 0 := by
      intro k
      have hk := hall k (Finset.mem_univ k)
      have htb0 : traceBilin (D.1 (H3Octonion.basisVec k)) (D.1 (H3Octonion.basisVec k)) = 0 :=
        (mul_eq_zero.mp hk).resolve_left (ne_of_gt (octOpDualWeight_pos k))
      exact (traceBilin_self_eq_zero_iff _).mp htb0
    apply Subtype.ext; apply LinearMap.ext; intro x
    rw [H3Octonion.basisVec_decomposition x, map_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [map_smul, hbas k, smul_zero]
  · rintro rfl
    simp

/-- **Cartan Involution Signature on `L(H₃(𝕆))` (`p`-part of `𝔢₆(-26)`)**:
`0 ≤ Tr(L_a²)`, with `Tr(L_a²) = 0 ↔ a = 0`. -/
theorem compactLmul_trace_sq_nonneg (a : H3Octonion ℝ) :
    0 ≤ LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) := by
  rw [h3Octonion_operatorTrace_eq_sum]
  have hterm : ∀ k : Fin 27,
      traceBilin (octOpDualVec k) ((jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) (H3Octonion.basisVec k)) =
        octOpDualWeight k * traceBilin (a * H3Octonion.basisVec k) (a * H3Octonion.basisVec k) := by
    intro k
    change traceBilin (octOpDualVec k) (a * (a * H3Octonion.basisVec k)) = _
    rw [octOpDualVec_traceBilin_apply, ← h3Octonion_traceBilin_jordanLmul_assoc]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (octOpDualWeight_pos k).le (traceBilin_self_nonneg _)

theorem compactLmul_trace_sq_eq_zero_iff (a : H3Octonion ℝ) :
    LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) = 0 ↔ a = 0 := by
  constructor
  · intro htr
    rw [h3Octonion_operatorTrace_eq_sum] at htr
    have hterm : ∀ k : Fin 27,
        traceBilin (octOpDualVec k) ((jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) (H3Octonion.basisVec k)) =
          octOpDualWeight k * traceBilin (a * H3Octonion.basisVec k) (a * H3Octonion.basisVec k) := by
      intro k
      change traceBilin (octOpDualVec k) (a * (a * H3Octonion.basisVec k)) = _
      rw [octOpDualVec_traceBilin_apply, ← h3Octonion_traceBilin_jordanLmul_assoc]
    rw [Finset.sum_congr rfl fun k _ => hterm k] at htr
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (octOpDualWeight_pos k).le (traceBilin_self_nonneg _)).mp htr
    have hbas : ∀ k : Fin 27, a * H3Octonion.basisVec k = 0 := by
      intro k
      have hk := hall k (Finset.mem_univ k)
      exact (traceBilin_self_eq_zero_iff _).mp
        ((mul_eq_zero.mp hk).resolve_left (ne_of_gt (octOpDualWeight_pos k)))
    have h0 : a * H3Octonion.basisVec 0 = 0 := hbas 0
    have h1 : a * H3Octonion.basisVec 1 = 0 := hbas 1
    have h2 : a * H3Octonion.basisVec 2 = 0 := hbas 2
    have hsum1 : H3Octonion.basisVec 0 + H3Octonion.basisVec 1 + H3Octonion.basisVec 2 =
        (1 : H3Octonion ℝ) := by
      apply ext_h3 <;> simp [H3Octonion.basisVec, diagCartan]
    have ha1 : a * (1 : H3Octonion ℝ) = 0 := by
      rw [← hsum1, mul_add, mul_add, h0, h1, h2, add_zero, add_zero]
    rwa [h3Octonion_mul_one] at ha1
  · rintro rfl
    have hl0 : jordanLmul (R := ℝ) (0 : H3Octonion ℝ) = 0 := by
      apply LinearMap.ext; intro x; simp [jordanLmul_apply]
    simp [hl0]

/-- Noncompact split witness inside `H3ZornF4Derivations` (`𝔣₄(4)`):
`splitF4TracePosWitness = [L_{E₁₂(e₀)}, L_{E₁₂(e₇)}]` has strictly positive
Killing trace-square `Tr(D²) = 3 / 2 > 0`, separating `𝔣₄(4)` from compact `𝔣₄(-52)`. -/
def splitF4TracePosWitness : H3ZornF4Derivations :=
  ⟨h3ZornJordanInnerDerivation (InfoGeometry.Algebra.h3_off₁₂ 0) (InfoGeometry.Algebra.h3_off₁₂ 7),
    h3ZornJordanInnerDerivation_mem_F4 _ _⟩

private theorem splitF4_witness_diag (d : Fin 3) :
    (splitF4TracePosWitness : Module.End ℝ (H3Zorn ℝ))
      (InfoGeometry.Algebra.h3ZornProbe ⟨d.val, by omega⟩) = 0 := by
  dsimp [splitF4TracePosWitness]
  change (h3ZornJordanInnerDerivation (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0))
      (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) : Module.End ℝ (H3Zorn ℝ)) _ = 0
  have hp : InfoGeometry.Algebra.h3ZornProbe ⟨d.val, by omega⟩ =
      match d.val with
      | 0 => InfoGeometry.Algebra.h3_diag₁
      | 1 => InfoGeometry.Algebra.h3_diag₂
      | _ => InfoGeometry.Algebra.h3_diag₃ := by
    fin_cases d <;> rfl
  rw [hp]
  fin_cases d <;> simp only [h3ZornJordanInnerDerivation_apply]
  · rw [_root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) InfoGeometry.Algebra.h3_diag₁,
      h3_diag₁_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12,
      _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) InfoGeometry.Algebra.h3_diag₁,
      h3_diag₁_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12, zornBilin_symm (zorn_basis 0)]
    module
  · rw [_root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) InfoGeometry.Algebra.h3_diag₂,
      h3_diag₂_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12,
      _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) InfoGeometry.Algebra.h3_diag₂,
      h3_diag₂_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12, zornBilin_symm (zorn_basis 0)]
    module
  · rw [_root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) InfoGeometry.Algebra.h3_diag₃,
      h3_diag₃_mul_embedJ12, mul_zero,
      _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) InfoGeometry.Algebra.h3_diag₃,
      h3_diag₃_mul_embedJ12, mul_zero, sub_self]

private theorem splitF4_witness_j12 (i : Fin 8) :
    (splitF4TracePosWitness : Module.End ℝ (H3Zorn ℝ))
      (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis i)) =
      if i = 0 then (1 / 2 : ℝ) • InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)
      else if i = 7 then (-1 / 2 : ℝ) • InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)
      else 0 := by
  rw [show (splitF4TracePosWitness : Module.End ℝ (H3Zorn ℝ)) =
    (h3ZornJordanInnerDerivation (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0))
      (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) : Module.End ℝ (H3Zorn ℝ)) from rfl]
  simp only [h3ZornJordanInnerDerivation_apply]
  rw [embedJ12_mul_embedJ12, embedJ12_mul_embedJ12, mul_smul_comm, mul_smul_comm,
    mul_add, mul_add,
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) InfoGeometry.Algebra.h3_diag₁,
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) InfoGeometry.Algebra.h3_diag₂,
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) InfoGeometry.Algebra.h3_diag₁,
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) InfoGeometry.Algebra.h3_diag₂]
  simp only [h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12]
  have hhalf0 : (1 / 2 : ℝ) • InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0) +
      (1 / 2 : ℝ) • InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0) =
      InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0) := by module
  have hhalf7 : (1 / 2 : ℝ) • InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7) +
      (1 / 2 : ℝ) • InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7) =
      InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7) := by module
  have hb7 : zornBilin (zorn_basis 7) (zorn_basis i) = if i = 0 then 1 else 0 := by
    fin_cases i <;> simp [zornBilin, zorn_basis, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVec3.dot]
  have hb0 : zornBilin (zorn_basis 0) (zorn_basis i) = if i = 7 then 1 else 0 := by
    fin_cases i <;> simp [zornBilin, zorn_basis, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVec3.dot]
  rw [hhalf0, hhalf7, hb7, hb0]
  by_cases hi0 : i = 0
  · subst hi0
    have h0ne7 : (0 : Fin 8) ≠ 7 := by decide
    simp only [h0ne7, ↓reduceIte]
    module
  · by_cases hi7 : i = 7
    · subst hi7
      simp only [hi0, ↓reduceIte]
      module
    · simp only [hi0, hi7, ↓reduceIte]
      module

private theorem splitF4_witness_j23 (i : Fin 8) :
    (splitF4TracePosWitness : Module.End ℝ (H3Zorn ℝ))
      (InfoGeometry.Algebra.embedJ23 (zorn_basis i)) =
      ((if i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 then (-1 / 4 : ℝ) else (1 / 4 : ℝ)) : ℝ) •
        InfoGeometry.Algebra.embedJ23 (zorn_basis i) := by
  have hconj0 : ZornVectorMatrix.conj (zorn_basis 0) = zorn_basis 7 := by
    ext k <;> (try fin_cases k) <;> simp [ZornVectorMatrix.conj, zorn_basis]
  have hconj7 : ZornVectorMatrix.conj (zorn_basis 7) = zorn_basis 0 := by
    ext k <;> (try fin_cases k) <;> simp [ZornVectorMatrix.conj, zorn_basis]
  have hz0_mul (x : ZornVectorMatrix ℝ) :
      ZornVectorMatrix.mul (zorn_basis 0) x = ⟨x.a, x.v, fun _ => 0, 0⟩ := by
    ext k <;>
      simp [ZornVectorMatrix.mul, zorn_basis, ZornVec3.dot, ZornVec3.cross]
  have hz7_mul (x : ZornVectorMatrix ℝ) :
      ZornVectorMatrix.mul (zorn_basis 7) x = ⟨0, fun _ => 0, x.w, x.b⟩ := by
    ext k <;>
      simp [ZornVectorMatrix.mul, zorn_basis, ZornVec3.dot, ZornVec3.cross]
  change (h3ZornJordanInnerDerivation (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0))
    (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) : Module.End ℝ (H3Zorn ℝ))
    (InfoGeometry.Algebra.embedJ23 (zorn_basis i)) = _
  simp only [h3ZornJordanInnerDerivation_apply]
  rw [embedJ12_mul_embedJ23, embedJ12_mul_embedJ23, mul_smul_comm, mul_smul_comm,
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) _,
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) _,
    embedJ31_mul_embedJ12, embedJ31_mul_embedJ12,
    ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
    ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
    hconj0, hconj7, hz7_mul, hz7_mul, hz0_mul, hz0_mul]
  fin_cases i
  all_goals
    apply H3Zorn.ext_h3 <;>
    (try ext k) <;>
    (try fin_cases k) <;>
    simp [InfoGeometry.Algebra.embedJ23, H3Zorn.sub_readback, H3Zorn.smul_readback, zorn_basis] <;>
    (try simp [ZornVectorMatrix.sub, ZornVectorMatrix.neg])
    norm_num

private theorem splitF4_witness_j31 (i : Fin 8) :
    (splitF4TracePosWitness : Module.End ℝ (H3Zorn ℝ))
      (InfoGeometry.Algebra.embedJ31 (zorn_basis i)) =
      ((if i.val = 0 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 then (-1 / 4 : ℝ) else (1 / 4 : ℝ)) : ℝ) •
        InfoGeometry.Algebra.embedJ31 (zorn_basis i) := by
  have hconj0 : ZornVectorMatrix.conj (zorn_basis 0) = zorn_basis 7 := by
    ext k <;> (try fin_cases k) <;> simp [ZornVectorMatrix.conj, zorn_basis]
  have hconj7 : ZornVectorMatrix.conj (zorn_basis 7) = zorn_basis 0 := by
    ext k <;> (try fin_cases k) <;> simp [ZornVectorMatrix.conj, zorn_basis]
  have hmul_z0 (x : ZornVectorMatrix ℝ) :
      ZornVectorMatrix.mul x (zorn_basis 0) = ⟨x.a, fun _ => 0, x.w, 0⟩ := by
    ext k <;>
      simp [ZornVectorMatrix.mul, zorn_basis, ZornVec3.dot, ZornVec3.cross]
  have hmul_z7 (x : ZornVectorMatrix ℝ) :
      ZornVectorMatrix.mul x (zorn_basis 7) = ⟨0, x.v, fun _ => 0, x.b⟩ := by
    ext k <;>
      simp [ZornVectorMatrix.mul, zorn_basis, ZornVec3.dot, ZornVec3.cross]
  change (h3ZornJordanInnerDerivation (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0))
    (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) : Module.End ℝ (H3Zorn ℝ))
    (InfoGeometry.Algebra.embedJ31 (zorn_basis i)) = _
  simp only [h3ZornJordanInnerDerivation_apply]
  rw [_root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7)) (InfoGeometry.Algebra.embedJ31 (zorn_basis i)),
    _root_.mul_comm (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0)) (InfoGeometry.Algebra.embedJ31 (zorn_basis i)),
    embedJ31_mul_embedJ12, embedJ31_mul_embedJ12, mul_smul_comm, mul_smul_comm,
    embedJ12_mul_embedJ23, embedJ12_mul_embedJ23,
    ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
    ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
    hconj0, hconj7, hmul_z7, hmul_z7, hmul_z0, hmul_z0]
  fin_cases i
  all_goals
    apply H3Zorn.ext_h3 <;>
    (try ext k) <;>
    (try fin_cases k) <;>
    simp [InfoGeometry.Algebra.embedJ31, H3Zorn.sub_readback, H3Zorn.smul_readback, zorn_basis] <;>
    (try simp [ZornVectorMatrix.sub, ZornVectorMatrix.neg])
    norm_num

private theorem splitF4_witness_diag_sq (k : Fin 27) :
    InfoGeometry.Algebra.h3ZornCoordinate
      ((splitF4TracePosWitness.1 * splitF4TracePosWitness.1)
        (InfoGeometry.Algebra.h3ZornProbe k)) k =
      if k.val = 3 ∨ k.val = 10 then (1 / 4 : ℝ)
      else if 11 ≤ k.val then (1 / 16 : ℝ)
      else 0 := by
  have hcoord_smul : ∀ (c : ℝ) (X : H3Zorn ℝ) (r : Fin 27),
      InfoGeometry.Algebra.h3ZornCoordinate (c • X) r =
        c * InfoGeometry.Algebra.h3ZornCoordinate X r := by
    intro c X r
    fin_cases r <;> rfl
  by_cases h3 : k.val < 3
  · have h0 := splitF4_witness_diag ⟨k.val, h3⟩
    have hsq : (splitF4TracePosWitness.1 * splitF4TracePosWitness.1)
        (InfoGeometry.Algebra.h3ZornProbe k) = 0 := by
      change splitF4TracePosWitness.1 (splitF4TracePosWitness.1
        (InfoGeometry.Algebra.h3ZornProbe k)) = 0
      rw [h0, map_zero]
    rw [hsq, h3ZornCoordinate_zero]
    have hnz1 : ¬(k.val = 3 ∨ k.val = 10) := by omega
    have hnz2 : ¬(11 ≤ k.val) := by omega
    simp [hnz1, hnz2]
  · by_cases h11 : k.val < 11
    · have hk : InfoGeometry.Algebra.h3ZornProbe k =
          InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis ⟨k.val - 3, by omega⟩) := by
        rcases k with ⟨m, hm⟩
        dsimp at h3 h11
        interval_cases m <;> rfl
      rw [hk]
      change InfoGeometry.Algebra.h3ZornCoordinate
        (splitF4TracePosWitness.1 (splitF4TracePosWitness.1
          (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis ⟨k.val - 3, by omega⟩)))) k = _
      rw [splitF4_witness_j12]
      by_cases hi0 : (⟨k.val - 3, by omega⟩ : Fin 8) = 0
      · have hk3 : k.val = 3 := by
          have := congrArg Fin.val hi0; dsimp at this; omega
        have h3or10 : k.val = 3 ∨ k.val = 10 := Or.inl hk3
        simp only [hi0, ↓reduceIte]
        rw [map_smul, splitF4_witness_j12]
        simp only [↓reduceIte, smul_smul,
          show InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 0) =
            InfoGeometry.Algebra.h3ZornProbe k from by
            rw [hk]; congr 2; exact hi0.symm,
          hcoord_smul, h3ZornProbe_coordinate_self, mul_one, h3or10]
        norm_num
      · by_cases hi7 : (⟨k.val - 3, by omega⟩ : Fin 8) = 7
        · have hk10 : k.val = 10 := by
            have := congrArg Fin.val hi7; dsimp at this; omega
          have h3or10 : k.val = 3 ∨ k.val = 10 := Or.inr hk10
          have h7ne0 : (7 : Fin 8) ≠ 0 := by decide
          simp only [hi7, h7ne0, ↓reduceIte]
          rw [map_smul, splitF4_witness_j12]
          simp only [h7ne0, ↓reduceIte, smul_smul,
            show InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis 7) =
              InfoGeometry.Algebra.h3ZornProbe k from by
              rw [hk]; congr 2; exact hi7.symm,
            hcoord_smul, h3ZornProbe_coordinate_self, mul_one, h3or10]
          norm_num
        · have hnz1 : ¬(k.val = 3 ∨ k.val = 10) := by
            have h1 : k.val ≠ 3 := fun h => hi0 (by ext; simp [h])
            have h2 : k.val ≠ 10 := fun h => hi7 (by ext; simp [h])
            tauto
          have hnz2 : ¬(11 ≤ k.val) := by omega
          simp only [hi0, hi7, ↓reduceIte, map_zero, h3ZornCoordinate_zero, hnz1, hnz2]
    · by_cases h19 : k.val < 19
      · have hk : InfoGeometry.Algebra.h3ZornProbe k =
            InfoGeometry.Algebra.embedJ23 (zorn_basis ⟨k.val - 11, by omega⟩) := by
          rcases k with ⟨m, hm⟩
          dsimp at h11 h19
          interval_cases m <;> rfl
        rw [hk]
        change InfoGeometry.Algebra.h3ZornCoordinate
          (splitF4TracePosWitness.1 (splitF4TracePosWitness.1
            (InfoGeometry.Algebra.embedJ23 (zorn_basis ⟨k.val - 11, by omega⟩)))) k = _
        rw [splitF4_witness_j23, map_smul, splitF4_witness_j23, smul_smul,
          ← hk, hcoord_smul, h3ZornProbe_coordinate_self, mul_one]
        have hnz1 : ¬(k.val = 3 ∨ k.val = 10) := by omega
        have h11' : 11 ≤ k.val := by omega
        simp only [hnz1, h11', ↓reduceIte]
        split_ifs <;> norm_num
      · have hk : InfoGeometry.Algebra.h3ZornProbe k =
            InfoGeometry.Algebra.embedJ31 (zorn_basis ⟨k.val - 19, by omega⟩) := by
          rcases k with ⟨m, hm⟩
          dsimp at h19
          interval_cases m <;> rfl
        rw [hk]
        change InfoGeometry.Algebra.h3ZornCoordinate
          (splitF4TracePosWitness.1 (splitF4TracePosWitness.1
            (InfoGeometry.Algebra.embedJ31 (zorn_basis ⟨k.val - 19, by omega⟩)))) k = _
        rw [splitF4_witness_j31, map_smul, splitF4_witness_j31, smul_smul,
          ← hk, hcoord_smul, h3ZornProbe_coordinate_self, mul_one]
        have hnz1 : ¬(k.val = 3 ∨ k.val = 10) := by omega
        have h11' : 11 ≤ k.val := by omega
        simp only [hnz1, h11', ↓reduceIte]
        split_ifs <;> norm_num

theorem splitF4TracePosWitness_trace_sq :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ InfoGeometry.Canonical.H3ZornBasis.h3ZornCoordinateBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    InfoGeometry.Canonical.H3ZornBasis.h3ZornCoordinateBasis_apply,
    InfoGeometry.Canonical.H3ZornBasis.h3ZornCoordinateBasis_repr_apply]
  rw [Finset.sum_congr rfl fun k _ => splitF4_witness_diag_sq k]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

theorem splitF4TracePosWitness_trace_sq_pos :
    0 < LinearMap.trace ℝ (H3Zorn ℝ)
      (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) := by
  rw [splitF4TracePosWitness_trace_sq]
  norm_num

end RealFormTraceSquareSignatures

end InfoGeometry.Algebra
