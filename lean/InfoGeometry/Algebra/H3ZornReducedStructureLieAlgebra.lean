/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornCubicOperatorGeometry
import InfoGeometry.Algebra.SplitAlbertStructureOperators
import InfoGeometry.Algebra.SplitAlbertJordanLmulTraceCoordinate
import InfoGeometry.Algebra.H3ZornAdjointProductIdentity
import InfoGeometry.Algebra.H3ZornF4DimensionClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# 78D Reduced Structure Lie Algebra `str₀(H₃(𝕆_s)) = 𝔣₄ ⊕ L(H₃⁰) = h3zornCubicStabilizer`
  and 79D Structure Lie Algebra `str(H₃(𝕆_s)) = 𝔣₄ ⊕ L(H₃)`

Directly on the full 27-dimensional split Albert Jordan algebra `H3Zorn ℝ`, this
module proves:

1. Exact operator-trace identity `LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul x) = 9 * linearTrace x`.
2. Every derivation `D ∈ H3ZornF4Derivations` has `linearTrace (D x) = 0`, is
   skew-adjoint for `traceBilin`, satisfies `D (x#) = x × (D x)`, and belongs to
   `h3zornCubicStabilizer`.
3. `jordanLmul (R := ℝ) a ∈ h3zornCubicStabilizer ↔ linearTrace a = 0`.
4. Exact direct-sum decompositions and certified dimensions:
   * `structureOperatorLieSubalgebra.toSubmodule = H3ZornF4Derivations.toSubmodule ⊕ h3zornLmulSubmodule`
     with `Module.finrank ℝ structureOperatorLieSubalgebra = 79`.
   * `h3zornCubicStabilizer.toSubmodule = H3ZornF4Derivations.toSubmodule ⊕ h3zornLmulTraceZeroSubmodule`
     with `Module.finrank ℝ h3zornCubicStabilizer = 78`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Algebra.SplitAlbertStructureOperators
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit

attribute [local instance 100] LieRing.ofAssociativeRing

private instance : Module.Finite ℝ (H3Zorn ℝ) :=
  Module.Finite.of_basis h3ZornCoordinateBasis

section OperatorTraceAndDerivations

private theorem h3Zorn_decomp (x : H3Zorn ℝ) :
    x = x.α₁ • h3_diag₁ + x.α₂ • h3_diag₂ + x.α₃ • h3_diag₃ +
      embedJ12 x.a + embedJ23 x.b + embedJ31 x.c := by
  apply ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
    add_readback, smul_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

private theorem h3Zorn_mul_diag₁_α₁ (x : H3Zorn ℝ) :
    (x * h3_diag₁).α₁ = x.α₁ := by
  conv_lhs => rw [h3Zorn_decomp x]
  simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_h3_diag₁,
    show h3_diag₂ * h3_diag₁ = 0 from by rw [mul_comm, h3_diag₁_mul_h3_diag₂],
    show h3_diag₃ * h3_diag₁ = 0 from by rw [mul_comm, h3_diag₁_mul_h3_diag₃],
    show embedJ12 x.a * h3_diag₁ = h3_diag₁ * embedJ12 x.a from mul_comm _ _,
    h3_diag₁_mul_embedJ12,
    show embedJ23 x.b * h3_diag₁ = h3_diag₁ * embedJ23 x.b from mul_comm _ _,
    h3_diag₁_mul_embedJ23,
    show embedJ31 x.c * h3_diag₁ = h3_diag₁ * embedJ31 x.c from mul_comm _ _,
    h3_diag₁_mul_embedJ31]
  simp [h3_diag₁, embedJ12, embedJ31, add_readback, smul_readback]

private theorem h3Zorn_mul_diag₂_α₂ (x : H3Zorn ℝ) :
    (x * h3_diag₂).α₂ = x.α₂ := by
  conv_lhs => rw [h3Zorn_decomp x]
  simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_h3_diag₂, h3_diag₂_mul_h3_diag₂,
    show h3_diag₃ * h3_diag₂ = 0 from by rw [mul_comm, h3_diag₂_mul_h3_diag₃],
    show embedJ12 x.a * h3_diag₂ = h3_diag₂ * embedJ12 x.a from mul_comm _ _,
    h3_diag₂_mul_embedJ12,
    show embedJ23 x.b * h3_diag₂ = h3_diag₂ * embedJ23 x.b from mul_comm _ _,
    h3_diag₂_mul_embedJ23,
    show embedJ31 x.c * h3_diag₂ = h3_diag₂ * embedJ31 x.c from mul_comm _ _,
    h3_diag₂_mul_embedJ31]
  simp [h3_diag₂, embedJ12, embedJ23, add_readback, smul_readback]

private theorem h3Zorn_mul_diag₃_α₃ (x : H3Zorn ℝ) :
    (x * h3_diag₃).α₃ = x.α₃ := by
  conv_lhs => rw [h3Zorn_decomp x]
  simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_h3_diag₃, h3_diag₂_mul_h3_diag₃,
    h3_diag₃_mul_h3_diag₃,
    show embedJ12 x.a * h3_diag₃ = h3_diag₃ * embedJ12 x.a from mul_comm _ _,
    h3_diag₃_mul_embedJ12,
    show embedJ23 x.b * h3_diag₃ = h3_diag₃ * embedJ23 x.b from mul_comm _ _,
    h3_diag₃_mul_embedJ23,
    show embedJ31 x.c * h3_diag₃ = h3_diag₃ * embedJ31 x.c from mul_comm _ _,
    h3_diag₃_mul_embedJ31]
  simp [h3_diag₃, embedJ23, embedJ31, add_readback, smul_readback]

private theorem h3Zorn_mul_embedJ12_a (x : H3Zorn ℝ) (z : ZornVectorMatrix ℝ) :
    (x * embedJ12 z).a = ((1 / 2 : ℝ) * (x.α₁ + x.α₂)) • z := by
  conv_lhs => rw [h3Zorn_decomp x]
  simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12,
    h3_diag₃_mul_embedJ12, embedJ12_mul_embedJ12,
    show embedJ23 x.b * embedJ12 z = embedJ12 z * embedJ23 x.b from mul_comm _ _,
    embedJ12_mul_embedJ23, embedJ31_mul_embedJ12]
  simp [h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31,
    add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.add] <;> ring

private theorem h3Zorn_mul_embedJ23_b (x : H3Zorn ℝ) (z : ZornVectorMatrix ℝ) :
    (x * embedJ23 z).b = ((1 / 2 : ℝ) * (x.α₂ + x.α₃)) • z := by
  conv_lhs => rw [h3Zorn_decomp x]
  simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_embedJ23, h3_diag₂_mul_embedJ23,
    h3_diag₃_mul_embedJ23, embedJ23_mul_embedJ23, embedJ12_mul_embedJ23,
    show embedJ31 x.c * embedJ23 z = embedJ23 z * embedJ31 x.c from mul_comm _ _,
    embedJ23_mul_embedJ31]
  simp [h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
    add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.add] <;> ring

private theorem h3Zorn_mul_embedJ31_c (x : H3Zorn ℝ) (z : ZornVectorMatrix ℝ) :
    (x * embedJ31 z).c = ((1 / 2 : ℝ) * (x.α₃ + x.α₁)) • z := by
  conv_lhs => rw [h3Zorn_decomp x]
  simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_embedJ31, h3_diag₂_mul_embedJ31,
    h3_diag₃_mul_embedJ31, embedJ31_mul_embedJ31, embedJ23_mul_embedJ31,
    show embedJ12 x.a * embedJ31 z = embedJ31 z * embedJ12 x.a from mul_comm _ _,
    embedJ31_mul_embedJ12]
  simp [h3_diag₃, h3_diag₁, embedJ12, embedJ23, embedJ31,
    add_readback, smul_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]
  ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.add] <;> ring

private theorem h3_off₁₂_eq_embedJ12 (i : Fin 8) :
    h3_off₁₂ i = embedJ12 (zorn_basis i) := rfl

private theorem h3_off₂₃_eq_embedJ23 (i : Fin 8) :
    h3_off₂₃ i = embedJ23 (zorn_basis i) := rfl

private theorem h3_off₃₁_eq_embedJ31 (i : Fin 8) :
    h3_off₃₁ i = embedJ31 (zorn_basis i) := rfl

/-- Exact relation between the native 27D operator trace of `L_x` and the scalar
Jordan trace: `Tr_{End}(L_x) = 9 * linearTrace x`. -/
theorem h3Zorn_jordanLmul_operatorTrace_eq_nine_linearTrace (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) x) = 9 * linearTrace x := by
  rw [LinearMap.trace_eq_matrix_trace ℝ h3ZornCoordinateBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    h3ZornCoordinateBasis_apply, h3ZornCoordinateBasis_repr_apply, jordanLmul_apply]
  have hs12 : ∀ (k : Fin 8),
      (h3ZornCoordinate (x * embedJ12 (zorn_basis k))) ⟨3 + k.val, by omega⟩ =
        (1 / 2 : ℝ) * (x.α₁ + x.α₂) := by
    intro k
    fin_cases k <;> dsimp [h3ZornCoordinate] <;> rw [h3Zorn_mul_embedJ12_a] <;>
      simp [ZornVectorMatrix.smul, zorn_basis]
  have hs23 : ∀ (k : Fin 8),
      (h3ZornCoordinate (x * embedJ23 (zorn_basis k))) ⟨11 + k.val, by omega⟩ =
        (1 / 2 : ℝ) * (x.α₂ + x.α₃) := by
    intro k
    fin_cases k <;> dsimp [h3ZornCoordinate] <;> rw [h3Zorn_mul_embedJ23_b] <;>
      simp [ZornVectorMatrix.smul, zorn_basis]
  have hs31 : ∀ (k : Fin 8),
      (h3ZornCoordinate (x * embedJ31 (zorn_basis k))) ⟨19 + k.val, by omega⟩ =
        (1 / 2 : ℝ) * (x.α₃ + x.α₁) := by
    intro k
    fin_cases k <;> dsimp [h3ZornCoordinate] <;> rw [h3Zorn_mul_embedJ31_c] <;>
      simp [ZornVectorMatrix.smul, zorn_basis]
  let diagVal : Fin 27 → ℝ := fun i =>
    match i.val with
    | 0 => x.α₁
    | 1 => x.α₂
    | 2 => x.α₃
    | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => (1 / 2 : ℝ) * (x.α₁ + x.α₂)
    | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 => (1 / 2 : ℝ) * (x.α₂ + x.α₃)
    | _ => (1 / 2 : ℝ) * (x.α₃ + x.α₁)
  have hdiag : ∀ i : Fin 27, h3ZornCoordinate (x * h3ZornProbe i) i = diagVal i := by
    intro i
    fin_cases i
    · exact h3Zorn_mul_diag₁_α₁ x
    · exact h3Zorn_mul_diag₂_α₂ x
    · exact h3Zorn_mul_diag₃_α₃ x
    · exact hs12 0
    · exact hs12 1
    · exact hs12 2
    · exact hs12 3
    · exact hs12 4
    · exact hs12 5
    · exact hs12 6
    · exact hs12 7
    · exact hs23 0
    · exact hs23 1
    · exact hs23 2
    · exact hs23 3
    · exact hs23 4
    · exact hs23 5
    · exact hs23 6
    · exact hs23 7
    · exact hs31 0
    · exact hs31 1
    · exact hs31 2
    · exact hs31 3
    · exact hs31 4
    · exact hs31 5
    · exact hs31 6
    · exact hs31 7
  rw [Finset.sum_congr rfl fun i _ => hdiag i]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, diagVal]
  change _ = 9 * (x.α₁ + x.α₂ + x.α₃)
  ring

/-- Every split-Albert derivation maps into the trace-zero hyperplane. -/
theorem h3ZornF4_derivation_linearTrace_zero (D : H3ZornF4Derivations) (x : H3Zorn ℝ) :
    linearTrace (D.1 x) = 0 := by
  have hop := h3ZornF4Derivation_jordanLmul_operatorTrace_zero D x
  rw [h3Zorn_jordanLmul_operatorTrace_eq_nine_linearTrace] at hop
  linarith

/-- Every split-Albert derivation is skew-adjoint with respect to `traceBilin`. -/
theorem h3ZornF4_derivation_traceBilin_skew (D : H3ZornF4Derivations) (x y : H3Zorn ℝ) :
    traceBilin (D.1 x) y + traceBilin x (D.1 y) = 0 := by
  rw [← h3Zorn_linearTrace_jordanMul (D.1 x) y, ← h3Zorn_linearTrace_jordanMul x (D.1 y),
    ← linearTrace_add, ← D.2 x y]
  exact h3ZornF4_derivation_linearTrace_zero D (x * y)

theorem h3Zorn_mul_self_eq_adjoint (x : H3Zorn ℝ) :
    x * x = linearTrace x • x - linearTrace (adjointQuad x) • (1 : H3Zorn ℝ) + adjointQuad x := by
  change candidateJordanMul x x = _
  rw [candidateJordanMul_trace_formula, crossProduct_self, linearTrace_smul]
  module

/-- Every split-Albert derivation differentiates the quadratic adjoint by
`D (x#) = x × (D x)`. -/
theorem h3ZornF4_derivation_adjointQuad (D : H3ZornF4Derivations) (x : H3Zorn ℝ) :
    D.1 (adjointQuad x) = crossProduct x (D.1 x) := by
  have h1 : D.1 1 = 0 := h3ZornF4_derivation_apply_one_eq_zero D
  have htr : linearTrace (D.1 x) = 0 := h3ZornF4_derivation_linearTrace_zero D x
  have hbil : traceBilin x (D.1 x) = 0 := by
    have hs := h3ZornF4_derivation_traceBilin_skew D x x
    rw [traceBilin_symm (D.1 x) x] at hs
    linarith
  have hsq : D.1 (x * x) = linearTrace x • D.1 x + D.1 (adjointQuad x) := by
    conv_lhs => rw [h3Zorn_mul_self_eq_adjoint x]
    simp only [map_add, map_sub, map_smul, h1, smul_zero, sub_zero]
  have hleib : D.1 (x * x) = linearTrace x • D.1 x + crossProduct x (D.1 x) := by
    rw [D.2 x x, mul_comm (D.1 x) x, ← two_smul ℝ (x * D.1 x)]
    change (2 : ℝ) • candidateJordanMul x (D.1 x) = _
    rw [candidateJordanMul_trace_formula, linearTrace_crossProduct, htr, hbil]
    simp only [zero_smul, mul_zero, sub_zero, add_zero]
    module
  have heq := hsq.symm.trans hleib
  exact add_left_cancel heq

private theorem symmetric_trilinear_eq_zero
    (F : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ)
    (h12 : ∀ x y z, F x y z = F y x z)
    (h23 : ∀ x y z, F x y z = F x z y)
    (hdiag : ∀ x, F x x x = 0) (x y z : H3Zorn ℝ) : F x y z = 0 := by
  have h13 (a b c : H3Zorn ℝ) : F a b c = F c b a := by
    rw [h12, h23, h12]
  have hpol : 6 * F x y z =
      F (x + y + z) (x + y + z) (x + y + z) -
      F (x + y) (x + y) (x + y) - F (x + z) (x + z) (x + z) -
      F (y + z) (y + z) (y + z) + F x x x + F y y y + F z z z := by
    simp only [map_add, LinearMap.add_apply]
    rw [h12 y x x, h23 x x y, h23 y y x, h12 y x y,
      h12 z x x, h23 x x z, h23 z z x, h12 z x z,
      h12 z y y, h23 y y z, h23 z z y, h12 z y z,
      h23 y z x, h12 y x z, h12 z x y, h23 x z y,
      h13 z y x]
    ring
  rw [hdiag, hdiag, hdiag, hdiag, hdiag, hdiag, hdiag] at hpol
  linarith

/-- Pointwise characterization of the infinitesimal cubic stabilizer `h3zornCubicStabilizer`:
`T ∈ h3zornCubicStabilizer ↔ ∀ x, T(x#, T x) = 0`. -/
theorem mem_h3zornCubicStabilizer_iff_traceBilin_adjointQuad
    (T : Module.End ℝ (H3Zorn ℝ)) :
    T ∈ h3zornCubicStabilizer ↔ ∀ x : H3Zorn ℝ, traceBilin (adjointQuad x) (T x) = 0 := by
  change (∀ x y z : H3Zorn ℝ,
      h3zornNormTrilin (T x) y z + h3zornNormTrilin x (T y) z +
        h3zornNormTrilin x y (T z) = 0) ↔
    ∀ x : H3Zorn ℝ, traceBilin (adjointQuad x) (T x) = 0
  have swap12 : ∀ a b c : H3Zorn ℝ, h3zornNormTrilin a b c = h3zornNormTrilin b a c :=
    h3zornCubicJordanDatum.normTrilin_swap₁₂
  have swap23 : ∀ a b c : H3Zorn ℝ, h3zornNormTrilin a b c = h3zornNormTrilin a c b :=
    h3zornCubicJordanDatum.normTrilin_swap₂₃
  let S : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ :=
    h3zornNormTrilin.comp T +
      { toFun := fun x =>
          { toFun := fun y =>
              { toFun := fun z => h3zornNormTrilin x (T y) z + h3zornNormTrilin x y (T z)
                map_add' := fun z₁ z₂ => by simp only [map_add, add_add_add_comm]
                map_smul' := fun r z => by
                  simp only [map_smul, smul_eq_mul, RingHom.id_apply, mul_add] }
            map_add' := fun y₁ y₂ => by
              ext z
              simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]
              ring
            map_smul' := fun r y => by
              ext z
              simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
                smul_eq_mul, RingHom.id_apply]
              ring }
        map_add' := fun x₁ x₂ => by
          ext y z
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]
          ring
        map_smul' := fun r x => by
          ext y z
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
            smul_eq_mul, RingHom.id_apply]
          ring }
  have hS_eval : ∀ x y z : H3Zorn ℝ,
      S x y z = h3zornNormTrilin (T x) y z + h3zornNormTrilin x (T y) z +
        h3zornNormTrilin x y (T z) := by
    intro x y z
    dsimp [S]
    ring
  have hS_diag : ∀ x : H3Zorn ℝ, S x x x = traceBilin (adjointQuad x) (T x) := by
    intro x
    rw [hS_eval]
    have hs1 : h3zornNormTrilin x (T x) x = h3zornNormTrilin (T x) x x :=
      swap12 x (T x) x
    have hs2 : h3zornNormTrilin x x (T x) = h3zornNormTrilin (T x) x x := by
      rw [swap23, swap12]
    rw [hs1, hs2, h3zornNormTrilin_apply, crossProduct_self, traceBilin_smul_right,
      traceBilin_symm]
    ring
  have hS_symm12 : ∀ x y z : H3Zorn ℝ, S x y z = S y x z := by
    intro x y z
    rw [hS_eval, hS_eval, swap12 (T x) y z, swap12 x (T y) z, swap12 x y (T z)]
    ring
  have hS_symm23 : ∀ x y z : H3Zorn ℝ, S x y z = S x z y := by
    intro x y z
    rw [hS_eval, hS_eval, swap23 (T x) y z, swap23 x (T y) z, swap23 x y (T z)]
    ring
  constructor
  · intro h x
    rw [← hS_diag x, hS_eval]
    exact h x x x
  · intro h x y z
    rw [← hS_eval x y z]
    exact symmetric_trilinear_eq_zero S hS_symm12 hS_symm23 (fun w => by rw [hS_diag, h w]) x y z

/-- **Reverse Lie-subalgebra inclusion**: every Jordan derivation of `H3Zorn ℝ`
lies in the infinitesimal cubic stabilizer `h3zornCubicStabilizer` (`str₀`). -/
theorem H3ZornF4Derivations_le_h3zornCubicStabilizer :
    H3ZornF4Derivations ≤ h3zornCubicStabilizer := by
  intro D hD
  rw [mem_h3zornCubicStabilizer_iff_traceBilin_adjointQuad]
  intro x
  let D' : H3ZornF4Derivations := ⟨D, hD⟩
  have h1 : traceBilin x (D'.1 (adjointQuad x)) = -traceBilin (adjointQuad x) (D'.1 x) := by
    have hs := h3ZornF4_derivation_traceBilin_skew D' x (adjointQuad x)
    rw [traceBilin_symm (D'.1 x) (adjointQuad x)] at hs
    linarith
  have h2 : traceBilin x (D'.1 (adjointQuad x)) = 2 * traceBilin (adjointQuad x) (D'.1 x) := by
    rw [h3ZornF4_derivation_adjointQuad D' x, ← traceBilin_crossProduct_assoc,
      crossProduct_self, traceBilin_smul_left]
  linarith

end OperatorTraceAndDerivations

section TraceZeroLmulAndDirectSums

theorem traceBilin_adjointQuad_jordanLmul (a x : H3Zorn ℝ) :
    traceBilin (adjointQuad x) (a * x) = normCubic x * linearTrace a := by
  calc
    traceBilin (adjointQuad x) (a * x) = traceBilin (x * a) (adjointQuad x) := by
      rw [mul_comm, traceBilin_symm]
    _ = traceBilin a (x * adjointQuad x) :=
      h3Zorn_traceBilin_jordanLmul_assoc x a (adjointQuad x)
    _ = traceBilin a (normCubic x • (1 : H3Zorn ℝ)) := by
      change traceBilin a (candidateJordanMul x (adjointQuad x)) = _
      rw [h3zorn_jordan_mul_adjoint_eq_norm_one x]
    _ = normCubic x * linearTrace a := by
      rw [traceBilin_smul_right, traceBilin_one, mul_comm]

/-- Left multiplication `L_a` stabilizes the cubic norm if and only if `linearTrace a = 0`. -/
theorem jordanLmul_mem_h3zornCubicStabilizer_iff (a : H3Zorn ℝ) :
    jordanLmul (R := ℝ) a ∈ h3zornCubicStabilizer ↔ linearTrace a = 0 := by
  rw [mem_h3zornCubicStabilizer_iff_traceBilin_adjointQuad]
  constructor
  · intro h
    have h1 := h 1
    rw [jordanLmul_apply, traceBilin_adjointQuad_jordanLmul, normCubic_one, one_mul] at h1
    exact h1
  · intro ha x
    rw [jordanLmul_apply, traceBilin_adjointQuad_jordanLmul, ha, mul_zero]

/-- Linear embedding `a ↦ L_a` from `H3Zorn ℝ` into `Module.End ℝ (H3Zorn ℝ)`. -/
def jordanLmulLinear : H3Zorn ℝ →ₗ[ℝ] Module.End ℝ (H3Zorn ℝ) where
  toFun a := jordanLmul (R := ℝ) a
  map_add' := h3Zorn_jordanLmul_add
  map_smul' := h3Zorn_jordanLmul_smul

theorem jordanLmulLinear_injective : Function.Injective jordanLmulLinear := by
  intro a b h
  have h1 := LinearMap.ext_iff.mp h (1 : H3Zorn ℝ)
  change a * (1 : H3Zorn ℝ) = b * (1 : H3Zorn ℝ) at h1
  change candidateJordanMul a 1 = candidateJordanMul b 1 at h1
  simpa only [candidateJordanMul_one_right] using h1

/-- Submodule `L(H₃)` of all left multiplication operators on `H3Zorn ℝ`. -/
def h3zornLmulSubmodule : Submodule ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  LinearMap.range jordanLmulLinear

theorem finrank_h3zornLmulSubmodule :
    Module.finrank ℝ h3zornLmulSubmodule = 27 := by
  rw [h3zornLmulSubmodule, LinearMap.finrank_range_of_inj jordanLmulLinear_injective,
    finrank_H3Zorn]

/-- Linear trace functional on `H3Zorn ℝ`. -/
def h3zornLinearTraceLinear : H3Zorn ℝ →ₗ[ℝ] ℝ where
  toFun := linearTrace
  map_add' := linearTrace_add
  map_smul' := linearTrace_smul

/-- The 26-dimensional trace-zero hyperplane `H₃⁰ = ker linearTrace` of `H3Zorn ℝ`. -/
def h3zornTraceZero : Submodule ℝ (H3Zorn ℝ) :=
  LinearMap.ker h3zornLinearTraceLinear

@[simp] theorem mem_h3zornTraceZero (a : H3Zorn ℝ) :
    a ∈ h3zornTraceZero ↔ linearTrace a = 0 := Iff.rfl

theorem finrank_h3zornTraceZero :
    Module.finrank ℝ h3zornTraceZero = 26 := by
  have hrange : LinearMap.range h3zornLinearTraceLinear = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro r
    refine ⟨(r / 3 : ℝ) • (1 : H3Zorn ℝ), ?_⟩
    simp only [h3zornLinearTraceLinear, LinearMap.coe_mk, AddHom.coe_mk, linearTrace_smul]
    have h1 : linearTrace (1 : H3Zorn ℝ) = 3 := by change (1 : ℝ) + 1 + 1 = 3; norm_num
    rw [h1]
    ring
  have hrk := LinearMap.finrank_range_add_finrank_ker h3zornLinearTraceLinear
  rw [hrange, finrank_top, finrank_H3Zorn, Module.finrank_self] at hrk
  change 1 + Module.finrank ℝ h3zornTraceZero = 27 at hrk
  omega

/-- Submodule `L(H₃⁰)` of trace-zero left multiplication operators on `H3Zorn ℝ`. -/
def h3zornLmulTraceZeroSubmodule : Submodule ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  h3zornTraceZero.map jordanLmulLinear

theorem finrank_h3zornLmulTraceZeroSubmodule :
    Module.finrank ℝ h3zornLmulTraceZeroSubmodule = 26 := by
  rw [h3zornLmulTraceZeroSubmodule,
    ← (h3zornTraceZero.equivMapOfInjective jordanLmulLinear jordanLmulLinear_injective).finrank_eq,
    finrank_h3zornTraceZero]

theorem disjoint_H3ZornF4Derivations_h3zornLmulSubmodule :
    Disjoint H3ZornF4Derivations.toSubmodule h3zornLmulSubmodule := by
  rw [Submodule.disjoint_def]
  intro T hTF4 hTL
  rcases hTL with ⟨a, rfl⟩
  have h1 : jordanLmulLinear a (1 : H3Zorn ℝ) = 0 :=
    h3ZornF4_derivation_apply_one_eq_zero ⟨jordanLmulLinear a, hTF4⟩
  have ha : a = 0 := by
    change a * (1 : H3Zorn ℝ) = 0 at h1
    change candidateJordanMul a 1 = 0 at h1
    simpa only [candidateJordanMul_one_right] using h1
  rw [ha, map_zero]

theorem disjoint_H3ZornF4Derivations_h3zornLmulTraceZeroSubmodule :
    Disjoint H3ZornF4Derivations.toSubmodule h3zornLmulTraceZeroSubmodule := by
  refine Disjoint.mono_right ?_ disjoint_H3ZornF4Derivations_h3zornLmulSubmodule
  intro T ⟨a, _, ha⟩
  exact ⟨a, ha⟩

/-- Internal direct-sum decomposition `structureOperatorLieSubalgebra = 𝔣₄ ⊕ L(H₃)`. -/
theorem structureOperatorLieSubalgebra_eq_sup :
    structureOperatorLieSubalgebra.toSubmodule =
      H3ZornF4Derivations.toSubmodule ⊔ h3zornLmulSubmodule := by
  apply le_antisymm
  · rintro T ⟨D, a, rfl⟩
    exact Submodule.add_mem _ (Submodule.mem_sup_left D.2)
      (Submodule.mem_sup_right ⟨a, rfl⟩)
  · rw [sup_le_iff]
    constructor
    · intro D hD
      refine ⟨⟨D, hD⟩, 0, ?_⟩
      change D = D + jordanLmul (R := ℝ) 0
      apply LinearMap.ext; intro x
      change D x = D x + (0 : H3Zorn ℝ) * x
      rw [zero_mul, add_zero]
    · rintro T ⟨a, rfl⟩
      exact ⟨0, a, by change jordanLmul (R := ℝ) a = 0 + jordanLmul (R := ℝ) a; simp⟩

/-- Direct-sum linear equivalence `(H3ZornF4Derivations × H3Zorn ℝ) ≃ₗ[ℝ] structureOperatorLieSubalgebra`. -/
def structureOperatorDirectSumEquiv :
    (H3ZornF4Derivations × H3Zorn ℝ) ≃ₗ[ℝ] structureOperatorLieSubalgebra :=
  LinearEquiv.ofBijective
    { toFun := fun p => ⟨structureOperator p.1 p.2, structureOperator_mem p.1 p.2⟩
      map_add' := fun p q => by
        apply Subtype.ext
        apply LinearMap.ext; intro x
        change (p.1.1 x + q.1.1 x) + (p.2 + q.2) * x = (p.1.1 x + p.2 * x) + (q.1.1 x + q.2 * x)
        rw [add_mul]
        abel
      map_smul' := fun r p => by
        apply Subtype.ext
        apply LinearMap.ext; intro x
        change ((r • p.1).1 x + (r • p.2) * x) = r • (p.1.1 x + p.2 * x)
        simp only [smul_add]
        rw [← candidateJordanMul_eq_mul, candidateJordanMul_smul_left, candidateJordanMul_eq_mul]
        rfl }
    ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨D, a⟩ h
      have h0 : structureOperator D a = 0 := congrArg Subtype.val h
      have h1 := LinearMap.ext_iff.mp h0 (1 : H3Zorn ℝ)
      have ha : a = 0 := by
        change D.1 1 + a * (1 : H3Zorn ℝ) = 0 at h1
        rw [h3ZornF4_derivation_apply_one_eq_zero D, zero_add] at h1
        change candidateJordanMul a 1 = 0 at h1
        simpa only [candidateJordanMul_one_right] using h1
      have hD0 : D = 0 := by
        apply Subtype.ext
        have hl0 : jordanLmul (R := ℝ) (0 : H3Zorn ℝ) = 0 := by
          apply LinearMap.ext; intro x; change (0 : H3Zorn ℝ) * x = 0; rw [zero_mul]
        change D.1 + jordanLmul (R := ℝ) a = 0 at h0
        rw [ha, hl0, add_zero] at h0
        exact h0
      exact Prod.ext hD0 ha,
    by
      rintro ⟨T, D, a, rfl⟩
      exact ⟨(D, a), rfl⟩⟩

/-- **Certified 79D dimension of `str(H₃(𝕆_s))`**:
`Module.finrank ℝ structureOperatorLieSubalgebra = 79`. -/
theorem finrank_structureOperatorLieSubalgebra :
    Module.finrank ℝ structureOperatorLieSubalgebra = 79 := by
  rw [← LinearEquiv.finrank_eq structureOperatorDirectSumEquiv, Module.finrank_prod,
    finrank_H3ZornF4Derivations, finrank_H3Zorn]

/-- **Full 78D Internal Direct-Sum Identification**:
`h3zornCubicStabilizer = H3ZornF4Derivations ⊕ L(H₃⁰)`. -/
theorem h3zornCubicStabilizer_eq_sup :
    h3zornCubicStabilizer.toSubmodule =
      H3ZornF4Derivations.toSubmodule ⊔ h3zornLmulTraceZeroSubmodule := by
  apply le_antisymm
  · intro T hT
    let a : H3Zorn ℝ := T 1
    have ha_tr : linearTrace a = 0 := by
      have h111 := hT 1 1 1
      have swap12 : ∀ u v w : H3Zorn ℝ, h3zornNormTrilin u v w = h3zornNormTrilin v u w :=
        h3zornCubicJordanDatum.normTrilin_swap₁₂
      have swap23 : ∀ u v w : H3Zorn ℝ, h3zornNormTrilin u v w = h3zornNormTrilin u w v :=
        h3zornCubicJordanDatum.normTrilin_swap₂₃
      have h3 : h3zornNormTrilin a 1 1 = 0 := by
        have hs : h3zornNormTrilin 1 a 1 = h3zornNormTrilin a 1 1 := swap12 1 a 1
        have hs' : h3zornNormTrilin 1 1 a = h3zornNormTrilin a 1 1 := by
          rw [swap23, swap12]
        dsimp [a]
        linarith
      rw [← h3zornNormTrilin_one_one a, h3, mul_zero]
    have hLa : jordanLmulLinear a ∈ h3zornCubicStabilizer :=
      (jordanLmul_mem_h3zornCubicStabilizer_iff a).mpr ha_tr
    let D : Module.End ℝ (H3Zorn ℝ) := T - jordanLmulLinear a
    have hD_stab : D ∈ h3zornCubicStabilizer := h3zornCubicStabilizer.sub_mem hT hLa
    have hD_unit : D ∈ h3zornUnitAnnihilator := by
      rw [mem_h3zornUnitAnnihilator]
      change T 1 - a * (1 : H3Zorn ℝ) = 0
      change a - candidateJordanMul a 1 = 0
      rw [candidateJordanMul_one_right, sub_self]
    have hD_F4 : D ∈ H3ZornF4Derivations :=
      h3zorn_cubic_unit_stabilizer_le_F4 ⟨hD_stab, hD_unit⟩
    have hdecomp : T = D + jordanLmulLinear a := by
      dsimp [D]; abel
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hD_F4)
      (Submodule.mem_sup_right ⟨a, ha_tr, rfl⟩)
  · rw [sup_le_iff]
    constructor
    · exact H3ZornF4Derivations_le_h3zornCubicStabilizer
    · rintro T ⟨a, ha, rfl⟩
      exact (jordanLmul_mem_h3zornCubicStabilizer_iff a).mpr ha

/-- Direct-sum linear equivalence `(H3ZornF4Derivations × h3zornTraceZero) ≃ₗ[ℝ] h3zornCubicStabilizer`. -/
def h3zornCubicStabilizerDirectSumEquiv :
    (H3ZornF4Derivations × h3zornTraceZero) ≃ₗ[ℝ] h3zornCubicStabilizer :=
  LinearEquiv.ofBijective
    { toFun := fun p =>
        ⟨p.1.1 + jordanLmulLinear p.2.1,
          h3zornCubicStabilizer.add_mem
            (H3ZornF4Derivations_le_h3zornCubicStabilizer p.1.2)
            ((jordanLmul_mem_h3zornCubicStabilizer_iff p.2.1).mpr p.2.2)⟩
      map_add' := fun p q => by
        apply Subtype.ext
        change (p.1.1 + q.1.1) + jordanLmulLinear (p.2.1 + q.2.1) =
          (p.1.1 + jordanLmulLinear p.2.1) + (q.1.1 + jordanLmulLinear q.2.1)
        rw [map_add]
        abel
      map_smul' := fun r p => by
        apply Subtype.ext
        change (r • p.1).1 + jordanLmulLinear (r • p.2.1) =
          r • (p.1.1 + jordanLmulLinear p.2.1)
        rw [map_smul]
        simp only [smul_add]
        rfl }
    ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨D, a⟩ h
      have h0 : D.1 + jordanLmulLinear a.1 = 0 := congrArg Subtype.val h
      have h1 := LinearMap.ext_iff.mp h0 (1 : H3Zorn ℝ)
      have ha1 : a.1 = 0 := by
        change D.1 1 + a.1 * (1 : H3Zorn ℝ) = 0 at h1
        rw [h3ZornF4_derivation_apply_one_eq_zero D, zero_add] at h1
        change candidateJordanMul a.1 1 = 0 at h1
        simpa only [candidateJordanMul_one_right] using h1
      have ha : a = 0 := Subtype.ext ha1
      have hD : D = 0 := by
        apply Subtype.ext
        rw [ha1, map_zero, add_zero] at h0
        exact h0
      exact Prod.ext hD ha,
    by
      rintro ⟨T, hT⟩
      let a : H3Zorn ℝ := T 1
      have ha_tr : a ∈ h3zornTraceZero := by
        rw [mem_h3zornTraceZero]
        have h111 := hT 1 1 1
        have swap12 : ∀ u v w : H3Zorn ℝ, h3zornNormTrilin u v w = h3zornNormTrilin v u w :=
          h3zornCubicJordanDatum.normTrilin_swap₁₂
        have swap23 : ∀ u v w : H3Zorn ℝ, h3zornNormTrilin u v w = h3zornNormTrilin u w v :=
          h3zornCubicJordanDatum.normTrilin_swap₂₃
        have h3 : h3zornNormTrilin a 1 1 = 0 := by
          have hs : h3zornNormTrilin 1 a 1 = h3zornNormTrilin a 1 1 := swap12 1 a 1
          have hs' : h3zornNormTrilin 1 1 a = h3zornNormTrilin a 1 1 := by
            rw [swap23, swap12]
          dsimp [a]
          linarith
        rw [← h3zornNormTrilin_one_one a, h3, mul_zero]
      let D : Module.End ℝ (H3Zorn ℝ) := T - jordanLmulLinear a
      have hD_F4 : D ∈ H3ZornF4Derivations := by
        apply h3zorn_cubic_unit_stabilizer_le_F4
        refine ⟨h3zornCubicStabilizer.sub_mem hT
          ((jordanLmul_mem_h3zornCubicStabilizer_iff a).mpr ha_tr), ?_⟩
        change D 1 = 0
        change a - candidateJordanMul a 1 = 0
        rw [candidateJordanMul_one_right, sub_self]
      refine ⟨(⟨D, hD_F4⟩, ⟨a, ha_tr⟩), ?_⟩
      apply Subtype.ext
      dsimp [D]
      abel⟩

/-- **Certified 78D Exact Dimension of `str₀(H₃(𝕆_s)) = h3zornCubicStabilizer`**:
`Module.finrank ℝ h3zornCubicStabilizer = 78`. -/
theorem finrank_h3zornCubicStabilizer :
    Module.finrank ℝ h3zornCubicStabilizer = 78 := by
  rw [← LinearEquiv.finrank_eq h3zornCubicStabilizerDirectSumEquiv, Module.finrank_prod,
    finrank_H3ZornF4Derivations, finrank_h3zornTraceZero]

/-- The reduced-structure direct-sum coordinates retain the actual operator bracket.

Under `h3zornCubicStabilizerDirectSumEquiv`, the bracket of `(D,a)` and `(E,b)` is
the derivation bracket plus the Jordan inner derivation, together with the action
`D b - E a` on the trace-zero multiplication coordinate. This is the concrete
bracket-level soldering needed before comparison with a Chevalley E₆ basis. -/
theorem h3zornCubicStabilizer_bracket_coordinate_formula
    (D E : H3ZornF4Derivations) (a b : h3zornTraceZero) :
    ⁅(h3zornCubicStabilizerDirectSumEquiv (D, a) :
        Module.End ℝ (H3Zorn ℝ)),
      (h3zornCubicStabilizerDirectSumEquiv (E, b) :
        Module.End ℝ (H3Zorn ℝ))⁆ =
      ⁅(D : Module.End ℝ (H3Zorn ℝ)),
        (E : Module.End ℝ (H3Zorn ℝ))⁆ +
        (h3ZornJordanInnerDerivation a.1 b.1 :
          Module.End ℝ (H3Zorn ℝ)) +
        jordanLmul (R := ℝ)
          ((D : Module.End ℝ (H3Zorn ℝ)) b.1 -
            (E : Module.End ℝ (H3Zorn ℝ)) a.1) := by
  change ⁅structureOperator D a.1, structureOperator E b.1⁆ = _
  exact structureOperator_lie_formula D E a.1 b.1

end TraceZeroLmulAndDirectSums

end InfoGeometry.Algebra
