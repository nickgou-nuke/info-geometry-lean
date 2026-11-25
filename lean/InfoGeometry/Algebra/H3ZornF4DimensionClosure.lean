/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Algebra.H3ZornTraceNondegenerate
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Unconditional 52-Dimensional Closure `f4BasisSpan = H3ZornF4Derivations`

Using the Peirce `24 + 28` decomposition from `H3ZornF4PeirceTrialitySplit`
together with the alternative/nonassociative octonion structure of `ZornVectorMatrix ℝ`,
this module proves unconditionally on the native `H3Zorn ℝ` carrier:

1. Exact Peirce multiplication formulas for `h3_diag₁`, `h3_diag₂`, `h3_diag₃`,
   `embedJ12`, `embedJ23`, and `embedJ31`.
2. Exact linear section `peirceShiftSection : Zorn³ →ₗ[ℝ] H3ZornF4Derivations`
   landing in `peirceShiftBasisSpan`, splitting off a 24D Peirce-shift subspace.
3. Injectivity of the restriction `D ↦ D|_{J₁₂}` from `ker peirceShiftEv` into
   the 28D skew-adjoint endomorphism space of `zornBilin`, via vanishing of the
   pure-imaginary split-octonion nucleus.
4. Direct linear independence of the 28 `trialityDerivation` elements via
   biorthogonal functionals, proving `trialityBasisSpan = ker peirceShiftEv`
   of dimension `28`.
5. **`f4BasisSpan_eq_H3ZornF4Derivations`** (`f4BasisSpan = H3ZornF4Derivations.toSubmodule`)
   and unconditional **`finrank_H3ZornF4Derivations : Module.finrank ℝ H3ZornF4Derivations = 52`**.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit

attribute [local instance 100] LieRing.ofAssociativeRing

section ZornBilinAndDual

/-- Split-octonion trace pairing `⟨x, y⟩ = tr(x * ȳ)`. -/
def zornBilin (x y : ZornVectorMatrix ℝ) : ℝ :=
  ZornVectorMatrix.trace (ZornVectorMatrix.mul x (ZornVectorMatrix.conj y))

@[simp] theorem zornBilin_symm (x y : ZornVectorMatrix ℝ) :
    zornBilin x y = zornBilin y x :=
  ZornVectorMatrix.trace_mul_conj_comm x y

@[simp] theorem zornBilin_add_left (x₁ x₂ y : ZornVectorMatrix ℝ) :
    zornBilin (x₁ + x₂) y = zornBilin x₁ y + zornBilin x₂ y := by
  change ZornVectorMatrix.trace (ZornVectorMatrix.mul (ZornVectorMatrix.add x₁ x₂)
      (ZornVectorMatrix.conj y)) =
    zornBilin x₁ y + zornBilin x₂ y
  rw [ZornVectorMatrix.add_mul, ZornVectorMatrix.trace_add]
  rfl

@[simp] theorem zornBilin_add_right (x y₁ y₂ : ZornVectorMatrix ℝ) :
    zornBilin x (y₁ + y₂) = zornBilin x y₁ + zornBilin x y₂ := by
  rw [zornBilin_symm, zornBilin_add_left, zornBilin_symm x y₁, zornBilin_symm x y₂]

@[simp] theorem zornBilin_smul_left (r : ℝ) (x y : ZornVectorMatrix ℝ) :
    zornBilin (r • x) y = r * zornBilin x y := by
  change ZornVectorMatrix.trace (ZornVectorMatrix.mul (ZornVectorMatrix.smul r x)
      (ZornVectorMatrix.conj y)) = r * zornBilin x y
  rw [ZornVectorMatrix.smul_mul, ZornVectorMatrix.trace_smul]
  rfl

@[simp] theorem zornBilin_smul_right (r : ℝ) (x y : ZornVectorMatrix ℝ) :
    zornBilin x (r • y) = r * zornBilin x y := by
  rw [zornBilin_symm, zornBilin_smul_left, zornBilin_symm x y]

@[simp] theorem zornBilin_neg_left (x y : ZornVectorMatrix ℝ) :
    zornBilin (-x) y = -zornBilin x y := by
  rw [show -x = (-1 : ℝ) • x by module, zornBilin_smul_left]
  ring

@[simp] theorem zornBilin_neg_right (x y : ZornVectorMatrix ℝ) :
    zornBilin x (-y) = -zornBilin x y := by
  rw [zornBilin_symm, zornBilin_neg_left, zornBilin_symm x y]

theorem zornBilin_norm_add (x y : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.norm (x + y) =
      ZornVectorMatrix.norm x + ZornVectorMatrix.norm y + zornBilin x y :=
  ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj x y

/-- Dual basis of `zorn_basis` with respect to `zornBilin`. -/
def zornDualBasis (i : Fin 8) : ZornVectorMatrix ℝ :=
  match i with
  | 0 => zorn_basis 7
  | 1 => -zorn_basis 4
  | 2 => -zorn_basis 5
  | 3 => -zorn_basis 6
  | 4 => -zorn_basis 1
  | 5 => -zorn_basis 2
  | 6 => -zorn_basis 3
  | 7 => zorn_basis 0

theorem zornBilin_basis_dual (i j : Fin 8) :
    zornBilin (zorn_basis i) (zornDualBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [zornBilin, zornDualBasis, zorn_basis,
      ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVec3.dot, ZornVectorMatrix.neg]

theorem zornBilin_dual_basis (i j : Fin 8) :
    zornBilin (zornDualBasis i) (zorn_basis j) = if i = j then 1 else 0 := by
  rw [zornBilin_symm, zornBilin_basis_dual]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem eq_zero_of_zornBilin_basis (x : ZornVectorMatrix ℝ)
    (h : ∀ i : Fin 8, zornBilin x (zorn_basis i) = 0) : x = 0 := by
  apply ZornVectorMatrix.eq_zero_of_trace_mul_conj_eq_zero x
  intro y
  change zornBilin x y = 0
  rw [← zorn_basis_decomposition y]
  have hlin : ∀ (s : Finset (Fin 8)) (f : Fin 8 → ZornVectorMatrix ℝ),
      zornBilin x (∑ i ∈ s, f i) = ∑ i ∈ s, zornBilin x (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      change zornBilin x 0 = 0
      simpa using zornBilin_smul_right 0 x 0
    | @insert a s has ih =>
      rw [Finset.sum_insert has, zornBilin_add_right, ih, Finset.sum_insert has]
  rw [hlin]
  apply Finset.sum_eq_zero
  intro i _
  change zornBilin x (_ • zorn_basis i) = 0
  rw [zornBilin_smul_right, h i, mul_zero]

end ZornBilinAndDual

section PeirceMultiplication

/-- Embedding into the `(2,3)` off-diagonal Peirce slot. -/
def embedJ23 (y : ZornVectorMatrix ℝ) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := 0, b := y, c := 0 }

/-- Embedding into the `(3,1)` off-diagonal Peirce slot. -/
def embedJ31 (z : ZornVectorMatrix ℝ) : H3Zorn ℝ :=
  { α₁ := 0, α₂ := 0, α₃ := 0, a := 0, b := 0, c := z }

private theorem zorn_zero_eq : (0 : ZornVectorMatrix ℝ) = ZornVectorMatrix.zero := rfl

private theorem ext_h3_mul_diag₁ (X : H3Zorn ℝ) :
    h3_diag₁ * X =
      { α₁ := X.α₁, α₂ := 0, α₃ := 0
        a := (1 / 2 : ℝ) • X.a, b := 0, c := (1 / 2 : ℝ) • X.c } := by
  change candidateJordanMul h3_diag₁ X = _
  rw [candidateJordanMul_trace_formula]
  have hcp : H3Zorn.crossProduct h3_diag₁ X =
      { α₁ := 0, α₂ := X.α₃, α₃ := X.α₂, a := 0, b := -X.b, c := 0 } := by
    change H3Zorn.crossProduct (diagCartan 1 0 0) X = _
    rw [crossProduct_diagCartan_left]
    apply ext_h3
    · ring
    · ring
    · ring
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  rw [hcp]
  apply ext_h3
  · simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · ext i <;> simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₁, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

private theorem ext_h3_mul_diag₂ (X : H3Zorn ℝ) :
    h3_diag₂ * X =
      { α₁ := 0, α₂ := X.α₂, α₃ := 0
        a := (1 / 2 : ℝ) • X.a, b := (1 / 2 : ℝ) • X.b, c := 0 } := by
  change candidateJordanMul h3_diag₂ X = _
  rw [candidateJordanMul_trace_formula]
  have hcp : H3Zorn.crossProduct h3_diag₂ X =
      { α₁ := X.α₃, α₂ := 0, α₃ := X.α₁, a := 0, b := 0, c := -X.c } := by
    change H3Zorn.crossProduct (diagCartan 0 1 0) X = _
    rw [crossProduct_diagCartan_left]
    apply ext_h3
    · ring
    · ring
    · ring
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg]
  rw [hcp]
  apply ext_h3
  · simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · ext i <;> simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₂, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

private theorem ext_h3_mul_diag₃ (X : H3Zorn ℝ) :
    h3_diag₃ * X =
      { α₁ := 0, α₂ := 0, α₃ := X.α₃
        a := 0, b := (1 / 2 : ℝ) • X.b, c := (1 / 2 : ℝ) • X.c } := by
  change candidateJordanMul h3_diag₃ X = _
  rw [candidateJordanMul_trace_formula]
  have hcp : H3Zorn.crossProduct h3_diag₃ X =
      { α₁ := X.α₂, α₂ := X.α₁, α₃ := 0, a := -X.a, b := 0, c := 0 } := by
    change H3Zorn.crossProduct (diagCartan 0 0 1) X = _
    rw [crossProduct_diagCartan_left]
    apply ext_h3
    · ring
    · ring
    · ring
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
    · ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  rw [hcp]
  apply ext_h3
  · simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback, one_readback]
  · simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback, one_readback]; ring
  · ext i <;> simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · ext i <;> simp [h3_diag₃, linearTrace, add_readback, sub_readback, smul_readback,
      one_readback, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

@[simp] theorem h3_diag₁_mul_h3_diag₁ : h3_diag₁ * h3_diag₁ = h3_diag₁ := by
  rw [ext_h3_mul_diag₁]; apply ext_h3 <;> simp [h3_diag₁, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₂_mul_h3_diag₂ : h3_diag₂ * h3_diag₂ = h3_diag₂ := by
  rw [ext_h3_mul_diag₂]; apply ext_h3 <;> simp [h3_diag₂, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₃_mul_h3_diag₃ : h3_diag₃ * h3_diag₃ = h3_diag₃ := by
  rw [ext_h3_mul_diag₃]; apply ext_h3 <;> simp [h3_diag₃, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₁_mul_h3_diag₂ : h3_diag₁ * h3_diag₂ = 0 := by
  rw [ext_h3_mul_diag₁]; apply ext_h3 <;> simp [h3_diag₂, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₁_mul_h3_diag₃ : h3_diag₁ * h3_diag₃ = 0 := by
  rw [ext_h3_mul_diag₁]; apply ext_h3 <;> simp [h3_diag₃, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₂_mul_h3_diag₃ : h3_diag₂ * h3_diag₃ = 0 := by
  rw [ext_h3_mul_diag₂]; apply ext_h3 <;> simp [h3_diag₃, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₁_mul_embedJ12 (x : ZornVectorMatrix ℝ) :
    h3_diag₁ * embedJ12 x = (1 / 2 : ℝ) • embedJ12 x := by
  rw [ext_h3_mul_diag₁]; apply ext_h3 <;> simp [embedJ12, smul_readback, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₂_mul_embedJ12 (x : ZornVectorMatrix ℝ) :
    h3_diag₂ * embedJ12 x = (1 / 2 : ℝ) • embedJ12 x := by
  rw [ext_h3_mul_diag₂]; apply ext_h3 <;> simp [embedJ12, smul_readback, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₃_mul_embedJ12 (x : ZornVectorMatrix ℝ) :
    h3_diag₃ * embedJ12 x = 0 := by
  rw [ext_h3_mul_diag₃]; apply ext_h3 <;> simp [embedJ12, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₁_mul_embedJ23 (y : ZornVectorMatrix ℝ) :
    h3_diag₁ * embedJ23 y = 0 := by
  rw [ext_h3_mul_diag₁]; apply ext_h3 <;> simp [embedJ23, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₂_mul_embedJ23 (y : ZornVectorMatrix ℝ) :
    h3_diag₂ * embedJ23 y = (1 / 2 : ℝ) • embedJ23 y := by
  rw [ext_h3_mul_diag₂]; apply ext_h3 <;> simp [embedJ23, smul_readback, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₃_mul_embedJ23 (y : ZornVectorMatrix ℝ) :
    h3_diag₃ * embedJ23 y = (1 / 2 : ℝ) • embedJ23 y := by
  rw [ext_h3_mul_diag₃]; apply ext_h3 <;> simp [embedJ23, smul_readback, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₁_mul_embedJ31 (z : ZornVectorMatrix ℝ) :
    h3_diag₁ * embedJ31 z = (1 / 2 : ℝ) • embedJ31 z := by
  rw [ext_h3_mul_diag₁]; apply ext_h3 <;> simp [embedJ31, smul_readback, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₂_mul_embedJ31 (z : ZornVectorMatrix ℝ) :
    h3_diag₂ * embedJ31 z = 0 := by
  rw [ext_h3_mul_diag₂]; apply ext_h3 <;> simp [embedJ31, ZornVectorMatrix.smul_zero]

@[simp] theorem h3_diag₃_mul_embedJ31 (z : ZornVectorMatrix ℝ) :
    h3_diag₃ * embedJ31 z = (1 / 2 : ℝ) • embedJ31 z := by
  rw [ext_h3_mul_diag₃]; apply ext_h3 <;> simp [embedJ31, smul_readback, ZornVectorMatrix.smul_zero]

theorem embedJ12_mul_embedJ12 (x y : ZornVectorMatrix ℝ) :
    embedJ12 x * embedJ12 y = ((1 / 2 : ℝ) * zornBilin x y) • (h3_diag₁ + h3_diag₂) := by
  change candidateJordanMul (embedJ12 x) (embedJ12 y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ12 x) = 0 := by simp [linearTrace, embedJ12]
  have hlt2 : linearTrace (embedJ12 y) = 0 := by simp [linearTrace, embedJ12]
  have hcp : H3Zorn.crossProduct (embedJ12 x) (embedJ12 y) =
      { α₁ := 0, α₂ := 0, α₃ := -zornBilin x y, a := 0, b := 0, c := 0 } := by
    have hn := zornBilin_norm_add x y
    change (x.add y).norm = x.norm + y.norm + zornBilin x y at hn
    apply ext_h3
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ12, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ12, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ12, sub_readback, add_readback]
      linarith
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, h3_diag₁, h3_diag₂, add_readback,
    smul_readback, one_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

theorem embedJ23_mul_embedJ23 (x y : ZornVectorMatrix ℝ) :
    embedJ23 x * embedJ23 y = ((1 / 2 : ℝ) * zornBilin x y) • (h3_diag₂ + h3_diag₃) := by
  change candidateJordanMul (embedJ23 x) (embedJ23 y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ23 x) = 0 := by simp [linearTrace, embedJ23]
  have hlt2 : linearTrace (embedJ23 y) = 0 := by simp [linearTrace, embedJ23]
  have hcp : H3Zorn.crossProduct (embedJ23 x) (embedJ23 y) =
      { α₁ := -zornBilin x y, α₂ := 0, α₃ := 0, a := 0, b := 0, c := 0 } := by
    have hn := zornBilin_norm_add x y
    change (x.add y).norm = x.norm + y.norm + zornBilin x y at hn
    apply ext_h3
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ23, sub_readback, add_readback]
      linarith
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ23, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ23, sub_readback, add_readback]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ23, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ23, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ23, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, h3_diag₂, h3_diag₃, add_readback,
    smul_readback, one_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

theorem embedJ31_mul_embedJ31 (x y : ZornVectorMatrix ℝ) :
    embedJ31 x * embedJ31 y = ((1 / 2 : ℝ) * zornBilin x y) • (h3_diag₃ + h3_diag₁) := by
  change candidateJordanMul (embedJ31 x) (embedJ31 y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ31 x) = 0 := by simp [linearTrace, embedJ31]
  have hlt2 : linearTrace (embedJ31 y) = 0 := by simp [linearTrace, embedJ31]
  have hcp : H3Zorn.crossProduct (embedJ31 x) (embedJ31 y) =
      { α₁ := 0, α₂ := -zornBilin x y, α₃ := 0, a := 0, b := 0, c := 0 } := by
    have hn := zornBilin_norm_add x y
    change (x.add y).norm = x.norm + y.norm + zornBilin x y at hn
    apply ext_h3
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ31, sub_readback, add_readback]
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ31, sub_readback, add_readback]
      linarith
    · simp [H3Zorn.crossProduct, adjointQuad, embedJ31, sub_readback, add_readback]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ31, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ31, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
    · ext i <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ31, sub_readback, add_readback,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
        ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, h3_diag₃, h3_diag₁, add_readback,
    smul_readback, one_readback, ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]

theorem embedJ12_mul_embedJ23 (x y : ZornVectorMatrix ℝ) :
    embedJ12 x * embedJ23 y =
      (1 / 2 : ℝ) • embedJ31 (ZornVectorMatrix.mul (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)) := by
  change candidateJordanMul (embedJ12 x) (embedJ23 y) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ12 x) = 0 := by simp [linearTrace, embedJ12]
  have hlt2 : linearTrace (embedJ23 y) = 0 := by simp [linearTrace, embedJ23]
  have hcp : H3Zorn.crossProduct (embedJ12 x) (embedJ23 y) =
      embedJ31 (ZornVectorMatrix.mul (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)) := by
    apply ext_h3 <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12, embedJ23, embedJ31,
      sub_readback, add_readback, ZornVectorMatrix.norm_zero, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.smul_zero,
      ZornVectorMatrix.sub_zero, ZornVectorMatrix.add_zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, embedJ31, add_readback, smul_readback,
    one_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]

theorem embedJ23_mul_embedJ31 (y z : ZornVectorMatrix ℝ) :
    embedJ23 y * embedJ31 z =
      (1 / 2 : ℝ) • embedJ12 (ZornVectorMatrix.mul (ZornVectorMatrix.conj z) (ZornVectorMatrix.conj y)) := by
  change candidateJordanMul (embedJ23 y) (embedJ31 z) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ23 y) = 0 := by simp [linearTrace, embedJ23]
  have hlt2 : linearTrace (embedJ31 z) = 0 := by simp [linearTrace, embedJ31]
  have hcp : H3Zorn.crossProduct (embedJ23 y) (embedJ31 z) =
      embedJ12 (ZornVectorMatrix.mul (ZornVectorMatrix.conj z) (ZornVectorMatrix.conj y)) := by
    apply ext_h3 <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12, embedJ23, embedJ31,
      sub_readback, add_readback, ZornVectorMatrix.norm_zero, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.smul_zero,
      ZornVectorMatrix.sub_zero, ZornVectorMatrix.add_zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, embedJ12, add_readback, smul_readback,
    one_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]

theorem embedJ31_mul_embedJ12 (z x : ZornVectorMatrix ℝ) :
    embedJ31 z * embedJ12 x =
      (1 / 2 : ℝ) • embedJ23 (ZornVectorMatrix.mul (ZornVectorMatrix.conj x) (ZornVectorMatrix.conj z)) := by
  change candidateJordanMul (embedJ31 z) (embedJ12 x) = _
  rw [candidateJordanMul_trace_formula]
  have hlt1 : linearTrace (embedJ31 z) = 0 := by simp [linearTrace, embedJ31]
  have hlt2 : linearTrace (embedJ12 x) = 0 := by simp [linearTrace, embedJ12]
  have hcp : H3Zorn.crossProduct (embedJ31 z) (embedJ12 x) =
      embedJ23 (ZornVectorMatrix.mul (ZornVectorMatrix.conj x) (ZornVectorMatrix.conj z)) := by
    apply ext_h3 <;> simp [H3Zorn.crossProduct, adjointQuad, embedJ12, embedJ23, embedJ31,
      sub_readback, add_readback, ZornVectorMatrix.norm_zero, ZornVectorMatrix.conj_zero,
      ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.smul_zero,
      ZornVectorMatrix.sub_zero, ZornVectorMatrix.add_zero]
  rw [hlt1, hlt2, hcp]
  apply ext_h3 <;> simp [linearTrace, embedJ23, add_readback, smul_readback,
    one_readback, ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero]

end PeirceMultiplication

section PeirceShiftSplitting

abbrev ZornTriple := ZornVectorMatrix ℝ × ZornVectorMatrix ℝ × ZornVectorMatrix ℝ

/-- Linear map evaluating a split-Albert derivation on the three Peirce idempotents. -/
def peirceShiftEv : H3ZornF4Derivations →ₗ[ℝ] ZornTriple where
  toFun D := ((D.1 h3_diag₁).a, (D.1 h3_diag₂).b, (D.1 h3_diag₃).c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def embedJ12LM : ZornVectorMatrix ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun := embedJ12
  map_add' x y := by
    apply ext_h3 <;> simp [embedJ12, add_readback, ZornVectorMatrix.add_zero]
  map_smul' r x := by
    apply ext_h3 <;> simp [embedJ12, smul_readback, ZornVectorMatrix.smul_zero]

private def embedJ23LM : ZornVectorMatrix ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun := embedJ23
  map_add' x y := by
    apply ext_h3 <;> simp [embedJ23, add_readback, ZornVectorMatrix.add_zero]
  map_smul' r x := by
    apply ext_h3 <;> simp [embedJ23, smul_readback, ZornVectorMatrix.smul_zero]

private def embedJ31LM : ZornVectorMatrix ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun := embedJ31
  map_add' x y := by
    apply ext_h3 <;> simp [embedJ31, add_readback, ZornVectorMatrix.add_zero]
  map_smul' r x := by
    apply ext_h3 <;> simp [embedJ31, smul_readback, ZornVectorMatrix.smul_zero]

/-- Explicit linear right-inverse to `peirceShiftEv` landing inside `peirceShiftBasisSpan`. -/
def peirceShiftSection : ZornTriple →ₗ[ℝ] H3ZornF4Derivations where
  toFun p :=
    (-4 : ℝ) • ⟨(h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 p.1) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩ +
    (-4 : ℝ) • ⟨(h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 p.2.1) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩ +
    (4 : ℝ) • ⟨(h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 p.2.2) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩
  map_add' p q := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    change (-4 : ℝ) • (h3_diag₁ * (embedJ12LM (p.1 + q.1) * w) -
          embedJ12LM (p.1 + q.1) * (h3_diag₁ * w)) +
        (-4 : ℝ) • (h3_diag₂ * (embedJ23LM (p.2.1 + q.2.1) * w) -
          embedJ23LM (p.2.1 + q.2.1) * (h3_diag₂ * w)) +
        (4 : ℝ) • (h3_diag₁ * (embedJ31LM (p.2.2 + q.2.2) * w) -
          embedJ31LM (p.2.2 + q.2.2) * (h3_diag₁ * w)) =
      ((-4 : ℝ) • (h3_diag₁ * (embedJ12 p.1 * w) - embedJ12 p.1 * (h3_diag₁ * w)) +
        (-4 : ℝ) • (h3_diag₂ * (embedJ23 p.2.1 * w) - embedJ23 p.2.1 * (h3_diag₂ * w)) +
        (4 : ℝ) • (h3_diag₁ * (embedJ31 p.2.2 * w) - embedJ31 p.2.2 * (h3_diag₁ * w))) +
      ((-4 : ℝ) • (h3_diag₁ * (embedJ12 q.1 * w) - embedJ12 q.1 * (h3_diag₁ * w)) +
        (-4 : ℝ) • (h3_diag₂ * (embedJ23 q.2.1 * w) - embedJ23 q.2.1 * (h3_diag₂ * w)) +
        (4 : ℝ) • (h3_diag₁ * (embedJ31 q.2.2 * w) - embedJ31 q.2.2 * (h3_diag₁ * w)))
    rw [embedJ12LM.map_add, embedJ23LM.map_add, embedJ31LM.map_add]
    dsimp only [embedJ12LM, embedJ23LM, embedJ31LM]
    simp only [add_mul, mul_add]
    module
  map_smul' r p := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    change (-4 : ℝ) • (h3_diag₁ * (embedJ12LM (r • p.1) * w) -
          embedJ12LM (r • p.1) * (h3_diag₁ * w)) +
        (-4 : ℝ) • (h3_diag₂ * (embedJ23LM (r • p.2.1) * w) -
          embedJ23LM (r • p.2.1) * (h3_diag₂ * w)) +
        (4 : ℝ) • (h3_diag₁ * (embedJ31LM (r • p.2.2) * w) -
          embedJ31LM (r • p.2.2) * (h3_diag₁ * w)) =
      r • ((-4 : ℝ) • (h3_diag₁ * (embedJ12 p.1 * w) - embedJ12 p.1 * (h3_diag₁ * w)) +
        (-4 : ℝ) • (h3_diag₂ * (embedJ23 p.2.1 * w) - embedJ23 p.2.1 * (h3_diag₂ * w)) +
        (4 : ℝ) • (h3_diag₁ * (embedJ31 p.2.2 * w) - embedJ31 p.2.2 * (h3_diag₁ * w)))
    rw [embedJ12LM.map_smul, embedJ23LM.map_smul, embedJ31LM.map_smul]
    dsimp only [embedJ12LM, embedJ23LM, embedJ31LM]
    simp only [smul_mul_assoc, mul_smul_comm]
    module

private theorem inner12_on_diags (x : ZornVectorMatrix ℝ) :
    (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3) h3_diag₁ =
        (-1 / 4 : ℝ) • embedJ12 x ∧
      (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3) h3_diag₂ =
        (1 / 4 : ℝ) • embedJ12 x ∧
      (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3) h3_diag₃ = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [h3ZornJordanInnerDerivation_apply]
  · rw [mul_comm (embedJ12 x) h3_diag₁, h3_diag₁_mul_embedJ12, mul_smul_comm,
      h3_diag₁_mul_embedJ12, h3_diag₁_mul_h3_diag₁,
      mul_comm (embedJ12 x) h3_diag₁, h3_diag₁_mul_embedJ12]
    module
  · rw [mul_comm (embedJ12 x) h3_diag₂, h3_diag₂_mul_embedJ12, mul_smul_comm,
      h3_diag₁_mul_embedJ12, h3_diag₁_mul_h3_diag₂, mul_zero]
    module
  · rw [mul_comm (embedJ12 x) h3_diag₃, h3_diag₃_mul_embedJ12, mul_zero,
      h3_diag₁_mul_h3_diag₃, mul_zero, sub_self]

private theorem inner23_on_diags (y : ZornVectorMatrix ℝ) :
    (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 y) : EndH3) h3_diag₁ = 0 ∧
      (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 y) : EndH3) h3_diag₂ =
        (-1 / 4 : ℝ) • embedJ23 y ∧
      (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 y) : EndH3) h3_diag₃ =
        (1 / 4 : ℝ) • embedJ23 y := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [h3ZornJordanInnerDerivation_apply]
  · rw [mul_comm (embedJ23 y) h3_diag₁, h3_diag₁_mul_embedJ23, mul_zero,
      h3_diag₂_mul_h3_diag₁_zero, mul_zero, sub_self]
  · rw [mul_comm (embedJ23 y) h3_diag₂, h3_diag₂_mul_embedJ23, mul_smul_comm,
      h3_diag₂_mul_embedJ23, h3_diag₂_mul_h3_diag₂,
      mul_comm (embedJ23 y) h3_diag₂, h3_diag₂_mul_embedJ23]
    module
  · rw [mul_comm (embedJ23 y) h3_diag₃, h3_diag₃_mul_embedJ23, mul_smul_comm,
      h3_diag₂_mul_embedJ23, h3_diag₂_mul_h3_diag₃, mul_zero]
    module
where
  h3_diag₂_mul_h3_diag₁_zero : h3_diag₂ * h3_diag₁ = 0 := by
    rw [mul_comm, h3_diag₁_mul_h3_diag₂]

private theorem inner31_on_diags (z : ZornVectorMatrix ℝ) :
    (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 z) : EndH3) h3_diag₁ =
        (-1 / 4 : ℝ) • embedJ31 z ∧
      (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 z) : EndH3) h3_diag₂ = 0 ∧
      (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 z) : EndH3) h3_diag₃ =
        (1 / 4 : ℝ) • embedJ31 z := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [h3ZornJordanInnerDerivation_apply]
  · rw [mul_comm (embedJ31 z) h3_diag₁, h3_diag₁_mul_embedJ31, mul_smul_comm,
      h3_diag₁_mul_embedJ31, h3_diag₁_mul_h3_diag₁,
      mul_comm (embedJ31 z) h3_diag₁, h3_diag₁_mul_embedJ31]
    module
  · rw [mul_comm (embedJ31 z) h3_diag₂, h3_diag₂_mul_embedJ31, mul_zero,
      h3_diag₁_mul_h3_diag₂, mul_zero, sub_self]
  · rw [mul_comm (embedJ31 z) h3_diag₃, h3_diag₃_mul_embedJ31, mul_smul_comm,
      h3_diag₁_mul_embedJ31, h3_diag₁_mul_h3_diag₃, mul_zero]
    module

@[simp] theorem peirceShiftEv_section (p : ZornTriple) :
    peirceShiftEv (peirceShiftSection p) = p := by
  rcases p with ⟨x, y, z⟩
  have h1 := inner12_on_diags x
  have h2 := inner23_on_diags y
  have h3 := inner31_on_diags z
  have ha : ((peirceShiftSection (x, y, z)).1 h3_diag₁).a = x := by
    have hev : (peirceShiftSection (x, y, z)).1 h3_diag₁ =
        (-4 : ℝ) • ((-1 / 4 : ℝ) • embedJ12 x) +
        (-4 : ℝ) • (0 : H3Zorn ℝ) +
        (4 : ℝ) • ((-1 / 4 : ℝ) • embedJ31 z) := by
      change (-4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3) h3_diag₁ +
        (-4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 y) : EndH3) h3_diag₁ +
        (4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 z) : EndH3) h3_diag₁ = _
      rw [h1.1, h2.1, h3.1]
    have hsimp : (-4 : ℝ) • ((-1 / 4 : ℝ) • embedJ12 x) +
        (-4 : ℝ) • (0 : H3Zorn ℝ) +
        (4 : ℝ) • ((-1 / 4 : ℝ) • embedJ31 z) = embedJ12 x - embedJ31 z := by
      module
    rw [hev, hsimp]
    simp [embedJ12, embedJ31, sub_readback, ZornVectorMatrix.sub_zero]
  have hb : ((peirceShiftSection (x, y, z)).1 h3_diag₂).b = y := by
    have hev : (peirceShiftSection (x, y, z)).1 h3_diag₂ =
        (-4 : ℝ) • ((1 / 4 : ℝ) • embedJ12 x) +
        (-4 : ℝ) • ((-1 / 4 : ℝ) • embedJ23 y) +
        (4 : ℝ) • (0 : H3Zorn ℝ) := by
      change (-4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3) h3_diag₂ +
        (-4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 y) : EndH3) h3_diag₂ +
        (4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 z) : EndH3) h3_diag₂ = _
      rw [h1.2.1, h2.2.1, h3.2.1]
    have hsimp : (-4 : ℝ) • ((1 / 4 : ℝ) • embedJ12 x) +
        (-4 : ℝ) • ((-1 / 4 : ℝ) • embedJ23 y) +
        (4 : ℝ) • (0 : H3Zorn ℝ) = -embedJ12 x + embedJ23 y := by
      module
    rw [hev, hsimp]
    ext i <;> simp [embedJ12, embedJ23, add_readback, neg_readback,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  have hc : ((peirceShiftSection (x, y, z)).1 h3_diag₃).c = z := by
    have hev : (peirceShiftSection (x, y, z)).1 h3_diag₃ =
        (-4 : ℝ) • (0 : H3Zorn ℝ) +
        (-4 : ℝ) • ((1 / 4 : ℝ) • embedJ23 y) +
        (4 : ℝ) • ((1 / 4 : ℝ) • embedJ31 z) := by
      change (-4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 x) : EndH3) h3_diag₃ +
        (-4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 y) : EndH3) h3_diag₃ +
        (4 : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 z) : EndH3) h3_diag₃ = _
      rw [h1.2.2, h2.2.2, h3.2.2]
    have hsimp : (-4 : ℝ) • (0 : H3Zorn ℝ) +
        (-4 : ℝ) • ((1 / 4 : ℝ) • embedJ23 y) +
        (4 : ℝ) • ((1 / 4 : ℝ) • embedJ31 z) = -embedJ23 y + embedJ31 z := by
      module
    rw [hev, hsimp]
    ext i <;> simp [embedJ23, embedJ31, add_readback, neg_readback,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.zero]
  exact Prod.ext ha (Prod.ext hb hc)

private theorem zorn_basis_inner12_mem (i : Fin 8) :
    (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 (zorn_basis i)) : EndH3) ∈
      peirceShiftBasisSpan := by
  let k : Fin 24 := ⟨i.val, by omega⟩
  have hk : shiftDerivation k =
      (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 (zorn_basis i)) : EndH3) := by
    fin_cases i <;> rfl
  rw [← hk]
  exact Submodule.subset_span ⟨k, rfl⟩

private theorem zorn_basis_inner31_mem (i : Fin 8) :
    (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 (zorn_basis i)) : EndH3) ∈
      peirceShiftBasisSpan := by
  let k : Fin 24 := ⟨8 + i.val, by omega⟩
  have hk : shiftDerivation k =
      (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 (zorn_basis i)) : EndH3) := by
    fin_cases i <;> rfl
  rw [← hk]
  exact Submodule.subset_span ⟨k, rfl⟩

private theorem zorn_basis_inner23_mem (i : Fin 8) :
    (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 (zorn_basis i)) : EndH3) ∈
      peirceShiftBasisSpan := by
  let k : Fin 24 := ⟨16 + i.val, by omega⟩
  have hk : shiftDerivation k =
      (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 (zorn_basis i)) : EndH3) := by
    fin_cases i <;> rfl
  rw [← hk]
  exact Submodule.subset_span ⟨k, rfl⟩

theorem peirceShiftSection_mem_peirceShiftBasisSpan (p : ZornTriple) :
    ((peirceShiftSection p : H3ZornF4Derivations) : EndH3) ∈ peirceShiftBasisSpan := by
  have h12 : (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 p.1) : EndH3) ∈
      peirceShiftBasisSpan := by
    have hsum := congrArg embedJ12LM (zorn_basis_decomposition p.1).symm
    simp only [map_sum, map_smul] at hsum
    change embedJ12 p.1 = _ at hsum
    have hmem : ∀ (c : Fin 8 → ℝ),
        (h3ZornJordanInnerDerivation h3_diag₁
          (∑ i : Fin 8, c i • embedJ12 (zorn_basis i)) : EndH3) ∈ peirceShiftBasisSpan := by
      intro c
      have hlin : (h3ZornJordanInnerDerivation h3_diag₁
            (∑ i : Fin 8, c i • embedJ12 (zorn_basis i)) : EndH3) =
          ∑ i : Fin 8, c i •
            (h3ZornJordanInnerDerivation h3_diag₁ (embedJ12 (zorn_basis i)) : EndH3) := by
        apply LinearMap.ext; intro w
        simp only [h3ZornJordanInnerDerivation_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_sub_distrib,
          smul_sub]
      rw [hlin]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (zorn_basis_inner12_mem i)
    rw [hsum]
    exact hmem _
  have h23 : (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 p.2.1) : EndH3) ∈
      peirceShiftBasisSpan := by
    have hsum := congrArg embedJ23LM (zorn_basis_decomposition p.2.1).symm
    simp only [map_sum, map_smul] at hsum
    change embedJ23 p.2.1 = _ at hsum
    have hmem : ∀ (c : Fin 8 → ℝ),
        (h3ZornJordanInnerDerivation h3_diag₂
          (∑ i : Fin 8, c i • embedJ23 (zorn_basis i)) : EndH3) ∈ peirceShiftBasisSpan := by
      intro c
      have hlin : (h3ZornJordanInnerDerivation h3_diag₂
            (∑ i : Fin 8, c i • embedJ23 (zorn_basis i)) : EndH3) =
          ∑ i : Fin 8, c i •
            (h3ZornJordanInnerDerivation h3_diag₂ (embedJ23 (zorn_basis i)) : EndH3) := by
        apply LinearMap.ext; intro w
        simp only [h3ZornJordanInnerDerivation_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_sub_distrib,
          smul_sub]
      rw [hlin]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (zorn_basis_inner23_mem i)
    rw [hsum]
    exact hmem _
  have h31 : (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 p.2.2) : EndH3) ∈
      peirceShiftBasisSpan := by
    have hsum := congrArg embedJ31LM (zorn_basis_decomposition p.2.2).symm
    simp only [map_sum, map_smul] at hsum
    change embedJ31 p.2.2 = _ at hsum
    have hmem : ∀ (c : Fin 8 → ℝ),
        (h3ZornJordanInnerDerivation h3_diag₁
          (∑ i : Fin 8, c i • embedJ31 (zorn_basis i)) : EndH3) ∈ peirceShiftBasisSpan := by
      intro c
      have hlin : (h3ZornJordanInnerDerivation h3_diag₁
            (∑ i : Fin 8, c i • embedJ31 (zorn_basis i)) : EndH3) =
          ∑ i : Fin 8, c i •
            (h3ZornJordanInnerDerivation h3_diag₁ (embedJ31 (zorn_basis i)) : EndH3) := by
        apply LinearMap.ext; intro w
        simp only [h3ZornJordanInnerDerivation_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_sub_distrib,
          smul_sub]
      rw [hlin]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (zorn_basis_inner31_mem i)
    rw [hsum]
    exact hmem _
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h12) (Submodule.smul_mem _ _ h23)) (Submodule.smul_mem _ _ h31)

theorem finrank_zornVectorMatrix : Module.finrank ℝ (ZornVectorMatrix ℝ) = 8 := by
  simpa using Module.finrank_eq_card_basis zornCoordinateBasis

private instance : Module.Finite ℝ (ZornVectorMatrix ℝ) :=
  Module.Finite.of_basis zornCoordinateBasis

private instance : Module.Finite ℝ H3 :=
  Module.Finite.of_basis InfoGeometry.Canonical.H3ZornBasis.h3ZornCoordinateBasis

private theorem zorn_eq_zero_of_half_smul_eq_zero {z : ZornVectorMatrix ℝ}
    (h : ((1 / 2 : ℝ) • z) = 0) : z = 0 := by
  calc
    z = (1 : ℝ) • z := (one_smul ℝ z).symm
    _ = ((2 : ℝ) * (1 / 2 : ℝ)) • z := by norm_num
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • z) := mul_smul _ _ _
    _ = 0 := by rw [h, smul_zero]

theorem ker_peirceShiftEv_iff_diags_zero (D : H3ZornF4Derivations) :
    D ∈ LinearMap.ker peirceShiftEv ↔
      D.1 h3_diag₁ = 0 ∧ D.1 h3_diag₂ = 0 ∧ D.1 h3_diag₃ = 0 := by
  constructor
  · intro hker
    have ha : (D.1 h3_diag₁).a = 0 := congrArg Prod.fst hker
    have hb : (D.1 h3_diag₂).b = 0 := congrArg (fun p : ZornTriple => p.2.1) hker
    have hc : (D.1 h3_diag₃).c = 0 := congrArg (fun p : ZornTriple => p.2.2) hker
    have hd1 : D.1 h3_diag₁ = (2 : ℝ) • (h3_diag₁ * D.1 h3_diag₁) := by
      have h := D.2 h3_diag₁ h3_diag₁
      rw [h3_diag₁_mul_h3_diag₁, mul_comm (D.1 h3_diag₁) h3_diag₁] at h
      simpa [two_smul] using h
    have hd2 : D.1 h3_diag₂ = (2 : ℝ) • (h3_diag₂ * D.1 h3_diag₂) := by
      have h := D.2 h3_diag₂ h3_diag₂
      rw [h3_diag₂_mul_h3_diag₂, mul_comm (D.1 h3_diag₂) h3_diag₂] at h
      simpa [two_smul] using h
    have hd3 : D.1 h3_diag₃ = (2 : ℝ) • (h3_diag₃ * D.1 h3_diag₃) := by
      have h := D.2 h3_diag₃ h3_diag₃
      rw [h3_diag₃_mul_h3_diag₃, mul_comm (D.1 h3_diag₃) h3_diag₃] at h
      simpa [two_smul] using h
    rw [ext_h3_mul_diag₁] at hd1
    rw [ext_h3_mul_diag₂] at hd2
    rw [ext_h3_mul_diag₃] at hd3
    have hα1₁ : (D.1 h3_diag₁).α₁ = 0 := by
      have ht := congrArg H3Zorn.α₁ hd1; change (D.1 h3_diag₁).α₁ = 2 * (D.1 h3_diag₁).α₁ at ht; linarith
    have hα2₁ : (D.1 h3_diag₁).α₂ = 0 := by
      have ht := congrArg H3Zorn.α₂ hd1; change (D.1 h3_diag₁).α₂ = 2 * 0 at ht; linarith
    have hα3₁ : (D.1 h3_diag₁).α₃ = 0 := by
      have ht := congrArg H3Zorn.α₃ hd1; change (D.1 h3_diag₁).α₃ = 2 * 0 at ht; linarith
    have hb₁ : (D.1 h3_diag₁).b = 0 := by
      have ht := congrArg H3Zorn.b hd1
      change (D.1 h3_diag₁).b = (2 : ℝ) • (0 : ZornVectorMatrix ℝ) at ht
      rw [ht, smul_zero]
    have hα1₂ : (D.1 h3_diag₂).α₁ = 0 := by
      have ht := congrArg H3Zorn.α₁ hd2; change (D.1 h3_diag₂).α₁ = 2 * 0 at ht; linarith
    have hα2₂ : (D.1 h3_diag₂).α₂ = 0 := by
      have ht := congrArg H3Zorn.α₂ hd2; change (D.1 h3_diag₂).α₂ = 2 * (D.1 h3_diag₂).α₂ at ht; linarith
    have hα3₂ : (D.1 h3_diag₂).α₃ = 0 := by
      have ht := congrArg H3Zorn.α₃ hd2; change (D.1 h3_diag₂).α₃ = 2 * 0 at ht; linarith
    have hc₂ : (D.1 h3_diag₂).c = 0 := by
      have ht := congrArg H3Zorn.c hd2
      change (D.1 h3_diag₂).c = (2 : ℝ) • (0 : ZornVectorMatrix ℝ) at ht
      rw [ht, smul_zero]
    have hα1₃ : (D.1 h3_diag₃).α₁ = 0 := by
      have ht := congrArg H3Zorn.α₁ hd3; change (D.1 h3_diag₃).α₁ = 2 * 0 at ht; linarith
    have hα2₃ : (D.1 h3_diag₃).α₂ = 0 := by
      have ht := congrArg H3Zorn.α₂ hd3; change (D.1 h3_diag₃).α₂ = 2 * 0 at ht; linarith
    have hα3₃ : (D.1 h3_diag₃).α₃ = 0 := by
      have ht := congrArg H3Zorn.α₃ hd3; change (D.1 h3_diag₃).α₃ = 2 * (D.1 h3_diag₃).α₃ at ht; linarith
    have ha₃ : (D.1 h3_diag₃).a = 0 := by
      have ht := congrArg H3Zorn.a hd3
      change (D.1 h3_diag₃).a = (2 : ℝ) • (0 : ZornVectorMatrix ℝ) at ht
      rw [ht, smul_zero]
    have hc₁ : (D.1 h3_diag₁).c = 0 := by
      have h := D.2 h3_diag₁ h3_diag₃
      rw [h3_diag₁_mul_h3_diag₃, map_zero, mul_comm (D.1 h3_diag₁) h3_diag₃] at h
      have h' := congrArg H3Zorn.c h.symm
      change (h3_diag₃ * D.1 h3_diag₁ + h3_diag₁ * D.1 h3_diag₃).c = 0 at h'
      rw [add_readback, ext_h3_mul_diag₃, ext_h3_mul_diag₁] at h'
      dsimp at h'
      change (1 / 2 : ℝ) • (D.1 h3_diag₁).c + (1 / 2 : ℝ) • (D.1 h3_diag₃).c = 0 at h'
      rw [hc, smul_zero, add_zero] at h'
      exact zorn_eq_zero_of_half_smul_eq_zero h'
    have ha₂ : (D.1 h3_diag₂).a = 0 := by
      have h := D.2 h3_diag₁ h3_diag₂
      rw [h3_diag₁_mul_h3_diag₂, map_zero, mul_comm (D.1 h3_diag₁) h3_diag₂] at h
      have h' := congrArg H3Zorn.a h.symm
      change (h3_diag₂ * D.1 h3_diag₁ + h3_diag₁ * D.1 h3_diag₂).a = 0 at h'
      rw [add_readback, ext_h3_mul_diag₂, ext_h3_mul_diag₁] at h'
      dsimp at h'
      change (1 / 2 : ℝ) • (D.1 h3_diag₁).a + (1 / 2 : ℝ) • (D.1 h3_diag₂).a = 0 at h'
      rw [ha, smul_zero, zero_add] at h'
      exact zorn_eq_zero_of_half_smul_eq_zero h'
    have hb₃ : (D.1 h3_diag₃).b = 0 := by
      have h := D.2 h3_diag₂ h3_diag₃
      rw [h3_diag₂_mul_h3_diag₃, map_zero, mul_comm (D.1 h3_diag₂) h3_diag₃] at h
      have h' := congrArg H3Zorn.b h.symm
      change (h3_diag₃ * D.1 h3_diag₂ + h3_diag₂ * D.1 h3_diag₃).b = 0 at h'
      rw [add_readback, ext_h3_mul_diag₃, ext_h3_mul_diag₂] at h'
      dsimp at h'
      change (1 / 2 : ℝ) • (D.1 h3_diag₂).b + (1 / 2 : ℝ) • (D.1 h3_diag₃).b = 0 at h'
      rw [hb, smul_zero, zero_add] at h'
      exact zorn_eq_zero_of_half_smul_eq_zero h'
    exact ⟨ext_h3 _ _ hα1₁ hα2₁ hα3₁ ha hb₁ hc₁,
      ext_h3 _ _ hα1₂ hα2₂ hα3₂ ha₂ hb hc₂,
      ext_h3 _ _ hα1₃ hα2₃ hα3₃ ha₃ hb₃ hc⟩
  · rintro ⟨h1, h2, h3⟩
    change ((D.1 h3_diag₁).a, (D.1 h3_diag₂).b, (D.1 h3_diag₃).c) = (0, 0, 0)
    rw [h1, h2, h3]
    rfl

end PeirceShiftSplitting

section TrialityUpperBound

/-- Skew-adjoint endomorphisms of `(ZornVectorMatrix ℝ, zornBilin)`. -/
def zornSkewAdjointSubmodule : Submodule ℝ (Module.End ℝ (ZornVectorMatrix ℝ)) where
  carrier := {f | ∀ x y : ZornVectorMatrix ℝ, zornBilin (f x) y + zornBilin x (f y) = 0}
  zero_mem' x y := by simp [zornBilin, ZornVectorMatrix.zero_mul, ZornVectorMatrix.mul_zero, ZornVectorMatrix.trace_zero]
  add_mem' {f g} hf hg x y := by
    simp only [LinearMap.add_apply, zornBilin_add_left, zornBilin_add_right]
    rw [add_add_add_comm, hf x y, hg x y, zero_add]
  smul_mem' r {f} hf x y := by
    simp only [LinearMap.smul_apply, zornBilin_smul_left, zornBilin_smul_right]
    rw [← mul_add, hf x y, mul_zero]

/-- Strictly upper-triangular index pairs `(i, j)` with `i < j` in `Fin 8` (`28` pairs). -/
abbrev StrictPair8 := {p : Fin 8 × Fin 8 // p.1 < p.2}

theorem card_strictPair8 : Fintype.card StrictPair8 = 28 := by
  decide

private def skewAdjointToUpper :
    zornSkewAdjointSubmodule →ₗ[ℝ] (StrictPair8 → ℝ) where
  toFun f p := zornBilin (zorn_basis p.1.1) (f.1 (zorn_basis p.1.2))
  map_add' f g := by
    ext p
    change zornBilin (zorn_basis p.1.1) (f.1 (zorn_basis p.1.2) + g.1 (zorn_basis p.1.2)) = _
    exact zornBilin_add_right _ _ _
  map_smul' r f := by
    ext p
    change zornBilin (zorn_basis p.1.1) (r • f.1 (zorn_basis p.1.2)) = _
    exact zornBilin_smul_right _ _ _

private theorem skewAdjointToUpper_injective :
    Function.Injective skewAdjointToUpper := by
  intro f g hfg
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  have hbasis : ∀ i j : Fin 8,
      zornBilin (zorn_basis i) (f.1 (zorn_basis j)) =
        zornBilin (zorn_basis i) (g.1 (zorn_basis j)) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact congrFun hfg ⟨(i, j), hij⟩
    · have hf := f.2 (zorn_basis i) (zorn_basis i)
      have hg := g.2 (zorn_basis i) (zorn_basis i)
      rw [zornBilin_symm (f.1 (zorn_basis i))] at hf
      rw [zornBilin_symm (g.1 (zorn_basis i))] at hg
      linarith
    · have hf := f.2 (zorn_basis i) (zorn_basis j)
      have hg := g.2 (zorn_basis i) (zorn_basis j)
      have hji' := congrFun hfg ⟨(j, i), hji⟩
      dsimp [skewAdjointToUpper] at hji'
      rw [zornBilin_symm (f.1 (zorn_basis i)) (zorn_basis j)] at hf
      rw [zornBilin_symm (g.1 (zorn_basis i)) (zorn_basis j)] at hg
      linarith
  have hrow : ∀ j : Fin 8, f.1 (zorn_basis j) = g.1 (zorn_basis j) := by
    intro j
    apply sub_eq_zero.mp
    apply eq_zero_of_zornBilin_basis
    intro i
    rw [zornBilin_symm, show f.1 (zorn_basis j) - g.1 (zorn_basis j) =
      f.1 (zorn_basis j) + (-1 : ℝ) • g.1 (zorn_basis j) by module,
      zornBilin_add_right, zornBilin_smul_right, hbasis i j]
    ring
  rw [← zorn_basis_decomposition y]
  have hfsum : f.1 (∑ j : Fin 8, (match j with
      | 0 => y.a | 1 => y.v 0 | 2 => y.v 1 | 3 => y.v 2
      | 4 => y.w 0 | 5 => y.w 1 | 6 => y.w 2 | 7 => y.b) • zorn_basis j) =
      g.1 (∑ j : Fin 8, (match j with
        | 0 => y.a | 1 => y.v 0 | 2 => y.v 1 | 3 => y.v 2
        | 4 => y.w 0 | 5 => y.w 1 | 6 => y.w 2 | 7 => y.b) • zorn_basis j) := by
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hrow j]
  exact hfsum

theorem finrank_zornSkewAdjointSubmodule_le :
    Module.finrank ℝ zornSkewAdjointSubmodule ≤ 28 := by
  have hle := LinearMap.finrank_le_finrank_of_injective skewAdjointToUpper_injective
  simpa [Module.finrank_fintype_fun_eq_card, card_strictPair8] using hle

/-- Vanishing of the pure-imaginary left nucleus of `ZornVectorMatrix ℝ`:
if `trace u = 0` and `∀ y z, (u * y) * z = u * (y * z)`, then `u = 0`. -/
theorem zorn_pureImaginary_left_nucleus_eq_zero (u : ZornVectorMatrix ℝ)
    (htr : ZornVectorMatrix.trace u = 0)
    (hassoc : ∀ y z : ZornVectorMatrix ℝ,
      ZornVectorMatrix.mul (ZornVectorMatrix.mul u y) z =
        ZornVectorMatrix.mul u (ZornVectorMatrix.mul y z)) :
    u = 0 := by
  have hv : ∀ i : Fin 3,
      ZornVec3.cross u.v (ZornVec3.basis i) = 0 := by
    intro i
    have h := hassoc (ZornVectorMatrix.U i) ZornVectorMatrix.E11
    have hR : ZornVectorMatrix.mul (ZornVectorMatrix.U (R := ℝ) i) ZornVectorMatrix.E11 =
        ZornVectorMatrix.zero := by
      ext j <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVectorMatrix.E11,
        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    rw [hR, ZornVectorMatrix.mul_zero] at h
    have hw := congrArg ZornVectorMatrix.w h
    ext j
    have hwj := congrFun hw j
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVectorMatrix.E11,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross] at hwj ⊢
    linarith
  have hw : ∀ i : Fin 3,
      ZornVec3.cross u.w (ZornVec3.basis i) = 0 := by
    intro i
    have h := hassoc (ZornVectorMatrix.V i) ZornVectorMatrix.E22
    have hR : ZornVectorMatrix.mul (ZornVectorMatrix.V (R := ℝ) i) ZornVectorMatrix.E22 =
        ZornVectorMatrix.zero := by
      ext j <;> simp [ZornVectorMatrix.mul, ZornVectorMatrix.V, ZornVectorMatrix.E22,
        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    rw [hR, ZornVectorMatrix.mul_zero] at h
    have hv' := congrArg ZornVectorMatrix.v h
    ext j
    have hvj := congrFun hv' j
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.V, ZornVectorMatrix.E22,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross] at hvj ⊢
    linarith
  have hv0 : u.v = 0 := by
    ext i
    fin_cases i
    · have h1 := congrFun (hv 1) 2; simp [ZornVec3.cross, ZornVec3.basis] at h1; exact h1
    · have h2 := congrFun (hv 2) 0; simp [ZornVec3.cross, ZornVec3.basis] at h2; exact h2
    · have h0 := congrFun (hv 0) 1; simp [ZornVec3.cross, ZornVec3.basis] at h0; exact h0
  have hw0 : u.w = 0 := by
    ext i
    fin_cases i
    · have h1 := congrFun (hw 1) 2; simp [ZornVec3.cross, ZornVec3.basis] at h1; exact h1
    · have h2 := congrFun (hw 2) 0; simp [ZornVec3.cross, ZornVec3.basis] at h2; exact h2
    · have h0 := congrFun (hw 0) 1; simp [ZornVec3.cross, ZornVec3.basis] at h0; exact h0
  have ha : u.a = 0 := by
    have h := hassoc (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1)
    have h2 := congrArg (fun x : ZornVectorMatrix ℝ => x.w 2) h
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVec3.cross, ZornVec3.basis,
      ZornVec3.dot, hv0, hw0] at h2
    have hb : u.b = -u.a := by
      have : u.a + u.b = 0 := htr
      linarith
    linarith
  have hb : u.b = 0 := by
    have : u.a + u.b = 0 := htr
    linarith
  exact ZornVectorMatrix.ext ha (by rw [hv0]; rfl) (by rw [hw0]; rfl) hb

private theorem ker_peirceShiftEv_preserves_slots
    (D : LinearMap.ker peirceShiftEv) :
    (∀ x, ∃ a', D.1.1 (embedJ12 x) = embedJ12 a') ∧
    (∀ y, ∃ b', D.1.1 (embedJ23 y) = embedJ23 b') ∧
    (∀ z, ∃ c', D.1.1 (embedJ31 z) = embedJ31 c') := by
  obtain ⟨hd1, hd2, hd3⟩ := (ker_peirceShiftEv_iff_diags_zero D.1).mp D.2
  refine ⟨?_, ?_, ?_⟩
  · intro x
    let Y := D.1.1 (embedJ12 x)
    have h1 := D.1.2 h3_diag₁ (embedJ12 x)
    rw [h3_diag₁_mul_embedJ12, map_smul, hd1, zero_mul, zero_add] at h1
    have h2 := D.1.2 h3_diag₂ (embedJ12 x)
    rw [h3_diag₂_mul_embedJ12, map_smul, hd2, zero_mul, zero_add] at h2
    rw [ext_h3_mul_diag₁] at h1
    rw [ext_h3_mul_diag₂] at h2
    refine ⟨Y.a, ext_h3 _ _ ?_ ?_ ?_ rfl ?_ ?_⟩
    · have ht := congrArg H3Zorn.α₁ h1
      change (1 / 2 : ℝ) * Y.α₁ = Y.α₁ at ht
      have ht' : (1 / 2 - 1 : ℝ) * Y.α₁ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
      exact (mul_eq_zero.mp ht').resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.α₂ h1
      change (1 / 2 : ℝ) * Y.α₂ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.α₃ h1
      change (1 / 2 : ℝ) * Y.α₃ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.b h1
      change (1 / 2 : ℝ) • Y.b = 0 at ht
      exact zorn_eq_zero_of_half_smul_eq_zero ht
    · have ht := congrArg H3Zorn.c h2
      change (1 / 2 : ℝ) • Y.c = 0 at ht
      exact zorn_eq_zero_of_half_smul_eq_zero ht
  · intro y
    let Y := D.1.1 (embedJ23 y)
    have h2 := D.1.2 h3_diag₂ (embedJ23 y)
    rw [h3_diag₂_mul_embedJ23, map_smul, hd2, zero_mul, zero_add] at h2
    have h3 := D.1.2 h3_diag₃ (embedJ23 y)
    rw [h3_diag₃_mul_embedJ23, map_smul, hd3, zero_mul, zero_add] at h3
    rw [ext_h3_mul_diag₂] at h2
    rw [ext_h3_mul_diag₃] at h3
    refine ⟨Y.b, ext_h3 _ _ ?_ ?_ ?_ ?_ rfl ?_⟩
    · have ht := congrArg H3Zorn.α₁ h2
      change (1 / 2 : ℝ) * Y.α₁ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.α₂ h2
      change (1 / 2 : ℝ) * Y.α₂ = Y.α₂ at ht
      have ht' : (1 / 2 - 1 : ℝ) * Y.α₂ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
      exact (mul_eq_zero.mp ht').resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.α₃ h2
      change (1 / 2 : ℝ) * Y.α₃ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.a h3
      change (1 / 2 : ℝ) • Y.a = 0 at ht
      exact zorn_eq_zero_of_half_smul_eq_zero ht
    · have ht := congrArg H3Zorn.c h2
      change (1 / 2 : ℝ) • Y.c = 0 at ht
      exact zorn_eq_zero_of_half_smul_eq_zero ht
  · intro z
    let Y := D.1.1 (embedJ31 z)
    have h3 := D.1.2 h3_diag₃ (embedJ31 z)
    rw [h3_diag₃_mul_embedJ31, map_smul, hd3, zero_mul, zero_add] at h3
    have h1 := D.1.2 h3_diag₁ (embedJ31 z)
    rw [h3_diag₁_mul_embedJ31, map_smul, hd1, zero_mul, zero_add] at h1
    rw [ext_h3_mul_diag₃] at h3
    rw [ext_h3_mul_diag₁] at h1
    refine ⟨Y.c, ext_h3 _ _ ?_ ?_ ?_ ?_ ?_ rfl⟩
    · have ht := congrArg H3Zorn.α₁ h3
      change (1 / 2 : ℝ) * Y.α₁ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.α₂ h3
      change (1 / 2 : ℝ) * Y.α₂ = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.α₃ h3
      change (1 / 2 : ℝ) * Y.α₃ = Y.α₃ at ht
      have ht' : (1 / 2 - 1 : ℝ) * Y.α₃ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
      exact (mul_eq_zero.mp ht').resolve_left (by norm_num)
    · have ht := congrArg H3Zorn.a h3
      change (1 / 2 : ℝ) • Y.a = 0 at ht
      exact zorn_eq_zero_of_half_smul_eq_zero ht
    · have ht := congrArg H3Zorn.b h1
      change (1 / 2 : ℝ) • Y.b = 0 at ht
      exact zorn_eq_zero_of_half_smul_eq_zero ht

private def kerPeirceSlotA (D : LinearMap.ker peirceShiftEv) :
    Module.End ℝ (ZornVectorMatrix ℝ) where
  toFun x := (D.1.1 (embedJ12 x)).a
  map_add' x y := by
    change (D.1.1 (embedJ12LM (x + y))).a = _
    rw [embedJ12LM.map_add, map_add]
    rfl
  map_smul' r x := by
    change (D.1.1 (embedJ12LM (r • x))).a = _
    rw [embedJ12LM.map_smul, map_smul]
    rfl

private def kerPeirceSlotB (D : LinearMap.ker peirceShiftEv) :
    Module.End ℝ (ZornVectorMatrix ℝ) where
  toFun y := (D.1.1 (embedJ23 y)).b
  map_add' x y := by
    change (D.1.1 (embedJ23LM (x + y))).b = _
    rw [embedJ23LM.map_add, map_add]
    rfl
  map_smul' r x := by
    change (D.1.1 (embedJ23LM (r • x))).b = _
    rw [embedJ23LM.map_smul, map_smul]
    rfl

private def kerPeirceSlotC (D : LinearMap.ker peirceShiftEv) :
    Module.End ℝ (ZornVectorMatrix ℝ) where
  toFun z := (D.1.1 (embedJ31 z)).c
  map_add' x y := by
    change (D.1.1 (embedJ31LM (x + y))).c = _
    rw [embedJ31LM.map_add, map_add]
    rfl
  map_smul' r x := by
    change (D.1.1 (embedJ31LM (r • x))).c = _
    rw [embedJ31LM.map_smul, map_smul]
    rfl

private theorem kerPeirceSlotA_skew (D : LinearMap.ker peirceShiftEv) :
    kerPeirceSlotA D ∈ zornSkewAdjointSubmodule := by
  intro x y
  obtain ⟨hd1, hd2, _⟩ := (ker_peirceShiftEv_iff_diags_zero D.1).mp D.2
  have hslots := ker_peirceShiftEv_preserves_slots D
  rcases hslots.1 x with ⟨a', ha'⟩
  rcases hslots.1 y with ⟨b', hb'⟩
  have hxa : a' = kerPeirceSlotA D x := (congrArg H3Zorn.a ha').symm
  have hyb : b' = kerPeirceSlotA D y := (congrArg H3Zorn.a hb').symm
  have hleib := D.1.2 (embedJ12 x) (embedJ12 y)
  rw [embedJ12_mul_embedJ12, map_smul, map_add, hd1, hd2, add_zero, smul_zero,
    ha', hb', hxa, hyb, embedJ12_mul_embedJ12, embedJ12_mul_embedJ12] at hleib
  have hα := congrArg H3Zorn.α₁ hleib.symm
  simp [h3_diag₁, h3_diag₂, add_readback, smul_readback] at hα
  rw [zornBilin_symm y, ← mul_add] at hα
  exact (mul_eq_zero.mp hα).resolve_left (by norm_num)

private theorem kerPeirceSlotC_skew (D : LinearMap.ker peirceShiftEv) :
    kerPeirceSlotC D ∈ zornSkewAdjointSubmodule := by
  intro x y
  obtain ⟨_, _, hd3⟩ := (ker_peirceShiftEv_iff_diags_zero D.1).mp D.2
  obtain ⟨hd1, _, _⟩ := (ker_peirceShiftEv_iff_diags_zero D.1).mp D.2
  have hslots := ker_peirceShiftEv_preserves_slots D
  rcases hslots.2.2 x with ⟨a', ha'⟩
  rcases hslots.2.2 y with ⟨b', hb'⟩
  have hxa : a' = kerPeirceSlotC D x := (congrArg H3Zorn.c ha').symm
  have hyb : b' = kerPeirceSlotC D y := (congrArg H3Zorn.c hb').symm
  have hleib := D.1.2 (embedJ31 x) (embedJ31 y)
  rw [embedJ31_mul_embedJ31, map_smul, map_add, hd3, hd1, add_zero, smul_zero,
    ha', hb', hxa, hyb, embedJ31_mul_embedJ31, embedJ31_mul_embedJ31] at hleib
  have hα := congrArg H3Zorn.α₁ hleib.symm
  simp [h3_diag₃, h3_diag₁, add_readback, smul_readback] at hα
  rw [zornBilin_symm y, ← mul_add] at hα
  exact (mul_eq_zero.mp hα).resolve_left (by norm_num)

private def kerPeirceResA :
    LinearMap.ker peirceShiftEv →ₗ[ℝ] zornSkewAdjointSubmodule where
  toFun D := ⟨kerPeirceSlotA D, kerPeirceSlotA_skew D⟩
  map_add' D E := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl
  map_smul' r D := by apply Subtype.ext; apply LinearMap.ext; intro x; rfl

private theorem kerPeirceResA_injective :
    Function.Injective kerPeirceResA := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  have hA0 : ∀ x : ZornVectorMatrix ℝ, kerPeirceSlotA D x = 0 := by
    intro x
    have := congrArg (fun f : zornSkewAdjointSubmodule => f.1 x) hD
    exact this
  have hslots := ker_peirceShiftEv_preserves_slots D
  have hDA : ∀ x, D.1.1 (embedJ12 x) = 0 := by
    intro x
    rcases hslots.1 x with ⟨a', ha'⟩
    have ha'' : a' = kerPeirceSlotA D x := (congrArg H3Zorn.a ha').symm
    rw [ha', ha'', hA0 x]
    rfl
  have hDB_eq : ∀ y, D.1.1 (embedJ23 y) = embedJ23 (kerPeirceSlotB D y) := by
    intro y
    rcases hslots.2.1 y with ⟨b', hb'⟩
    have hb'' : b' = kerPeirceSlotB D y := (congrArg H3Zorn.b hb').symm
    rw [hb', hb'']
  have hDC_eq : ∀ z, D.1.1 (embedJ31 z) = embedJ31 (kerPeirceSlotC D z) := by
    intro z
    rcases hslots.2.2 z with ⟨c', hc'⟩
    have hc'' : c' = kerPeirceSlotC D z := (congrArg H3Zorn.c hc').symm
    rw [hc', hc'']
  have hleib12_23 : ∀ x y : ZornVectorMatrix ℝ,
      kerPeirceSlotC D (ZornVectorMatrix.mul (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)) =
        ZornVectorMatrix.mul (ZornVectorMatrix.conj (kerPeirceSlotB D y))
          (ZornVectorMatrix.conj x) := by
    intro x y
    have h := D.1.2 (embedJ12 x) (embedJ23 y)
    rw [embedJ12_mul_embedJ23, map_smul, hDC_eq, hDA x, zero_mul, zero_add,
      hDB_eq y, embedJ12_mul_embedJ23] at h
    have hc' : (1 / 2 : ℝ) •
          kerPeirceSlotC D (ZornVectorMatrix.mul (ZornVectorMatrix.conj y) (ZornVectorMatrix.conj x)) =
        (1 / 2 : ℝ) •
          ZornVectorMatrix.mul (ZornVectorMatrix.conj (kerPeirceSlotB D y)) (ZornVectorMatrix.conj x) :=
      congrArg H3Zorn.c h
    have h2 := congrArg ((2 : ℝ) • ·) hc'
    simpa only [smul_smul, show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_smul] using h2
  let u : ZornVectorMatrix ℝ := kerPeirceSlotC D ZornVectorMatrix.one
  have htrace_u : ZornVectorMatrix.trace u = 0 := by
    have hskew := kerPeirceSlotC_skew D ZornVectorMatrix.one ZornVectorMatrix.one
    change zornBilin u ZornVectorMatrix.one + zornBilin ZornVectorMatrix.one u = 0 at hskew
    have h1 : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
        ZornVectorMatrix.one := by
      ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
    have hzb : zornBilin u ZornVectorMatrix.one = ZornVectorMatrix.trace u := by
      simp [zornBilin, h1, ZornVectorMatrix.mul_one]
    rw [zornBilin_symm ZornVectorMatrix.one u, hzb] at hskew
    linarith
  have hDC_mul : ∀ A B : ZornVectorMatrix ℝ,
      kerPeirceSlotC D (ZornVectorMatrix.mul A B) =
        ZornVectorMatrix.mul (kerPeirceSlotC D A) B := by
    intro A B
    have h1 := hleib12_23 ZornVectorMatrix.one (ZornVectorMatrix.conj A)
    have hc1 : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
        ZornVectorMatrix.one := by
      ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
    rw [hc1, ZornVectorMatrix.conj_conj, ZornVectorMatrix.mul_one, ZornVectorMatrix.mul_one] at h1
    have h2 := hleib12_23 (ZornVectorMatrix.conj B) (ZornVectorMatrix.conj A)
    rw [ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj] at h2
    rw [h2, ← h1]
  have hDC_u : ∀ B : ZornVectorMatrix ℝ,
      kerPeirceSlotC D B = ZornVectorMatrix.mul u B := by
    intro B
    have h := hDC_mul ZornVectorMatrix.one B
    rw [ZornVectorMatrix.one_mul] at h
    exact h
  have hu_assoc : ∀ A B : ZornVectorMatrix ℝ,
      ZornVectorMatrix.mul (ZornVectorMatrix.mul u A) B =
        ZornVectorMatrix.mul u (ZornVectorMatrix.mul A B) := by
    intro A B
    rw [← hDC_u A, ← hDC_mul A B, hDC_u (ZornVectorMatrix.mul A B)]
  have hu0 : u = 0 := zorn_pureImaginary_left_nucleus_eq_zero u htrace_u hu_assoc
  have hDC0 : ∀ z, kerPeirceSlotC D z = 0 := by
    intro z
    rw [hDC_u z, hu0]
    exact ZornVectorMatrix.zero_mul z
  have hDB0 : ∀ y, kerPeirceSlotB D y = 0 := by
    intro y
    have h := hleib12_23 ZornVectorMatrix.one y
    have hc1 : ZornVectorMatrix.conj (ZornVectorMatrix.one : ZornVectorMatrix ℝ) =
        ZornVectorMatrix.one := by
      ext i <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.one]
    rw [hc1, ZornVectorMatrix.mul_one, ZornVectorMatrix.mul_one, hDC0] at h
    have hc := congrArg ZornVectorMatrix.conj h.symm
    simpa [ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_zero] using hc
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro W
  obtain ⟨hd1, hd2, hd3⟩ := (ker_peirceShiftEv_iff_diags_zero D.1).mp D.2
  have hW : W = W.α₁ • h3_diag₁ + W.α₂ • h3_diag₂ + W.α₃ • h3_diag₃ +
      embedJ12 W.a + embedJ23 W.b + embedJ31 W.c := by
    apply ext_h3
    · simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31, add_readback, smul_readback]
    · simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31, add_readback, smul_readback]
    · simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31, add_readback, smul_readback]
    · simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31, add_readback, smul_readback,
        ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]
    · simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31, add_readback, smul_readback,
        ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]
    · simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31, add_readback, smul_readback,
        ZornVectorMatrix.add_zero, ZornVectorMatrix.smul_zero]
  rw [hW]
  simp only [map_add, map_smul, hd1, hd2, hd3, hDA, hDB_eq, hDC_eq, hDB0, hDC0, smul_zero,
    add_zero, zero_add, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  apply ext_h3 <;> simp [embedJ23, embedJ31, add_readback, ZornVectorMatrix.add_zero]

private theorem finrank_of_linear_split
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (ev : E →ₗ[ℝ] F) (σ : F →ₗ[ℝ] E) (h_sec : ∀ y, ev (σ y) = y) :
    Module.finrank ℝ E = Module.finrank ℝ (LinearMap.ker ev) + Module.finrank ℝ F := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker ev
  have h_range : LinearMap.range ev = ⊤ := by
    ext y
    simp only [Submodule.mem_top, iff_true, LinearMap.mem_range]
    exact ⟨σ y, h_sec y⟩
  rw [h_range, finrank_top] at h_rn
  omega

theorem finrank_ker_peirceShiftEv_le :
    Module.finrank ℝ (LinearMap.ker peirceShiftEv) ≤ 28 := by
  exact le_trans (LinearMap.finrank_le_finrank_of_injective kerPeirceResA_injective)
    finrank_zornSkewAdjointSubmodule_le

theorem finrank_H3ZornF4Derivations_le_52 :
    Module.finrank ℝ H3ZornF4Derivations ≤ 52 := by
  have hsplit := finrank_of_linear_split
    peirceShiftEv peirceShiftSection peirceShiftEv_section
  have htriple : Module.finrank ℝ ZornTriple = 24 := by
    simp [ZornTriple, Module.finrank_prod, finrank_zornVectorMatrix]
  rw [htriple] at hsplit
  have hle := finrank_ker_peirceShiftEv_le
  omega

end TrialityUpperBound

section TrialityBasisLowerBoundAndClosure

/-- Exact 28 pairs `(i, j)` with `i < j` matching `f4Basis` indices `24..51`. -/
def trialityPair (k : Fin 28) : Fin 8 × Fin 8 :=
  match k.val with
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (0, 4) | 4 => (0, 5) | 5 => (0, 6) | 6 => (0, 7)
  | 7 => (1, 2) | 8 => (1, 3) | 9 => (1, 4) | 10 => (1, 5) | 11 => (1, 6) | 12 => (1, 7)
  | 13 => (2, 3) | 14 => (2, 4) | 15 => (2, 5) | 16 => (2, 6) | 17 => (2, 7)
  | 18 => (3, 4) | 19 => (3, 5) | 20 => (3, 6) | 21 => (3, 7)
  | 22 => (4, 5) | 23 => (4, 6) | 24 => (4, 7)
  | 25 => (5, 6) | 26 => (5, 7)
  | 27 => (6, 7)
  | _ => (0, 1)

theorem trialityPair_lt (k : Fin 28) : (trialityPair k).1 < (trialityPair k).2 := by
  fin_cases k <;> decide

private theorem trialityPair_injective : Function.Injective trialityPair := by
  decide

theorem trialityDerivation_eq_inner (k : Fin 28) :
    trialityDerivation k =
      (h3ZornJordanInnerDerivation (embedJ12 (zorn_basis (trialityPair k).1))
        (embedJ12 (zorn_basis (trialityPair k).2)) : EndH3) := by
  fin_cases k <;> rfl

theorem inner12_embedJ12_a (x y z : ZornVectorMatrix ℝ) :
    ((h3ZornJordanInnerDerivation (embedJ12 x) (embedJ12 y) : EndH3) (embedJ12 z)).a =
      (1 / 2 : ℝ) • (zornBilin y z • x - zornBilin x z • y) := by
  rw [h3ZornJordanInnerDerivation_apply, embedJ12_mul_embedJ12, embedJ12_mul_embedJ12]
  simp only [mul_smul_comm, mul_add,
    mul_comm (embedJ12 x) h3_diag₁, mul_comm (embedJ12 x) h3_diag₂,
    mul_comm (embedJ12 y) h3_diag₁, mul_comm (embedJ12 y) h3_diag₂,
    h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12]
  have hhalf : (1 / 2 : ℝ) • embedJ12 x + (1 / 2 : ℝ) • embedJ12 x = embedJ12 x := by module
  have hhalf' : (1 / 2 : ℝ) • embedJ12 y + (1 / 2 : ℝ) • embedJ12 y = embedJ12 y := by module
  rw [hhalf, hhalf']
  change (1 / 2 * zornBilin y z) • x - (1 / 2 * zornBilin x z) • y =
    (1 / 2 : ℝ) • (zornBilin y z • x - zornBilin x z • y)
  rw [mul_smul, mul_smul, ← smul_sub]

private def trialitySeparatingCoord (k : Fin 28) : EndH3 →ₗ[ℝ] ℝ where
  toFun D := zornBilin (zornDualBasis (trialityPair k).1)
    ((D (embedJ12 (zornDualBasis (trialityPair k).2))).a)
  map_add' D E := by
    change zornBilin (zornDualBasis (trialityPair k).1)
      ((D (embedJ12 (zornDualBasis (trialityPair k).2))).a +
        (E (embedJ12 (zornDualBasis (trialityPair k).2))).a) = _
    exact zornBilin_add_right _ _ _
  map_smul' r D := by
    change zornBilin (zornDualBasis (trialityPair k).1)
      (r • (D (embedJ12 (zornDualBasis (trialityPair k).2))).a) = _
    exact zornBilin_smul_right _ _ _

theorem trialityDerivation_linearIndependent :
    LinearIndependent ℝ trialityDerivation := by
  refine linearIndependent_of_separating_coordinate trialityDerivation trialitySeparatingCoord
    ?_ ?_
  · intro k
    rw [trialityDerivation_eq_inner k]
    dsimp [trialitySeparatingCoord]
    rw [inner12_embedJ12_a]
    have hlin : zornBilin (zornDualBasis (trialityPair k).1)
        ((1 / 2 : ℝ) • (zornBilin (zorn_basis (trialityPair k).2)
            (zornDualBasis (trialityPair k).2) • zorn_basis (trialityPair k).1 -
          zornBilin (zorn_basis (trialityPair k).1)
            (zornDualBasis (trialityPair k).2) • zorn_basis (trialityPair k).2)) =
        (1 / 2 : ℝ) := by
      have hne : (trialityPair k).1 ≠ (trialityPair k).2 := ne_of_lt (trialityPair_lt k)
      rw [zornBilin_smul_right, show ∀ A B : ZornVectorMatrix ℝ, A - B = A + (-1 : ℝ) • B by
        intro _ _; module, zornBilin_add_right, zornBilin_smul_right,
        zornBilin_smul_right, zornBilin_smul_right, zornBilin_basis_dual,
        zornBilin_basis_dual, zornBilin_dual_basis, zornBilin_dual_basis]
      simp [hne]
    rw [hlin]
    norm_num
  · intro k j hkj
    rw [trialityDerivation_eq_inner j]
    dsimp [trialitySeparatingCoord]
    rw [inner12_embedJ12_a]
    have hlt_j := trialityPair_lt j
    have hlt_k := trialityPair_lt k
    rw [zornBilin_smul_right, show ∀ A B : ZornVectorMatrix ℝ, A - B = A + (-1 : ℝ) • B by
      intro _ _; module, zornBilin_add_right, zornBilin_smul_right,
      zornBilin_smul_right, zornBilin_smul_right, zornBilin_basis_dual,
      zornBilin_basis_dual, zornBilin_dual_basis, zornBilin_dual_basis]
    have hneq_pair : trialityPair j ≠ trialityPair k :=
      fun h => hkj (trialityPair_injective h.symm)
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
    have hexp :
        (1 / 2 : ℝ) *
            ((if (trialityPair j).2 = (trialityPair k).2 then (1 : ℝ) else 0) *
                (if (trialityPair k).1 = (trialityPair j).1 then (1 : ℝ) else 0) +
              (-1 : ℝ) *
                ((if (trialityPair j).1 = (trialityPair k).2 then (1 : ℝ) else 0) *
                  (if (trialityPair k).1 = (trialityPair j).2 then (1 : ℝ) else 0))) =
          0 := by
      rw [ha0, hb0]
      ring
    simpa [mul_assoc] using hexp

theorem trialityBasisSpan_finrank :
    Module.finrank ℝ trialityBasisSpan = 28 := by
  rw [trialityBasisSpan]
  exact (finrank_span_eq_card trialityDerivation_linearIndependent).trans (by simp)

private theorem trialityDerivation_mem_ker_peirceShiftEv (k : Fin 28) :
    (⟨trialityDerivation k, (f4Basis (trialityIndex k)).property⟩ : H3ZornF4Derivations) ∈
      LinearMap.ker peirceShiftEv := by
  rw [ker_peirceShiftEv_iff_diags_zero]
  change (trialityDerivation k) h3_diag₁ = 0 ∧
    (trialityDerivation k) h3_diag₂ = 0 ∧ (trialityDerivation k) h3_diag₃ = 0
  rw [trialityDerivation_eq_inner k]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [h3ZornJordanInnerDerivation_apply]
  · rw [mul_comm (embedJ12 (zorn_basis (trialityPair k).2)) h3_diag₁,
      h3_diag₁_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12,
      mul_comm (embedJ12 (zorn_basis (trialityPair k).1)) h3_diag₁,
      h3_diag₁_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12,
      zornBilin_symm (zorn_basis (trialityPair k).1)]
    module
  · rw [mul_comm (embedJ12 (zorn_basis (trialityPair k).2)) h3_diag₂,
      h3_diag₂_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12,
      mul_comm (embedJ12 (zorn_basis (trialityPair k).1)) h3_diag₂,
      h3_diag₂_mul_embedJ12, mul_smul_comm, embedJ12_mul_embedJ12,
      zornBilin_symm (zorn_basis (trialityPair k).1)]
    module
  · rw [mul_comm (embedJ12 (zorn_basis (trialityPair k).2)) h3_diag₃,
      h3_diag₃_mul_embedJ12, mul_zero,
      mul_comm (embedJ12 (zorn_basis (trialityPair k).1)) h3_diag₃,
      h3_diag₃_mul_embedJ12, mul_zero, sub_self]

theorem trialityBasisSpan_le_f4BasisSpan :
    trialityBasisSpan ≤ f4BasisSpan := by
  rw [trialityBasisSpan, f4BasisSpan]
  refine Submodule.span_le.mpr ?_
  rintro D ⟨k, rfl⟩
  exact Submodule.subset_span ⟨trialityIndex k, rfl⟩

theorem peirceShiftBasisSpan_le_f4BasisSpan :
    peirceShiftBasisSpan ≤ f4BasisSpan := by
  rw [peirceShiftBasisSpan, f4BasisSpan]
  refine Submodule.span_le.mpr ?_
  rintro D ⟨k, rfl⟩
  exact Submodule.subset_span ⟨shiftIndex k, rfl⟩

/-- **Unconditional Exact Generation Theorem**: the 52 explicit generators in
`f4Basis` span the entire derivation Lie algebra `H3ZornF4Derivations`. -/
theorem f4BasisSpan_eq_H3ZornF4Derivations :
    f4BasisSpan = H3ZornF4Derivations.toSubmodule := by
  apply le_antisymm f4BasisSpan_le_F4Derivations
  let K : Submodule ℝ EndH3 :=
    (LinearMap.ker peirceShiftEv).map H3ZornF4Derivations.toSubmodule.subtype
  have htri_le_K : trialityBasisSpan ≤ K := by
    rw [trialityBasisSpan]
    refine Submodule.span_le.mpr ?_
    rintro D ⟨k, rfl⟩
    exact ⟨⟨trialityDerivation k, (f4Basis (trialityIndex k)).property⟩,
      trialityDerivation_mem_ker_peirceShiftEv k, rfl⟩
  have hK_fin : Module.finrank ℝ K ≤ 28 := by
    rw [← ((LinearMap.ker peirceShiftEv).equivMapOfInjective
      H3ZornF4Derivations.toSubmodule.subtype H3ZornF4Derivations.toSubmodule.injective_subtype).finrank_eq]
    exact finrank_ker_peirceShiftEv_le
  have htri_eq_K : trialityBasisSpan = K := by
    have : Module.Finite ℝ K :=
      Module.Finite.equiv
        ((LinearMap.ker peirceShiftEv).equivMapOfInjective
          H3ZornF4Derivations.toSubmodule.subtype H3ZornF4Derivations.toSubmodule.injective_subtype)
    apply Submodule.eq_of_le_of_finrank_le htri_le_K
    rw [trialityBasisSpan_finrank]
    exact hK_fin
  intro D hD
  let D_sub : H3ZornF4Derivations := ⟨D, hD⟩
  let S : H3ZornF4Derivations := peirceShiftSection (peirceShiftEv D_sub)
  let R : H3ZornF4Derivations := D_sub - S
  have hR_ker : R ∈ LinearMap.ker peirceShiftEv := by
    simp only [LinearMap.mem_ker, map_sub, R, S, peirceShiftEv_section, sub_self]
  have hR_tri : (R : EndH3) ∈ trialityBasisSpan := by
    rw [htri_eq_K]
    exact ⟨R, hR_ker, rfl⟩
  have hS_shift : (S : EndH3) ∈ peirceShiftBasisSpan :=
    peirceShiftSection_mem_peirceShiftBasisSpan _
  have hdecomp : D = (S : EndH3) + (R : EndH3) := by
    dsimp [R, S, D_sub]
    abel
  rw [hdecomp]
  exact Submodule.add_mem _
    (peirceShiftBasisSpan_le_f4BasisSpan hS_shift)
    (trialityBasisSpan_le_f4BasisSpan hR_tri)

/-- **Unconditional Exact Dimension of `𝔣₄ = Der(H₃(𝕆_s))`**:
`Module.finrank ℝ H3ZornF4Derivations = 52`. -/
theorem finrank_H3ZornF4Derivations :
    Module.finrank ℝ H3ZornF4Derivations = 52 := by
  have hsplit := finrank_of_linear_split
    peirceShiftEv peirceShiftSection peirceShiftEv_section
  have htriple : Module.finrank ℝ ZornTriple = 24 := by
    simp [ZornTriple, Module.finrank_prod, finrank_zornVectorMatrix]
  have hK_ge : 28 ≤ Module.finrank ℝ (LinearMap.ker peirceShiftEv) := by
    let K : Submodule ℝ EndH3 :=
      (LinearMap.ker peirceShiftEv).map H3ZornF4Derivations.toSubmodule.subtype
    have htri_le_K : trialityBasisSpan ≤ K := by
      rw [trialityBasisSpan]
      refine Submodule.span_le.mpr ?_
      rintro D ⟨k, rfl⟩
      exact ⟨⟨trialityDerivation k, (f4Basis (trialityIndex k)).property⟩,
        trialityDerivation_mem_ker_peirceShiftEv k, rfl⟩
    have : Module.Finite ℝ K :=
      Module.Finite.equiv
        ((LinearMap.ker peirceShiftEv).equivMapOfInjective
          H3ZornF4Derivations.toSubmodule.subtype H3ZornF4Derivations.toSubmodule.injective_subtype)
    have hfin := Submodule.finrank_mono htri_le_K
    rw [trialityBasisSpan_finrank] at hfin
    exact hfin.trans_eq
      ((LinearMap.ker peirceShiftEv).equivMapOfInjective
        H3ZornF4Derivations.toSubmodule.subtype
        H3ZornF4Derivations.toSubmodule.injective_subtype).finrank_eq.symm
  have hK_eq : Module.finrank ℝ (LinearMap.ker peirceShiftEv) = 28 :=
    le_antisymm finrank_ker_peirceShiftEv_le hK_ge
  rw [hsplit, hK_eq, htriple]

theorem finrank_f4BasisSpan : Module.finrank ℝ f4BasisSpan = 52 := by
  rw [f4BasisSpan_eq_H3ZornF4Derivations]
  exact finrank_H3ZornF4Derivations

end TrialityBasisLowerBoundAndClosure

end InfoGeometry.Algebra
