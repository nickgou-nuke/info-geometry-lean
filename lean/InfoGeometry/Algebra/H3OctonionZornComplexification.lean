/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3OctonionLieAlgebra
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Basic.Complex.Basic

/-!
# Complexification Equivalence `H₃(𝕆) ⊗ ℝ ℂ ≃ H₃(𝕆_s) ⊗ ℝ ℂ` and `E₆(ℂ)` / `F₄(ℂ)` Isomorphisms

This module proves that the compact and split octonions and Albert Jordan algebras become
isomorphic upon complexification:

1. `octonionComplexEquiv : CompactOctonion ℂ ≃ₗ[ℂ] ZornVectorMatrix ℂ` preserving `1`, `mul`,
   `conj`, `trace`, and `norm`.
2. `h3OctonionComplexEquiv : H3Octonion ℂ ≃ₗ[ℂ] H3Zorn ℂ` preserving `1`, `linearTrace`,
   `traceBilin`, `normCubic`, `adjointQuad`, `crossProduct`, `U`, `T`, `h3NormTrilin`, and
   the complex Jordan product `candidateJordanMulOctℂ` / `candidateJordanMulZornℂ`.
3. `h3OctonionTensorEquivH3Zorn : ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] ℂ ⊗[ℝ] H3Zorn ℝ` via the
   real/imaginary base-change equivalences `tensorEquivH3Octonion` and `tensorEquivH3Zorn`.
4. Diamond-free complexified Lie algebra isomorphisms via `Mathlib.Algebra.Lie.BaseChange`:
   - `h3OctonionCubicStabilizerBaseChangeEquiv : ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3zornCubicStabilizer` (`E₆(ℂ)`)
   - `h3OctonionF4DerivationsBaseChangeEquiv : ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] H3ZornF4Derivations` (`F₄(ℂ)`)
-/

noncomputable section

namespace InfoGeometry.Algebra

open scoped TensorProduct

section ComplexOctonionIsomorphism

/-- Explicit `ℂ`-linear map from `CompactOctonion ℂ` to `ZornVectorMatrix ℂ` diagonalizing
the `e₇` imaginary axis (`e₇² = -1` over `ℂ`). -/
def octonionComplexToZornFun (x : CompactOctonion ℂ) : ZornVectorMatrix ℂ where
  a := x.e0 - Complex.I * x.e7
  v := fun i => match i with
    | 0 => -x.e1 + Complex.I * x.e3
    | 1 => -x.e2 + Complex.I * x.e6
    | 2 => -x.e4 + Complex.I * x.e5
  w := fun i => match i with
    | 0 => x.e1 + Complex.I * x.e3
    | 1 => x.e2 + Complex.I * x.e6
    | 2 => x.e4 + Complex.I * x.e5
  b := x.e0 + Complex.I * x.e7

/-- Explicit inverse `ℂ`-linear map from `ZornVectorMatrix ℂ` to `CompactOctonion ℂ`. -/
def zornToOctonionComplexFun (X : ZornVectorMatrix ℂ) : CompactOctonion ℂ where
  e0 := (1 / 2 : ℂ) * (X.a + X.b)
  e1 := (1 / 2 : ℂ) * (X.w 0 - X.v 0)
  e2 := (1 / 2 : ℂ) * (X.w 1 - X.v 1)
  e3 := -(Complex.I / 2) * (X.v 0 + X.w 0)
  e4 := (1 / 2 : ℂ) * (X.w 2 - X.v 2)
  e5 := -(Complex.I / 2) * (X.v 2 + X.w 2)
  e6 := -(Complex.I / 2) * (X.v 1 + X.w 1)
  e7 := (Complex.I / 2) * (X.a - X.b)

/-- Explicit `ℂ`-linear equivalence `CompactOctonion ℂ ≃ₗ[ℂ] ZornVectorMatrix ℂ`. -/
def octonionComplexEquiv : CompactOctonion ℂ ≃ₗ[ℂ] ZornVectorMatrix ℂ where
  toFun := octonionComplexToZornFun
  invFun := zornToOctonionComplexFun
  map_add' x y := by
    ext i <;> (try fin_cases i) <;> simp [octonionComplexToZornFun] <;> ring
  map_smul' z x := by
    ext i <;> (try fin_cases i) <;>
      simp [octonionComplexToZornFun, ZornVectorMatrix.smul] <;> ring
  left_inv x := by
    ext <;> simp [octonionComplexToZornFun, zornToOctonionComplexFun] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> any_goals ring
  right_inv X := by
    ext i <;> (try fin_cases i) <;>
      simp [octonionComplexToZornFun, zornToOctonionComplexFun] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> any_goals ring

@[simp] theorem octonionComplexEquiv_one :
    octonionComplexEquiv 1 = ZornVectorMatrix.one := by
  ext i <;> (try fin_cases i) <;>
    simp [octonionComplexEquiv, octonionComplexToZornFun, ZornVectorMatrix.one]

@[simp] theorem octonionComplexEquiv_conj (x : CompactOctonion ℂ) :
    octonionComplexEquiv (CompactOctonion.conj x) =
      ZornVectorMatrix.conj (octonionComplexEquiv x) := by
  ext i <;> (try fin_cases i) <;>
    simp [octonionComplexEquiv, octonionComplexToZornFun, CompactOctonion.conj,
      ZornVectorMatrix.conj] <;> ring

@[simp] theorem octonionComplexEquiv_trace (x : CompactOctonion ℂ) :
    ZornVectorMatrix.trace (octonionComplexEquiv x) = CompactOctonion.trace x := by
  simp [octonionComplexEquiv, octonionComplexToZornFun, ZornVectorMatrix.trace,
    CompactOctonion.trace]

@[simp] theorem octonionComplexEquiv_norm (x : CompactOctonion ℂ) :
    ZornVectorMatrix.norm (octonionComplexEquiv x) = CompactOctonion.norm x := by
  simp [octonionComplexEquiv, octonionComplexToZornFun, ZornVectorMatrix.norm,
    ZornVec3.dot, Fin.sum_univ_three, CompactOctonion.norm]
  ring_nf
  simp only [Complex.I_sq]
  ring

@[simp] theorem octonionComplexEquiv_mul (x y : CompactOctonion ℂ) :
    octonionComplexEquiv (CompactOctonion.mul x y) =
      ZornVectorMatrix.mul (octonionComplexEquiv x) (octonionComplexEquiv y) := by
  ext i <;> (try fin_cases i) <;>
    simp [octonionComplexEquiv, octonionComplexToZornFun, CompactOctonion.mul,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> any_goals ring

@[simp] theorem octonionComplexEquiv_symm_one :
    octonionComplexEquiv.symm ZornVectorMatrix.one = 1 := by
  rw [← octonionComplexEquiv_one, octonionComplexEquiv.symm_apply_apply]

@[simp] theorem octonionComplexEquiv_symm_conj (X : ZornVectorMatrix ℂ) :
    octonionComplexEquiv.symm (ZornVectorMatrix.conj X) =
      CompactOctonion.conj (octonionComplexEquiv.symm X) := by
  apply octonionComplexEquiv.injective
  rw [octonionComplexEquiv_conj, octonionComplexEquiv.apply_symm_apply,
    octonionComplexEquiv.apply_symm_apply]

@[simp] theorem octonionComplexEquiv_symm_trace (X : ZornVectorMatrix ℂ) :
    CompactOctonion.trace (octonionComplexEquiv.symm X) = ZornVectorMatrix.trace X := by
  rw [← octonionComplexEquiv_trace, octonionComplexEquiv.apply_symm_apply]

@[simp] theorem octonionComplexEquiv_symm_norm (X : ZornVectorMatrix ℂ) :
    CompactOctonion.norm (octonionComplexEquiv.symm X) = ZornVectorMatrix.norm X := by
  rw [← octonionComplexEquiv_norm, octonionComplexEquiv.apply_symm_apply]

@[simp] theorem octonionComplexEquiv_symm_mul (X Y : ZornVectorMatrix ℂ) :
    octonionComplexEquiv.symm (ZornVectorMatrix.mul X Y) =
      CompactOctonion.mul (octonionComplexEquiv.symm X) (octonionComplexEquiv.symm Y) := by
  apply octonionComplexEquiv.injective
  rw [octonionComplexEquiv_mul, octonionComplexEquiv.apply_symm_apply,
    octonionComplexEquiv.apply_symm_apply, octonionComplexEquiv.apply_symm_apply]

end ComplexOctonionIsomorphism

section ComplexAlbertIsomorphism

/-- Lifted `ℂ`-linear equivalence `H3Octonion ℂ ≃ₗ[ℂ] H3Zorn ℂ` applying
`octonionComplexEquiv` to the three octonion entries. -/
def h3OctonionComplexEquiv : H3Octonion ℂ ≃ₗ[ℂ] H3Zorn ℂ where
  toFun x :=
    { α₁ := x.α₁
      α₂ := x.α₂
      α₃ := x.α₃
      a := octonionComplexEquiv x.a
      b := octonionComplexEquiv x.b
      c := octonionComplexEquiv x.c }
  invFun X :=
    { α₁ := X.α₁
      α₂ := X.α₂
      α₃ := X.α₃
      a := octonionComplexEquiv.symm X.a
      b := octonionComplexEquiv.symm X.b
      c := octonionComplexEquiv.symm X.c }
  map_add' x y := by
    apply H3Zorn.ext_h3 <;> simp [H3Zorn.add_readback]
  map_smul' z x := by
    apply H3Zorn.ext_h3 <;> simp [H3Zorn.smul_readback]
  left_inv x := by
    apply H3Octonion.ext_h3 <;> simp
  right_inv X := by
    apply H3Zorn.ext_h3 <;> simp

@[simp] theorem h3OctonionComplexEquiv_one :
    h3OctonionComplexEquiv (1 : H3Octonion ℂ) = (1 : H3Zorn ℂ) := by
  apply H3Zorn.ext_h3 <;> simp [h3OctonionComplexEquiv, H3Zorn.one_readback]

@[simp] theorem h3OctonionComplexEquiv_linearTrace (x : H3Octonion ℂ) :
    H3Zorn.linearTrace (h3OctonionComplexEquiv x) = H3Octonion.linearTrace x := by
  simp [H3Zorn.linearTrace, H3Octonion.linearTrace, h3OctonionComplexEquiv]

@[simp] theorem h3OctonionComplexEquiv_traceBilin (x y : H3Octonion ℂ) :
    H3Zorn.traceBilin (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) =
      H3Octonion.traceBilin x y := by
  simp [H3Zorn.traceBilin, H3Octonion.traceBilin, h3OctonionComplexEquiv,
    ← octonionComplexEquiv_conj, ← octonionComplexEquiv_mul, octonionComplexEquiv_trace]

@[simp] theorem h3OctonionComplexEquiv_normCubic (x : H3Octonion ℂ) :
    H3Zorn.normCubic (h3OctonionComplexEquiv x) = H3Octonion.normCubic x := by
  simp [H3Zorn.normCubic, H3Octonion.normCubic, h3OctonionComplexEquiv,
    octonionComplexEquiv_norm, ← octonionComplexEquiv_mul, octonionComplexEquiv_trace]

@[simp] theorem h3OctonionComplexEquiv_adjointQuad (x : H3Octonion ℂ) :
    h3OctonionComplexEquiv (H3Octonion.adjointQuad x) =
      H3Zorn.adjointQuad (h3OctonionComplexEquiv x) := by
  apply H3Zorn.ext_h3
  · simp [h3OctonionComplexEquiv, H3Octonion.adjointQuad, H3Zorn.adjointQuad]
  · simp [h3OctonionComplexEquiv, H3Octonion.adjointQuad, H3Zorn.adjointQuad]; ring
  · simp [h3OctonionComplexEquiv, H3Octonion.adjointQuad, H3Zorn.adjointQuad]
  · change octonionComplexEquiv (CompactOctonion.mul (CompactOctonion.conj x.c)
        (CompactOctonion.conj x.b) - x.α₃ • x.a) =
      ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj (octonionComplexEquiv x.c))
        (ZornVectorMatrix.conj (octonionComplexEquiv x.b)))
        (ZornVectorMatrix.smul x.α₃ (octonionComplexEquiv x.a))
    rw [map_sub, octonionComplexEquiv_mul, octonionComplexEquiv_conj, octonionComplexEquiv_conj]
    have hsm := octonionComplexEquiv.map_smul x.α₃ x.a
    exact congrArg (fun u => ZornVectorMatrix.mul _ _ - u) hsm
  · change octonionComplexEquiv (CompactOctonion.mul (CompactOctonion.conj x.a)
        (CompactOctonion.conj x.c) - x.α₁ • x.b) =
      ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj (octonionComplexEquiv x.a))
        (ZornVectorMatrix.conj (octonionComplexEquiv x.c)))
        (ZornVectorMatrix.smul x.α₁ (octonionComplexEquiv x.b))
    rw [map_sub, octonionComplexEquiv_mul, octonionComplexEquiv_conj, octonionComplexEquiv_conj]
    have hsm := octonionComplexEquiv.map_smul x.α₁ x.b
    exact congrArg (fun u => ZornVectorMatrix.mul _ _ - u) hsm
  · change octonionComplexEquiv (CompactOctonion.mul (CompactOctonion.conj x.b)
        (CompactOctonion.conj x.a) - x.α₂ • x.c) =
      ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj (octonionComplexEquiv x.b))
        (ZornVectorMatrix.conj (octonionComplexEquiv x.a)))
        (ZornVectorMatrix.smul x.α₂ (octonionComplexEquiv x.c))
    rw [map_sub, octonionComplexEquiv_mul, octonionComplexEquiv_conj, octonionComplexEquiv_conj]
    have hsm := octonionComplexEquiv.map_smul x.α₂ x.c
    exact congrArg (fun u => ZornVectorMatrix.mul _ _ - u) hsm

@[simp] theorem h3OctonionComplexEquiv_crossProduct (x y : H3Octonion ℂ) :
    h3OctonionComplexEquiv (H3Octonion.crossProduct x y) =
      H3Zorn.crossProduct (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) := by
  have hdef : H3Octonion.crossProduct x y =
      H3Octonion.adjointQuad (x + y) - H3Octonion.adjointQuad x - H3Octonion.adjointQuad y := by
    rw [H3Octonion.adjointQuad_add]; abel
  rw [hdef, map_sub, map_sub, h3OctonionComplexEquiv_adjointQuad,
    h3OctonionComplexEquiv_adjointQuad, h3OctonionComplexEquiv_adjointQuad, map_add]
  rfl

@[simp] theorem h3OctonionComplexEquiv_U (x y : H3Octonion ℂ) :
    h3OctonionComplexEquiv (H3Octonion.U x y) =
      H3Zorn.U (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) := by
  simp [H3Octonion.U, H3Zorn.U, map_sub, map_smul, h3OctonionComplexEquiv_traceBilin,
    h3OctonionComplexEquiv_crossProduct, h3OctonionComplexEquiv_adjointQuad]

@[simp] theorem h3OctonionComplexEquiv_T (x y z : H3Octonion ℂ) :
    h3OctonionComplexEquiv (H3Octonion.T x y z) =
      H3Zorn.T (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) (h3OctonionComplexEquiv z) := by
  simp [H3Octonion.T, H3Zorn.T, map_sub, map_add, h3OctonionComplexEquiv_U]

/-- Complex cubic norm trilinear form on `H3Octonion ℂ`. -/
def h3OctonionNormTrilinℂ :
    H3Octonion ℂ →ₗ[ℂ] H3Octonion ℂ →ₗ[ℂ] H3Octonion ℂ →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => (1 / 6 : ℂ) * H3Octonion.traceBilin (H3Octonion.crossProduct x y) z
          map_add' := fun z₁ z₂ => by simp [H3Octonion.traceBilin_add_right, mul_add]
          map_smul' := fun r z => by simp [H3Octonion.traceBilin_smul_right]; ring }
      map_add' := fun y₁ y₂ => by
        ext z; simp [H3Octonion.crossProduct_add_right, H3Octonion.traceBilin_add_left, mul_add]
      map_smul' := fun r y => by
        ext z; simp [H3Octonion.crossProduct_smul_right, H3Octonion.traceBilin_smul_left]; ring }
  map_add' x₁ x₂ := by
    ext y z; simp [H3Octonion.crossProduct_add_left, H3Octonion.traceBilin_add_left, mul_add]
  map_smul' r x := by
    ext y z; simp [H3Octonion.crossProduct_smul_left, H3Octonion.traceBilin_smul_left]; ring

/-- Complex cubic norm trilinear form on `H3Zorn ℂ`. -/
def h3zornNormTrilinℂ :
    H3Zorn ℂ →ₗ[ℂ] H3Zorn ℂ →ₗ[ℂ] H3Zorn ℂ →ₗ[ℂ] ℂ where
  toFun X :=
    { toFun := fun Y =>
        { toFun := fun Z => (1 / 6 : ℂ) * H3Zorn.traceBilin X (H3Zorn.crossProduct Y Z)
          map_add' := fun Z₁ Z₂ => by
            simp only [H3Zorn.crossProduct_add_right, H3Zorn.traceBilin_add_right, mul_add]
          map_smul' := fun r Z => by
            dsimp; simp only [H3Zorn.crossProduct_smul_right, H3Zorn.traceBilin_smul_right]; ring }
      map_add' := fun Y₁ Y₂ => by
        ext Z; dsimp; simp only [H3Zorn.crossProduct_add_left, H3Zorn.traceBilin_add_right, mul_add]
      map_smul' := fun r Y => by
        ext Z; dsimp; simp only [H3Zorn.crossProduct_smul_left, H3Zorn.traceBilin_smul_right]; ring }
  map_add' X₁ X₂ := by
    ext Y Z; dsimp; simp only [H3Zorn.traceBilin_add_left, mul_add]
  map_smul' r X := by
    ext Y Z; dsimp; simp only [H3Zorn.traceBilin_smul_left]; ring

@[simp] theorem h3OctonionComplexEquiv_normTrilin (x y z : H3Octonion ℂ) :
    h3zornNormTrilinℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y)
        (h3OctonionComplexEquiv z) =
      h3OctonionNormTrilinℂ x y z := by
  dsimp [h3zornNormTrilinℂ, h3OctonionNormTrilinℂ]
  rw [← H3Zorn.traceBilin_crossProduct_assoc, ← h3OctonionComplexEquiv_crossProduct,
    h3OctonionComplexEquiv_traceBilin]

/-- Complex Jordan product on `H3Octonion ℂ` (kept explicit to avoid global `Mul` pollution). -/
def candidateJordanMulOctℂ (x y : H3Octonion ℂ) : H3Octonion ℂ :=
  (1 / 2 : ℂ) • H3Octonion.T x 1 y

/-- Complex Jordan product on `H3Zorn ℂ` (kept explicit to avoid global `Mul` pollution). -/
def candidateJordanMulZornℂ (X Y : H3Zorn ℂ) : H3Zorn ℂ :=
  (1 / 2 : ℂ) • H3Zorn.T X 1 Y

@[simp] theorem h3OctonionComplexEquiv_jordanMul (x y : H3Octonion ℂ) :
    h3OctonionComplexEquiv (candidateJordanMulOctℂ x y) =
      candidateJordanMulZornℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y) := by
  simp [candidateJordanMulOctℂ, candidateJordanMulZornℂ, map_smul,
    h3OctonionComplexEquiv_T, h3OctonionComplexEquiv_one]

end ComplexAlbertIsomorphism

section RealImaginaryBaseChange

/-- Canonical `ℝ`-linear embedding `CompactOctonion ℝ →ₗ[ℝ] CompactOctonion ℂ`. -/
def ofRealCompactOctonion : CompactOctonion ℝ →ₗ[ℝ] CompactOctonion ℂ where
  toFun x := ⟨x.e0, x.e1, x.e2, x.e3, x.e4, x.e5, x.e6, x.e7⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by
    rw [← Complex.coe_smul]
    ext <;> exact Complex.ofReal_mul r _

def rePartCompactOctonion : CompactOctonion ℂ →ₗ[ℝ] CompactOctonion ℝ where
  toFun x := ⟨x.e0.re, x.e1.re, x.e2.re, x.e3.re, x.e4.re, x.e5.re, x.e6.re, x.e7.re⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by
    rw [← Complex.coe_smul]
    ext <;> exact Complex.re_ofReal_mul r _

def imPartCompactOctonion : CompactOctonion ℂ →ₗ[ℝ] CompactOctonion ℝ where
  toFun x := ⟨x.e0.im, x.e1.im, x.e2.im, x.e3.im, x.e4.im, x.e5.im, x.e6.im, x.e7.im⟩
  map_add' x y := by ext <;> simp
  map_smul' r x := by
    rw [← Complex.coe_smul]
    ext <;> exact Complex.im_ofReal_mul r _

/-- Canonical `ℝ`-linear embedding `ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℂ`. -/
def ofRealZornVectorMatrix : ZornVectorMatrix ℝ →ₗ[ℝ] ZornVectorMatrix ℂ where
  toFun X := ⟨X.a, fun i => (X.v i : ℂ), fun i => (X.w i : ℂ), X.b⟩
  map_add' X Y := by ext i <;> simp [ZornVectorMatrix.add]
  map_smul' r X := by
    rw [← Complex.coe_smul]
    ext i <;> exact Complex.ofReal_mul r _

def rePartZornVectorMatrix : ZornVectorMatrix ℂ →ₗ[ℝ] ZornVectorMatrix ℝ where
  toFun X := ⟨X.a.re, fun i => (X.v i).re, fun i => (X.w i).re, X.b.re⟩
  map_add' X Y := by ext i <;> simp [ZornVectorMatrix.add]
  map_smul' r X := by
    rw [← Complex.coe_smul]
    ext i <;> exact Complex.re_ofReal_mul r _

def imPartZornVectorMatrix : ZornVectorMatrix ℂ →ₗ[ℝ] ZornVectorMatrix ℝ where
  toFun X := ⟨X.a.im, fun i => (X.v i).im, fun i => (X.w i).im, X.b.im⟩
  map_add' X Y := by ext i <;> simp [ZornVectorMatrix.add]
  map_smul' r X := by
    rw [← Complex.coe_smul]
    ext i <;> exact Complex.im_ofReal_mul r _

/-- Canonical `ℝ`-linear embedding `H3Octonion ℝ →ₗ[ℝ] H3Octonion ℂ`. -/
def ofRealH3Octonion : H3Octonion ℝ →ₗ[ℝ] H3Octonion ℂ where
  toFun x := ⟨x.α₁, x.α₂, x.α₃,
    ofRealCompactOctonion x.a, ofRealCompactOctonion x.b, ofRealCompactOctonion x.c⟩
  map_add' x y := by
    apply H3Octonion.ext_h3 <;> simp [ofRealCompactOctonion.map_add]
  map_smul' r x := by
    apply H3Octonion.ext_h3
    · change ((r * x.α₁ : ℝ) : ℂ) = (r • (⟨(x.α₁ : ℂ), (x.α₂ : ℂ), (x.α₃ : ℂ),
        ofRealCompactOctonion x.a, ofRealCompactOctonion x.b, ofRealCompactOctonion x.c⟩ :
        H3Octonion ℂ)).α₁
      rw [← Complex.coe_smul]; exact Complex.ofReal_mul r x.α₁
    · rw [← Complex.coe_smul]; exact Complex.ofReal_mul r x.α₂
    · rw [← Complex.coe_smul]; exact Complex.ofReal_mul r x.α₃
    · exact ofRealCompactOctonion.map_smul r x.a
    · exact ofRealCompactOctonion.map_smul r x.b
    · exact ofRealCompactOctonion.map_smul r x.c

def rePartH3Octonion : H3Octonion ℂ →ₗ[ℝ] H3Octonion ℝ where
  toFun x := ⟨x.α₁.re, x.α₂.re, x.α₃.re,
    rePartCompactOctonion x.a, rePartCompactOctonion x.b, rePartCompactOctonion x.c⟩
  map_add' x y := by
    apply H3Octonion.ext_h3 <;> simp [rePartCompactOctonion.map_add]
  map_smul' r x := by
    apply H3Octonion.ext_h3
    · rw [← Complex.coe_smul]; exact Complex.re_ofReal_mul r x.α₁
    · rw [← Complex.coe_smul]; exact Complex.re_ofReal_mul r x.α₂
    · rw [← Complex.coe_smul]; exact Complex.re_ofReal_mul r x.α₃
    · exact rePartCompactOctonion.map_smul r x.a
    · exact rePartCompactOctonion.map_smul r x.b
    · exact rePartCompactOctonion.map_smul r x.c

def imPartH3Octonion : H3Octonion ℂ →ₗ[ℝ] H3Octonion ℝ where
  toFun x := ⟨x.α₁.im, x.α₂.im, x.α₃.im,
    imPartCompactOctonion x.a, imPartCompactOctonion x.b, imPartCompactOctonion x.c⟩
  map_add' x y := by
    apply H3Octonion.ext_h3 <;> simp [imPartCompactOctonion.map_add]
  map_smul' r x := by
    apply H3Octonion.ext_h3
    · rw [← Complex.coe_smul]; exact Complex.im_ofReal_mul r x.α₁
    · rw [← Complex.coe_smul]; exact Complex.im_ofReal_mul r x.α₂
    · rw [← Complex.coe_smul]; exact Complex.im_ofReal_mul r x.α₃
    · exact imPartCompactOctonion.map_smul r x.a
    · exact imPartCompactOctonion.map_smul r x.b
    · exact imPartCompactOctonion.map_smul r x.c

/-- Canonical `ℝ`-linear embedding `H3Zorn ℝ →ₗ[ℝ] H3Zorn ℂ`. -/
def ofRealH3Zorn : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℂ where
  toFun X := ⟨X.α₁, X.α₂, X.α₃,
    ofRealZornVectorMatrix X.a, ofRealZornVectorMatrix X.b, ofRealZornVectorMatrix X.c⟩
  map_add' X Y := by
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback]
    · simp [H3Zorn.add_readback]
    · simp [H3Zorn.add_readback]
    · exact ofRealZornVectorMatrix.map_add X.a Y.a
    · exact ofRealZornVectorMatrix.map_add X.b Y.b
    · exact ofRealZornVectorMatrix.map_add X.c Y.c
  map_smul' r X := by
    apply H3Zorn.ext_h3
    · rw [← Complex.coe_smul]; exact Complex.ofReal_mul r X.α₁
    · rw [← Complex.coe_smul]; exact Complex.ofReal_mul r X.α₂
    · rw [← Complex.coe_smul]; exact Complex.ofReal_mul r X.α₃
    · exact ofRealZornVectorMatrix.map_smul r X.a
    · exact ofRealZornVectorMatrix.map_smul r X.b
    · exact ofRealZornVectorMatrix.map_smul r X.c

def rePartH3Zorn : H3Zorn ℂ →ₗ[ℝ] H3Zorn ℝ where
  toFun X := ⟨X.α₁.re, X.α₂.re, X.α₃.re,
    rePartZornVectorMatrix X.a, rePartZornVectorMatrix X.b, rePartZornVectorMatrix X.c⟩
  map_add' X Y := by
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback]
    · simp [H3Zorn.add_readback]
    · simp [H3Zorn.add_readback]
    · exact rePartZornVectorMatrix.map_add X.a Y.a
    · exact rePartZornVectorMatrix.map_add X.b Y.b
    · exact rePartZornVectorMatrix.map_add X.c Y.c
  map_smul' r X := by
    apply H3Zorn.ext_h3
    · rw [← Complex.coe_smul]; exact Complex.re_ofReal_mul r X.α₁
    · rw [← Complex.coe_smul]; exact Complex.re_ofReal_mul r X.α₂
    · rw [← Complex.coe_smul]; exact Complex.re_ofReal_mul r X.α₃
    · exact rePartZornVectorMatrix.map_smul r X.a
    · exact rePartZornVectorMatrix.map_smul r X.b
    · exact rePartZornVectorMatrix.map_smul r X.c

def imPartH3Zorn : H3Zorn ℂ →ₗ[ℝ] H3Zorn ℝ where
  toFun X := ⟨X.α₁.im, X.α₂.im, X.α₃.im,
    imPartZornVectorMatrix X.a, imPartZornVectorMatrix X.b, imPartZornVectorMatrix X.c⟩
  map_add' X Y := by
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback]
    · simp [H3Zorn.add_readback]
    · simp [H3Zorn.add_readback]
    · exact imPartZornVectorMatrix.map_add X.a Y.a
    · exact imPartZornVectorMatrix.map_add X.b Y.b
    · exact imPartZornVectorMatrix.map_add X.c Y.c
  map_smul' r X := by
    apply H3Zorn.ext_h3
    · rw [← Complex.coe_smul]; exact Complex.im_ofReal_mul r X.α₁
    · rw [← Complex.coe_smul]; exact Complex.im_ofReal_mul r X.α₂
    · rw [← Complex.coe_smul]; exact Complex.im_ofReal_mul r X.α₃
    · exact imPartZornVectorMatrix.map_smul r X.a
    · exact imPartZornVectorMatrix.map_smul r X.b
    · exact imPartZornVectorMatrix.map_smul r X.c

@[simp] theorem rePartH3Octonion_ofReal (x : H3Octonion ℝ) :
    rePartH3Octonion (ofRealH3Octonion x) = x := by
  apply H3Octonion.ext_h3
  · rfl
  · rfl
  · rfl
  · ext <;> rfl
  · ext <;> rfl
  · ext <;> rfl

@[simp] theorem imPartH3Octonion_ofReal (x : H3Octonion ℝ) :
    imPartH3Octonion (ofRealH3Octonion x) = 0 := by
  apply H3Octonion.ext_h3
  · rfl
  · rfl
  · rfl
  · ext <;> rfl
  · ext <;> rfl
  · ext <;> rfl

theorem ofReal_rePart_add_I_imPart_H3Octonion (x : H3Octonion ℂ) :
    ofRealH3Octonion (rePartH3Octonion x) + Complex.I • ofRealH3Octonion (imPartH3Octonion x) = x := by
  apply H3Octonion.ext_h3
  · simp [ofRealH3Octonion, rePartH3Octonion, imPartH3Octonion, mul_comm Complex.I]
  · simp [ofRealH3Octonion, rePartH3Octonion, imPartH3Octonion, mul_comm Complex.I]
  · simp [ofRealH3Octonion, rePartH3Octonion, imPartH3Octonion, mul_comm Complex.I]
  · ext <;> simp [ofRealH3Octonion, rePartH3Octonion, imPartH3Octonion,
      ofRealCompactOctonion, rePartCompactOctonion, imPartCompactOctonion, mul_comm Complex.I]
  · ext <;> simp [ofRealH3Octonion, rePartH3Octonion, imPartH3Octonion,
      ofRealCompactOctonion, rePartCompactOctonion, imPartCompactOctonion, mul_comm Complex.I]
  · ext <;> simp [ofRealH3Octonion, rePartH3Octonion, imPartH3Octonion,
      ofRealCompactOctonion, rePartCompactOctonion, imPartCompactOctonion, mul_comm Complex.I]

@[simp] theorem rePartH3Octonion_I_smul (x : H3Octonion ℂ) :
    rePartH3Octonion (Complex.I • x) = -imPartH3Octonion x := by
  apply H3Octonion.ext_h3
  · simp [rePartH3Octonion, imPartH3Octonion]
  · simp [rePartH3Octonion, imPartH3Octonion]
  · simp [rePartH3Octonion, imPartH3Octonion]
  · ext <;> simp [rePartH3Octonion, imPartH3Octonion, rePartCompactOctonion, imPartCompactOctonion]
  · ext <;> simp [rePartH3Octonion, imPartH3Octonion, rePartCompactOctonion, imPartCompactOctonion]
  · ext <;> simp [rePartH3Octonion, imPartH3Octonion, rePartCompactOctonion, imPartCompactOctonion]

@[simp] theorem imPartH3Octonion_I_smul (x : H3Octonion ℂ) :
    imPartH3Octonion (Complex.I • x) = rePartH3Octonion x := by
  apply H3Octonion.ext_h3
  · simp [rePartH3Octonion, imPartH3Octonion]
  · simp [rePartH3Octonion, imPartH3Octonion]
  · simp [rePartH3Octonion, imPartH3Octonion]
  · ext <;> simp [rePartH3Octonion, imPartH3Octonion, rePartCompactOctonion, imPartCompactOctonion]
  · ext <;> simp [rePartH3Octonion, imPartH3Octonion, rePartCompactOctonion, imPartCompactOctonion]
  · ext <;> simp [rePartH3Octonion, imPartH3Octonion, rePartCompactOctonion, imPartCompactOctonion]

@[simp] theorem rePartH3Zorn_ofReal (X : H3Zorn ℝ) :
    rePartH3Zorn (ofRealH3Zorn X) = X := by
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · ext i <;> rfl
  · ext i <;> rfl
  · ext i <;> rfl

@[simp] theorem imPartH3Zorn_ofReal (X : H3Zorn ℝ) :
    imPartH3Zorn (ofRealH3Zorn X) = 0 := by
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · ext i <;> rfl
  · ext i <;> rfl
  · ext i <;> rfl

theorem ofReal_rePart_add_I_imPart_H3Zorn (X : H3Zorn ℂ) :
    ofRealH3Zorn (rePartH3Zorn X) + Complex.I • ofRealH3Zorn (imPartH3Zorn X) = X := by
  apply H3Zorn.ext_h3
  · simp [ofRealH3Zorn, rePartH3Zorn, imPartH3Zorn, H3Zorn.add_readback, H3Zorn.smul_readback,
      mul_comm Complex.I]
  · simp [ofRealH3Zorn, rePartH3Zorn, imPartH3Zorn, H3Zorn.add_readback, H3Zorn.smul_readback,
      mul_comm Complex.I]
  · simp [ofRealH3Zorn, rePartH3Zorn, imPartH3Zorn, H3Zorn.add_readback, H3Zorn.smul_readback,
      mul_comm Complex.I]
  · ext i <;> simp [ofRealH3Zorn, rePartH3Zorn, imPartH3Zorn,
      ofRealZornVectorMatrix, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.add_readback, H3Zorn.smul_readback, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      mul_comm Complex.I]
  · ext i <;> simp [ofRealH3Zorn, rePartH3Zorn, imPartH3Zorn,
      ofRealZornVectorMatrix, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.add_readback, H3Zorn.smul_readback, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      mul_comm Complex.I]
  · ext i <;> simp [ofRealH3Zorn, rePartH3Zorn, imPartH3Zorn,
      ofRealZornVectorMatrix, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.add_readback, H3Zorn.smul_readback, ZornVectorMatrix.add, ZornVectorMatrix.smul,
      mul_comm Complex.I]

@[simp] theorem rePartH3Zorn_I_smul (X : H3Zorn ℂ) :
    rePartH3Zorn (Complex.I • X) = -imPartH3Zorn X := by
  apply H3Zorn.ext_h3
  · simp [rePartH3Zorn, imPartH3Zorn, H3Zorn.smul_readback, H3Zorn.neg_readback]
  · simp [rePartH3Zorn, imPartH3Zorn, H3Zorn.smul_readback, H3Zorn.neg_readback]
  · simp [rePartH3Zorn, imPartH3Zorn, H3Zorn.smul_readback, H3Zorn.neg_readback]
  · ext i <;> simp [rePartH3Zorn, imPartH3Zorn, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.smul_readback, H3Zorn.neg_readback, ZornVectorMatrix.smul, ZornVectorMatrix.neg]
  · ext i <;> simp [rePartH3Zorn, imPartH3Zorn, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.smul_readback, H3Zorn.neg_readback, ZornVectorMatrix.smul, ZornVectorMatrix.neg]
  · ext i <;> simp [rePartH3Zorn, imPartH3Zorn, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.smul_readback, H3Zorn.neg_readback, ZornVectorMatrix.smul, ZornVectorMatrix.neg]

@[simp] theorem imPartH3Zorn_I_smul (X : H3Zorn ℂ) :
    imPartH3Zorn (Complex.I • X) = rePartH3Zorn X := by
  apply H3Zorn.ext_h3
  · simp [rePartH3Zorn, imPartH3Zorn, H3Zorn.smul_readback]
  · simp [rePartH3Zorn, imPartH3Zorn, H3Zorn.smul_readback]
  · simp [rePartH3Zorn, imPartH3Zorn, H3Zorn.smul_readback]
  · ext i <;> simp [rePartH3Zorn, imPartH3Zorn, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.smul_readback, ZornVectorMatrix.smul]
  · ext i <;> simp [rePartH3Zorn, imPartH3Zorn, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.smul_readback, ZornVectorMatrix.smul]
  · ext i <;> simp [rePartH3Zorn, imPartH3Zorn, rePartZornVectorMatrix, imPartZornVectorMatrix,
      H3Zorn.smul_readback, ZornVectorMatrix.smul]

private theorem complex_smul_split {M : Type*} [AddCommGroup M] [Module ℂ M]
    (z : ℂ) (w : M) :
    z • w = z.re • w + z.im • (Complex.I • w) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, Complex.coe_smul, mul_smul, Complex.coe_smul]

/-- Generic `ℂ`-linear equivalence `ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ` from real/imaginary projections. -/
def mkComplexTensorEquiv {V V_ℂ : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup V_ℂ] [Module ℂ V_ℂ]
    (ofReal : V →ₗ[ℝ] V_ℂ) (rePart imPart : V_ℂ →ₗ[ℝ] V)
    (hre : ∀ v, rePart (ofReal v) = v)
    (him : ∀ v, imPart (ofReal v) = 0)
    (hdecomp : ∀ w, ofReal (rePart w) + Complex.I • ofReal (imPart w) = w)
    (hreI : ∀ w, rePart (Complex.I • w) = -imPart w)
    (himI : ∀ w, imPart (Complex.I • w) = rePart w) :
    ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ :=
  let toFun : ℂ ⊗[ℝ] V →ₗ[ℂ] V_ℂ :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun z =>
          { toFun := fun v => z • ofReal v
            map_add' := fun v₁ v₂ => by rw [map_add, smul_add]
            map_smul' := fun r v => by
              simp only [RingHom.id_apply, map_smul]
              rw [smul_comm] }
        map_add' := fun z₁ z₂ => by
          ext v; simp [add_smul]
        map_smul' := fun c z => by
          ext v; simp [mul_smul] }
  let invFun : V_ℂ →ₗ[ℂ] ℂ ⊗[ℝ] V :=
    { toFun := fun w => (1 : ℂ) ⊗ₜ[ℝ] rePart w + Complex.I ⊗ₜ[ℝ] imPart w
      map_add' := fun w₁ w₂ => by
        simp only [map_add, TensorProduct.tmul_add]; abel
      map_smul' := fun z w => by
        rw [complex_smul_split z w, map_add, map_add,
          rePart.map_smul, rePart.map_smul, imPart.map_smul, imPart.map_smul,
          hreI, himI]
        simp only [TensorProduct.tmul_add]
        rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
          ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
          Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul,
          mul_one, mul_one]
        have hz : z • ((1 : ℂ) ⊗ₜ[ℝ] rePart w + Complex.I ⊗ₜ[ℝ] imPart w) =
            z ⊗ₜ[ℝ] rePart w + (z * Complex.I) ⊗ₜ[ℝ] imPart w := by
          rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
            smul_eq_mul, smul_eq_mul, mul_one]
        rw [RingHom.id_apply, hz]
        have hz1 : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
        have hz2 : (-(z.im : ℂ) + (z.re : ℂ) * Complex.I) = z * Complex.I := by
          conv_rhs => rw [← Complex.re_add_im z]
          ring_nf; simp [Complex.I_sq]
        have hre_tmul : (z.re : ℂ) ⊗ₜ[ℝ] rePart w + ((z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] rePart w =
            z ⊗ₜ[ℝ] rePart w := by
          rw [← TensorProduct.add_tmul, hz1]
        have him_tmul : (-(z.im : ℂ)) ⊗ₜ[ℝ] imPart w + ((z.re : ℂ) * Complex.I) ⊗ₜ[ℝ] imPart w =
            (z * Complex.I) ⊗ₜ[ℝ] imPart w := by
          rw [← TensorProduct.add_tmul, hz2]
        rw [← hre_tmul, ← him_tmul, TensorProduct.neg_tmul, TensorProduct.tmul_neg]
        abel }
  { toFun := toFun
    invFun := invFun
    map_add' := toFun.map_add'
    map_smul' := toFun.map_smul'
    left_inv := fun u => by
      induction u using TensorProduct.inductionOn with
      | tmul z v =>
        have hlift : toFun (z ⊗ₜ[ℝ] v) = z • ofReal v := rfl
        rw [hlift]
        have hre_z : rePart (z • ofReal v) = z.re • v := by
          rw [complex_smul_split z (ofReal v), map_add, map_smul, map_smul, hre, hreI, him,
            neg_zero, smul_zero, add_zero]
        have him_z : imPart (z • ofReal v) = z.im • v := by
          rw [complex_smul_split z (ofReal v), map_add, map_smul, map_smul, him, himI, hre,
            smul_zero, zero_add]
        change (1 : ℂ) ⊗ₜ[ℝ] rePart (z • ofReal v) + Complex.I ⊗ₜ[ℝ] imPart (z • ofReal v) =
          z ⊗ₜ[ℝ] v
        rw [hre_z, him_z, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
          Complex.real_smul, Complex.real_smul, mul_one,
          ← TensorProduct.add_tmul, Complex.re_add_im]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    right_inv := fun w => by
      change toFun ((1 : ℂ) ⊗ₜ[ℝ] rePart w + Complex.I ⊗ₜ[ℝ] imPart w) = w
      rw [map_add]
      have h1 : toFun ((1 : ℂ) ⊗ₜ[ℝ] rePart w) = ofReal (rePart w) := by
        change (1 : ℂ) • ofReal (rePart w) = _; simp
      have h2 : toFun (Complex.I ⊗ₜ[ℝ] imPart w) = Complex.I • ofReal (imPart w) := rfl
      rw [h1, h2, hdecomp] }

@[simp] theorem mkComplexTensorEquiv_tmul {V V_ℂ : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup V_ℂ] [Module ℂ V_ℂ]
    (ofReal : V →ₗ[ℝ] V_ℂ) (rePart imPart : V_ℂ →ₗ[ℝ] V)
    (hre : ∀ v, rePart (ofReal v) = v)
    (him : ∀ v, imPart (ofReal v) = 0)
    (hdecomp : ∀ w, ofReal (rePart w) + Complex.I • ofReal (imPart w) = w)
    (hreI : ∀ w, rePart (Complex.I • w) = -imPart w)
    (himI : ∀ w, imPart (Complex.I • w) = rePart w)
    (z : ℂ) (v : V) :
    mkComplexTensorEquiv ofReal rePart imPart hre him hdecomp hreI himI (z ⊗ₜ[ℝ] v) =
      z • ofReal v := rfl

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] H3Octonion ℂ`. -/
def tensorEquivH3Octonion : ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] H3Octonion ℂ :=
  mkComplexTensorEquiv ofRealH3Octonion rePartH3Octonion imPartH3Octonion
    rePartH3Octonion_ofReal imPartH3Octonion_ofReal
    ofReal_rePart_add_I_imPart_H3Octonion rePartH3Octonion_I_smul imPartH3Octonion_I_smul

/-- `ℂ`-linear equivalence `ℂ ⊗[ℝ] H3Zorn ℝ ≃ₗ[ℂ] H3Zorn ℂ`. -/
def tensorEquivH3Zorn : ℂ ⊗[ℝ] H3Zorn ℝ ≃ₗ[ℂ] H3Zorn ℂ :=
  mkComplexTensorEquiv ofRealH3Zorn rePartH3Zorn imPartH3Zorn
    rePartH3Zorn_ofReal imPartH3Zorn_ofReal
    ofReal_rePart_add_I_imPart_H3Zorn rePartH3Zorn_I_smul imPartH3Zorn_I_smul

@[simp] theorem tensorEquivH3Octonion_tmul (z : ℂ) (x : H3Octonion ℝ) :
    tensorEquivH3Octonion (z ⊗ₜ[ℝ] x) = z • ofRealH3Octonion x := rfl

@[simp] theorem tensorEquivH3Zorn_tmul (z : ℂ) (X : H3Zorn ℝ) :
    tensorEquivH3Zorn (z ⊗ₜ[ℝ] X) = z • ofRealH3Zorn X := rfl

/-- Complexification equivalence `ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] ℂ ⊗[ℝ] H3Zorn ℝ` between the
compact and split Albert Jordan algebras. -/
def h3OctonionTensorEquivH3Zorn : ℂ ⊗[ℝ] H3Octonion ℝ ≃ₗ[ℂ] ℂ ⊗[ℝ] H3Zorn ℝ :=
  tensorEquivH3Octonion.trans (h3OctonionComplexEquiv.trans tensorEquivH3Zorn.symm)

theorem h3OctonionTensorEquivH3Zorn_one :
    h3OctonionTensorEquivH3Zorn ((1 : ℂ) ⊗ₜ[ℝ] (1 : H3Octonion ℝ)) =
      (1 : ℂ) ⊗ₜ[ℝ] (1 : H3Zorn ℝ) := by
  dsimp [h3OctonionTensorEquivH3Zorn]
  have hof1 : ofRealH3Octonion (1 : H3Octonion ℝ) = (1 : H3Octonion ℂ) := by
    apply H3Octonion.ext_h3
    · rfl
    · rfl
    · rfl
    · ext <;> rfl
    · ext <;> rfl
    · ext <;> rfl
  have hof2 : ofRealH3Zorn (1 : H3Zorn ℝ) = (1 : H3Zorn ℂ) := by
    apply H3Zorn.ext_h3
    · rfl
    · rfl
    · rfl
    · ext i <;> rfl
    · ext i <;> rfl
    · ext i <;> rfl
  rw [one_smul, hof1, h3OctonionComplexEquiv_one, ← hof2]
  apply tensorEquivH3Zorn.injective
  simp

theorem h3OctonionTensorEquivH3Zorn_traceBilin (u v : ℂ ⊗[ℝ] H3Octonion ℝ) :
    H3Zorn.traceBilin (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u))
        (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn v)) =
      H3Octonion.traceBilin (tensorEquivH3Octonion u) (tensorEquivH3Octonion v) := by
  dsimp [h3OctonionTensorEquivH3Zorn]
  simp only [LinearEquiv.apply_symm_apply, h3OctonionComplexEquiv_traceBilin]

theorem h3OctonionTensorEquivH3Zorn_normCubic (u : ℂ ⊗[ℝ] H3Octonion ℝ) :
    H3Zorn.normCubic (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u)) =
      H3Octonion.normCubic (tensorEquivH3Octonion u) := by
  dsimp [h3OctonionTensorEquivH3Zorn]
  simp only [LinearEquiv.apply_symm_apply, h3OctonionComplexEquiv_normCubic]

theorem h3OctonionTensorEquivH3Zorn_normTrilin (u v w : ℂ ⊗[ℝ] H3Octonion ℝ) :
    h3zornNormTrilinℂ (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn u))
        (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn v))
        (tensorEquivH3Zorn (h3OctonionTensorEquivH3Zorn w)) =
      h3OctonionNormTrilinℂ (tensorEquivH3Octonion u) (tensorEquivH3Octonion v)
        (tensorEquivH3Octonion w) := by
  dsimp [h3OctonionTensorEquivH3Zorn]
  simp only [LinearEquiv.apply_symm_apply, h3OctonionComplexEquiv_normTrilin]

end RealImaginaryBaseChange

section ComplexifiedLieSubalgebras

@[simp] theorem ofRealCompactOctonion_mul (x y : CompactOctonion ℝ) :
    ofRealCompactOctonion (CompactOctonion.mul x y) =
      CompactOctonion.mul (ofRealCompactOctonion x) (ofRealCompactOctonion y) := by
  ext <;> simp [ofRealCompactOctonion, CompactOctonion.mul]

@[simp] theorem ofRealCompactOctonion_conj (x : CompactOctonion ℝ) :
    ofRealCompactOctonion (CompactOctonion.conj x) =
      CompactOctonion.conj (ofRealCompactOctonion x) := by
  ext <;> simp [ofRealCompactOctonion, CompactOctonion.conj]

@[simp] theorem ofRealCompactOctonion_trace (x : CompactOctonion ℝ) :
    CompactOctonion.trace (ofRealCompactOctonion x) = ((CompactOctonion.trace x : ℝ) : ℂ) := by
  dsimp only [ofRealCompactOctonion, CompactOctonion.trace, LinearMap.coe_mk, AddHom.coe_mk]
  push_cast
  rfl

@[simp] theorem ofRealCompactOctonion_norm (x : CompactOctonion ℝ) :
    CompactOctonion.norm (ofRealCompactOctonion x) = ((CompactOctonion.norm x : ℝ) : ℂ) := by
  dsimp only [ofRealCompactOctonion, CompactOctonion.norm, LinearMap.coe_mk, AddHom.coe_mk]
  push_cast
  rfl

@[simp] theorem ofRealZornVectorMatrix_mul (X Y : ZornVectorMatrix ℝ) :
    ofRealZornVectorMatrix (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.mul (ofRealZornVectorMatrix X) (ofRealZornVectorMatrix Y) := by
  ext i <;> (try fin_cases i) <;>
    simp [ofRealZornVectorMatrix, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]

@[simp] theorem ofRealZornVectorMatrix_conj (X : ZornVectorMatrix ℝ) :
    ofRealZornVectorMatrix (ZornVectorMatrix.conj X) =
      ZornVectorMatrix.conj (ofRealZornVectorMatrix X) := by
  ext i <;> simp [ofRealZornVectorMatrix, ZornVectorMatrix.conj]

@[simp] theorem ofRealZornVectorMatrix_trace (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.trace (ofRealZornVectorMatrix X) = ((ZornVectorMatrix.trace X : ℝ) : ℂ) := by
  dsimp only [ofRealZornVectorMatrix, ZornVectorMatrix.trace, LinearMap.coe_mk, AddHom.coe_mk]
  push_cast
  rfl

@[simp] theorem ofRealZornVectorMatrix_norm (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.norm (ofRealZornVectorMatrix X) = ((ZornVectorMatrix.norm X : ℝ) : ℂ) := by
  dsimp only [ofRealZornVectorMatrix, ZornVectorMatrix.norm, ZornVec3.dot,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp [Fin.sum_univ_three]

@[simp] theorem ofRealH3Octonion_one :
    ofRealH3Octonion (1 : H3Octonion ℝ) = (1 : H3Octonion ℂ) := by
  apply H3Octonion.ext_h3
  · rfl
  · rfl
  · rfl
  · ext <;> rfl
  · ext <;> rfl
  · ext <;> rfl

@[simp] theorem ofRealH3Octonion_traceBilin (x y : H3Octonion ℝ) :
    H3Octonion.traceBilin (ofRealH3Octonion x) (ofRealH3Octonion y) =
      ((H3Octonion.traceBilin x y : ℝ) : ℂ) := by
  dsimp only [ofRealH3Octonion, H3Octonion.traceBilin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofRealCompactOctonion_conj, ← ofRealCompactOctonion_mul, ofRealCompactOctonion_trace,
    ← ofRealCompactOctonion_conj, ← ofRealCompactOctonion_mul, ofRealCompactOctonion_trace,
    ← ofRealCompactOctonion_conj, ← ofRealCompactOctonion_mul, ofRealCompactOctonion_trace]
  push_cast
  rfl

@[simp] theorem ofRealH3Octonion_adjointQuad (x : H3Octonion ℝ) :
    ofRealH3Octonion (H3Octonion.adjointQuad x) = H3Octonion.adjointQuad (ofRealH3Octonion x) := by
  apply H3Octonion.ext_h3
  · dsimp only [ofRealH3Octonion, H3Octonion.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealCompactOctonion_norm]
    push_cast; rfl
  · dsimp only [ofRealH3Octonion, H3Octonion.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealCompactOctonion_norm]
    push_cast; rfl
  · dsimp only [ofRealH3Octonion, H3Octonion.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealCompactOctonion_norm]
    push_cast; rfl
  · dsimp only [ofRealH3Octonion, H3Octonion.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealCompactOctonion.map_sub, ofRealCompactOctonion_mul, ofRealCompactOctonion_conj,
      ofRealCompactOctonion_conj, ofRealCompactOctonion.map_smul, ← Complex.coe_smul]
  · dsimp only [ofRealH3Octonion, H3Octonion.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealCompactOctonion.map_sub, ofRealCompactOctonion_mul, ofRealCompactOctonion_conj,
      ofRealCompactOctonion_conj, ofRealCompactOctonion.map_smul, ← Complex.coe_smul]
  · dsimp only [ofRealH3Octonion, H3Octonion.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealCompactOctonion.map_sub, ofRealCompactOctonion_mul, ofRealCompactOctonion_conj,
      ofRealCompactOctonion_conj, ofRealCompactOctonion.map_smul, ← Complex.coe_smul]

@[simp] theorem ofRealH3Octonion_crossProduct (x y : H3Octonion ℝ) :
    ofRealH3Octonion (H3Octonion.crossProduct x y) =
      H3Octonion.crossProduct (ofRealH3Octonion x) (ofRealH3Octonion y) := by
  have hdefR : H3Octonion.crossProduct x y =
      H3Octonion.adjointQuad (x + y) - H3Octonion.adjointQuad x - H3Octonion.adjointQuad y := by
    rw [H3Octonion.adjointQuad_add]; abel
  have hdefC : H3Octonion.crossProduct (ofRealH3Octonion x) (ofRealH3Octonion y) =
      H3Octonion.adjointQuad (ofRealH3Octonion x + ofRealH3Octonion y) -
        H3Octonion.adjointQuad (ofRealH3Octonion x) -
        H3Octonion.adjointQuad (ofRealH3Octonion y) := by
    rw [H3Octonion.adjointQuad_add]; abel
  rw [hdefR, hdefC, map_sub, map_sub, ofRealH3Octonion_adjointQuad,
    ofRealH3Octonion_adjointQuad, ofRealH3Octonion_adjointQuad, map_add]

@[simp] theorem ofRealH3Octonion_U (x y : H3Octonion ℝ) :
    ofRealH3Octonion (H3Octonion.U x y) =
      H3Octonion.U (ofRealH3Octonion x) (ofRealH3Octonion y) := by
  simp only [H3Octonion.U, map_sub, map_smul, ← Complex.coe_smul,
    ofRealH3Octonion_traceBilin, ofRealH3Octonion_crossProduct, ofRealH3Octonion_adjointQuad]

@[simp] theorem ofRealH3Octonion_T (x y z : H3Octonion ℝ) :
    ofRealH3Octonion (H3Octonion.T x y z) =
      H3Octonion.T (ofRealH3Octonion x) (ofRealH3Octonion y) (ofRealH3Octonion z) := by
  simp [H3Octonion.T, map_sub, map_add, ofRealH3Octonion_U]

@[simp] theorem ofRealH3Octonion_normTrilin (x y z : H3Octonion ℝ) :
    h3OctonionNormTrilinℂ (ofRealH3Octonion x) (ofRealH3Octonion y) (ofRealH3Octonion z) =
      ((h3OctonionNormTrilin x y z : ℝ) : ℂ) := by
  dsimp only [h3OctonionNormTrilinℂ, h3OctonionNormTrilin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofRealH3Octonion_crossProduct, ofRealH3Octonion_traceBilin]
  push_cast; rfl

@[simp] theorem ofRealH3Octonion_jordanMul (x y : H3Octonion ℝ) :
    ofRealH3Octonion (x * y) = candidateJordanMulOctℂ (ofRealH3Octonion x) (ofRealH3Octonion y) := by
  change ofRealH3Octonion ((1 / 2 : ℝ) • H3Octonion.T x 1 y) =
    (1 / 2 : ℂ) • H3Octonion.T (ofRealH3Octonion x) 1 (ofRealH3Octonion y)
  rw [map_smul, ofRealH3Octonion_T, ofRealH3Octonion_one, ← Complex.coe_smul]
  norm_num

@[simp] theorem ofRealH3Zorn_one :
    ofRealH3Zorn (1 : H3Zorn ℝ) = (1 : H3Zorn ℂ) := by
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · ext i <;> rfl
  · ext i <;> rfl
  · ext i <;> rfl

@[simp] theorem ofRealH3Zorn_traceBilin (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin (ofRealH3Zorn X) (ofRealH3Zorn Y) = ((H3Zorn.traceBilin X Y : ℝ) : ℂ) := by
  dsimp only [ofRealH3Zorn, H3Zorn.traceBilin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofRealZornVectorMatrix_conj, ← ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_trace,
    ← ofRealZornVectorMatrix_conj, ← ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_trace,
    ← ofRealZornVectorMatrix_conj, ← ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_trace]
  push_cast
  rfl

private theorem ofRealZornVectorMatrix_sub (X Y : ZornVectorMatrix ℝ) :
    ofRealZornVectorMatrix (ZornVectorMatrix.sub X Y) =
      ZornVectorMatrix.sub (ofRealZornVectorMatrix X) (ofRealZornVectorMatrix Y) := by
  ext i <;> simp [ofRealZornVectorMatrix, ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg]

private theorem ofRealZornVectorMatrix_smul (r : ℝ) (X : ZornVectorMatrix ℝ) :
    ofRealZornVectorMatrix (ZornVectorMatrix.smul r X) =
      ZornVectorMatrix.smul (r : ℂ) (ofRealZornVectorMatrix X) := by
  ext i <;> simp [ofRealZornVectorMatrix, ZornVectorMatrix.smul]

@[simp] theorem ofRealH3Zorn_adjointQuad (X : H3Zorn ℝ) :
    ofRealH3Zorn (H3Zorn.adjointQuad X) = H3Zorn.adjointQuad (ofRealH3Zorn X) := by
  apply H3Zorn.ext_h3
  · dsimp only [ofRealH3Zorn, H3Zorn.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealZornVectorMatrix_norm]
    push_cast; rfl
  · dsimp only [ofRealH3Zorn, H3Zorn.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealZornVectorMatrix_norm]
    push_cast; rfl
  · dsimp only [ofRealH3Zorn, H3Zorn.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealZornVectorMatrix_norm]
    push_cast; rfl
  · dsimp only [ofRealH3Zorn, H3Zorn.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealZornVectorMatrix_sub, ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_conj,
      ofRealZornVectorMatrix_conj, ofRealZornVectorMatrix_smul]
  · dsimp only [ofRealH3Zorn, H3Zorn.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealZornVectorMatrix_sub, ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_conj,
      ofRealZornVectorMatrix_conj, ofRealZornVectorMatrix_smul]
  · dsimp only [ofRealH3Zorn, H3Zorn.adjointQuad, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ofRealZornVectorMatrix_sub, ofRealZornVectorMatrix_mul, ofRealZornVectorMatrix_conj,
      ofRealZornVectorMatrix_conj, ofRealZornVectorMatrix_smul]

@[simp] theorem ofRealH3Zorn_crossProduct (X Y : H3Zorn ℝ) :
    ofRealH3Zorn (H3Zorn.crossProduct X Y) =
      H3Zorn.crossProduct (ofRealH3Zorn X) (ofRealH3Zorn Y) := by
  simp only [H3Zorn.crossProduct, map_sub, ofRealH3Zorn_adjointQuad, ← map_add]

@[simp] theorem ofRealH3Zorn_U (X Y : H3Zorn ℝ) :
    ofRealH3Zorn (H3Zorn.U X Y) = H3Zorn.U (ofRealH3Zorn X) (ofRealH3Zorn Y) := by
  simp only [H3Zorn.U, map_sub, map_smul, ← Complex.coe_smul,
    ofRealH3Zorn_traceBilin, ofRealH3Zorn_crossProduct, ofRealH3Zorn_adjointQuad]

@[simp] theorem ofRealH3Zorn_T (X Y Z : H3Zorn ℝ) :
    ofRealH3Zorn (H3Zorn.T X Y Z) =
      H3Zorn.T (ofRealH3Zorn X) (ofRealH3Zorn Y) (ofRealH3Zorn Z) := by
  simp [H3Zorn.T, map_sub, map_add, ofRealH3Zorn_U]

@[simp] theorem ofRealH3Zorn_normTrilin (X Y Z : H3Zorn ℝ) :
    h3zornNormTrilinℂ (ofRealH3Zorn X) (ofRealH3Zorn Y) (ofRealH3Zorn Z) =
      ((h3zornNormTrilin X Y Z : ℝ) : ℂ) := by
  dsimp only [h3zornNormTrilinℂ, h3zornNormTrilin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofRealH3Zorn_crossProduct, ofRealH3Zorn_traceBilin]
  push_cast; rfl

@[simp] theorem ofRealH3Zorn_jordanMul (X Y : H3Zorn ℝ) :
    ofRealH3Zorn (X * Y) = candidateJordanMulZornℂ (ofRealH3Zorn X) (ofRealH3Zorn Y) := by
  change ofRealH3Zorn ((1 / 2 : ℝ) • H3Zorn.T X 1 Y) =
    (1 / 2 : ℂ) • H3Zorn.T (ofRealH3Zorn X) 1 (ofRealH3Zorn Y)
  rw [map_smul, ofRealH3Zorn_T, ofRealH3Zorn_one, ← Complex.coe_smul]
  norm_num

section DiamondFreeBaseChange

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Complexified cubic stabilizer Lie subalgebra `𝔢₆(ℂ)` on `H3Octonion ℂ`. -/
def h3OctonionCubicStabilizerℂ : LieSubalgebra ℂ (Module.End ℂ (H3Octonion ℂ)) :=
  TrilinearStabilizer.trilinearStabilizer h3OctonionNormTrilinℂ

/-- Complexified cubic stabilizer Lie subalgebra `𝔢₆(ℂ)` on `H3Zorn ℂ`. -/
def h3zornCubicStabilizerℂ : LieSubalgebra ℂ (Module.End ℂ (H3Zorn ℂ)) :=
  TrilinearStabilizer.trilinearStabilizer h3zornNormTrilinℂ

private theorem candidateJordanMulOctℂ_zero_left (y : H3Octonion ℂ) :
    candidateJordanMulOctℂ 0 y = 0 := by
  simp [candidateJordanMulOctℂ, H3Octonion.T_outer_formula]

private theorem candidateJordanMulOctℂ_zero_right (x : H3Octonion ℂ) :
    candidateJordanMulOctℂ x 0 = 0 := by
  simp [candidateJordanMulOctℂ, H3Octonion.T_outer_formula]

private theorem candidateJordanMulOctℂ_add_left (x₁ x₂ y : H3Octonion ℂ) :
    candidateJordanMulOctℂ (x₁ + x₂) y =
      candidateJordanMulOctℂ x₁ y + candidateJordanMulOctℂ x₂ y := by
  simp [candidateJordanMulOctℂ, H3Octonion.T_add_left, smul_add]

private theorem candidateJordanMulOctℂ_add_right (x y₁ y₂ : H3Octonion ℂ) :
    candidateJordanMulOctℂ x (y₁ + y₂) =
      candidateJordanMulOctℂ x y₁ + candidateJordanMulOctℂ x y₂ := by
  simp [candidateJordanMulOctℂ, H3Octonion.T_add_outer, smul_add]

private theorem candidateJordanMulOctℂ_smul_left (z : ℂ) (x y : H3Octonion ℂ) :
    candidateJordanMulOctℂ (z • x) y = z • candidateJordanMulOctℂ x y := by
  rw [candidateJordanMulOctℂ, candidateJordanMulOctℂ, H3Octonion.T_smul_left,
    smul_comm z (1 / 2 : ℂ)]

private theorem candidateJordanMulOctℂ_smul_right (z : ℂ) (x y : H3Octonion ℂ) :
    candidateJordanMulOctℂ x (z • y) = z • candidateJordanMulOctℂ x y := by
  rw [candidateJordanMulOctℂ, candidateJordanMulOctℂ, H3Octonion.T_smul_outer,
    smul_comm z (1 / 2 : ℂ)]

private theorem candidateJordanMulOctℂ_sub_left (x₁ x₂ y : H3Octonion ℂ) :
    candidateJordanMulOctℂ (x₁ - x₂) y =
      candidateJordanMulOctℂ x₁ y - candidateJordanMulOctℂ x₂ y := by
  rw [sub_eq_add_neg, candidateJordanMulOctℂ_add_left,
    show -x₂ = (-1 : ℂ) • x₂ by module, candidateJordanMulOctℂ_smul_left]
  module

private theorem candidateJordanMulOctℂ_sub_right (x y₁ y₂ : H3Octonion ℂ) :
    candidateJordanMulOctℂ x (y₁ - y₂) =
      candidateJordanMulOctℂ x y₁ - candidateJordanMulOctℂ x y₂ := by
  rw [sub_eq_add_neg, candidateJordanMulOctℂ_add_right,
    show -y₂ = (-1 : ℂ) • y₂ by module, candidateJordanMulOctℂ_smul_right]
  module

private theorem h3zorn_adjointQuad_zero :
    H3Zorn.adjointQuad (0 : H3Zorn ℂ) = 0 := by
  apply H3Zorn.ext_h3 <;>
    simp [H3Zorn.adjointQuad, ZornVectorMatrix.norm, ZornVec3.dot,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVec3.cross,
      ZornVectorMatrix.zero]

private theorem h3zorn_crossProduct_zero_left (Y : H3Zorn ℂ) :
    H3Zorn.crossProduct (0 : H3Zorn ℂ) Y = 0 := by
  rw [H3Zorn.crossProduct, zero_add, h3zorn_adjointQuad_zero, sub_zero, sub_self]

private theorem h3zorn_crossProduct_zero_right (X : H3Zorn ℂ) :
    H3Zorn.crossProduct X (0 : H3Zorn ℂ) = 0 := by
  rw [H3Zorn.crossProduct, add_zero, h3zorn_adjointQuad_zero, sub_self, sub_zero]

private theorem h3zorn_linearTrace_zero : H3Zorn.linearTrace (0 : H3Zorn ℂ) = 0 := by
  simp [H3Zorn.linearTrace]

private theorem candidateJordanMulZornℂ_zero_left (Y : H3Zorn ℂ) :
    candidateJordanMulZornℂ 0 Y = 0 := by
  rw [candidateJordanMulZornℂ, H3Zorn.T_outer_formula, H3Zorn.traceBilin_zero_left, zero_smul,
    smul_zero, h3zorn_crossProduct_zero_left, h3zorn_crossProduct_zero_left, sub_zero, add_zero,
    smul_zero]

private theorem candidateJordanMulZornℂ_zero_right (X : H3Zorn ℂ) :
    candidateJordanMulZornℂ X 0 = 0 := by
  rw [candidateJordanMulZornℂ, H3Zorn.T_outer_formula, smul_zero, H3Zorn.traceBilin_zero_left,
    zero_smul, h3zorn_crossProduct_zero_right, h3zorn_crossProduct_zero_left, sub_zero, add_zero,
    smul_zero]

private theorem candidateJordanMulZornℂ_add_left (X₁ X₂ Y : H3Zorn ℂ) :
    candidateJordanMulZornℂ (X₁ + X₂) Y =
      candidateJordanMulZornℂ X₁ Y + candidateJordanMulZornℂ X₂ Y := by
  simp [candidateJordanMulZornℂ, H3Zorn.T_add_left, smul_add]

private theorem candidateJordanMulZornℂ_add_right (X Y₁ Y₂ : H3Zorn ℂ) :
    candidateJordanMulZornℂ X (Y₁ + Y₂) =
      candidateJordanMulZornℂ X Y₁ + candidateJordanMulZornℂ X Y₂ := by
  simp [candidateJordanMulZornℂ, H3Zorn.T_add_right, smul_add]

private theorem candidateJordanMulZornℂ_smul_left (z : ℂ) (X Y : H3Zorn ℂ) :
    candidateJordanMulZornℂ (z • X) Y = z • candidateJordanMulZornℂ X Y := by
  rw [candidateJordanMulZornℂ, candidateJordanMulZornℂ, H3Zorn.T_smul_left,
    smul_comm z (1 / 2 : ℂ)]

private theorem candidateJordanMulZornℂ_smul_right (z : ℂ) (X Y : H3Zorn ℂ) :
    candidateJordanMulZornℂ X (z • Y) = z • candidateJordanMulZornℂ X Y := by
  rw [candidateJordanMulZornℂ, candidateJordanMulZornℂ, H3Zorn.T_smul_right,
    smul_comm z (1 / 2 : ℂ)]

private theorem candidateJordanMulZornℂ_sub_left (X₁ X₂ Y : H3Zorn ℂ) :
    candidateJordanMulZornℂ (X₁ - X₂) Y =
      candidateJordanMulZornℂ X₁ Y - candidateJordanMulZornℂ X₂ Y := by
  rw [sub_eq_add_neg, candidateJordanMulZornℂ_add_left,
    show -X₂ = (-1 : ℂ) • X₂ by module, candidateJordanMulZornℂ_smul_left]
  module

private theorem candidateJordanMulZornℂ_sub_right (X Y₁ Y₂ : H3Zorn ℂ) :
    candidateJordanMulZornℂ X (Y₁ - Y₂) =
      candidateJordanMulZornℂ X Y₁ - candidateJordanMulZornℂ X Y₂ := by
  rw [sub_eq_add_neg, candidateJordanMulZornℂ_add_right,
    show -Y₂ = (-1 : ℂ) • Y₂ by module, candidateJordanMulZornℂ_smul_right]
  module

/-- Complexified Jordan derivation Lie subalgebra `𝔣₄(ℂ)` on `H3Octonion ℂ` (without global `Mul`). -/
def h3OctonionF4Derivationsℂ : LieSubalgebra ℂ (Module.End ℂ (H3Octonion ℂ)) where
  carrier := {D | ∀ x y : H3Octonion ℂ,
    D (candidateJordanMulOctℂ x y) =
      candidateJordanMulOctℂ (D x) y + candidateJordanMulOctℂ x (D y)}
  zero_mem' := by
    intro x y
    simp [candidateJordanMulOctℂ_zero_left, candidateJordanMulOctℂ_zero_right]
  add_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    simp only [LinearMap.add_apply]
    rw [h₁ x y, h₂ x y, candidateJordanMulOctℂ_add_left, candidateJordanMulOctℂ_add_right]
    abel
  smul_mem' := by
    intro z D h x y
    simp only [LinearMap.smul_apply]
    rw [h x y, smul_add, candidateJordanMulOctℂ_smul_left, candidateJordanMulOctℂ_smul_right]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ x y
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply]
    rw [h₂ x y, map_add, h₁ (D₂ x) y, h₁ x (D₂ y),
      h₁ x y, map_add, h₂ (D₁ x) y, h₂ x (D₁ y),
      candidateJordanMulOctℂ_sub_left, candidateJordanMulOctℂ_sub_right]
    abel

/-- Complexified Jordan derivation Lie subalgebra `𝔣₄(ℂ)` on `H3Zorn ℂ` (without global `Mul`). -/
def h3zornF4Derivationsℂ : LieSubalgebra ℂ (Module.End ℂ (H3Zorn ℂ)) where
  carrier := {D | ∀ X Y : H3Zorn ℂ,
    D (candidateJordanMulZornℂ X Y) =
      candidateJordanMulZornℂ (D X) Y + candidateJordanMulZornℂ X (D Y)}
  zero_mem' := by
    intro X Y
    simp only [LinearMap.zero_apply, candidateJordanMulZornℂ_zero_left,
      candidateJordanMulZornℂ_zero_right, add_zero]
  add_mem' := by
    intro D₁ D₂ h₁ h₂ X Y
    simp only [LinearMap.add_apply]
    rw [h₁ X Y, h₂ X Y, candidateJordanMulZornℂ_add_left, candidateJordanMulZornℂ_add_right]
    abel
  smul_mem' := by
    intro z D h X Y
    simp only [LinearMap.smul_apply]
    rw [h X Y, smul_add, candidateJordanMulZornℂ_smul_left, candidateJordanMulZornℂ_smul_right]
  lie_mem' := by
    intro D₁ D₂ h₁ h₂ X Y
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply]
    rw [h₂ X Y, map_add, h₁ (D₂ X) Y, h₁ X (D₂ Y),
      h₁ X Y, map_add, h₂ (D₁ X) Y, h₂ X (D₁ Y),
      candidateJordanMulZornℂ_sub_left, candidateJordanMulZornℂ_sub_right]
    abel

section EndLift

variable {V V_ℂ : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup V_ℂ] [Module ℂ V_ℂ]

/-- Lift an `ℝ`-linear endomorphism of `V` to a `ℂ`-linear endomorphism of `V_ℂ`
through `τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ`. -/
def liftEnd (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (D : Module.End ℝ V) : Module.End ℂ V_ℂ :=
  τ.conj (D.baseChange ℂ)

def reEnd (ofReal : V →ₗ[ℝ] V_ℂ) (rePart : V_ℂ →ₗ[ℝ] V) (T : Module.End ℂ V_ℂ) :
    Module.End ℝ V :=
  rePart ∘ₗ T.restrictScalars ℝ ∘ₗ ofReal

def imEnd (ofReal : V →ₗ[ℝ] V_ℂ) (imPart : V_ℂ →ₗ[ℝ] V) (T : Module.End ℂ V_ℂ) :
    Module.End ℝ V :=
  imPart ∘ₗ T.restrictScalars ℝ ∘ₗ ofReal

theorem liftEnd_apply_ofReal (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (ofReal : V →ₗ[ℝ] V_ℂ)
    (htau : ∀ (z : ℂ) (v : V), τ (z ⊗ₜ[ℝ] v) = z • ofReal v)
    (D : Module.End ℝ V) (v : V) :
    liftEnd τ D (ofReal v) = ofReal (D v) := by
  have h1 : ofReal v = τ ((1 : ℂ) ⊗ₜ[ℝ] v) := by simp [htau]
  rw [h1]
  dsimp [liftEnd]
  rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, htau, one_smul]

theorem liftEnd_mul (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (D₁ D₂ : Module.End ℝ V) :
    liftEnd τ (D₁ * D₂) = liftEnd τ D₁ * liftEnd τ D₂ := by
  change τ.conj (LinearMap.baseChange ℂ (D₁ ∘ₗ D₂)) =
    (τ.conj (LinearMap.baseChange ℂ D₁)).comp (τ.conj (LinearMap.baseChange ℂ D₂))
  rw [LinearMap.baseChange_comp, LinearEquiv.conj_comp]

theorem liftEnd_lie (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (D₁ D₂ : Module.End ℝ V) :
    liftEnd τ ⁅D₁, D₂⁆ = ⁅liftEnd τ D₁, liftEnd τ D₂⁆ := by
  change liftEnd τ (D₁ * D₂ - D₂ * D₁) = liftEnd τ D₁ * liftEnd τ D₂ - liftEnd τ D₂ * liftEnd τ D₁
  have hsub : ∀ f g : Module.End ℝ V, liftEnd τ (f - g) = liftEnd τ f - liftEnd τ g := by
    intro f g; simp [liftEnd, map_sub]
  rw [hsub, liftEnd_mul, liftEnd_mul]

theorem liftEnd_add (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (D₁ D₂ : Module.End ℝ V) :
    liftEnd τ (D₁ + D₂) = liftEnd τ D₁ + liftEnd τ D₂ := by
  simp [liftEnd, LinearMap.baseChange_add, map_add]

theorem liftEnd_smul (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (r : ℝ) (D : Module.End ℝ V) :
    liftEnd τ (r • D) = (r : ℂ) • liftEnd τ D := by
  ext w
  obtain ⟨u, rfl⟩ := τ.surjective w
  induction u using TensorProduct.inductionOn with
  | tmul z v =>
    simp only [liftEnd, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      LinearMap.baseChange_tmul, LinearMap.smul_apply]
    rw [← TensorProduct.smul_tmul, Complex.real_smul, ← smul_eq_mul,
      ← TensorProduct.smul_tmul']
    simp only [map_smul]
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    rw [hx, hy]

theorem reEnd_liftEnd (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (ofReal : V →ₗ[ℝ] V_ℂ)
    (rePart : V_ℂ →ₗ[ℝ] V) (htau : ∀ z v, τ (z ⊗ₜ[ℝ] v) = z • ofReal v)
    (hre : ∀ v, rePart (ofReal v) = v) (D : Module.End ℝ V) :
    reEnd ofReal rePart (liftEnd τ D) = D := by
  ext v
  simp [reEnd, liftEnd_apply_ofReal τ ofReal htau D v, hre]

theorem imEnd_liftEnd (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (ofReal : V →ₗ[ℝ] V_ℂ)
    (imPart : V_ℂ →ₗ[ℝ] V) (htau : ∀ z v, τ (z ⊗ₜ[ℝ] v) = z • ofReal v)
    (him : ∀ v, imPart (ofReal v) = 0) (D : Module.End ℝ V) :
    imEnd ofReal imPart (liftEnd τ D) = 0 := by
  ext v
  simp [imEnd, liftEnd_apply_ofReal τ ofReal htau D v, him]

theorem liftEnd_reEnd_add_I_imEnd (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (ofReal : V →ₗ[ℝ] V_ℂ)
    (rePart imPart : V_ℂ →ₗ[ℝ] V) (htau : ∀ z v, τ (z ⊗ₜ[ℝ] v) = z • ofReal v)
    (hdecomp : ∀ w, ofReal (rePart w) + Complex.I • ofReal (imPart w) = w)
    (T : Module.End ℂ V_ℂ) :
    liftEnd τ (reEnd ofReal rePart T) + Complex.I • liftEnd τ (imEnd ofReal imPart T) = T := by
  ext w
  rw [← hdecomp w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    liftEnd_apply_ofReal τ ofReal htau]
  simp only [reEnd, imEnd, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hdecomp]

/-- Generic diamond-free `ℂ`-Lie algebra isomorphism `ℂ ⊗[ℝ] S ≃ₗ⁅ℂ⁆ S_ℂ` for a
real Lie subalgebra `S ≤ End ℝ V` and complex Lie subalgebra `S_ℂ ≤ End ℂ V_ℂ`. -/
def mkBaseChangeLieEquiv
    (τ : ℂ ⊗[ℝ] V ≃ₗ[ℂ] V_ℂ) (ofReal : V →ₗ[ℝ] V_ℂ)
    (rePart imPart : V_ℂ →ₗ[ℝ] V)
    (htau : ∀ z v, τ (z ⊗ₜ[ℝ] v) = z • ofReal v)
    (hre : ∀ v, rePart (ofReal v) = v)
    (him : ∀ v, imPart (ofReal v) = 0)
    (hdecomp : ∀ w, ofReal (rePart w) + Complex.I • ofReal (imPart w) = w)
    (hreI : ∀ w, rePart (Complex.I • w) = -imPart w)
    (himI : ∀ w, imPart (Complex.I • w) = rePart w)
    (S : LieSubalgebra ℝ (Module.End ℝ V))
    (S_ℂ : LieSubalgebra ℂ (Module.End ℂ V_ℂ))
    (hlift : ∀ D ∈ S, liftEnd τ D ∈ S_ℂ)
    (hsplit : ∀ T ∈ S_ℂ, reEnd ofReal rePart T ∈ S ∧ imEnd ofReal imPart T ∈ S) :
    ℂ ⊗[ℝ] S ≃ₗ⁅ℂ⁆ S_ℂ :=
  let toFun : ℂ ⊗[ℝ] S →ₗ[ℂ] S_ℂ :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun z =>
          { toFun := fun D => ⟨z • liftEnd τ D.1, S_ℂ.smul_mem z (hlift D.1 D.2)⟩
            map_add' := fun D₁ D₂ => by
              apply Subtype.ext
              change z • liftEnd τ (D₁.1 + D₂.1) = z • liftEnd τ D₁.1 + z • liftEnd τ D₂.1
              rw [liftEnd_add, smul_add]
            map_smul' := fun r D => by
              apply Subtype.ext
              change z • liftEnd τ (r • D.1) = (r : ℂ) • (z • liftEnd τ D.1)
              rw [liftEnd_smul, smul_comm z (r : ℂ)] }
        map_add' := fun z₁ z₂ => by
          apply LinearMap.ext; intro D; apply Subtype.ext; simp [add_smul]
        map_smul' := fun c z => by
          apply LinearMap.ext; intro D; apply Subtype.ext; simp [mul_smul] }
  let invFun : S_ℂ →ₗ[ℂ] ℂ ⊗[ℝ] S :=
    { toFun := fun T =>
        (1 : ℂ) ⊗ₜ[ℝ] ⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ +
        Complex.I ⊗ₜ[ℝ] ⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩
      map_add' := fun T₁ T₂ => by
        have hre_add : (⟨reEnd ofReal rePart (T₁ + T₂).1, (hsplit _ (T₁ + T₂).2).1⟩ : S) =
            ⟨reEnd ofReal rePart T₁.1, (hsplit T₁.1 T₁.2).1⟩ +
            ⟨reEnd ofReal rePart T₂.1, (hsplit T₂.1 T₂.2).1⟩ := by
          apply Subtype.ext; ext v; simp [reEnd]
        have him_add : (⟨imEnd ofReal imPart (T₁ + T₂).1, (hsplit _ (T₁ + T₂).2).2⟩ : S) =
            ⟨imEnd ofReal imPart T₁.1, (hsplit T₁.1 T₁.2).2⟩ +
            ⟨imEnd ofReal imPart T₂.1, (hsplit T₂.1 T₂.2).2⟩ := by
          apply Subtype.ext; ext v; simp [imEnd]
        rw [hre_add, him_add, TensorProduct.tmul_add, TensorProduct.tmul_add]; abel
      map_smul' := fun z T => by
        have hre_smul : (⟨reEnd ofReal rePart (z • T).1, (hsplit _ (z • T).2).1⟩ : S) =
            z.re • ⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ -
            z.im • ⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ := by
          apply Subtype.ext; ext v
          change rePart ((z • T.1) (ofReal v)) =
            z.re • rePart (T.1 (ofReal v)) - z.im • imPart (T.1 (ofReal v))
          rw [LinearMap.smul_apply, complex_smul_split z (T.1 (ofReal v)), map_add, map_smul,
            map_smul, hreI]
          simp [sub_eq_add_neg]
        have him_smul : (⟨imEnd ofReal imPart (z • T).1, (hsplit _ (z • T).2).2⟩ : S) =
            z.re • ⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ +
            z.im • ⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ := by
          apply Subtype.ext; ext v
          change imPart ((z • T.1) (ofReal v)) =
            z.re • imPart (T.1 (ofReal v)) + z.im • rePart (T.1 (ofReal v))
          rw [LinearMap.smul_apply, complex_smul_split z (T.1 (ofReal v)), map_add, map_smul,
            map_smul, himI]
        rw [hre_smul, him_smul, TensorProduct.tmul_sub, TensorProduct.tmul_add,
          ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
          ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
          Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul,
          mul_one, mul_one]
        have hRHS : (RingHom.id ℂ) z •
            ((1 : ℂ) ⊗ₜ[ℝ] (⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ : S) +
              Complex.I ⊗ₜ[ℝ] (⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ : S)) =
            z ⊗ₜ[ℝ] (⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ : S) +
            (z * Complex.I) ⊗ₜ[ℝ] (⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ : S) := by
          rw [RingHom.id_apply, smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
            smul_eq_mul, smul_eq_mul, mul_one]
        rw [hRHS]
        have hz1 : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
        have hz2 : (-(z.im : ℂ) + (z.re : ℂ) * Complex.I) = z * Complex.I := by
          conv_rhs => rw [← Complex.re_add_im z]
          ring_nf; simp [Complex.I_sq]
        have h1 : (z.re : ℂ) ⊗ₜ[ℝ] (⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ : S) +
            ((z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] (⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ : S) =
            z ⊗ₜ[ℝ] (⟨reEnd ofReal rePart T.1, (hsplit T.1 T.2).1⟩ : S) := by
          rw [← TensorProduct.add_tmul, hz1]
        have h2 : (-(z.im : ℂ)) ⊗ₜ[ℝ] (⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ : S) +
            ((z.re : ℂ) * Complex.I) ⊗ₜ[ℝ] (⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ : S) =
            (z * Complex.I) ⊗ₜ[ℝ] (⟨imEnd ofReal imPart T.1, (hsplit T.1 T.2).2⟩ : S) := by
          rw [← TensorProduct.add_tmul, hz2]
        rw [← h1, ← h2, TensorProduct.neg_tmul, sub_eq_add_neg]
        abel }
  { toFun := toFun
    invFun := invFun
    map_add' := toFun.map_add'
    map_smul' := toFun.map_smul'
    left_inv := fun u => by
      induction u using TensorProduct.inductionOn with
      | tmul z D =>
        have hlift_tmul : toFun (z ⊗ₜ[ℝ] D) =
            ⟨z • liftEnd τ D.1, S_ℂ.smul_mem z (hlift D.1 D.2)⟩ := rfl
        rw [hlift_tmul]
        change (1 : ℂ) ⊗ₜ[ℝ] ⟨reEnd ofReal rePart (z • liftEnd τ D.1), _⟩ +
          Complex.I ⊗ₜ[ℝ] ⟨imEnd ofReal imPart (z • liftEnd τ D.1), _⟩ = z ⊗ₜ[ℝ] D
        have hreD : (⟨reEnd ofReal rePart (z • liftEnd τ D.1),
            (hsplit _ (S_ℂ.smul_mem z (hlift D.1 D.2))).1⟩ : S) = z.re • D := by
          apply Subtype.ext; ext v
          change rePart ((z • liftEnd τ D.1) (ofReal v)) = (z.re • D.1) v
          rw [LinearMap.smul_apply, liftEnd_apply_ofReal τ ofReal htau D.1 v,
            complex_smul_split z (ofReal (D.1 v)), map_add, map_smul, map_smul,
            hre, hreI, him, neg_zero, smul_zero, add_zero, LinearMap.smul_apply]
        have himD : (⟨imEnd ofReal imPart (z • liftEnd τ D.1),
            (hsplit _ (S_ℂ.smul_mem z (hlift D.1 D.2))).2⟩ : S) = z.im • D := by
          apply Subtype.ext; ext v
          change imPart ((z • liftEnd τ D.1) (ofReal v)) = (z.im • D.1) v
          rw [LinearMap.smul_apply, liftEnd_apply_ofReal τ ofReal htau D.1 v,
            complex_smul_split z (ofReal (D.1 v)), map_add, map_smul, map_smul,
            him, himI, hre, smul_zero, zero_add, LinearMap.smul_apply]
        rw [hreD, himD, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
          Complex.real_smul, Complex.real_smul, mul_one,
          ← TensorProduct.add_tmul, Complex.re_add_im]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    right_inv := fun T => by
      apply Subtype.ext
      change (1 : ℂ) • liftEnd τ (reEnd ofReal rePart T.1) +
        Complex.I • liftEnd τ (imEnd ofReal imPart T.1) = T.1
      rw [one_smul]
      exact liftEnd_reEnd_add_I_imEnd τ ofReal rePart imPart htau hdecomp T.1
    map_lie' := fun {x y} => by
      induction x using TensorProduct.inductionOn generalizing y with
      | tmul z₁ D₁ =>
        induction y using TensorProduct.inductionOn with
        | tmul z₂ D₂ =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul]
          apply Subtype.ext
          change (z₁ * z₂) • liftEnd τ (⁅D₁, D₂⁆ : S).1 =
            ⁅(⟨z₁ • liftEnd τ D₁.1, S_ℂ.smul_mem z₁ (hlift D₁.1 D₁.2)⟩ : S_ℂ),
             (⟨z₂ • liftEnd τ D₂.1, S_ℂ.smul_mem z₂ (hlift D₂.1 D₂.2)⟩ : S_ℂ)⁆.1
          change (z₁ * z₂) • liftEnd τ ⁅D₁.1, D₂.1⁆ = ⁅z₁ • liftEnd τ D₁.1, z₂ • liftEnd τ D₂.1⁆
          rw [liftEnd_lie, smul_lie, lie_smul, smul_smul]
        | add a b ha hb =>
          rw [lie_add, map_add, map_add, lie_add, ha, hb]
      | add a b ha hb =>
        rw [add_lie, map_add, map_add, add_lie, ha, hb] }

end EndLift

section MembershipLemmas

private theorem liftEnd_h3Octonion_trilinearStabilizer
    (D : Module.End ℝ (H3Octonion ℝ)) (hD : D ∈ h3OctonionCubicStabilizer) :
    liftEnd tensorEquivH3Octonion D ∈ h3OctonionCubicStabilizerℂ := by
  rw [h3OctonionCubicStabilizerℂ, TrilinearStabilizer.mem_trilinearStabilizer]
  intro x y z
  rw [← ofReal_rePart_add_I_imPart_H3Octonion x,
    ← ofReal_rePart_add_I_imPart_H3Octonion y,
    ← ofReal_rePart_add_I_imPart_H3Octonion z]
  have hreal : ∀ a b c : H3Octonion ℝ,
      h3OctonionNormTrilinℂ (liftEnd tensorEquivH3Octonion D (ofRealH3Octonion a))
          (ofRealH3Octonion b) (ofRealH3Octonion c) +
        h3OctonionNormTrilinℂ (ofRealH3Octonion a)
          (liftEnd tensorEquivH3Octonion D (ofRealH3Octonion b)) (ofRealH3Octonion c) +
        h3OctonionNormTrilinℂ (ofRealH3Octonion a) (ofRealH3Octonion b)
          (liftEnd tensorEquivH3Octonion D (ofRealH3Octonion c)) = 0 := by
    intro a b c
    rw [liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul,
      liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul,
      liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul,
      ofRealH3Octonion_normTrilin, ofRealH3Octonion_normTrilin, ofRealH3Octonion_normTrilin]
    norm_cast
    exact hD a b c
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination
    hreal (rePartH3Octonion x) (rePartH3Octonion y) (rePartH3Octonion z) +
    Complex.I * hreal (rePartH3Octonion x) (rePartH3Octonion y) (imPartH3Octonion z) +
    Complex.I * hreal (rePartH3Octonion x) (imPartH3Octonion y) (rePartH3Octonion z) +
    (Complex.I * Complex.I) * hreal (rePartH3Octonion x) (imPartH3Octonion y) (imPartH3Octonion z) +
    Complex.I * hreal (imPartH3Octonion x) (rePartH3Octonion y) (rePartH3Octonion z) +
    (Complex.I * Complex.I) * hreal (imPartH3Octonion x) (rePartH3Octonion y) (imPartH3Octonion z) +
    (Complex.I * Complex.I) * hreal (imPartH3Octonion x) (imPartH3Octonion y) (rePartH3Octonion z) +
    (Complex.I * Complex.I * Complex.I) *
      hreal (imPartH3Octonion x) (imPartH3Octonion y) (imPartH3Octonion z)

private theorem split_h3Octonion_trilinearStabilizer
    (T : Module.End ℂ (H3Octonion ℂ)) (hT : T ∈ h3OctonionCubicStabilizerℂ) :
    reEnd ofRealH3Octonion rePartH3Octonion T ∈ h3OctonionCubicStabilizer ∧
    imEnd ofRealH3Octonion imPartH3Octonion T ∈ h3OctonionCubicStabilizer := by
  have hreal : ∀ a b c : H3Octonion ℝ,
      h3OctonionNormTrilinℂ (T (ofRealH3Octonion a)) (ofRealH3Octonion b) (ofRealH3Octonion c) +
        h3OctonionNormTrilinℂ (ofRealH3Octonion a) (T (ofRealH3Octonion b)) (ofRealH3Octonion c) +
        h3OctonionNormTrilinℂ (ofRealH3Octonion a) (ofRealH3Octonion b) (T (ofRealH3Octonion c)) = 0 :=
    fun a b c => hT _ _ _
  have hre_eval : ∀ b c : H3Octonion ℝ, ∀ u : H3Octonion ℂ,
      (h3OctonionNormTrilinℂ u (ofRealH3Octonion b) (ofRealH3Octonion c)).re =
        h3OctonionNormTrilin (rePartH3Octonion u) b c ∧
      (h3OctonionNormTrilinℂ u (ofRealH3Octonion b) (ofRealH3Octonion c)).im =
        h3OctonionNormTrilin (imPartH3Octonion u) b c := by
    intro b c u
    have hu := (ofReal_rePart_add_I_imPart_H3Octonion u).symm
    have hval : h3OctonionNormTrilinℂ u (ofRealH3Octonion b) (ofRealH3Octonion c) =
        (h3OctonionNormTrilin (rePartH3Octonion u) b c : ℂ) +
          Complex.I * (h3OctonionNormTrilin (imPartH3Octonion u) b c : ℂ) := by
      conv_lhs => rw [hu]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ofRealH3Octonion_normTrilin]
    rw [hval]
    simp
  have hsymm : ∀ a b c : H3Octonion ℝ, ∀ u : H3Octonion ℂ,
      h3OctonionNormTrilinℂ (ofRealH3Octonion a) u (ofRealH3Octonion c) =
        h3OctonionNormTrilinℂ u (ofRealH3Octonion a) (ofRealH3Octonion c) ∧
      h3OctonionNormTrilinℂ (ofRealH3Octonion a) (ofRealH3Octonion b) u =
        h3OctonionNormTrilinℂ u (ofRealH3Octonion a) (ofRealH3Octonion b) := by
    intro a b c u
    have htr_symm : ∀ x y z : H3Octonion ℂ,
        h3OctonionNormTrilinℂ x y z =
          h3zornNormTrilinℂ (h3OctonionComplexEquiv x) (h3OctonionComplexEquiv y)
            (h3OctonionComplexEquiv z) := fun x y z =>
      (h3OctonionComplexEquiv_normTrilin x y z).symm
    have hz12 : ∀ X Y Z : H3Zorn ℂ,
        h3zornNormTrilinℂ X Y Z = h3zornNormTrilinℂ Y X Z := by
      intro X Y Z
      dsimp [h3zornNormTrilinℂ]
      rw [H3Zorn.traceBilin_symm X, H3Zorn.traceBilin_crossProduct_assoc, H3Zorn.crossProduct_symm Z X]
    have hz23 : ∀ X Y Z : H3Zorn ℂ,
        h3zornNormTrilinℂ X Y Z = h3zornNormTrilinℂ X Z Y := by
      intro X Y Z
      dsimp [h3zornNormTrilinℂ]
      rw [H3Zorn.crossProduct_symm Y Z]
    constructor
    · rw [htr_symm, htr_symm, hz12]
    · rw [htr_symm, htr_symm, hz23, hz12]
  constructor
  · intro a b c
    have h0 := congrArg Complex.re (hreal a b c)
    rw [Complex.zero_re, Complex.add_re, Complex.add_re] at h0
    have h1 := (hre_eval b c (T (ofRealH3Octonion a))).1
    have h2 := (hre_eval a c (T (ofRealH3Octonion b))).1
    have h3 := (hre_eval a b (T (ofRealH3Octonion c))).1
    rw [(hsymm a b c (T (ofRealH3Octonion b))).1, (hsymm a b c (T (ofRealH3Octonion c))).2] at h0
    rw [h1, h2, h3] at h0
    have hba : h3OctonionNormTrilin (rePartH3Octonion (T (ofRealH3Octonion b))) a c =
        h3OctonionNormTrilin a (rePartH3Octonion (T (ofRealH3Octonion b))) c :=
      h3OctonionNormTrilin_symm_12 _ a c
    have hca : h3OctonionNormTrilin (rePartH3Octonion (T (ofRealH3Octonion c))) a b =
        h3OctonionNormTrilin a b (rePartH3Octonion (T (ofRealH3Octonion c))) := by
      rw [h3OctonionNormTrilin_symm_12, h3OctonionNormTrilin_symm_23]
    change h3OctonionNormTrilin (rePartH3Octonion (T (ofRealH3Octonion a))) b c +
      h3OctonionNormTrilin a (rePartH3Octonion (T (ofRealH3Octonion b))) c +
      h3OctonionNormTrilin a b (rePartH3Octonion (T (ofRealH3Octonion c))) = 0
    rw [← hba, ← hca]
    exact h0
  · intro a b c
    have h0 := congrArg Complex.im (hreal a b c)
    rw [Complex.zero_im, Complex.add_im, Complex.add_im] at h0
    have h1 := (hre_eval b c (T (ofRealH3Octonion a))).2
    have h2 := (hre_eval a c (T (ofRealH3Octonion b))).2
    have h3 := (hre_eval a b (T (ofRealH3Octonion c))).2
    rw [(hsymm a b c (T (ofRealH3Octonion b))).1, (hsymm a b c (T (ofRealH3Octonion c))).2] at h0
    rw [h1, h2, h3] at h0
    have hba : h3OctonionNormTrilin (imPartH3Octonion (T (ofRealH3Octonion b))) a c =
        h3OctonionNormTrilin a (imPartH3Octonion (T (ofRealH3Octonion b))) c :=
      h3OctonionNormTrilin_symm_12 _ a c
    have hca : h3OctonionNormTrilin (imPartH3Octonion (T (ofRealH3Octonion c))) a b =
        h3OctonionNormTrilin a b (imPartH3Octonion (T (ofRealH3Octonion c))) := by
      rw [h3OctonionNormTrilin_symm_12, h3OctonionNormTrilin_symm_23]
    change h3OctonionNormTrilin (imPartH3Octonion (T (ofRealH3Octonion a))) b c +
      h3OctonionNormTrilin a (imPartH3Octonion (T (ofRealH3Octonion b))) c +
      h3OctonionNormTrilin a b (imPartH3Octonion (T (ofRealH3Octonion c))) = 0
    rw [← hba, ← hca]
    exact h0

private theorem liftEnd_h3zorn_trilinearStabilizer
    (D : Module.End ℝ (H3Zorn ℝ)) (hD : D ∈ h3zornCubicStabilizer) :
    liftEnd tensorEquivH3Zorn D ∈ h3zornCubicStabilizerℂ := by
  rw [h3zornCubicStabilizerℂ, TrilinearStabilizer.mem_trilinearStabilizer]
  intro X Y Z
  rw [← ofReal_rePart_add_I_imPart_H3Zorn X,
    ← ofReal_rePart_add_I_imPart_H3Zorn Y,
    ← ofReal_rePart_add_I_imPart_H3Zorn Z]
  have hreal : ∀ A B C : H3Zorn ℝ,
      h3zornNormTrilinℂ (liftEnd tensorEquivH3Zorn D (ofRealH3Zorn A))
          (ofRealH3Zorn B) (ofRealH3Zorn C) +
        h3zornNormTrilinℂ (ofRealH3Zorn A)
          (liftEnd tensorEquivH3Zorn D (ofRealH3Zorn B)) (ofRealH3Zorn C) +
        h3zornNormTrilinℂ (ofRealH3Zorn A) (ofRealH3Zorn B)
          (liftEnd tensorEquivH3Zorn D (ofRealH3Zorn C)) = 0 := by
    intro A B C
    rw [liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
      liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
      liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
      ofRealH3Zorn_normTrilin, ofRealH3Zorn_normTrilin, ofRealH3Zorn_normTrilin]
    norm_cast
    exact hD A B C
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination
    hreal (rePartH3Zorn X) (rePartH3Zorn Y) (rePartH3Zorn Z) +
    Complex.I * hreal (rePartH3Zorn X) (rePartH3Zorn Y) (imPartH3Zorn Z) +
    Complex.I * hreal (rePartH3Zorn X) (imPartH3Zorn Y) (rePartH3Zorn Z) +
    (Complex.I * Complex.I) * hreal (rePartH3Zorn X) (imPartH3Zorn Y) (imPartH3Zorn Z) +
    Complex.I * hreal (imPartH3Zorn X) (rePartH3Zorn Y) (rePartH3Zorn Z) +
    (Complex.I * Complex.I) * hreal (imPartH3Zorn X) (rePartH3Zorn Y) (imPartH3Zorn Z) +
    (Complex.I * Complex.I) * hreal (imPartH3Zorn X) (imPartH3Zorn Y) (rePartH3Zorn Z) +
    (Complex.I * Complex.I * Complex.I) *
      hreal (imPartH3Zorn X) (imPartH3Zorn Y) (imPartH3Zorn Z)

private theorem split_h3zorn_trilinearStabilizer
    (T : Module.End ℂ (H3Zorn ℂ)) (hT : T ∈ h3zornCubicStabilizerℂ) :
    reEnd ofRealH3Zorn rePartH3Zorn T ∈ h3zornCubicStabilizer ∧
    imEnd ofRealH3Zorn imPartH3Zorn T ∈ h3zornCubicStabilizer := by
  have hreal : ∀ A B C : H3Zorn ℝ,
      h3zornNormTrilinℂ (T (ofRealH3Zorn A)) (ofRealH3Zorn B) (ofRealH3Zorn C) +
        h3zornNormTrilinℂ (ofRealH3Zorn A) (T (ofRealH3Zorn B)) (ofRealH3Zorn C) +
        h3zornNormTrilinℂ (ofRealH3Zorn A) (ofRealH3Zorn B) (T (ofRealH3Zorn C)) = 0 :=
    fun A B C => hT _ _ _
  have hre_eval : ∀ B C : H3Zorn ℝ, ∀ U : H3Zorn ℂ,
      (h3zornNormTrilinℂ U (ofRealH3Zorn B) (ofRealH3Zorn C)).re =
        h3zornNormTrilin (rePartH3Zorn U) B C ∧
      (h3zornNormTrilinℂ U (ofRealH3Zorn B) (ofRealH3Zorn C)).im =
        h3zornNormTrilin (imPartH3Zorn U) B C := by
    intro B C U
    have hU := (ofReal_rePart_add_I_imPart_H3Zorn U).symm
    have hval : h3zornNormTrilinℂ U (ofRealH3Zorn B) (ofRealH3Zorn C) =
        (h3zornNormTrilin (rePartH3Zorn U) B C : ℂ) +
          Complex.I * (h3zornNormTrilin (imPartH3Zorn U) B C : ℂ) := by
      conv_lhs => rw [hU]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ofRealH3Zorn_normTrilin]
    rw [hval]
    simp
  have hz12 : ∀ X Y Z : H3Zorn ℂ,
      h3zornNormTrilinℂ X Y Z = h3zornNormTrilinℂ Y X Z := by
    intro X Y Z
    dsimp [h3zornNormTrilinℂ]
    rw [H3Zorn.traceBilin_symm X, H3Zorn.traceBilin_crossProduct_assoc, H3Zorn.crossProduct_symm Z X]
  have hz23 : ∀ X Y Z : H3Zorn ℂ,
      h3zornNormTrilinℂ X Y Z = h3zornNormTrilinℂ X Z Y := by
    intro X Y Z
    dsimp [h3zornNormTrilinℂ]
    rw [H3Zorn.crossProduct_symm Y Z]
  constructor
  · intro A B C
    have h0 := congrArg Complex.re (hreal A B C)
    rw [Complex.zero_re, Complex.add_re, Complex.add_re] at h0
    rw [hz12 (ofRealH3Zorn A) (T (ofRealH3Zorn B)),
      hz23 (ofRealH3Zorn A) (ofRealH3Zorn B), hz12 (ofRealH3Zorn A) (T (ofRealH3Zorn C))] at h0
    have h1 := (hre_eval B C (T (ofRealH3Zorn A))).1
    have h2 := (hre_eval A C (T (ofRealH3Zorn B))).1
    have h3 := (hre_eval A B (T (ofRealH3Zorn C))).1
    rw [h1, h2, h3] at h0
    have hba : h3zornNormTrilin (rePartH3Zorn (T (ofRealH3Zorn B))) A C =
        h3zornNormTrilin A (rePartH3Zorn (T (ofRealH3Zorn B))) C := by
      exact h3zornCubicJordanDatum.normTrilin_swap₁₂
        (rePartH3Zorn (T (ofRealH3Zorn B))) A C
    have hca : h3zornNormTrilin (rePartH3Zorn (T (ofRealH3Zorn C))) A B =
        h3zornNormTrilin A B (rePartH3Zorn (T (ofRealH3Zorn C))) := by
      calc
        h3zornNormTrilin (rePartH3Zorn (T (ofRealH3Zorn C))) A B
          = h3zornNormTrilin A (rePartH3Zorn (T (ofRealH3Zorn C))) B :=
              h3zornCubicJordanDatum.normTrilin_swap₁₂ _ A B
        _ = h3zornNormTrilin A B (rePartH3Zorn (T (ofRealH3Zorn C))) :=
              h3zornCubicJordanDatum.normTrilin_swap₂₃ A _ B
    change h3zornNormTrilin (rePartH3Zorn (T (ofRealH3Zorn A))) B C +
      h3zornNormTrilin A (rePartH3Zorn (T (ofRealH3Zorn B))) C +
      h3zornNormTrilin A B (rePartH3Zorn (T (ofRealH3Zorn C))) = 0
    rw [← hba, ← hca]
    exact h0
  · intro A B C
    have h0 := congrArg Complex.im (hreal A B C)
    rw [Complex.zero_im, Complex.add_im, Complex.add_im] at h0
    rw [hz12 (ofRealH3Zorn A) (T (ofRealH3Zorn B)),
      hz23 (ofRealH3Zorn A) (ofRealH3Zorn B), hz12 (ofRealH3Zorn A) (T (ofRealH3Zorn C))] at h0
    have h1 := (hre_eval B C (T (ofRealH3Zorn A))).2
    have h2 := (hre_eval A C (T (ofRealH3Zorn B))).2
    have h3 := (hre_eval A B (T (ofRealH3Zorn C))).2
    rw [h1, h2, h3] at h0
    have hba : h3zornNormTrilin (imPartH3Zorn (T (ofRealH3Zorn B))) A C =
        h3zornNormTrilin A (imPartH3Zorn (T (ofRealH3Zorn B))) C := by
      exact h3zornCubicJordanDatum.normTrilin_swap₁₂
        (imPartH3Zorn (T (ofRealH3Zorn B))) A C
    have hca : h3zornNormTrilin (imPartH3Zorn (T (ofRealH3Zorn C))) A B =
        h3zornNormTrilin A B (imPartH3Zorn (T (ofRealH3Zorn C))) := by
      calc
        h3zornNormTrilin (imPartH3Zorn (T (ofRealH3Zorn C))) A B
          = h3zornNormTrilin A (imPartH3Zorn (T (ofRealH3Zorn C))) B :=
              h3zornCubicJordanDatum.normTrilin_swap₁₂ _ A B
        _ = h3zornNormTrilin A B (imPartH3Zorn (T (ofRealH3Zorn C))) :=
              h3zornCubicJordanDatum.normTrilin_swap₂₃ A _ B
    change h3zornNormTrilin (imPartH3Zorn (T (ofRealH3Zorn A))) B C +
      h3zornNormTrilin A (imPartH3Zorn (T (ofRealH3Zorn B))) C +
      h3zornNormTrilin A B (imPartH3Zorn (T (ofRealH3Zorn C))) = 0
    rw [← hba, ← hca]
    exact h0

private theorem liftEnd_h3Octonion_F4Derivations
    (D : Module.End ℝ (H3Octonion ℝ)) (hD : D ∈ H3OctonionF4Derivations) :
    liftEnd tensorEquivH3Octonion D ∈ h3OctonionF4Derivationsℂ := by
  intro x y
  rw [← ofReal_rePart_add_I_imPart_H3Octonion x,
    ← ofReal_rePart_add_I_imPart_H3Octonion y]
  have hreal : ∀ a b : H3Octonion ℝ,
      liftEnd tensorEquivH3Octonion D (candidateJordanMulOctℂ (ofRealH3Octonion a) (ofRealH3Octonion b)) =
        candidateJordanMulOctℂ (liftEnd tensorEquivH3Octonion D (ofRealH3Octonion a)) (ofRealH3Octonion b) +
        candidateJordanMulOctℂ (ofRealH3Octonion a) (liftEnd tensorEquivH3Octonion D (ofRealH3Octonion b)) := by
    intro a b
    rw [← ofRealH3Octonion_jordanMul,
      liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul,
      liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul,
      liftEnd_apply_ofReal tensorEquivH3Octonion ofRealH3Octonion tensorEquivH3Octonion_tmul,
      hD a b, map_add, ofRealH3Octonion_jordanMul, ofRealH3Octonion_jordanMul]
  simp only [candidateJordanMulOctℂ_add_left, candidateJordanMulOctℂ_add_right,
    candidateJordanMulOctℂ_smul_left, candidateJordanMulOctℂ_smul_right,
    map_add, map_smul]
  rw [hreal (rePartH3Octonion x) (rePartH3Octonion y),
    hreal (rePartH3Octonion x) (imPartH3Octonion y),
    hreal (imPartH3Octonion x) (rePartH3Octonion y),
    hreal (imPartH3Octonion x) (imPartH3Octonion y)]
  simp only [smul_add]
  abel

private theorem split_h3Octonion_F4Derivations
    (T : Module.End ℂ (H3Octonion ℂ)) (hT : T ∈ h3OctonionF4Derivationsℂ) :
    reEnd ofRealH3Octonion rePartH3Octonion T ∈ H3OctonionF4Derivations ∧
    imEnd ofRealH3Octonion imPartH3Octonion T ∈ H3OctonionF4Derivations := by
  have hmul : ∀ a b : H3Octonion ℝ,
      T (ofRealH3Octonion (a * b)) =
        candidateJordanMulOctℂ (T (ofRealH3Octonion a)) (ofRealH3Octonion b) +
        candidateJordanMulOctℂ (ofRealH3Octonion a) (T (ofRealH3Octonion b)) := by
    intro a b
    rw [ofRealH3Octonion_jordanMul]
    exact hT (ofRealH3Octonion a) (ofRealH3Octonion b)
  have hmul_decomp : ∀ a b : H3Octonion ℝ,
      candidateJordanMulOctℂ (T (ofRealH3Octonion a)) (ofRealH3Octonion b) +
        candidateJordanMulOctℂ (ofRealH3Octonion a) (T (ofRealH3Octonion b)) =
      ofRealH3Octonion (rePartH3Octonion (T (ofRealH3Octonion a)) * b +
        a * rePartH3Octonion (T (ofRealH3Octonion b))) +
      Complex.I • ofRealH3Octonion (imPartH3Octonion (T (ofRealH3Octonion a)) * b +
        a * imPartH3Octonion (T (ofRealH3Octonion b))) := by
    intro a b
    conv_lhs =>
      rw [← ofReal_rePart_add_I_imPart_H3Octonion (T (ofRealH3Octonion a)),
        ← ofReal_rePart_add_I_imPart_H3Octonion (T (ofRealH3Octonion b))]
    simp only [candidateJordanMulOctℂ_add_left, candidateJordanMulOctℂ_add_right,
      candidateJordanMulOctℂ_smul_left, candidateJordanMulOctℂ_smul_right,
      ← ofRealH3Octonion_jordanMul, map_add, smul_add]
    abel
  constructor
  · intro a b
    have h0 := congrArg rePartH3Octonion (hmul a b)
    rw [hmul_decomp, map_add, rePartH3Octonion_ofReal,
      rePartH3Octonion_I_smul, imPartH3Octonion_ofReal, neg_zero, add_zero] at h0
    exact h0
  · intro a b
    have h0 := congrArg imPartH3Octonion (hmul a b)
    rw [hmul_decomp, map_add, imPartH3Octonion_ofReal,
      imPartH3Octonion_I_smul, rePartH3Octonion_ofReal, zero_add] at h0
    exact h0

private theorem liftEnd_h3zorn_F4Derivations
    (D : Module.End ℝ (H3Zorn ℝ)) (hD : D ∈ H3ZornF4Derivations) :
    liftEnd tensorEquivH3Zorn D ∈ h3zornF4Derivationsℂ := by
  intro X Y
  rw [← ofReal_rePart_add_I_imPart_H3Zorn X,
    ← ofReal_rePart_add_I_imPart_H3Zorn Y]
  have hreal : ∀ A B : H3Zorn ℝ,
      liftEnd tensorEquivH3Zorn D (candidateJordanMulZornℂ (ofRealH3Zorn A) (ofRealH3Zorn B)) =
        candidateJordanMulZornℂ (liftEnd tensorEquivH3Zorn D (ofRealH3Zorn A)) (ofRealH3Zorn B) +
        candidateJordanMulZornℂ (ofRealH3Zorn A) (liftEnd tensorEquivH3Zorn D (ofRealH3Zorn B)) := by
    intro A B
    rw [← ofRealH3Zorn_jordanMul,
      liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
      liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
      liftEnd_apply_ofReal tensorEquivH3Zorn ofRealH3Zorn tensorEquivH3Zorn_tmul,
      hD A B, map_add, ofRealH3Zorn_jordanMul, ofRealH3Zorn_jordanMul]
  simp only [candidateJordanMulZornℂ_add_left, candidateJordanMulZornℂ_add_right,
    candidateJordanMulZornℂ_smul_left, candidateJordanMulZornℂ_smul_right,
    map_add, map_smul]
  rw [hreal (rePartH3Zorn X) (rePartH3Zorn Y),
    hreal (rePartH3Zorn X) (imPartH3Zorn Y),
    hreal (imPartH3Zorn X) (rePartH3Zorn Y),
    hreal (imPartH3Zorn X) (imPartH3Zorn Y)]
  simp only [smul_add]
  abel

private theorem split_h3zorn_F4Derivations
    (T : Module.End ℂ (H3Zorn ℂ)) (hT : T ∈ h3zornF4Derivationsℂ) :
    reEnd ofRealH3Zorn rePartH3Zorn T ∈ H3ZornF4Derivations ∧
    imEnd ofRealH3Zorn imPartH3Zorn T ∈ H3ZornF4Derivations := by
  have hmul : ∀ A B : H3Zorn ℝ,
      T (ofRealH3Zorn (A * B)) =
        candidateJordanMulZornℂ (T (ofRealH3Zorn A)) (ofRealH3Zorn B) +
        candidateJordanMulZornℂ (ofRealH3Zorn A) (T (ofRealH3Zorn B)) := by
    intro A B
    rw [ofRealH3Zorn_jordanMul]
    exact hT (ofRealH3Zorn A) (ofRealH3Zorn B)
  have hmul_decomp : ∀ A B : H3Zorn ℝ,
      candidateJordanMulZornℂ (T (ofRealH3Zorn A)) (ofRealH3Zorn B) +
        candidateJordanMulZornℂ (ofRealH3Zorn A) (T (ofRealH3Zorn B)) =
      ofRealH3Zorn (rePartH3Zorn (T (ofRealH3Zorn A)) * B +
        A * rePartH3Zorn (T (ofRealH3Zorn B))) +
      Complex.I • ofRealH3Zorn (imPartH3Zorn (T (ofRealH3Zorn A)) * B +
        A * imPartH3Zorn (T (ofRealH3Zorn B))) := by
    intro A B
    conv_lhs =>
      rw [← ofReal_rePart_add_I_imPart_H3Zorn (T (ofRealH3Zorn A)),
        ← ofReal_rePart_add_I_imPart_H3Zorn (T (ofRealH3Zorn B))]
    simp only [candidateJordanMulZornℂ_add_left, candidateJordanMulZornℂ_add_right,
      candidateJordanMulZornℂ_smul_left, candidateJordanMulZornℂ_smul_right,
      ← ofRealH3Zorn_jordanMul, map_add, smul_add]
    abel
  constructor
  · intro A B
    have h0 := congrArg rePartH3Zorn (hmul A B)
    rw [hmul_decomp, map_add, rePartH3Zorn_ofReal,
      rePartH3Zorn_I_smul, imPartH3Zorn_ofReal, neg_zero, add_zero] at h0
    exact h0
  · intro A B
    have h0 := congrArg imPartH3Zorn (hmul A B)
    rw [hmul_decomp, map_add, imPartH3Zorn_ofReal,
      imPartH3Zorn_I_smul, rePartH3Zorn_ofReal, zero_add] at h0
    exact h0

end MembershipLemmas

/-- `ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ h3OctonionCubicStabilizerℂ`. -/
def h3OctonionCubicStabilizerExtendEquiv :
    ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ h3OctonionCubicStabilizerℂ :=
  mkBaseChangeLieEquiv tensorEquivH3Octonion ofRealH3Octonion rePartH3Octonion imPartH3Octonion
    tensorEquivH3Octonion_tmul rePartH3Octonion_ofReal imPartH3Octonion_ofReal
    ofReal_rePart_add_I_imPart_H3Octonion rePartH3Octonion_I_smul imPartH3Octonion_I_smul
    h3OctonionCubicStabilizer h3OctonionCubicStabilizerℂ
    liftEnd_h3Octonion_trilinearStabilizer split_h3Octonion_trilinearStabilizer

/-- `ℂ ⊗[ℝ] h3zornCubicStabilizer ≃ₗ⁅ℂ⁆ h3zornCubicStabilizerℂ`. -/
def h3zornCubicStabilizerExtendEquiv :
    ℂ ⊗[ℝ] h3zornCubicStabilizer ≃ₗ⁅ℂ⁆ h3zornCubicStabilizerℂ :=
  mkBaseChangeLieEquiv tensorEquivH3Zorn ofRealH3Zorn rePartH3Zorn imPartH3Zorn
    tensorEquivH3Zorn_tmul rePartH3Zorn_ofReal imPartH3Zorn_ofReal
    ofReal_rePart_add_I_imPart_H3Zorn rePartH3Zorn_I_smul imPartH3Zorn_I_smul
    h3zornCubicStabilizer h3zornCubicStabilizerℂ
    liftEnd_h3zorn_trilinearStabilizer split_h3zorn_trilinearStabilizer

/-- `ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ h3OctonionF4Derivationsℂ`. -/
def h3OctonionF4DerivationsExtendEquiv :
    ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ h3OctonionF4Derivationsℂ :=
  mkBaseChangeLieEquiv tensorEquivH3Octonion ofRealH3Octonion rePartH3Octonion imPartH3Octonion
    tensorEquivH3Octonion_tmul rePartH3Octonion_ofReal imPartH3Octonion_ofReal
    ofReal_rePart_add_I_imPart_H3Octonion rePartH3Octonion_I_smul imPartH3Octonion_I_smul
    H3OctonionF4Derivations h3OctonionF4Derivationsℂ
    liftEnd_h3Octonion_F4Derivations split_h3Octonion_F4Derivations

/-- `ℂ ⊗[ℝ] H3ZornF4Derivations ≃ₗ⁅ℂ⁆ h3zornF4Derivationsℂ`. -/
def h3zornF4DerivationsExtendEquiv :
    ℂ ⊗[ℝ] H3ZornF4Derivations ≃ₗ⁅ℂ⁆ h3zornF4Derivationsℂ :=
  mkBaseChangeLieEquiv tensorEquivH3Zorn ofRealH3Zorn rePartH3Zorn imPartH3Zorn
    tensorEquivH3Zorn_tmul rePartH3Zorn_ofReal imPartH3Zorn_ofReal
    ofReal_rePart_add_I_imPart_H3Zorn rePartH3Zorn_I_smul imPartH3Zorn_I_smul
    H3ZornF4Derivations h3zornF4Derivationsℂ
    liftEnd_h3zorn_F4Derivations split_h3zorn_F4Derivations

/-- Conjugation by `h3OctonionComplexEquiv` induces `h3OctonionCubicStabilizerℂ ≃ₗ⁅ℂ⁆ h3zornCubicStabilizerℂ`. -/
def h3OctonionCubicStabilizerℂEquiv :
    h3OctonionCubicStabilizerℂ ≃ₗ⁅ℂ⁆ h3zornCubicStabilizerℂ :=
  LieEquiv.ofSubalgebras h3OctonionCubicStabilizerℂ h3zornCubicStabilizerℂ
    h3OctonionComplexEquiv.lieConj
    (TrilinearStabilizer.map_trilinearStabilizer_lieConj
      h3OctonionNormTrilinℂ h3zornNormTrilinℂ h3OctonionComplexEquiv (1 : ℂˣ)
      (fun x y z => by simp [h3OctonionComplexEquiv_normTrilin]))

/-- Conjugation by `h3OctonionComplexEquiv` induces `h3OctonionF4Derivationsℂ ≃ₗ⁅ℂ⁆ h3zornF4Derivationsℂ`. -/
def h3OctonionF4DerivationsℂEquiv :
    h3OctonionF4Derivationsℂ ≃ₗ⁅ℂ⁆ h3zornF4Derivationsℂ :=
  LieEquiv.ofSubalgebras h3OctonionF4Derivationsℂ h3zornF4Derivationsℂ
    h3OctonionComplexEquiv.lieConj
    (by
      ext D
      rw [LieSubalgebra.mem_map]
      constructor
      · rintro ⟨E, hE, rfl⟩ X Y
        obtain ⟨x, rfl⟩ := h3OctonionComplexEquiv.surjective X
        obtain ⟨y, rfl⟩ := h3OctonionComplexEquiv.surjective Y
        simp only [LieEquiv.coe_toLieHom, LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
          LinearEquiv.symm_apply_apply, ← h3OctonionComplexEquiv_jordanMul, hE x y, map_add]
      · intro hD
        have hsymm : ∀ X Y : H3Zorn ℂ,
            h3OctonionComplexEquiv.symm (candidateJordanMulZornℂ X Y) =
              candidateJordanMulOctℂ (h3OctonionComplexEquiv.symm X)
                (h3OctonionComplexEquiv.symm Y) := by
          intro X Y
          apply h3OctonionComplexEquiv.injective
          simp [h3OctonionComplexEquiv_jordanMul]
        refine ⟨h3OctonionComplexEquiv.symm.lieConj D, ?_, ?_⟩
        · intro x y
          change (h3OctonionComplexEquiv.symm.lieConj D) (candidateJordanMulOctℂ x y) =
            candidateJordanMulOctℂ ((h3OctonionComplexEquiv.symm.lieConj D) x) y +
              candidateJordanMulOctℂ x ((h3OctonionComplexEquiv.symm.lieConj D) y)
          simp only [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
            LinearEquiv.symm_symm]
          rw [h3OctonionComplexEquiv_jordanMul, hD, map_add, hsymm, hsymm,
            LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
        · apply LinearMap.ext; intro X; simp [LinearEquiv.lieConj_apply])

/-- **Main Complexified `E₆` Lie Algebra Isomorphism**:
`ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3zornCubicStabilizer`. -/
def h3OctonionCubicStabilizerBaseChangeEquiv :
    ℂ ⊗[ℝ] h3OctonionCubicStabilizer ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] h3zornCubicStabilizer :=
  h3OctonionCubicStabilizerExtendEquiv.trans
    (h3OctonionCubicStabilizerℂEquiv.trans h3zornCubicStabilizerExtendEquiv.symm)

/-- **Main Complexified `F₄` Lie Algebra Isomorphism**:
`ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] H3ZornF4Derivations`. -/
def h3OctonionF4DerivationsBaseChangeEquiv :
    ℂ ⊗[ℝ] H3OctonionF4Derivations ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] H3ZornF4Derivations :=
  h3OctonionF4DerivationsExtendEquiv.trans
    (h3OctonionF4DerivationsℂEquiv.trans h3zornF4DerivationsExtendEquiv.symm)

end DiamondFreeBaseChange

end ComplexifiedLieSubalgebras

end InfoGeometry.Algebra
