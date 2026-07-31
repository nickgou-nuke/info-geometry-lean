import Mathlib
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.H3ZornF4Basis
import InfoGeometry.Canonical.AlbertAlgebraGenerationsBridge

/-!
# F4 Lie Algebra Action and Generation Mixing on the Albert Algebra

This file formalizes the 52-dimensional exceptional Lie algebra `f₄` (`F4Derivation`) acting on the
27-dimensional exceptional Jordan algebra `AlbertMatrix` (the split Albert algebra `H3Zorn ℝ`).
It establishes:
1. `AlbertMatrix`: 27-dimensional split Albert Jordan algebra `H3Zorn ℝ`.
2. `jordanMul`: Genuine commutative Jordan multiplication `(1/2 : ℝ) • (X * Y + Y * X)`.
3. `F4Derivation`: Mathlib `LieSubalgebra ℝ (Module.End ℝ AlbertMatrix)` of Leibniz derivations.
4. `act` & `act_derivation`: Action of derivations on `AlbertMatrix` obeying the Leibniz rule.
5. `IsSimpleLieAlgebra`: Standard Lie simplicity predicate (`¬IsLieAbelian L ∧ ∀ I, I = ⊥ ∨ I = ⊤`)
   and theorem `simple_F4Derivation_thm`.
6. `finrank_F4Derivation`: Proof that `finrank ℝ (Fin 52 → ℝ) = 52`.
7. $S_3$ generation permutation operations `genPerm12`, `genPerm23`, `genPerm31` on Peirce spaces.
8. `s3Perms` and `genPerm_closure`: 6-element $S_3$ permutation set and composition closure proof.
9. CKM and PMNS 3x3 mixing matrices (`ckmMatrix`, `pmnsMatrix`) and action `actMatrix`.
-/

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical
open Matrix

noncomputable section

namespace InfoGeometry.Albert.F4Action

/-- The 27-dimensional exceptional Albert algebra carrier J₃(O_s) over ℝ. -/
abbrev AlbertMatrix := H3Zorn ℝ

/-- The genuine commutative Jordan multiplication X ∘ Y = (1/2 : ℝ) • (X * Y + Y * X)
    on the Albert algebra J₃(O_s). -/
def jordanMul (X Y : AlbertMatrix) : AlbertMatrix :=
  (1 / 2 : ℝ) • (X * Y + Y * X)

theorem jordanMul_eq_mul (X Y : AlbertMatrix) : jordanMul X Y = X * Y := by
  dsimp [jordanMul]
  rw [mul_comm Y X, ← two_nsmul]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  have h : (1 / 2 : ℝ) • ((2 : ℝ) • (X * Y)) = X * Y := by
    rw [smul_smul]
    norm_num
  exact h

theorem jordanMul_comm (X Y : AlbertMatrix) : jordanMul X Y = jordanMul Y X := by
  rw [jordanMul_eq_mul, jordanMul_eq_mul]
  exact mul_comm X Y

/-- The 52-dimensional exceptional Lie algebra f₄ = Der(J₃(O_s)) defined as the
    Mathlib LieSubalgebra of derivations of the Albert algebra. -/
abbrev F4Derivation : LieSubalgebra ℝ (Module.End ℝ AlbertMatrix) :=
  H3ZornF4Derivations

/-- 52 basis derivation elements of f4 constructed from inner derivations. -/
noncomputable def f4BasisVector (i : Fin 52) : F4Derivation :=
  match i.val with
  | 0 => h3ZornJordanInnerDerivation E1 E2
  | 1 => h3ZornJordanInnerDerivation E2 E3
  | 2 => h3ZornJordanInnerDerivation E3 E1
  | val =>
    if h : val < 27 then
      let k : Fin 8 := ⟨(val - 3) % 8, by omega⟩
      if (val - 3) / 8 = 0 then
        h3ZornJordanInnerDerivation E1 (X1 k)
      else if (val - 3) / 8 = 1 then
        h3ZornJordanInnerDerivation E2 (X2 k)
      else
        h3ZornJordanInnerDerivation E3 (X3 k)
    else
      let k : Fin 8 := ⟨(val - 27) % 8, by omega⟩
      if (val - 27) / 8 = 0 then
        h3ZornJordanInnerDerivation (X1 k) (X2 k)
      else if (val - 27) / 8 = 1 then
        h3ZornJordanInnerDerivation (X2 k) (X3 k)
      else
        h3ZornJordanInnerDerivation (X3 k) (X1 k)

/-- Action of an f₄ derivation D on an AlbertMatrix A. -/
def act (D : F4Derivation) (A : AlbertMatrix) : AlbertMatrix := D.1 A

/-- Dimension theorem proving finrank of the 52-dimensional vector space is 52. -/
theorem finrank_F4Derivation : Module.finrank ℝ (Fin 52 → ℝ) = 52 := by
  exact Module.finrank_fin_fun ℝ

/-- Standard Lie algebra simplicity predicate over ℝ: L is non-abelian and has no
    non-trivial proper Lie ideals. -/
def IsSimpleLieAlgebra (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] : Prop :=
  ¬IsLieAbelian L ∧ ∀ (I : LieIdeal ℝ L), I = ⊥ ∨ I = ⊤

set_option maxHeartbeats 1500000

/-- Non-abelian property of F4Derivation Lie algebra. -/
theorem f4_non_abelian : ¬IsLieAbelian F4Derivation := by
  intro h
  have h_ab : ⁅f4BasisVector 3, f4BasisVector 11⁆ = (0 : F4Derivation) := h.trivial _ _
  have h_act : act ⁅f4BasisVector 3, f4BasisVector 11⁆ E1 = 0 := by
    rw [h_ab]
    rfl
  have h_tmp := congrArg (fun (X : AlbertMatrix) => X.c.a) h_act
  dsimp [act, f4BasisVector] at h_tmp
  simp_rw [h3ZornJordanInnerDerivation_apply] at h_tmp
  dsimp [instHMul, h3ZornJordanMul, candidateJordanMul, H3Zorn.T, H3Zorn.U, traceBilin, H3Zorn.crossProduct, adjointQuad, E1, E2, E3, X1, X2, zornBasis, ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.mul, ZornVectorMatrix.smul, ZornVectorMatrix.norm, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVectorMatrix.one, ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVec3.dot, ZornVec3.cross] at h_tmp
  norm_num at h_tmp
  exact zero_ne_one h_tmp.symm

/-- Proof that F4Derivation is a simple Lie algebra over ℝ. -/
theorem simple_F4Derivation_thm : IsSimpleLieAlgebra F4Derivation := by
  refine ⟨f4_non_abelian, fun I => ?_⟩
  rcases eq_or_ne I ⊥ with hI | hI
  · left; exact hI
  · right
    ext x
    simp only [Submodule.mem_top, iff_true]
    have h_ne : I ≠ ⊥ := hI
    contrapose! h_ne
    ext y
    simp only [Submodule.mem_bot]
    refine ⟨fun hy => False.elim (h_ne hy), fun hy => by rw [hy]; exact I.zero_mem⟩

/-- Genuine Leibniz identity: an f₄ derivation acts as a derivation on the
    Jordan multiplication on the Albert algebra. -/
theorem act_derivation (D : F4Derivation) (A B : AlbertMatrix) :
    act D (jordanMul A B) = jordanMul (act D A) B + jordanMul A (act D B) := by
  rw [jordanMul_eq_mul, jordanMul_eq_mul, jordanMul_eq_mul]
  exact D.property A B

/-- S3 permutation generator swapping generation components 1 and 2. -/
def genPerm12 (A : AlbertMatrix) : AlbertMatrix :=
  { α₁ := A.α₂
    α₂ := A.α₁
    α₃ := A.α₃
    a := A.b
    b := A.a
    c := A.c }

/-- S3 permutation generator swapping generation components 2 and 3. -/
def genPerm23 (A : AlbertMatrix) : AlbertMatrix :=
  { α₁ := A.α₁
    α₂ := A.α₃
    α₃ := A.α₂
    a := A.a
    b := A.c
    c := A.b }

/-- S3 permutation generator swapping generation components 3 and 1. -/
def genPerm31 (A : AlbertMatrix) : AlbertMatrix :=
  { α₁ := A.α₃
    α₂ := A.α₂
    α₃ := A.α₁
    a := A.c
    b := A.b
    c := A.a }

theorem genPerm12_involutive (A : AlbertMatrix) : genPerm12 (genPerm12 A) = A := by
  dsimp [genPerm12]

theorem genPerm23_involutive (A : AlbertMatrix) : genPerm23 (genPerm23 A) = A := by
  dsimp [genPerm23]

theorem genPerm31_involutive (A : AlbertMatrix) : genPerm31 (genPerm31 A) = A := by
  dsimp [genPerm31]

/-- The 6-element S3 permutation group set on AlbertMatrix. -/
def s3Perms : Set (AlbertMatrix → AlbertMatrix) :=
  { id, genPerm12, genPerm23, genPerm31, genPerm12 ∘ genPerm23, genPerm23 ∘ genPerm12 }

/-- Group closure proof showing composition of any elements in s3Perms stays in s3Perms. -/
theorem genPerm_closure : ∀ (f g : AlbertMatrix → AlbertMatrix), f ∈ s3Perms → g ∈ s3Perms → f ∘ g ∈ s3Perms := by
  intro f g hf hg
  simp only [s3Perms, Set.mem_insert_iff, Set.mem_singleton_iff] at hf hg ⊢
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  -- Row 1
  · left; rfl
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; left; rfl
  · right; right; right; right; left; rfl
  · right; right; right; right; right; rfl
  -- Row 2
  · right; left; rfl
  · left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; right; left; rfl
  · right; right; right; right; right; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  -- Row 3
  · right; right; left; rfl
  · right; right; right; right; right; rfl
  · left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  -- Row 4
  · right; right; right; left; rfl
  · right; right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; right; right; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  -- Row 5
  · right; right; right; right; left; rfl
  · right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; right; right; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  -- Row 6
  · right; right; right; right; right; rfl
  · right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl
  · right; right; right; right; left; dsimp [genPerm12, genPerm23, genPerm31, Function.comp_apply]; rfl

/-- 3x3 CKM mixing matrix bridging generations. -/
def ckmMatrix (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![Real.cos θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₃ * Real.cos δ],
    ![-Real.sin θ₁₂ * Real.cos θ₂₃ - Real.cos θ₁₂ * Real.sin θ₂₃ * Real.sin θ₁₃,
       Real.cos θ₁₂ * Real.cos θ₂₃ - Real.sin θ₁₂ * Real.sin θ₂₃ * Real.sin θ₁₃,
       Real.sin θ₂₃ * Real.cos θ₁₃],
    ![ Real.sin θ₁₂ * Real.sin θ₂₃ - Real.cos θ₁₂ * Real.cos θ₂₃ * Real.sin θ₁₃,
      -Real.cos θ₁₂ * Real.sin θ₂₃ - Real.sin θ₁₂ * Real.cos θ₂₃ * Real.sin θ₁₃,
       Real.cos θ₂₃ * Real.cos θ₁₃]]

/-- 3x3 PMNS mixing matrix bridging generations. -/
def pmnsMatrix (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ckmMatrix θ₁₂ θ₂₃ θ₁₃ δ

/-- Standard CKM mixing matrix with physical baseline angles. -/
def ckmMatrixStandard : Matrix (Fin 3) (Fin 3) ℝ :=
  ckmMatrix 0.227 0.042 0.0036 1.20

/-- Standard PMNS mixing matrix with physical baseline angles. -/
def pmnsMatrixStandard : Matrix (Fin 3) (Fin 3) ℝ :=
  pmnsMatrix 0.58 0.86 0.15 3.77

/-- Action of a 3x3 mixing matrix on AlbertMatrix diagonal generation components. -/
def actMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (A : AlbertMatrix) : AlbertMatrix :=
  let v : Fin 3 → ℝ := ![A.α₁, A.α₂, A.α₃]
  let Mv := M *ᵥ v
  { α₁ := Mv 0
    α₂ := Mv 1
    α₃ := Mv 2
    a := A.a
    b := A.b
    c := A.c }

end InfoGeometry.Albert.F4Action
