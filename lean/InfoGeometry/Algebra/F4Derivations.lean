import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Derivation Algebra from H₃(𝕆_s) Peirce Decomposition

This file defines the Lie subalgebra of Jordan derivations of the
split-octonion Jordan algebra H₃(𝕆_s), using the Peirce decomposition of the
H3Zorn matrix and the S₃ permutation action.  The 52-dimensional real-form
identification of 𝔣₄ is carried by the dedicated classification owner.

The dimension decomposition and an explicit basis are packaged in the
classification lane.

The S₃ action permutes the three Peirce-2 spaces (J₁₂, J₂₃, J₃₁).
-/

namespace InfoGeometry.Algebra

open H3Zorn
open ZornVectorMatrix

noncomputable section

/-- The S₃ group as permutations of the 3 Peirce-2 indices. -/
inductive S3Perm where
  | id
  | s12
  | s23
  | s31
  | s12_s23
  | s23_s12
  deriving DecidableEq, Fintype

def S3Perm.inverse : S3Perm → S3Perm
  | S3Perm.id => S3Perm.id
  | S3Perm.s12 => S3Perm.s12
  | S3Perm.s23 => S3Perm.s23
  | S3Perm.s31 => S3Perm.s31
  | S3Perm.s12_s23 => S3Perm.s23_s12
  | S3Perm.s23_s12 => S3Perm.s12_s23

/-- Composition table for the six Peirce-slot permutations.  `comp σ τ`
means first apply `σ` and then `τ`. -/
def S3Perm.comp : S3Perm → S3Perm → S3Perm
  | S3Perm.id, τ => τ
  | S3Perm.s12, S3Perm.id => S3Perm.s12
  | S3Perm.s12, S3Perm.s12 => S3Perm.id
  | S3Perm.s12, S3Perm.s23 => S3Perm.s23_s12
  | S3Perm.s12, S3Perm.s31 => S3Perm.s12_s23
  | S3Perm.s12, S3Perm.s12_s23 => S3Perm.s31
  | S3Perm.s12, S3Perm.s23_s12 => S3Perm.s23
  | S3Perm.s23, S3Perm.id => S3Perm.s23
  | S3Perm.s23, S3Perm.s12 => S3Perm.s12_s23
  | S3Perm.s23, S3Perm.s23 => S3Perm.id
  | S3Perm.s23, S3Perm.s31 => S3Perm.s23_s12
  | S3Perm.s23, S3Perm.s12_s23 => S3Perm.s12
  | S3Perm.s23, S3Perm.s23_s12 => S3Perm.s31
  | S3Perm.s31, S3Perm.id => S3Perm.s31
  | S3Perm.s31, S3Perm.s12 => S3Perm.s23_s12
  | S3Perm.s31, S3Perm.s23 => S3Perm.s12_s23
  | S3Perm.s31, S3Perm.s31 => S3Perm.id
  | S3Perm.s31, S3Perm.s12_s23 => S3Perm.s23
  | S3Perm.s31, S3Perm.s23_s12 => S3Perm.s12
  | S3Perm.s12_s23, S3Perm.id => S3Perm.s12_s23
  | S3Perm.s12_s23, S3Perm.s12 => S3Perm.s23
  | S3Perm.s12_s23, S3Perm.s23 => S3Perm.s31
  | S3Perm.s12_s23, S3Perm.s31 => S3Perm.s12
  | S3Perm.s12_s23, S3Perm.s12_s23 => S3Perm.s23_s12
  | S3Perm.s12_s23, S3Perm.s23_s12 => S3Perm.id
  | S3Perm.s23_s12, S3Perm.id => S3Perm.s23_s12
  | S3Perm.s23_s12, S3Perm.s12 => S3Perm.s31
  | S3Perm.s23_s12, S3Perm.s23 => S3Perm.s12
  | S3Perm.s23_s12, S3Perm.s31 => S3Perm.s23
  | S3Perm.s23_s12, S3Perm.s12_s23 => S3Perm.id
  | S3Perm.s23_s12, S3Perm.s23_s12 => S3Perm.s12_s23

instance : Group S3Perm where
  mul := S3Perm.comp
  one := S3Perm.id
  inv := S3Perm.inverse
  div := fun σ τ => S3Perm.comp σ (S3Perm.inverse τ)
  mul_assoc := by
    intro σ τ υ
    rcases σ <;> rcases τ <;> rcases υ <;> rfl
  one_mul := by
    intro σ
    cases σ <;> rfl
  mul_one := by
    intro σ
    cases σ <;> rfl
  inv_mul_cancel := by
    intro σ
    cases σ <;> rfl
  div_eq_mul_inv := by
    intro σ τ
    rfl

/-- Peirce-2 space type (each ≃ 𝕆_s). We use the off-diagonal components from H3Zorn ℝ. -/
def Peirce2Space := ZornVectorMatrix ℝ

/-- Action of S₃ on a triple of Peirce-2 spaces. -/
def S3_actOnPeirce2 (σ : S3Perm) :
    (Peirce2Space × Peirce2Space × Peirce2Space) →
    (Peirce2Space × Peirce2Space × Peirce2Space) :=
  match σ with
  | S3Perm.id => fun ⟨X₁₂, X₂₃, X₃₁⟩ => ⟨X₁₂, X₂₃, X₃₁⟩
  | S3Perm.s12 => fun ⟨X₁₂, X₂₃, X₃₁⟩ => ⟨X₂₃, X₁₂, X₃₁⟩
  | S3Perm.s23 => fun ⟨X₁₂, X₂₃, X₃₁⟩ => ⟨X₁₂, X₃₁, X₂₃⟩
  | S3Perm.s31 => fun ⟨X₁₂, X₂₃, X₃₁⟩ => ⟨X₃₁, X₂₃, X₁₂⟩
  | S3Perm.s12_s23 => fun ⟨X₁₂, X₂₃, X₃₁⟩ => ⟨X₃₁, X₁₂, X₂₃⟩
  | S3Perm.s23_s12 => fun ⟨X₁₂, X₂₃, X₃₁⟩ => ⟨X₂₃, X₃₁, X₁₂⟩

/-- The 6 permutations form a group. -/
theorem S3_group_closure (σ τ : S3Perm) :
    ∃ (ρ : S3Perm), S3_actOnPeirce2 ρ = S3_actOnPeirce2 τ ∘ S3_actOnPeirce2 σ := by
  refine ⟨S3Perm.comp σ τ, ?_⟩
  rcases σ <;> rcases τ <;> rfl

/-- Peirce decomposition of an H3Zorn element into diagonal and off-diagonal parts. -/
structure H3ZornPeirce where
  diag₁ : ℝ
  diag₂ : ℝ
  diag₃ : ℝ
  off₁₂ : Peirce2Space  -- a = J₁₂
  off₂₃ : Peirce2Space  -- b = J₂₃
  off₃₁ : Peirce2Space  -- c = J₃₁

@[ext] lemma H3ZornPeirce.ext (P Q : H3ZornPeirce)
    (h₁ : P.diag₁ = Q.diag₁) (h₂ : P.diag₂ = Q.diag₂)
    (h₃ : P.diag₃ = Q.diag₃) (h₁₂ : P.off₁₂ = Q.off₁₂)
    (h₂₃ : P.off₂₃ = Q.off₂₃) (h₃₁ : P.off₃₁ = Q.off₃₁) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Peirce decomposition map for H3Zorn ℝ. -/
def h3zornPeirce (X : H3Zorn ℝ) : H3ZornPeirce :=
  { diag₁ := X.α₁
    diag₂ := X.α₂
    diag₃ := X.α₃
    off₁₂ := X.a
    off₂₃ := X.b
    off₃₁ := X.c }

/-- Reconstruct H3Zorn ℝ from Peirce components. -/
def h3zornFromPeirce (P : H3ZornPeirce) : H3Zorn ℝ :=
  { α₁ := P.diag₁
    α₂ := P.diag₂
    α₃ := P.diag₃
    a := P.off₁₂
    b := P.off₂₃
    c := P.off₃₁ }

@[simp] theorem h3zornFromPeirce_h3zornPeirce (X : H3Zorn ℝ) :
    h3zornFromPeirce (h3zornPeirce X) = X := by
  rfl

@[simp] theorem h3zornPeirce_h3zornFromPeirce (P : H3ZornPeirce) :
    h3zornPeirce (h3zornFromPeirce P) = P := by
  rfl

/-- S₃ action on the Peirce decomposition of H₃(𝕆_s). -/
def S3OnH3ZornPeirce (σ : S3Perm) (P : H3ZornPeirce) : H3ZornPeirce :=
  match σ with
  | S3Perm.id => P
  | S3Perm.s12 =>
    { diag₁ := P.diag₂
      diag₂ := P.diag₁
      diag₃ := P.diag₃
      off₁₂ := ZornVectorMatrix.conj P.off₁₂
      off₂₃ := ZornVectorMatrix.conj P.off₃₁
      off₃₁ := ZornVectorMatrix.conj P.off₂₃ }
  | S3Perm.s23 =>
    { diag₁ := P.diag₁
      diag₂ := P.diag₃
      diag₃ := P.diag₂
      off₁₂ := ZornVectorMatrix.conj P.off₃₁
      off₂₃ := ZornVectorMatrix.conj P.off₂₃
      off₃₁ := ZornVectorMatrix.conj P.off₁₂ }
  | S3Perm.s31 =>
    { diag₁ := P.diag₃
      diag₂ := P.diag₂
      diag₃ := P.diag₁
      off₁₂ := ZornVectorMatrix.conj P.off₂₃
      off₂₃ := ZornVectorMatrix.conj P.off₁₂
      off₃₁ := ZornVectorMatrix.conj P.off₃₁ }
  | S3Perm.s12_s23 =>
    { diag₁ := P.diag₃
      diag₂ := P.diag₁
      diag₃ := P.diag₂
      off₁₂ := P.off₃₁
      off₂₃ := P.off₁₂
      off₃₁ := P.off₂₃ }
  | S3Perm.s23_s12 =>
    { diag₁ := P.diag₂
      diag₂ := P.diag₃
      diag₃ := P.diag₁
      off₁₂ := P.off₂₃
      off₂₃ := P.off₃₁
      off₃₁ := P.off₁₂ }

@[simp] theorem S3OnH3ZornPeirce_s12_involutive (P : H3ZornPeirce) :
    S3OnH3ZornPeirce S3Perm.s12
      (S3OnH3ZornPeirce S3Perm.s12 P) = P := by
  cases P
  simp [S3OnH3ZornPeirce, ZornVectorMatrix.conj_conj]

@[simp] theorem S3OnH3ZornPeirce_s23_involutive (P : H3ZornPeirce) :
    S3OnH3ZornPeirce S3Perm.s23
      (S3OnH3ZornPeirce S3Perm.s23 P) = P := by
  cases P
  simp [S3OnH3ZornPeirce, ZornVectorMatrix.conj_conj]

@[simp] theorem S3OnH3ZornPeirce_s31_involutive (P : H3ZornPeirce) :
    S3OnH3ZornPeirce S3Perm.s31
      (S3OnH3ZornPeirce S3Perm.s31 P) = P := by
  cases P
  simp [S3OnH3ZornPeirce, ZornVectorMatrix.conj_conj]

/-- Action of S₃ on H3Zorn ℝ via Peirce decomposition. -/
def S3OnH3Zorn (σ : S3Perm) (X : H3Zorn ℝ) : H3Zorn ℝ :=
  h3zornFromPeirce (S3OnH3ZornPeirce σ (h3zornPeirce X))

@[simp] theorem S3OnH3Zorn_id (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.id X = X := by
  rfl

@[simp] theorem S3OnH3Zorn_s12_involutive (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s12 (S3OnH3Zorn S3Perm.s12 X) = X := by
  unfold S3OnH3Zorn
  rw [h3zornPeirce_h3zornFromPeirce,
    S3OnH3ZornPeirce_s12_involutive,
    h3zornFromPeirce_h3zornPeirce]

@[simp] theorem S3OnH3Zorn_s23_involutive (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s23 (S3OnH3Zorn S3Perm.s23 X) = X := by
  unfold S3OnH3Zorn
  rw [h3zornPeirce_h3zornFromPeirce,
    S3OnH3ZornPeirce_s23_involutive,
    h3zornFromPeirce_h3zornPeirce]

@[simp] theorem S3OnH3Zorn_s31_involutive (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s31 (S3OnH3Zorn S3Perm.s31 X) = X := by
  unfold S3OnH3Zorn
  rw [h3zornPeirce_h3zornFromPeirce,
    S3OnH3ZornPeirce_s31_involutive,
    h3zornFromPeirce_h3zornPeirce]

/-- S₃ action is additive on H3Zorn ℝ. -/
theorem S3OnH3Zorn_add (σ : S3Perm) (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (X + Y) = S3OnH3Zorn σ X + S3OnH3Zorn σ Y := by
  rcases σ <;> cases X <;> cases Y <;>
    simp [S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce,
      H3Zorn.add_readback, ZornVectorMatrix.conj_add]

/-- S₃ action preserves real scalar multiplication. -/
theorem S3OnH3Zorn_smul (σ : S3Perm) (r : ℝ) (X : H3Zorn ℝ) :
    S3OnH3Zorn σ (r • X) = r • S3OnH3Zorn σ X := by
  rcases σ <;> cases X <;>
    simp [S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce,
      H3Zorn.smul_readback, ZornVectorMatrix.conj_smul]

/-- Linear map implementing the S₃ action. -/
def S3OnH3ZornLinearMap (σ : S3Perm) :
    H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun := S3OnH3Zorn σ
  map_add' := S3OnH3Zorn_add σ
  map_smul' := S3OnH3Zorn_smul σ

@[simp] theorem S3OnH3ZornLinearMap_apply (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornLinearMap σ X = S3OnH3Zorn σ X := rfl

/-- The named composition law for the six concrete permutations. -/
theorem S3OnH3Zorn_comp (σ τ : S3Perm) :
    S3OnH3Zorn (S3Perm.comp σ τ) =
      S3OnH3Zorn τ ∘ S3OnH3Zorn σ := by
  rcases σ <;> rcases τ <;> funext X <;> cases X <;>
    simp [S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_conj]

/-- The S₃ action composes on elements according to the finite multiplication table. -/
@[simp] theorem S3OnH3Zorn_comp_apply (σ τ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn (S3Perm.comp σ τ) X =
      S3OnH3Zorn τ (S3OnH3Zorn σ X) := by
  exact congrFun (S3OnH3Zorn_comp σ τ) X

/-- Inverse action cancels on both sides. -/
theorem S3OnH3Zorn_inverse_apply (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn (S3Perm.inverse σ) (S3OnH3Zorn σ X) = X := by
  rcases σ <;> cases X <;>
    simp [S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_conj]

end

end InfoGeometry.Algebra
