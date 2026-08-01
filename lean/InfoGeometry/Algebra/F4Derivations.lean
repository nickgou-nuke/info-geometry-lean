import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Candidate Derivation Algebra from H₃(𝕆_s) Peirce Decomposition

This file defines the Lie subalgebra of Jordan derivations of the
split-octonion Jordan algebra H₃(𝕆_s), using the Peirce decomposition of the
H3Zorn matrix and the S₃ permutation action.  The identification of this
subalgebra with the 52-dimensional real form of 𝔣₄ is not asserted here.

The usual 52-dimensional identification is not used as an axiom here.  The
dimension decomposition and an explicit basis remain separate obligations.

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

theorem S3OnH3ZornPeirce_group_closure (σ τ : S3Perm) :
    ∃ (ρ : S3Perm),
      S3OnH3ZornPeirce ρ =
        S3OnH3ZornPeirce τ ∘ S3OnH3ZornPeirce σ := by
  refine ⟨S3Perm.comp σ τ, ?_⟩
  funext P
  rcases σ <;> rcases τ <;> cases P <;>
    apply H3ZornPeirce.ext <;>
      simp [S3Perm.comp, S3OnH3ZornPeirce, Function.comp_def,
        ZornVectorMatrix.conj_conj]

def S3OnH3Zorn (σ : S3Perm) (X : H3Zorn ℝ) : H3Zorn ℝ :=
  h3zornFromPeirce (S3OnH3ZornPeirce σ (h3zornPeirce X))

theorem S3OnH3Zorn_add (σ : S3Perm) (X Y : H3Zorn ℝ) :
    S3OnH3Zorn σ (X + Y) = S3OnH3Zorn σ X + S3OnH3Zorn σ Y := by
  rcases σ with (_ | _ | _ | _ | _ | _)
  <;> cases X
  <;> cases Y
  <;> simp [S3Perm.inverse, HMul.hMul, Mul.mul, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce,
      h3zornFromPeirce, H3Zorn.add_readback, ZornVectorMatrix.conj_add]

theorem S3OnH3Zorn_smul (σ : S3Perm) (r : ℝ) (X : H3Zorn ℝ) :
    S3OnH3Zorn σ (r • X) = r • S3OnH3Zorn σ X := by
  rcases σ with (_ | _ | _ | _ | _ | _)
  <;> cases X
  <;> simp [S3Perm.inverse, HMul.hMul, Mul.mul, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce,
      h3zornFromPeirce, H3Zorn.smul_readback, ZornVectorMatrix.conj_smul]

@[simp] theorem S3OnH3Zorn_one (σ : S3Perm) :
    S3OnH3Zorn σ (1 : H3Zorn ℝ) = 1 := by
  change S3OnH3Zorn σ H3Zorn.one = H3Zorn.one
  rcases σ with (_ | _ | _ | _ | _ | _)
  <;> simp [S3Perm.inverse, HMul.hMul, Mul.mul, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce,
      h3zornFromPeirce, H3Zorn.one, ZornVectorMatrix.conj,
      ZornVectorMatrix.zero]

theorem S3OnH3Zorn_linearTrace (σ : S3Perm) (X : H3Zorn ℝ) :
    H3Zorn.linearTrace (S3OnH3Zorn σ X) = H3Zorn.linearTrace X := by
  rcases σ with (_ | _ | _ | _ | _ | _)
  <;> cases X
  <;> simp [S3Perm.inverse, HMul.hMul, Mul.mul, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce,
      h3zornFromPeirce, H3Zorn.linearTrace]
  <;> ring

def S3OnH3ZornLinearMap (σ : S3Perm) :
    H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun := S3OnH3Zorn σ
  map_add' := S3OnH3Zorn_add σ
  map_smul' := S3OnH3Zorn_smul σ

@[simp] theorem S3OnH3ZornLinearMap_apply (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornLinearMap σ X = S3OnH3Zorn σ X := rfl

theorem S3OnH3Zorn_group_closure (σ τ : S3Perm) :
    ∃ (ρ : S3Perm),
      S3OnH3Zorn ρ = S3OnH3Zorn τ ∘ S3OnH3Zorn σ := by
  rcases S3OnH3ZornPeirce_group_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  funext X
  unfold S3OnH3Zorn
  rw [hρ]
  simp [Function.comp_apply]

/-- The named composition law for the six concrete permutations. -/
theorem S3OnH3Zorn_comp (σ τ : S3Perm) :
    S3OnH3Zorn (S3Perm.comp σ τ) =
      S3OnH3Zorn τ ∘ S3OnH3Zorn σ := by
  funext X
  rcases σ <;> rcases τ <;> cases X <;>
    dsimp [S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornPeirce, h3zornFromPeirce]
  all_goals
    apply H3Zorn.ext_h3 <;>
      simp [Function.comp_def, ZornVectorMatrix.conj,
        ZornVectorMatrix.add, ZornVectorMatrix.neg, neg_neg] <;>
      ring

theorem S3OnH3ZornLinearMap_comp_closure (σ τ : S3Perm) :
    ∃ (ρ : S3Perm),
      S3OnH3ZornLinearMap ρ =
        (S3OnH3ZornLinearMap τ).comp (S3OnH3ZornLinearMap σ) := by
  rcases S3OnH3Zorn_group_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  apply LinearMap.ext
  intro X
  change S3OnH3Zorn ρ X =
    S3OnH3Zorn τ (S3OnH3Zorn σ X)
  rw [hρ]
  rfl

@[simp] theorem S3OnH3Zorn_inverse_left (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn (S3Perm.inverse σ) (S3OnH3Zorn σ X) = X := by
  rcases σ with (_ | _ | _ | _ | _ | _)
  <;> cases X
  <;> simp [Inv.inv, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce, h3zornFromPeirce, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul]

@[simp] theorem S3OnH3Zorn_inverse_right (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3Zorn σ (S3OnH3Zorn (S3Perm.inverse σ) X) = X := by
  rcases σ with (_ | _ | _ | _ | _ | _)
  <;> cases X
  <;> simp [Inv.inv, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce, h3zornFromPeirce, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul]

def S3OnH3ZornLinearEquiv (σ : S3Perm) :
    H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ where
  toFun := S3OnH3Zorn σ
  invFun := S3OnH3Zorn (S3Perm.inverse σ)
  left_inv := S3OnH3Zorn_inverse_left σ
  right_inv := S3OnH3Zorn_inverse_right σ
  map_add' := S3OnH3Zorn_add σ
  map_smul' := S3OnH3Zorn_smul σ

theorem S3OnH3ZornLinearEquiv_comp_closure (σ τ : S3Perm) :
    ∃ (ρ : S3Perm),
      S3OnH3ZornLinearEquiv ρ =
        (S3OnH3ZornLinearEquiv σ).trans (S3OnH3ZornLinearEquiv τ) := by
  rcases S3OnH3Zorn_group_closure σ τ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  apply LinearEquiv.ext
  intro X
  change S3OnH3Zorn ρ X =
    S3OnH3Zorn τ (S3OnH3Zorn σ X)
  rw [hρ]
  rfl

theorem S3OnH3ZornLinearEquiv_comp (σ τ : S3Perm) :
    S3OnH3ZornLinearEquiv (S3Perm.comp σ τ) =
      (S3OnH3ZornLinearEquiv σ).trans (S3OnH3ZornLinearEquiv τ) := by
  apply LinearEquiv.ext
  intro X
  change S3OnH3Zorn (S3Perm.comp σ τ) X =
    S3OnH3Zorn τ (S3OnH3Zorn σ X)
  exact congrFun (S3OnH3Zorn_comp σ τ) X

@[simp] theorem S3OnH3Zorn_s12_involutive (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s12 (S3OnH3Zorn S3Perm.s12 X) = X := by
  unfold S3OnH3Zorn
  simp [Inv.inv, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce, h3zornFromPeirce, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul]

@[simp] theorem S3OnH3Zorn_s23_involutive (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s23 (S3OnH3Zorn S3Perm.s23 X) = X := by
  unfold S3OnH3Zorn
  simp [Inv.inv, S3Perm.inverse, S3Perm.comp, S3OnH3Zorn, S3OnH3ZornPeirce, h3zornPeirce, h3zornFromPeirce, ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul]

@[simp] theorem S3OnH3Zorn_s31_involutive (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s31 (S3OnH3Zorn S3Perm.s31 X) = X := by
  unfold S3OnH3Zorn
  simp [S3OnH3ZornPeirce, h3zornPeirce, h3zornFromPeirce, ZornVectorMatrix.conj_conj]

/-- The Lie subalgebra of Jordan derivations of H₃(𝕆_s). -/
def H3ZornDerivationLieSubalgebra : LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  H3ZornF4Derivations

theorem H3ZornDerivationLieSubalgebra_commutator_mem
    (D E : Module.End ℝ (H3Zorn ℝ))
    (hD : D ∈ H3ZornDerivationLieSubalgebra)
    (hE : E ∈ H3ZornDerivationLieSubalgebra) :
    ⁅D, E⁆ ∈ H3ZornDerivationLieSubalgebra := by
  exact H3ZornDerivationLieSubalgebra.lie_mem hD hE

/-- Dimension count for the F₄ decomposition. -/
theorem F4_dimension_decomposition :
    14 + 16 + 22 = 52 := by norm_num

/-- The three Peirce-2 spaces in H₃(𝕆_s) (J₁₂, J₂₃, J₃₁), each isomorphic to 𝕆_s. -/
def Peirce2Spaces := Peirce2Space × Peirce2Space × Peirce2Space

/-- S₃ acts on the three Peirce-2 spaces by permutation. -/
def S3ActsOnPeirce2 (σ : S3Perm) (P : Peirce2Spaces) : Peirce2Spaces :=
  S3_actOnPeirce2 σ P

end
