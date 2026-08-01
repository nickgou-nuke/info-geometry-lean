import InfoGeometry.Canonical.H3ZornS3JordanTopologicalReadout
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Bundled topological Jordan automorphisms for the `S₃` action

Mathlib exposes the linear/topological equivalence directly, but does not
provide a universal `JordanAlgEquiv` wrapper.  This small structure records
exactly the additional multiplication law already proved for `H3Zorn ℝ`.
No Jordan-product preservation is inferred from linearity alone.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open CategoryTheory

noncomputable section

structure ContinuousJordanAutomorphism where
  toContinuousLinearEquiv : H3Zorn ℝ ≃L[ℝ] H3Zorn ℝ
  map_mul' : ∀ X Y : H3Zorn ℝ,
    toContinuousLinearEquiv (X * Y) =
      toContinuousLinearEquiv X * toContinuousLinearEquiv Y

instance : CoeFun ContinuousJordanAutomorphism
    (fun _ => H3Zorn ℝ → H3Zorn ℝ) :=
  ⟨fun e => e.toContinuousLinearEquiv⟩

@[simp] theorem ContinuousJordanAutomorphism.apply_eq
    (e : ContinuousJordanAutomorphism) (X : H3Zorn ℝ) :
    e X = e.toContinuousLinearEquiv X := rfl

@[simp] theorem ContinuousJordanAutomorphism.map_mul
    (e : ContinuousJordanAutomorphism) (X Y : H3Zorn ℝ) :
    e (X * Y) = e X * e Y :=
  e.map_mul' X Y

theorem ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
    {e f : ContinuousJordanAutomorphism}
    (h : e.toContinuousLinearEquiv = f.toContinuousLinearEquiv) :
    e = f := by
  cases e
  cases f
  cases h
  rfl

def ContinuousJordanAutomorphism.trans
    (e f : ContinuousJordanAutomorphism) :
    ContinuousJordanAutomorphism where
  toContinuousLinearEquiv :=
    e.toContinuousLinearEquiv.trans f.toContinuousLinearEquiv
  map_mul' X Y := by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.trans_apply]
    rw [e.map_mul', f.map_mul']

def S3OnH3ZornJordanAutomorphism (σ : S3Perm) :
    ContinuousJordanAutomorphism where
  toContinuousLinearEquiv := S3OnH3ZornContinuousLinearEquiv σ
  map_mul' X Y := S3OnH3Zorn_preserve_candidateJordanMul σ X Y

@[simp] theorem S3OnH3ZornJordanAutomorphism_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornJordanAutomorphism σ X = S3OnH3Zorn σ X :=
  rfl

theorem S3OnH3ZornJordanAutomorphism_trans
    (σ τ : S3Perm) :
    (S3OnH3ZornJordanAutomorphism σ).trans
        (S3OnH3ZornJordanAutomorphism τ) =
      S3OnH3ZornJordanAutomorphism (σ * τ) := by
  apply ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
  exact S3OnH3ZornContinuousLinearEquiv_comp_mul σ τ

def S3OnH3ZornJordanTopCat (σ : S3Perm) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  s3OnH3ZornReadoutTopCat σ

@[simp] theorem S3OnH3ZornJordanTopCat_apply
    (σ : S3Perm) (X : H3Zorn ℝ) :
    S3OnH3ZornJordanTopCat σ X = S3OnH3ZornJordanAutomorphism σ X :=
  rfl

theorem S3OnH3ZornJordanTopCat_comp_mul (σ τ : S3Perm) :
    S3OnH3ZornJordanTopCat σ ≫ S3OnH3ZornJordanTopCat τ =
      S3OnH3ZornJordanTopCat (σ * τ) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change S3OnH3Zorn τ (S3OnH3Zorn σ X) =
    S3OnH3Zorn (σ * τ) X
  exact (S3OnH3Zorn_mul_apply σ τ X).symm

end
end InfoGeometry.Canonical
