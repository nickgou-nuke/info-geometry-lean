/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange

/-!
# Tripotent grades inside invariant subspaces

The existing grouped Peirce projectors are polynomials in the native adjoint
endomorphism. Consequently every real submodule invariant under that adjoint
is the internal direct sum of its five intersections with the existing grade
ranges. Individual left/right Peirce blocks need not preserve the submodule.

All results concern an arbitrary associative real algebra. The Lie-subalgebra
results use the native commutator and require only the stated adjoint stability;
they do not identify a particular KKT algebra or supply a star involution.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra
open scoped DirectSum Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Each owned five-grade projector is the Lagrange polynomial of the native
adjoint operator at its five distinct possible weights. -/
theorem fiveGradeProjector_eq_aeval_lagrange {S : A} (hS : S * S * S = S)
    (k : FiveGrade) :
    fiveGradeProjector S k =
      Polynomial.aeval (LieAlgebra.ad ℝ A S)
        (Lagrange.basis Finset.univ (fun j : FiveGrade => (fiveGradeValue j : ℝ)) k) := by
  let p : ℝ[X] :=
    Lagrange.basis Finset.univ (fun j : FiveGrade => (fiveGradeValue j : ℝ)) k
  have hnodes : Set.InjOn (fun j : FiveGrade => (fiveGradeValue j : ℝ))
      (Finset.univ : Finset FiveGrade) :=
    fiveGradeValue_real_injective.injOn
  have hcomponent (j : FiveGrade) (x : A) :
      Polynomial.aeval (LieAlgebra.ad ℝ A S) p (fiveGradeProjector S j x) =
        fiveGradeProjector S k (fiveGradeProjector S j x) := by
    have heigen : LieAlgebra.ad ℝ A S (fiveGradeProjector S j x) =
        (fiveGradeValue j : ℝ) • fiveGradeProjector S j x :=
      mem_fiveGradeRange_implies_adjoint_eigen hS j ⟨x, rfl⟩
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul heigen]
    by_cases hkj : k = j
    · subst j
      change (Lagrange.basis Finset.univ
        (fun j : FiveGrade => (fiveGradeValue j : ℝ)) k).eval
          (fiveGradeValue k : ℝ) • fiveGradeProjector S k x = _
      rw [Lagrange.eval_basis_self hnodes (Finset.mem_univ k), one_smul]
      exact (fiveGradeProjector_apply_range_self hS k
        ⟨fiveGradeProjector S k x, ⟨x, rfl⟩⟩).symm
    · change (Lagrange.basis Finset.univ
        (fun j : FiveGrade => (fiveGradeValue j : ℝ)) k).eval
          (fiveGradeValue j : ℝ) • fiveGradeProjector S j x = _
      rw [Lagrange.eval_basis_of_ne hkj (Finset.mem_univ j), zero_smul]
      exact (fiveGradeProjector_apply_range_eq_zero_of_ne hS hkj
        ⟨fiveGradeProjector S j x, ⟨x, rfl⟩⟩).symm
  apply LinearMap.ext
  intro x
  have hrec := fiveGrade_recompose_decompose S x
  change fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
    fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
    fiveGradeProjector S .posTwo x = x at hrec
  change fiveGradeProjector S k x = Polynomial.aeval (LieAlgebra.ad ℝ A S) p x
  calc
    fiveGradeProjector S k x = fiveGradeProjector S k
        (fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
          fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
          fiveGradeProjector S .posTwo x) := congrArg (fiveGradeProjector S k) hrec.symm
    _ = Polynomial.aeval (LieAlgebra.ad ℝ A S) p
        (fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
          fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
          fiveGradeProjector S .posTwo x) := by
      simp only [map_add, hcomponent]
    _ = Polynomial.aeval (LieAlgebra.ad ℝ A S) p x :=
      congrArg (Polynomial.aeval (LieAlgebra.ad ℝ A S) p) hrec

/-- Adjoint invariance suffices for every grouped grade projector to preserve
a submodule. No closure under individual associative corners is assumed. -/
theorem fiveGradeProjector_preserves_adInvariant {S : A} (hS : S * S * S = S)
    (q : Submodule ℝ A) (hq : q ≤ q.comap (LieAlgebra.ad ℝ A S)) (k : FiveGrade) :
    q ≤ q.comap (fiveGradeProjector S k) := by
  intro x hx
  change fiveGradeProjector S k x ∈ q
  rw [fiveGradeProjector_eq_aeval_lagrange hS k]
  exact Polynomial.aeval_apply_smul_mem_of_le_comap hx _ _ hq

/-- The grade intersection inside an invariant submodule is precisely the
native eigenspace of the restricted adjoint endomorphism. -/
theorem fiveGradeRange_comap_eq_restrict_eigenspace {S : A}
    (hS : S * S * S = S) (q : Submodule ℝ A)
    (hq : q ≤ q.comap (LieAlgebra.ad ℝ A S)) (k : FiveGrade) :
    (fiveGradeRange S k).comap q.subtype =
      ((LieAlgebra.ad ℝ A S).restrict (fun x hx => hq hx)).eigenspace
        (fiveGradeValue k : ℝ) := by
  rw [fiveGradeRange_eq_eigenspace hS]
  exact ((LieAlgebra.ad ℝ A S).genEigenspace_restrict q 1
    (fiveGradeValue k : ℝ) (fun x hx => hq hx)).symm

/-- Every adjoint-invariant submodule is the actual internal direct sum of
its five grade intersections. No finite-dimensional hypothesis is used. -/
theorem fiveGradeRange_comap_isInternal {S : A} (hS : S * S * S = S)
    (q : Submodule ℝ A) (hq : q ≤ q.comap (LieAlgebra.ad ℝ A S)) :
    DirectSum.IsInternal
      (fun k : FiveGrade => (fiveGradeRange S k).comap q.subtype) := by
  let Dq : Module.End ℝ q :=
    (LieAlgebra.ad ℝ A S).restrict (fun x hx => hq hx)
  have hgrades :
      (fun k : FiveGrade => (fiveGradeRange S k).comap q.subtype) =
        (fun k : FiveGrade => Dq.eigenspace (fiveGradeValue k : ℝ)) := by
    funext k
    exact fiveGradeRange_comap_eq_restrict_eigenspace hS q hq k
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [hgrades]
    exact Dq.eigenspaces_iSupIndep.comp fiveGradeValue_real_injective
  · apply top_unique
    intro x hx
    let component (k : FiveGrade) : q :=
      ⟨fiveGradeProjector S k (x : A),
        fiveGradeProjector_preserves_adInvariant hS q hq k x.property⟩
    have hmem (k : FiveGrade) :
        component k ∈ (fiveGradeRange S k).comap q.subtype := by
      change fiveGradeProjector S k (x : A) ∈ fiveGradeRange S k
      exact ⟨(x : A), rfl⟩
    have hinto (k : FiveGrade) : component k ∈
        ⨆ j : FiveGrade, (fiveGradeRange S j).comap q.subtype :=
      Submodule.mem_iSup_of_mem k (hmem k)
    have hrec : component .negTwo + component .negOne + component .zero +
        component .posOne + component .posTwo = x := by
      apply Subtype.ext
      exact fiveGrade_recompose_decompose S (x : A)
    rw [← hrec]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _ (hinto .negTwo) (hinto .negOne)) (hinto .zero))
        (hinto .posOne)) (hinto .posTwo)

/-- Viewed in the ambient algebra, the same decomposition spans exactly the
original invariant submodule. -/
theorem iSup_inf_fiveGradeRange_eq_of_adInvariant {S : A} (hS : S * S * S = S)
    (q : Submodule ℝ A) (hq : q ≤ q.comap (LieAlgebra.ad ℝ A S)) :
    (⨆ k : FiveGrade, q ⊓ fiveGradeRange S k) = q := by
  have hsum := (fiveGradeRange_comap_isInternal hS q hq).submodule_iSup_eq_top
  have hmap := congrArg (Submodule.map q.subtype) hsum
  simpa only [Submodule.map_iSup, Submodule.map_comap_eq,
    Submodule.range_subtype, Submodule.map_top] using hmap

/-- An adjoint-stable native Lie subalgebra inherits both the internal
decomposition and homogeneous bracket closure. Stability is the sole
additional assumption; membership of `S` in the subalgebra is not required. -/
theorem adInvariant_lieSubalgebra_fiveGrade_decomposition {S : A}
    (hS : S * S * S = S) (L : LieSubalgebra ℝ A)
    (hL : L.toSubmodule ≤ L.toSubmodule.comap (LieAlgebra.ad ℝ A S)) :
    DirectSum.IsInternal
        (fun k : FiveGrade => (fiveGradeRange S k).comap L.toSubmodule.subtype) ∧
      ∀ (i j k : FiveGrade),
        fiveGradeValue i + fiveGradeValue j = fiveGradeValue k →
        ∀ (x y : A), x ∈ L.toSubmodule ⊓ fiveGradeRange S i →
          y ∈ L.toSubmodule ⊓ fiveGradeRange S j →
          ⁅x, y⁆ ∈ L.toSubmodule ⊓ fiveGradeRange S k := by
  refine ⟨fiveGradeRange_comap_isInternal hS L.toSubmodule hL, ?_⟩
  intro i j k hijk x y hx hy
  exact ⟨L.lie_mem hx.1 hy.1, lie_mem_fiveGradeRange hS hijk hx.2 hy.2⟩

end InfoGeometry.Core.TripotentAdjoint
