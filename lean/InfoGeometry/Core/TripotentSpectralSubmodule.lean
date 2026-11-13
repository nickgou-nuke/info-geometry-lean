/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.DirectSum.Module

/-!
# Spectral projectors and invariant subspaces of a tripotent adjoint

The existing grouped Peirce projectors are evaluations of the native Lagrange
basis polynomials at the adjoint endomorphism. Consequently every submodule
stable under the adjoint is stable under all five grouped projections and
decomposes as the native internal direct sum of its homogeneous intersections.
No stability under the individual left/right Peirce corners is assumed.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra Polynomial
open scoped DirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The native interpolation polynomial selecting one of the five weights. -/
def fiveGradeLagrangePolynomial (k : FiveGrade) : Polynomial ℝ :=
  Lagrange.basis Finset.univ (fun j : FiveGrade => (fiveGradeValue j : ℝ)) k

theorem fiveGradeLagrangePolynomial_eval_self (k : FiveGrade) :
    (fiveGradeLagrangePolynomial k).eval (fiveGradeValue k : ℝ) = 1 := by
  exact Lagrange.eval_basis_self fiveGradeValue_real_injective.injOn (Finset.mem_univ k)

theorem fiveGradeLagrangePolynomial_eval_of_ne {i j : FiveGrade} (hij : i ≠ j) :
    (fiveGradeLagrangePolynomial i).eval (fiveGradeValue j : ℝ) = 0 := by
  exact Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)

theorem fiveGradeLagrangePolynomial_natDegree (k : FiveGrade) :
    (fiveGradeLagrangePolynomial k).natDegree = 4 := by
  rw [fiveGradeLagrangePolynomial,
    Lagrange.natDegree_basis fiveGradeValue_real_injective.injOn (Finset.mem_univ k)]
  decide

/-- Polynomial evaluation agrees with the existing projector on every grade. -/
theorem aeval_fiveGradeLagrangePolynomial_component {S : A}
    (hS : S * S * S = S) (i j : FiveGrade) (X : A) :
    aeval (LieAlgebra.ad ℝ A S) (fiveGradeLagrangePolynomial i)
        (fiveGradeProjector S j X) =
      fiveGradeProjector S i (fiveGradeProjector S j X) := by
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul
    (f := LieAlgebra.ad ℝ A S) (p := fiveGradeLagrangePolynomial i)
    (mem_fiveGradeRange_implies_adjoint_eigen hS j ⟨X, rfl⟩)]
  by_cases hij : i = j
  · subst j
    rw [fiveGradeLagrangePolynomial_eval_self, one_smul]
    exact (fiveGradeProjector_apply_range_self hS i ⟨_, ⟨X, rfl⟩⟩).symm
  · rw [fiveGradeLagrangePolynomial_eval_of_ne hij, zero_smul]
    exact (fiveGradeProjector_apply_range_eq_zero_of_ne hS hij ⟨_, ⟨X, rfl⟩⟩).symm

/-- Grouped Peirce projection is a degree-four polynomial in the adjoint. -/
theorem fiveGradeProjector_eq_aeval_lagrange {S : A}
    (hS : S * S * S = S) (k : FiveGrade) :
    fiveGradeProjector S k =
      aeval (LieAlgebra.ad ℝ A S) (fiveGradeLagrangePolynomial k) := by
  apply LinearMap.ext
  intro X
  have hrec := fiveGrade_recompose_decompose S X
  change fiveGradeProjector S .negTwo X + fiveGradeProjector S .negOne X +
      fiveGradeProjector S .zero X + fiveGradeProjector S .posOne X +
      fiveGradeProjector S .posTwo X = X at hrec
  rw [← hrec]
  simp only [map_add, aeval_fiveGradeLagrangePolynomial_component hS]

/-- Adjoint invariance implies invariance under each grouped spectral projection. -/
theorem fiveGradeProjector_mem_of_ad_invariant {S : A}
    (hS : S * S * S = S) (p : Submodule ℝ A)
    (hp : ∀ X ∈ p, LieAlgebra.ad ℝ A S X ∈ p)
    (k : FiveGrade) {X : A} (hX : X ∈ p) : fiveGradeProjector S k X ∈ p := by
  rw [fiveGradeProjector_eq_aeval_lagrange hS]
  exact aeval_apply_smul_mem_of_le_comap hX (fiveGradeLagrangePolynomial k)
    (LieAlgebra.ad ℝ A S) hp

/-- An invariant submodule is the sum of its five homogeneous intersections. -/
theorem iSup_inf_fiveGradeRange_eq_of_ad_invariant {S : A}
    (hS : S * S * S = S) (p : Submodule ℝ A)
    (hp : ∀ X ∈ p, LieAlgebra.ad ℝ A S X ∈ p) :
    (⨆ k : FiveGrade, p ⊓ fiveGradeRange S k) = p := by
  apply le_antisymm (iSup_le fun _ => inf_le_left)
  intro X hX
  let q : Submodule ℝ A := ⨆ k : FiveGrade, p ⊓ fiveGradeRange S k
  have hcomponent (k : FiveGrade) : fiveGradeProjector S k X ∈ q :=
    (le_iSup (fun j : FiveGrade => p ⊓ fiveGradeRange S j) k)
      ⟨fiveGradeProjector_mem_of_ad_invariant hS p hp k hX, ⟨X, rfl⟩⟩
  have hrec := fiveGrade_recompose_decompose S X
  change fiveGradeProjector S .negTwo X + fiveGradeProjector S .negOne X +
      fiveGradeProjector S .zero X + fiveGradeProjector S .posOne X +
      fiveGradeProjector S .posTwo X = X at hrec
  rw [← hrec]
  exact q.add_mem (q.add_mem (q.add_mem (q.add_mem (hcomponent .negTwo)
    (hcomponent .negOne)) (hcomponent .zero)) (hcomponent .posOne))
    (hcomponent .posTwo)

/-- Homogeneous pieces inside an invariant submodule are the native eigenspaces
of the restricted adjoint. -/
theorem fiveGradeRange_comap_eq_restrict_eigenspace {S : A}
    (hS : S * S * S = S) (p : Submodule ℝ A)
    (hp : ∀ X ∈ p, LieAlgebra.ad ℝ A S X ∈ p) (k : FiveGrade) :
    (fiveGradeRange S k).comap p.subtype =
      ((LieAlgebra.ad ℝ A S).restrict hp).eigenspace (fiveGradeValue k : ℝ) := by
  rw [fiveGradeRange_eq_eigenspace hS]
  exact ((LieAlgebra.ad ℝ A S).genEigenspace_restrict p 1
    (fiveGradeValue k : ℝ) hp).symm

/-- The invariant submodule has an actual internal direct-sum decomposition. -/
theorem isInternal_fiveGradeRange_comap_of_ad_invariant {S : A}
    (hS : S * S * S = S) (p : Submodule ℝ A)
    (hp : ∀ X ∈ p, LieAlgebra.ad ℝ A S X ∈ p) :
    DirectSum.IsInternal (fun k : FiveGrade => (fiveGradeRange S k).comap p.subtype) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · simpa only [fiveGradeRange_comap_eq_restrict_eigenspace hS p hp,
      Function.comp_def] using
      (((LieAlgebra.ad ℝ A S).restrict hp).eigenspaces_iSupIndep.comp
        fiveGradeValue_real_injective)
  · apply Submodule.map_injective_of_injective (f := p.subtype) Subtype.coe_injective
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype, Submodule.map_top,
      Submodule.range_subtype, iSup_inf_fiveGradeRange_eq_of_ad_invariant hS p hp]

/-- Canonical reconstruction of an invariant submodule from its homogeneous
pieces, as a native linear equivalence. -/
def invariantFiveGradeLinearEquiv {S : A} (hS : S * S * S = S)
    (p : Submodule ℝ A) (hp : ∀ X ∈ p, LieAlgebra.ad ℝ A S X ∈ p) :
    (⨁ k : FiveGrade, (fiveGradeRange S k).comap p.subtype) ≃ₗ[ℝ] p :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _)
    (isInternal_fiveGradeRange_comap_of_ad_invariant hS p hp)

end InfoGeometry.Core.TripotentAdjoint
