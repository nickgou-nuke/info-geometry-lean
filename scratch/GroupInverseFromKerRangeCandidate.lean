/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.QuantumContext.MarkovDrazinSemisimplicity

/-!
# Group inverse from a kernel/range complement

Finite-dimensional endomorphism lemma candidate.  If the kernel and range of
an endomorphism are complementary, its restriction to the range is an
automorphism; extending that inverse by zero on the kernel gives a group
inverse.  This is deliberately a scratch proof candidate pending a sequential
kernel check.
-/

noncomputable section

namespace InfoGeometry.Canonical.GroupInverseFromKerRangeCandidate

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A complement of `ker A` and `range A` yields a genuine group inverse. -/
theorem exists_groupInverse_of_isCompl_ker_range (A : Module.End ℝ V)
    (hcomp : IsCompl A.ker A.range) :
    ∃ D : Module.End ℝ V, IsGroupInverse A D := by
  let Ran : Submodule ℝ V := A.range
  have hcompl : IsCompl A.ker Ran := hcomp
  let πRan : V →ₗ[ℝ] Ran := Ran.projectionOnto A.ker hcompl.symm
  have hA_map_Ran : ∀ x : Ran, A x.1 ∈ Ran := by
    intro x
    exact ⟨x.1, rfl⟩
  let AR : Ran →ₗ[ℝ] Ran :=
    LinearMap.codRestrict Ran (A ∘ₗ Ran.subtype) hA_map_Ran
  have hAR_inj : Function.Injective AR := by
    intro x y hxy
    apply Subtype.ext
    have hAxy : A (x.1 - y.1) = 0 := by
      have hval' := congrArg Subtype.val hxy
      change A x.1 = A y.1 at hval'
      have hval : A x.1 = A y.1 := hval'
      rw [map_sub, hval, sub_self]
    have hxker : (x.1 - y.1) ∈ A.ker := by
      simpa [LinearMap.mem_ker] using hAxy
    have hxrange : (x.1 - y.1) ∈ Ran := by
      exact (Ran.sub_mem x.2 y.2)
    have hzero : (x.1 - y.1) ∈ (⊥ : Submodule ℝ V) := by
      have hint : (x.1 - y.1) ∈ A.ker ⊓ Ran := ⟨hxker, hxrange⟩
      simpa [hcompl.inf_eq_bot] using hint
    have hxyval : x.1 = y.1 := sub_eq_zero.mp (by simpa using hzero)
    exact hxyval
  let eRan : Ran ≃ₗ[ℝ] Ran := LinearEquiv.ofInjectiveEndo AR hAR_inj
  let D : Module.End ℝ V := Ran.subtype ∘ₗ (eRan.symm : Ran →ₗ[ℝ] Ran) ∘ₗ πRan
  let P : Module.End ℝ V := Ran.subtype ∘ₗ πRan
  have hAD : A * D = P := by
    ext x
    have hright : AR (eRan.symm (πRan x)) = πRan x := by
      change eRan (eRan.symm (πRan x)) = πRan x
      exact eRan.apply_symm_apply (πRan x)
    change A ((eRan.symm (πRan x) : Ran) : V) = P x
    change ((AR (eRan.symm (πRan x)) : Ran) : V) = P x
    rw [hright]
    rfl
  have hDA : D * A = P := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hcompl x with
      ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 :=
      Submodule.projectionOnto_apply_right hcompl.symm xK
    have hπR : πRan xR = xR :=
      Submodule.projectionOnto_apply_left hcompl.symm xR
    have hAK : A (xK : V) = 0 := xK.2
    have hπAK : πRan (A (xK : V)) = 0 := by simp [hAK]
    have hARxR : A (xR : V) ∈ Ran := hA_map_Ran xR
    have hπARxR : πRan (A (xR : V)) = ⟨A xR, hARxR⟩ :=
      Submodule.projectionOnto_apply_left hcompl.symm ⟨A xR, hARxR⟩
    have hARxR_eq : (⟨A xR, hARxR⟩ : Ran) = AR xR := by
      apply Subtype.ext
      rfl
    have hleftInv : eRan.symm (AR xR) = xR := by
      change eRan.symm (eRan xR) = xR
      exact eRan.symm_apply_apply xR
    have hPsum : P ((xK : V) + xR) = (xR : V) := by
      change (πRan ((xK : V) + xR) : V) = (xR : V)
      simp [map_add, hπK, hπR]
    calc
      (D * A) x = D (A ((xK : V) + xR)) := by simp [hsum]
      _ = D (A (xK : V) + A xR) := by simp [map_add]
      _ = Ran.subtype (eRan.symm (πRan (A (xK : V) + A xR))) := rfl
      _ = Ran.subtype (eRan.symm (πRan (A (xK : V)) + πRan (A xR))) := by
        rw [map_add]
      _ = Ran.subtype (eRan.symm (0 + ⟨A xR, hARxR⟩)) := by
        rw [hπAK, hπARxR]
      _ = Ran.subtype (eRan.symm (AR xR)) := by rw [hARxR_eq]; simp
      _ = (xR : V) := by simp [hleftInv]
      _ = P ((xK : V) + xR) := by rw [hPsum]
      _ = P x := by rw [hsum]
  have hPD : P * D = D := by
    ext x
    have hDx : D x ∈ Ran := by
      unfold D
      exact (eRan.symm (πRan x)).2
    calc
      (P * D) x = Ran.subtype (πRan (D x)) := rfl
      _ = Ran.subtype ⟨D x, hDx⟩ := by
        rw [Submodule.projectionOnto_apply_left hcompl.symm ⟨D x, hDx⟩]
      _ = D x := rfl
  have hPA : P * A = A := by
    ext x
    change (πRan (A x) : V) = A x
    exact congrArg Subtype.val
      (Submodule.projectionOnto_apply_left hcompl.symm ⟨A x, ⟨x, rfl⟩⟩)
  have hADA : A * D * A = A := by
    calc
      A * D * A = (A * D) * A := by simp [mul_assoc]
      _ = P * A := by rw [hAD]
      _ = A := hPA
  have hDAD : D * A * D = D := by
    calc
      D * A * D = (D * A) * D := by simp [mul_assoc]
      _ = P * D := by rw [hDA]
      _ = D := hPD
  exact ⟨D, hADA, hDAD, hAD.trans hDA.symm⟩

/-- If no nonzero vector lies in both `range A` and `ker A`, rank-nullity
makes these subspaces complementary in finite dimension. -/
theorem isCompl_ker_range_of_no_length_two_chain (A : Module.End ℝ V)
    (hchain : ¬ ∃ x y : V, A x = y ∧ A y = 0 ∧ y ≠ 0) :
    IsCompl A.ker A.range := by
  have hdisjoint : Disjoint A.ker A.range := by
    apply disjoint_iff_inf_le.mpr
    intro y hy
    rcases hy with ⟨hker, hrange⟩
    rcases hrange with ⟨x, hxy⟩
    have hyzero : y = 0 := by
      by_contra hyne
      exact hchain ⟨x, y, hxy, hker, hyne⟩
    simp [hyzero]
  have hdim : Module.finrank ℝ V ≤
      Module.finrank ℝ A.ker + Module.finrank ℝ A.range := by
    calc
      Module.finrank ℝ V = Module.finrank ℝ A.range + Module.finrank ℝ A.ker :=
        (LinearMap.finrank_range_add_finrank_ker A).symm
      _ = Module.finrank ℝ A.ker + Module.finrank ℝ A.range := Nat.add_comm _ _
      _ ≤ Module.finrank ℝ A.ker + Module.finrank ℝ A.range := le_rfl
  exact (Submodule.isCompl_iff_disjoint A.ker A.range hdim).mpr hdisjoint

/-- A row-stochastic matrix yields a group inverse for its Markov Laplacian.
The no-chain fact is supplied by the repository's bounded-orbit theorem. -/
theorem exists_stochastic_laplacian_groupInverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ D : Module.End ℝ (ι → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - P)) D := by
  have hNoChain :
      ¬ ∃ x y : ι → ℝ,
        Matrix.toLin' (1 - P) x = y ∧ Matrix.toLin' (1 - P) y = 0 ∧ y ≠ 0 := by
    rintro ⟨x, y, hxy, hyy, hyne⟩
    have hxy' : (1 - P) *ᵥ x = y := by
      simpa only [Matrix.toLin'_apply] using hxy
    have hyy' : (1 - P) *ᵥ y = 0 := by
      simpa only [Matrix.toLin'_apply] using hyy
    exact hyne (InfoGeometry.QuantumContext.MarkovDrazin.no_length_two_generalized_fixed_vector
      P hP x y hxy' hyy')
  have hcomp := isCompl_ker_range_of_no_length_two_chain
    (Matrix.toLin' (1 - P)) hNoChain
  exact exists_groupInverse_of_isCompl_ker_range (Matrix.toLin' (1 - P)) hcomp

end InfoGeometry.Canonical.GroupInverseFromKerRangeCandidate
