/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PartnerEigenspaces
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Generalized eigenspaces of composable operator partners

The map `A : X →ₗ[K] Y` identifies the generalized eigenspaces of `BA` and
`AB` at every nonzero eigenvalue and every finite or maximal depth. The
operators are unrestricted linear maps; no commutation, adjoint relation,
diagonalization, or finite-dimensional hypothesis is imposed.

Surjectivity is derived from the nilpotent part of each finite Jordan chain:
the restriction of the operator is a unit because it is a nonzero scalar
unit plus a commuting nilpotent. This also handles maximal generalized
eigenspaces by the native finite-depth membership witness.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PartnerEigenspaces

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The native restriction of an operator to one of its generalized eigenspaces. -/
def genEigenspaceRestriction (T : Module.End K X) (μ : K) (k : ℕ∞) :
    Module.End K (T.genEigenspace μ k) :=
  T.restrict (Module.End.mapsTo_genEigenspace_of_comp T rfl μ k)

@[simp]
theorem genEigenspaceRestriction_apply (T : Module.End K X) (μ : K) (k : ℕ∞)
    (x : T.genEigenspace μ k) :
    (genEigenspaceRestriction T μ k x : X) = T x := rfl

/-- The nonzero scalar part makes the operator invertible on a finite Jordan chain. -/
theorem isUnit_genEigenspaceRestriction (T : Module.End K X) (μ : K)
    (hμ : μ ≠ 0) (k : ℕ) :
    IsUnit (genEigenspaceRestriction T μ k) := by
  let N : Module.End K (T.genEigenspace μ k) :=
    (T - μ • 1).restrict
      (Module.End.mapsTo_genEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes T μ) μ k)
  have hN : IsNilpotent N := T.isNilpotent_restrict_genEigenspace_nat μ k
  have hscalar : IsUnit (μ • (1 : Module.End K (T.genEigenspace μ k))) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isUnit_iff_ne_zero.mpr hμ).map
        (algebraMap K (Module.End K (T.genEigenspace μ k)))
  have hcomm : Commute N (μ • 1) := by
    change N * (μ • 1) = (μ • 1) * N
    simp only [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  have hunit := hN.isUnit_add_right_of_commute hscalar hcomm
  have heq : N + μ • 1 = genEigenspaceRestriction T μ k := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (T x - μ • (x : X)) + μ • (x : X) = T x
    exact sub_add_cancel _ _
  rwa [heq] at hunit

/-- Every finite-depth generalized eigenvector has a preimage at that same depth. -/
theorem exists_genEigenspace_preimage_nat (T : Module.End K X) (μ : K)
    (hμ : μ ≠ 0) (l : ℕ) (y : X) (hy : y ∈ T.genEigenspace μ (l : ℕ∞)) :
    ∃ z : X, z ∈ T.genEigenspace μ (l : ℕ∞) ∧ T z = y := by
  have hsurj := ((Module.End.isUnit_iff _).mp
    (isUnit_genEigenspaceRestriction T μ hμ l)).surjective
  obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
  refine ⟨z, z.property, ?_⟩
  have heq := congrArg (fun w : T.genEigenspace μ (l : ℕ∞) => (w : X)) hz
  exact heq

/-- Restriction remains onto at every depth, including the maximal generalized eigenspace. -/
theorem surjective_genEigenspaceRestriction (T : Module.End K X) (μ : K)
    (hμ : μ ≠ 0) (k : ℕ∞) :
    Function.Surjective (genEigenspaceRestriction T μ k) := by
  intro y
  obtain ⟨l, hl, hy⟩ := Module.End.mem_genEigenspace.mp y.property
  have hyl : (y : X) ∈ T.genEigenspace μ (l : ℕ∞) :=
    Module.End.mem_genEigenspace_nat.mpr hy
  obtain ⟨z, hz, hTz⟩ := exists_genEigenspace_preimage_nat T μ hμ l y hyl
  refine ⟨⟨z, (T.genEigenspace μ).monotone hl hz⟩, ?_⟩
  apply Subtype.ext
  change T z = (y : X)
  exact hTz

/-- A composable map transports every native generalized eigenspace of its partners. -/
theorem map_partner_genEigenspace (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (k : ℕ∞) :
    Set.MapsTo A (Module.End.genEigenspace (B.comp A) μ k)
      (Module.End.genEigenspace (A.comp B) μ k) :=
  Module.End.mapsTo_genEigenspace_of_comp
    (f := B.comp A) (g := A.comp B) A (by ext x; rfl) μ k

/-- Restrict the actual operator `A`, retaining the generalized-eigenspace depth. -/
def partnerGenEigenspaceMap (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (k : ℕ∞) :
    Module.End.genEigenspace (B.comp A) μ k →ₗ[K] Module.End.genEigenspace (A.comp B) μ k :=
  A.restrict (map_partner_genEigenspace A B μ k)

/-- Away from zero, a generalized eigenvector cannot lie in the kernel of the partner map. -/
theorem injective_partnerGenEigenspaceMap (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) (k : ℕ∞) :
    Function.Injective (partnerGenEigenspaceMap A B μ k) := by
  apply (partnerGenEigenspaceMap A B μ k).ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hAx : A (x : X) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  have hxzero : (x : X) ∈ Module.End.genEigenspace (B.comp A) 0 1 := by
    apply Module.End.mem_genEigenspace_one.mpr
    simp [LinearMap.comp_apply, hAx]
  have hbot : (x : X) ∈ (⊥ : Submodule K X) := by
    rw [← (Module.End.disjoint_genEigenspace (B.comp A) hμ k 1).eq_bot]
    exact ⟨x.property, hxzero⟩
  simp only [Submodule.mem_bot]
  apply Subtype.ext
  simpa only [Submodule.mem_bot, ZeroMemClass.coe_zero] using hbot

/-- Local invertibility of `AB` supplies a preimage under `A`; no dimension argument is used. -/
theorem surjective_partnerGenEigenspaceMap (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) (k : ℕ∞) :
    Function.Surjective (partnerGenEigenspaceMap A B μ k) := by
  intro y
  obtain ⟨z, hz⟩ := surjective_genEigenspaceRestriction (A.comp B) μ hμ k y
  refine ⟨partnerGenEigenspaceMap B A μ k z, ?_⟩
  exact hz

/-- The genuine generalized-eigenspace equivalence, with forward operator exactly `A`. -/
def nonzeroGenEigenspaceEquiv (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.End.genEigenspace (B.comp A) μ k ≃ₗ[K] Module.End.genEigenspace (A.comp B) μ k :=
  LinearEquiv.ofBijective (partnerGenEigenspaceMap A B μ k)
    ⟨injective_partnerGenEigenspaceMap A B μ hμ k,
      surjective_partnerGenEigenspaceMap A B μ hμ k⟩

@[simp]
theorem nonzeroGenEigenspaceEquiv_apply (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) (k : ℕ∞)
    (x : Module.End.genEigenspace (B.comp A) μ k) :
    (nonzeroGenEigenspaceEquiv A B μ hμ k x : Y) = A x := rfl

/-- Depth one recovers the existing ordinary partner-eigenspace owner exactly. -/
theorem nonzeroGenEigenspaceEquiv_one (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) :
    nonzeroGenEigenspaceEquiv A B μ hμ 1 = nonzeroEigenspaceEquiv A B μ hμ := by
  ext x
  rfl

/-- Native finite-rank readouts agree. They are generalized multiplicities when the
eigenspaces are finite-dimensional; the equivalence also covers infinite-dimensional spaces. -/
theorem nonzero_genEigenspace_finrank_eq
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X) (μ : K) (hμ : μ ≠ 0) (k : ℕ∞) :
    Module.finrank K (Module.End.genEigenspace (B.comp A) μ k) =
      Module.finrank K (Module.End.genEigenspace (A.comp B) μ k) :=
  (nonzeroGenEigenspaceEquiv A B μ hμ k).finrank_eq

/-- The map carries the entire shifted-operator Jordan chain, not only its vanishing endpoint. -/
theorem partner_shifted_power_apply (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (j : ℕ) (x : X) :
    ((A.comp B - μ • 1) ^ j) (A x) =
      A (((B.comp A - μ • 1) ^ j) x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul]

end InfoGeometry.OperatorAlgebra.PartnerEigenspaces
