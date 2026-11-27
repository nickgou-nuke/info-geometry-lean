/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Group
import InfoGeometry.Canonical.AtiyahSingerDiracSupertraceCapstone
import InfoGeometry.Algebra.FiniteSUSYBlocks

/-!
# Supersymmetric Quantum Mechanics and the Witten Index on Super Hilbert Spaces

Formalization of Kudinoor (2023), *Supersymmetry and the Witten Index*, §1.1–1.3:

1. **Super Hilbert spaces** (`SuperHilbertSpace ℋ`): a complex Hilbert space `ℋ` equipped with a
   self-adjoint involution `K` (`K ∘L K = id`), yielding the orthogonal decomposition
   `ℋ = ℋ_B ⊕ ℋ_F` into bosonic (`ker (K - 1)`) and fermionic (`ker (K + 1)`) subspaces,
   and even/odd grading of bounded operators.
2. **N = n supersymmetric quantum systems** (`SUSYQuantumSystem n ℋ`): a super Hilbert space
   with even self-adjoint Hamiltonian `H` and odd self-adjoint supercharges `Q : Fin n → (ℋ →L[ℂ] ℋ)`
   satisfying the SUSY anticommutation relations `{Q_i, Q_j} = 2 δ_{ij} H`.
3. **Algebraic factor-of-2 note**: Setting `i = j` in `{Q_i, Q_j} = 2 δ_{ij} H` yields
   `Q_i ∘L Q_i + Q_i ∘L Q_i = (2 : ℂ) • H`, hence `H = Q_i ∘L Q_i` (rather than `(1 / 2) • Q_i²`,
   which appears as an algebraic slip on p. 3 of Kudinoor 2023). Using `H = Q_i ∘L Q_i` aligns
   the superalgebra `{Q_i, Q_j} = 2 δ_{ij} H` with `re ⟪x, H x⟫_ℂ = ‖Q_i x‖^2 ≥ 0`,
   the unitary pairing `((Real.sqrt E)⁻¹ : ℂ) • Q_i` on nonzero energy eigenspaces `E > 0`,
   and the standard 2-term graded Fredholm Laplacian `H = Q_0² = diag(D_- D_+, D_+ D_-)`.
4. **Operator relationships & Witten index**: `[Q_i, H] = 0`, `[K, H] = 0` (derived directly
   from `Q_odd` and `superalgebra`), `H ≥ 0`, `ker H = ⋂_i ker Q_i`, Bose–Fermi isomorphism
   and isometry on positive energy levels `E > 0`, `β`-independence of the thermal supertrace
   `Tr((-1)^F e^{-βH}) = n_0`, finite-dimensional `Tr(K) = dim ℋ_B - dim ℋ_F`, and links to
   `InfoGeometry.Canonical.AtiyahSingerDirac` and `InfoGeometry.Algebra.FiniteSUSY`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate Matrix
open Complex

namespace InfoGeometry.Quantum.SUSYHilbertWittenIndex

section SuperHilbert

variable {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- A 2-graded (super) complex Hilbert space `(ℋ, K)` where `K` is a self-adjoint involution
(`K² = 1`). The `+1` eigenspace is the bosonic subspace `ℋ_B` and the `-1` eigenspace is the
fermionic subspace `ℋ_F`. -/
structure SuperHilbertSpace (ℋ : Type*)
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] where
  K : ℋ →L[ℂ] ℋ
  K_selfAdjoint : IsSelfAdjoint K
  K_involution : K ∘L K = ContinuousLinearMap.id ℂ ℋ

namespace SuperHilbertSpace

variable (S : SuperHilbertSpace ℋ)

@[simp]
theorem K_apply_K (x : ℋ) : S.K (S.K x) = x := by
  have h := ContinuousLinearMap.ext_iff.mp S.K_involution x
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

/-- Bosonic (`+1` / even-graded) subspace `ℋ_B = ker (K - 1)`. -/
def bosonicSubspace : Submodule ℂ ℋ :=
  LinearMap.ker ((S.K - ContinuousLinearMap.id ℂ ℋ : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)

/-- Fermionic (`-1` / odd-graded) subspace `ℋ_F = ker (K + 1)`. -/
def fermionicSubspace : Submodule ℂ ℋ :=
  LinearMap.ker ((S.K + ContinuousLinearMap.id ℂ ℋ : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)

@[simp]
theorem mem_bosonicSubspace_iff (x : ℋ) : x ∈ S.bosonicSubspace ↔ S.K x = x := by
  simp [bosonicSubspace, LinearMap.mem_ker, sub_eq_zero]

@[simp]
theorem mem_fermionicSubspace_iff (x : ℋ) : x ∈ S.fermionicSubspace ↔ S.K x = -x := by
  simp [fermionicSubspace, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

theorem isClosed_bosonicSubspace : IsClosed (S.bosonicSubspace : Set ℋ) :=
  (S.K - ContinuousLinearMap.id ℂ ℋ).isClosed_ker

theorem isClosed_fermionicSubspace : IsClosed (S.fermionicSubspace : Set ℋ) :=
  (S.K + ContinuousLinearMap.id ℂ ℋ).isClosed_ker

instance instCompleteSpaceBosonicSubspace : CompleteSpace S.bosonicSubspace :=
  S.isClosed_bosonicSubspace.completeSpace_coe

instance instCompleteSpaceFermionicSubspace : CompleteSpace S.fermionicSubspace :=
  S.isClosed_fermionicSubspace.completeSpace_coe

instance instHasOrthogonalProjectionBosonic : S.bosonicSubspace.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace S.bosonicSubspace

instance instHasOrthogonalProjectionFermionic : S.fermionicSubspace.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace S.fermionicSubspace

/-- Bosonic (`+1`) and fermionic (`-1`) states are mutually orthogonal. -/
theorem bosonic_isOrtho_fermionic : S.bosonicSubspace ⟂ S.fermionicSubspace := by
  intro u hu v hv
  rw [S.mem_bosonicSubspace_iff] at hu
  rw [S.mem_fermionicSubspace_iff] at hv
  have hsymm : ⟪S.K u, v⟫_ℂ = ⟪u, S.K v⟫_ℂ := S.K_selfAdjoint.isSymmetric u v
  rw [hu, hv, inner_neg_right] at hsymm
  have h2 : (2 : ℂ) * ⟪u, v⟫_ℂ = 0 := by
    linear_combination hsymm
  exact inner_eq_zero_symm.mp ((mul_eq_zero.mp h2).resolve_left (by norm_num))

/-- The fermionic subspace is precisely the orthogonal complement of the bosonic subspace. -/
theorem fermionicSubspace_eq_orthogonal : S.fermionicSubspace = S.bosonicSubspaceᗮ := by
  refine le_antisymm S.bosonic_isOrtho_fermionic.ge ?_
  intro v hv
  rw [Submodule.mem_orthogonal] at hv
  rw [S.mem_fermionicSubspace_iff]
  have hw_mem : v + S.K v ∈ S.bosonicSubspace := by
    rw [S.mem_bosonicSubspace_iff, map_add, S.K_apply_K, add_comm]
  have h_ortho_v : ⟪v + S.K v, v⟫_ℂ = 0 := hv (v + S.K v) hw_mem
  have h_ortho_Kv : ⟪v + S.K v, S.K v⟫_ℂ = 0 := by
    have hsymm : ⟪v + S.K v, S.K v⟫_ℂ = ⟪S.K (v + S.K v), v⟫_ℂ :=
      (S.K_selfAdjoint.isSymmetric _ _).symm
    have hKv : S.K (v + S.K v) = v + S.K v := (S.mem_bosonicSubspace_iff _).mp hw_mem
    rw [hKv, h_ortho_v] at hsymm
    exact hsymm
  have h_sum_zero : ⟪v + S.K v, v + S.K v⟫_ℂ = 0 := by
    rw [inner_add_right, h_ortho_v, h_ortho_Kv, add_zero]
  have hv_add : v + S.K v = 0 := inner_self_eq_zero.mp h_sum_zero
  exact eq_neg_of_add_eq_zero_right hv_add

/-- `ℋ` decomposes as the direct sum `ℋ_B ⊕ ℋ_F`. -/
theorem isCompl_bosonic_fermionic : IsCompl S.bosonicSubspace S.fermionicSubspace := by
  rw [S.fermionicSubspace_eq_orthogonal]
  exact S.bosonicSubspace.isCompl_orthogonal

/-- Orthogonal `L²` decomposition `ℋ ≃ₗᵢ[ℂ] WithLp 2 (ℋ_B × ℋ_F)`. -/
def orthogonalDecomposition : ℋ ≃ₗᵢ[ℂ] WithLp 2 (S.bosonicSubspace × S.fermionicSubspace) :=
  let eOrth : S.bosonicSubspaceᗮ ≃ₗᵢ[ℂ] S.fermionicSubspace :=
    LinearIsometryEquiv.ofEq _ _ S.fermionicSubspace_eq_orthogonal.symm
  let eProd : WithLp 2 (S.bosonicSubspace × S.bosonicSubspaceᗮ) ≃ₗᵢ[ℂ]
      WithLp 2 (S.bosonicSubspace × S.fermionicSubspace) :=
    { toLinearEquiv :=
        (WithLp.linearEquiv 2 ℂ _).trans
          ((LinearEquiv.refl ℂ S.bosonicSubspace).prodCongr eOrth.toLinearEquiv |>.trans
            (WithLp.linearEquiv 2 ℂ _).symm)
      norm_map' := fun x => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
        simp [WithLp.prod_norm_sq_eq_of_L2, eOrth] }
  S.bosonicSubspace.orthogonalDecomposition.trans eProd

/-- An operator `A` is even with respect to `K` if it commutes with `K`. -/
def IsEvenOp (A : ℋ →L[ℂ] ℋ) : Prop :=
  A ∘L S.K = S.K ∘L A

/-- An operator `A` is odd with respect to `K` if it anticommutes with `K`. -/
def IsOddOp (A : ℋ →L[ℂ] ℋ) : Prop :=
  A ∘L S.K = -(S.K ∘L A)

theorem IsEvenOp.maps_bosonic {A : ℋ →L[ℂ] ℋ} (hA : S.IsEvenOp A) {x : ℋ}
    (hx : x ∈ S.bosonicSubspace) : A x ∈ S.bosonicSubspace := by
  rw [S.mem_bosonicSubspace_iff] at hx ⊢
  have hcomp : S.K (A x) = A (S.K x) := by
    have h := ContinuousLinearMap.ext_iff.mp hA x
    simpa [ContinuousLinearMap.comp_apply] using h.symm
  rw [hcomp, hx]

theorem IsEvenOp.maps_fermionic {A : ℋ →L[ℂ] ℋ} (hA : S.IsEvenOp A) {x : ℋ}
    (hx : x ∈ S.fermionicSubspace) : A x ∈ S.fermionicSubspace := by
  rw [S.mem_fermionicSubspace_iff] at hx ⊢
  have hcomp : S.K (A x) = A (S.K x) := by
    have h := ContinuousLinearMap.ext_iff.mp hA x
    simpa [ContinuousLinearMap.comp_apply] using h.symm
  rw [hcomp, hx, map_neg]

theorem IsOddOp.maps_bosonic_to_fermionic {A : ℋ →L[ℂ] ℋ} (hA : S.IsOddOp A) {x : ℋ}
    (hx : x ∈ S.bosonicSubspace) : A x ∈ S.fermionicSubspace := by
  rw [S.mem_bosonicSubspace_iff] at hx
  rw [S.mem_fermionicSubspace_iff]
  have hcomp : A (S.K x) = -(S.K (A x)) := by
    have h := ContinuousLinearMap.ext_iff.mp hA x
    simpa [ContinuousLinearMap.comp_apply, neg_apply] using h
  rw [hx] at hcomp
  exact neg_eq_iff_eq_neg.mp hcomp.symm

theorem IsOddOp.maps_fermionic_to_bosonic {A : ℋ →L[ℂ] ℋ} (hA : S.IsOddOp A) {x : ℋ}
    (hx : x ∈ S.fermionicSubspace) : A x ∈ S.bosonicSubspace := by
  rw [S.mem_fermionicSubspace_iff] at hx
  rw [S.mem_bosonicSubspace_iff]
  have hcomp : A (S.K x) = -(S.K (A x)) := by
    have h := ContinuousLinearMap.ext_iff.mp hA x
    simpa [ContinuousLinearMap.comp_apply, neg_apply] using h
  rw [hx, map_neg] at hcomp
  exact (neg_inj.mp hcomp).symm

end SuperHilbertSpace

end SuperHilbert

section SUSYSystem

variable {n : ℕ} {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- An `N = n` supersymmetric quantum system `(ℋ, K, H, Q_1, ..., Q_n)` (Kudinoor Def. 1.4).
The supercharges satisfy `{Q_i, Q_j} = 2 δ_{ij} H`. -/
structure SUSYQuantumSystem (n : ℕ) (ℋ : Type*)
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    extends SuperHilbertSpace ℋ where
  H : ℋ →L[ℂ] ℋ
  H_selfAdjoint : IsSelfAdjoint H
  H_even : H ∘L K = K ∘L H
  Q : Fin n → (ℋ →L[ℂ] ℋ)
  Q_selfAdjoint : ∀ i, IsSelfAdjoint (Q i)
  Q_odd : ∀ i, Q i ∘L K = -(K ∘L Q i)
  superalgebra : ∀ i j, Q i ∘L Q j + Q j ∘L Q i = (if i = j then (2 : ℂ) else 0) • H

namespace SUSYQuantumSystem

variable (sys : SUSYQuantumSystem n ℋ)

/-- Restriction of the `i`-th supercharge `Q_i` to `ℋ_B → ℋ_F`. -/
def superchargeB (i : Fin n) : sys.bosonicSubspace →L[ℂ] sys.fermionicSubspace :=
  (sys.Q i).restrict fun _ hx =>
    SuperHilbertSpace.IsOddOp.maps_bosonic_to_fermionic sys.toSuperHilbertSpace (sys.Q_odd i) hx

/-- Restriction of the `i`-th supercharge `Q_i` to `ℋ_F → ℋ_B`. -/
def superchargeF (i : Fin n) : sys.fermionicSubspace →L[ℂ] sys.bosonicSubspace :=
  (sys.Q i).restrict fun _ hx =>
    SuperHilbertSpace.IsOddOp.maps_fermionic_to_bosonic sys.toSuperHilbertSpace (sys.Q_odd i) hx

@[simp]
theorem superchargeB_apply (i : Fin n) (x : sys.bosonicSubspace) :
    ((sys.superchargeB i x : sys.fermionicSubspace) : ℋ) = sys.Q i x := rfl

@[simp]
theorem superchargeF_apply (i : Fin n) (x : sys.fermionicSubspace) :
    ((sys.superchargeF i x : sys.bosonicSubspace) : ℋ) = sys.Q i x := rfl

/-- The adjoint of `Q_i^B : ℋ_B → ℋ_F` is `Q_i^F : ℋ_F → ℋ_B` (Kudinoor §1.1). -/
theorem adjoint_superchargeB_eq_superchargeF (i : Fin n) :
    (sys.superchargeB i).adjoint = sys.superchargeF i := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪((sys.superchargeB i x : sys.fermionicSubspace) : ℋ), (y : ℋ)⟫_ℂ =
    ⟪(x : ℋ), ((sys.superchargeF i y : sys.bosonicSubspace) : ℋ)⟫_ℂ
  simpa [superchargeB_apply, superchargeF_apply] using
    (sys.Q_selfAdjoint i).isSymmetric (x : ℋ) (y : ℋ)

/-- From `{Q_i, Q_j} = 2 δ_{ij} H` at `i = j`, we obtain `H = Q_i ∘L Q_i`. -/
theorem hamiltonian_eq_supercharge_sq (i : Fin n) :
    sys.H = sys.Q i ∘L sys.Q i := by
  have h_sa := sys.superalgebra i i
  simp only [↓reduceIte] at h_sa
  rw [← two_smul ℂ (sys.Q i ∘L sys.Q i)] at h_sa
  exact (smul_right_injective (ℋ →L[ℂ] ℋ) (by norm_num : (2 : ℂ) ≠ 0) h_sa).symm

/-- Proposition 1.1 (Kudinoor): `[Q_i, H] = 0` for every supercharge `Q_i`. -/
theorem hamiltonian_commutes_supercharge (i : Fin n) :
    sys.Q i ∘L sys.H = sys.H ∘L sys.Q i := by
  rw [sys.hamiltonian_eq_supercharge_sq i, ContinuousLinearMap.comp_assoc]

/-- Proposition 1.2 (Kudinoor): `[K, H] = 0` derived directly from `Q_odd` and `superalgebra`. -/
theorem grading_commutes_hamiltonian (i : Fin n) :
    sys.K ∘L sys.H = sys.H ∘L sys.K := by
  rw [sys.hamiltonian_eq_supercharge_sq i]
  have hodd : sys.Q i ∘L sys.K = -(sys.K ∘L sys.Q i) := sys.Q_odd i
  have hK : sys.K ∘L sys.Q i = -(sys.Q i ∘L sys.K) := by
    rw [hodd, neg_neg]
  calc
    sys.K ∘L (sys.Q i ∘L sys.Q i)
        = (sys.K ∘L sys.Q i) ∘L sys.Q i := by rw [ContinuousLinearMap.comp_assoc]
    _ = (-(sys.Q i ∘L sys.K)) ∘L sys.Q i := by rw [hK]
    _ = -(sys.Q i ∘L (sys.K ∘L sys.Q i)) := by
      rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    _ = -(sys.Q i ∘L (-(sys.Q i ∘L sys.K))) := by rw [hK]
    _ = (sys.Q i ∘L sys.Q i) ∘L sys.K := by
      rw [ContinuousLinearMap.comp_neg, neg_neg, ContinuousLinearMap.comp_assoc]

/-- Expectation value identity: `re ⟪x, H x⟫_ℂ = ‖Q_i x‖^2`. -/
theorem re_inner_hamiltonian_eq_norm_sq (i : Fin n) (x : ℋ) :
    Complex.re ⟪x, sys.H x⟫_ℂ = ‖sys.Q i x‖ ^ 2 := by
  rw [sys.hamiltonian_eq_supercharge_sq i, ContinuousLinearMap.comp_apply]
  have hsymm : ⟪x, sys.Q i (sys.Q i x)⟫_ℂ = ⟪sys.Q i x, sys.Q i x⟫_ℂ :=
    (sys.Q_selfAdjoint i).isSymmetric x (sys.Q i x) |>.symm
  rw [hsymm]
  exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (sys.Q i x)).symm

/-- Remark 1.1 (Kudinoor): `H ≥ 0` on `ℋ` whenever `n ≥ 1`. -/
theorem hamiltonian_nonneg [NeZero n] :
    (∀ x : ℋ, 0 ≤ Complex.re ⟪x, sys.H x⟫_ℂ) ∧ sys.H.IsPositive := by
  have h_re : ∀ x : ℋ, 0 ≤ Complex.re ⟪x, sys.H x⟫_ℂ := fun x => by
    rw [sys.re_inner_hamiltonian_eq_norm_sq (0 : Fin n) x]
    positivity
  refine ⟨h_re, (ContinuousLinearMap.isPositive_iff' sys.H).mpr ⟨sys.H_selfAdjoint, fun x => ?_⟩⟩
  rw [sys.hamiltonian_eq_supercharge_sq (0 : Fin n), ContinuousLinearMap.comp_apply]
  have hsymm : ⟪sys.Q 0 (sys.Q 0 x), x⟫_ℂ = ⟪sys.Q 0 x, sys.Q 0 x⟫_ℂ :=
    (sys.Q_selfAdjoint (0 : Fin n)).isSymmetric (sys.Q 0 x) x
  rw [hsymm, inner_self_eq_norm_sq_to_K]
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- Proposition 1.3 (Kudinoor): `H x = 0 ↔ ∀ i, Q_i x = 0` (when `n ≥ 1`). -/
theorem ker_hamiltonian_iff_ker_supercharges [NeZero n] (x : ℋ) :
    sys.H x = 0 ↔ ∀ i : Fin n, sys.Q i x = 0 := by
  constructor
  · intro hx i
    have hnorm : ‖sys.Q i x‖ ^ 2 = 0 := by
      rw [← sys.re_inner_hamiltonian_eq_norm_sq i x, hx, inner_zero_right, Complex.zero_re]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · intro hQ
    rw [sys.hamiltonian_eq_supercharge_sq (0 : Fin n), ContinuousLinearMap.comp_apply,
      hQ (0 : Fin n), map_zero]

/-- Submodule kernel equality `ker H = ⋂_i ker Q_i`. -/
theorem ker_hamiltonian_eq_iInf_ker_supercharges [NeZero n] :
    LinearMap.ker (sys.H : ℋ →ₗ[ℂ] ℋ) = ⨅ i : Fin n, LinearMap.ker (sys.Q i : ℋ →ₗ[ℂ] ℋ) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  exact sys.ker_hamiltonian_iff_ker_supercharges x

/-- Energy eigenspace `ℋ(E) = ker (H - E • I)`. -/
def energyEigenspace (E : ℝ) : Submodule ℂ ℋ :=
  LinearMap.ker ((sys.H - (E : ℂ) • ContinuousLinearMap.id ℂ ℋ : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)

/-- Bosonic subspace at energy `E`: `ℋ(E)^B = ℋ(E) ∩ ℋ_B`. -/
def bosonicEigenspace (E : ℝ) : Submodule ℂ ℋ :=
  sys.energyEigenspace E ⊓ sys.bosonicSubspace

/-- Fermionic subspace at energy `E`: `ℋ(E)^F = ℋ(E) ∩ ℋ_F`. -/
def fermionicEigenspace (E : ℝ) : Submodule ℂ ℋ :=
  sys.energyEigenspace E ⊓ sys.fermionicSubspace

@[simp]
theorem mem_energyEigenspace_iff {E : ℝ} {x : ℋ} :
    x ∈ sys.energyEigenspace E ↔ sys.H x = (E : ℂ) • x := by
  simp [energyEigenspace, LinearMap.mem_ker, sub_eq_zero]

@[simp]
theorem mem_bosonicEigenspace_iff {E : ℝ} {x : ℋ} :
    x ∈ sys.bosonicEigenspace E ↔ sys.H x = (E : ℂ) • x ∧ sys.K x = x := by
  simp [bosonicEigenspace]

@[simp]
theorem mem_fermionicEigenspace_iff {E : ℝ} {x : ℋ} :
    x ∈ sys.fermionicEigenspace E ↔ sys.H x = (E : ℂ) • x ∧ sys.K x = -x := by
  simp [fermionicEigenspace]

theorem isClosed_energyEigenspace (E : ℝ) : IsClosed (sys.energyEigenspace E : Set ℋ) :=
  (sys.H - (E : ℂ) • ContinuousLinearMap.id ℂ ℋ).isClosed_ker

theorem isClosed_bosonicEigenspace (E : ℝ) : IsClosed (sys.bosonicEigenspace E : Set ℋ) :=
  (sys.isClosed_energyEigenspace E).inter sys.isClosed_bosonicSubspace

theorem isClosed_fermionicEigenspace (E : ℝ) : IsClosed (sys.fermionicEigenspace E : Set ℋ) :=
  (sys.isClosed_energyEigenspace E).inter sys.isClosed_fermionicSubspace

/-- Negative energy eigenspaces are trivial (`H ≥ 0`). -/
theorem neg_energy_eigenspace_eq_bot [NeZero n] {E : ℝ} (hE : E < 0) :
    sys.energyEigenspace E = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [sys.mem_energyEigenspace_iff] at hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hnonneg : 0 ≤ Complex.re ⟪x, sys.H x⟫_ℂ := (sys.hamiltonian_nonneg).1 x
  rw [hx, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_eq_norm_sq_to_K] at hnonneg
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, Complex.ofReal_re] at hnonneg
  have hnorm_pos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hneg : E * ‖x‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hE hnorm_pos
  exact not_le_of_gt hneg hnonneg

theorem bosonicEigenspace_isOrtho_fermionicEigenspace (E : ℝ) :
    sys.bosonicEigenspace E ⟂ sys.fermionicEigenspace E :=
  sys.bosonic_isOrtho_fermionic.mono inf_le_right inf_le_right

theorem bosonicEigenspace_sup_fermionicEigenspace (E : ℝ) :
    sys.bosonicEigenspace E ⊔ sys.fermionicEigenspace E = sys.energyEigenspace E := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  intro x hx
  rw [sys.mem_energyEigenspace_iff] at hx
  have hHK : sys.H (sys.K x) = (E : ℂ) • sys.K x := by
    have hcomm := ContinuousLinearMap.ext_iff.mp sys.H_even x
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    rw [hcomm, hx, map_smul]
  have h_even_proj : (1 / 2 : ℂ) • (x + sys.K x) ∈ sys.bosonicEigenspace E := by
    rw [sys.mem_bosonicEigenspace_iff]
    refine ⟨?_, ?_⟩
    · rw [map_smul, map_add, hx, hHK]
      module
    · rw [map_smul, map_add, sys.K_apply_K, add_comm]
  have h_odd_proj : (1 / 2 : ℂ) • (x - sys.K x) ∈ sys.fermionicEigenspace E := by
    rw [sys.mem_fermionicEigenspace_iff]
    refine ⟨?_, ?_⟩
    · rw [map_smul, map_sub, hx, hHK]
      module
    · rw [map_smul, map_sub, sys.K_apply_K, ← smul_neg, neg_sub]
  have h_sum : x = (1 / 2 : ℂ) • (x + sys.K x) + (1 / 2 : ℂ) • (x - sys.K x) := by
    module
  rw [h_sum]
  exact Submodule.add_mem_sup h_even_proj h_odd_proj

theorem finrank_energyEigenspace_eq_add (E : ℝ) [FiniteDimensional ℂ (sys.energyEigenspace E)] :
    Module.finrank ℂ (sys.energyEigenspace E) =
      Module.finrank ℂ (sys.bosonicEigenspace E) + Module.finrank ℂ (sys.fermionicEigenspace E) := by
  have h_bose_fd : FiniteDimensional ℂ (sys.bosonicEigenspace E) :=
    Submodule.finiteDimensional_of_le (inf_le_left : sys.bosonicEigenspace E ≤ sys.energyEigenspace E)
  have h_fermi_fd : FiniteDimensional ℂ (sys.fermionicEigenspace E) :=
    Submodule.finiteDimensional_of_le (inf_le_left : sys.fermionicEigenspace E ≤ sys.energyEigenspace E)
  have h_disj : Disjoint (sys.bosonicEigenspace E) (sys.fermionicEigenspace E) :=
    (sys.bosonicEigenspace_isOrtho_fermionicEigenspace E).disjoint
  have h_inf : Module.finrank ℂ (sys.bosonicEigenspace E ⊓ sys.fermionicEigenspace E : Submodule ℂ ℋ) = 0 := by
    rw [h_disj.eq_bot, finrank_bot]
  have h_sum := Submodule.finrank_sup_add_finrank_inf_eq
    (sys.bosonicEigenspace E) (sys.fermionicEigenspace E)
  rw [sys.bosonicEigenspace_sup_fermionicEigenspace E, h_inf, add_zero] at h_sum
  exact h_sum

private lemma supercharge_maps_bosonicEigenspace_to_fermionic (i : Fin n) (E : ℝ) {x : ℋ}
    (hx : x ∈ sys.bosonicEigenspace E) : sys.Q i x ∈ sys.fermionicEigenspace E := by
  rw [sys.mem_bosonicEigenspace_iff] at hx
  rw [sys.mem_fermionicEigenspace_iff]
  refine ⟨?_, ?_⟩
  · have hcomm := ContinuousLinearMap.ext_iff.mp (sys.hamiltonian_commutes_supercharge i) x
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    rw [← hcomm, hx.1, map_smul]
  · have hodd := ContinuousLinearMap.ext_iff.mp (sys.Q_odd i) x
    simp only [ContinuousLinearMap.comp_apply, neg_apply] at hodd
    rw [hx.2] at hodd
    exact neg_eq_iff_eq_neg.mp hodd.symm

private lemma supercharge_maps_fermionicEigenspace_to_bosonic (i : Fin n) (E : ℝ) {x : ℋ}
    (hx : x ∈ sys.fermionicEigenspace E) : sys.Q i x ∈ sys.bosonicEigenspace E := by
  rw [sys.mem_fermionicEigenspace_iff] at hx
  rw [sys.mem_bosonicEigenspace_iff]
  refine ⟨?_, ?_⟩
  · have hcomm := ContinuousLinearMap.ext_iff.mp (sys.hamiltonian_commutes_supercharge i) x
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    rw [← hcomm, hx.1, map_smul]
  · have hodd := ContinuousLinearMap.ext_iff.mp (sys.Q_odd i) x
    simp only [ContinuousLinearMap.comp_apply, neg_apply] at hodd
    rw [hx.2, map_neg] at hodd
    exact (neg_inj.mp hodd).symm

/-- Theorem 1.1 (Kudinoor): On any nonzero energy level `E > 0`, `Q_i` induces a continuous linear
equivalence `ℋ(E)^B ≃L[ℂ] ℋ(E)^F` with inverse `(E : ℂ)⁻¹ • Q_i`. -/
def nonzero_eigenspace_bose_fermi_iso (i : Fin n) {E : ℝ} (hE : 0 < E) :
    sys.bosonicEigenspace E ≃L[ℂ] sys.fermionicEigenspace E where
  toFun x := ⟨sys.Q i x, sys.supercharge_maps_bosonicEigenspace_to_fermionic i E x.2⟩
  invFun y := ⟨((E : ℂ)⁻¹) • sys.Q i y,
    Submodule.smul_mem _ _ (sys.supercharge_maps_fermionicEigenspace_to_bosonic i E y.2)⟩
  map_add' x y := Subtype.ext (map_add (sys.Q i) (x : ℋ) (y : ℋ))
  map_smul' c x := Subtype.ext (map_smul (sys.Q i) c (x : ℋ))
  left_inv x := by
    apply Subtype.ext
    have hsq : sys.Q i (sys.Q i x) = sys.H x := by
      rw [← ContinuousLinearMap.comp_apply, ← sys.hamiltonian_eq_supercharge_sq i]
    have hxH : sys.H x = (E : ℂ) • (x : ℋ) := (sys.mem_bosonicEigenspace_iff.mp x.2).1
    have hE0 : (E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hE)
    change ((E : ℂ)⁻¹) • sys.Q i (sys.Q i x) = (x : ℋ)
    rw [hsq, hxH, smul_smul, inv_mul_cancel₀ hE0, one_smul]
  right_inv y := by
    apply Subtype.ext
    have hsq : sys.Q i (sys.Q i y) = sys.H y := by
      rw [← ContinuousLinearMap.comp_apply, ← sys.hamiltonian_eq_supercharge_sq i]
    have hyH : sys.H y = (E : ℂ) • (y : ℋ) := (sys.mem_fermionicEigenspace_iff.mp y.2).1
    have hE0 : (E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hE)
    change sys.Q i (((E : ℂ)⁻¹) • sys.Q i y) = (y : ℋ)
    rw [map_smul, hsq, hyH, smul_smul, inv_mul_cancel₀ hE0, one_smul]
  continuous_toFun :=
    (ContinuousLinearMap.continuous (sys.Q i)).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun :=
    (continuous_const.smul ((ContinuousLinearMap.continuous (sys.Q i)).comp
      continuous_subtype_val)).subtype_mk _

/-- Unitary (isometric) version of Theorem 1.1: `((Real.sqrt E)⁻¹ : ℂ) • Q_i` defines a linear
isometry equivalence `ℋ(E)^B ≃ₗᵢ[ℂ] ℋ(E)^F` for `E > 0`. -/
def nonzero_eigenspace_bose_fermi_isometry (i : Fin n) {E : ℝ} (hE : 0 < E) :
    sys.bosonicEigenspace E ≃ₗᵢ[ℂ] sys.fermionicEigenspace E where
  toFun x := ⟨((Real.sqrt E : ℂ)⁻¹) • sys.Q i x,
    Submodule.smul_mem _ _ (sys.supercharge_maps_bosonicEigenspace_to_fermionic i E x.2)⟩
  invFun y := ⟨((Real.sqrt E : ℂ)⁻¹) • sys.Q i y,
    Submodule.smul_mem _ _ (sys.supercharge_maps_fermionicEigenspace_to_bosonic i E y.2)⟩
  map_add' x y := Subtype.ext (by
    change (Real.sqrt E : ℂ)⁻¹ • sys.Q i ((x : ℋ) + (y : ℋ)) =
      (Real.sqrt E : ℂ)⁻¹ • sys.Q i (x : ℋ) + (Real.sqrt E : ℂ)⁻¹ • sys.Q i (y : ℋ)
    rw [map_add, smul_add])
  map_smul' c x := Subtype.ext (by
    change (Real.sqrt E : ℂ)⁻¹ • sys.Q i (c • (x : ℋ)) =
      c • ((Real.sqrt E : ℂ)⁻¹ • sys.Q i (x : ℋ))
    rw [map_smul, smul_comm])
  left_inv x := by
    apply Subtype.ext
    have hsq : sys.Q i (sys.Q i x) = sys.H x := by
      rw [← ContinuousLinearMap.comp_apply, ← sys.hamiltonian_eq_supercharge_sq i]
    have hxH : sys.H x = (E : ℂ) • (x : ℋ) := (sys.mem_bosonicEigenspace_iff.mp x.2).1
    have hs_pos : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
    have hs_ne : (Real.sqrt E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have h_mul : (Real.sqrt E : ℂ)⁻¹ * ((Real.sqrt E : ℂ)⁻¹ * (E : ℂ)) = 1 := by
      have hsq_r : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt (le_of_lt hE)
      have hsq_c : (Real.sqrt E : ℂ) * (Real.sqrt E : ℂ) = (E : ℂ) := by
        exact_mod_cast hsq_r
      rw [← hsq_c]
      field_simp [hs_ne]
    change (Real.sqrt E : ℂ)⁻¹ • sys.Q i ((Real.sqrt E : ℂ)⁻¹ • sys.Q i x) = (x : ℋ)
    rw [map_smul, hsq, hxH, smul_smul, smul_smul, mul_assoc, h_mul, one_smul]
  right_inv y := by
    apply Subtype.ext
    have hsq : sys.Q i (sys.Q i y) = sys.H y := by
      rw [← ContinuousLinearMap.comp_apply, ← sys.hamiltonian_eq_supercharge_sq i]
    have hyH : sys.H y = (E : ℂ) • (y : ℋ) := (sys.mem_fermionicEigenspace_iff.mp y.2).1
    have hs_pos : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
    have hs_ne : (Real.sqrt E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs_pos)
    have h_mul : (Real.sqrt E : ℂ)⁻¹ * ((Real.sqrt E : ℂ)⁻¹ * (E : ℂ)) = 1 := by
      have hsq_r : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt (le_of_lt hE)
      have hsq_c : (Real.sqrt E : ℂ) * (Real.sqrt E : ℂ) = (E : ℂ) := by
        exact_mod_cast hsq_r
      rw [← hsq_c]
      field_simp [hs_ne]
    change (Real.sqrt E : ℂ)⁻¹ • sys.Q i ((Real.sqrt E : ℂ)⁻¹ • sys.Q i y) = (y : ℋ)
    rw [map_smul, hsq, hyH, smul_smul, smul_smul, mul_assoc, h_mul, one_smul]
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    change ‖(Real.sqrt E : ℂ)⁻¹ • sys.Q i (x : ℋ)‖ ^ 2 = ‖(x : ℋ)‖ ^ 2
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg E)]
    have hQ_norm : ‖sys.Q i (x : ℋ)‖ ^ 2 = E * ‖(x : ℋ)‖ ^ 2 := by
      rw [← sys.re_inner_hamiltonian_eq_norm_sq i (x : ℋ)]
      have hxH : sys.H (x : ℋ) = (E : ℂ) • (x : ℋ) := (sys.mem_bosonicEigenspace_iff.mp x.2).1
      rw [hxH, inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, inner_self_eq_norm_sq_to_K]
      simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hQ_norm, inv_pow, Real.sq_sqrt (le_of_lt hE), ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hE), one_mul]

/-- Equal bosonic and fermionic dimensions on every positive energy eigenspace `E > 0`. -/
theorem nonzero_eigenspace_finrank_eq (i : Fin n) {E : ℝ} (hE : 0 < E) :
    Module.finrank ℂ (sys.bosonicEigenspace E) = Module.finrank ℂ (sys.fermionicEigenspace E) :=
  (sys.nonzero_eigenspace_bose_fermi_iso i hE).toLinearEquiv.finrank_eq

end SUSYQuantumSystem

end SUSYSystem

section WittenIndex

variable {n : ℕ} {ℋ ι : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- Discrete energy-level decomposition of a supersymmetric quantum system
`ℋ = ⨁_m ℋ(E_m)` with `E_{zeroIdx} = 0`, `E_{m ≠ zeroIdx} > 0`, and finite-dimensional
energy eigenspaces (Kudinoor §1.2–1.3). -/
structure DiscreteSUSYSpectrum (n : ℕ) (ℋ ι : Type*)
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (sys : SUSYQuantumSystem n ℋ) where
  energy : ι → ℝ
  zeroIdx : ι
  energy_zeroIdx : energy zeroIdx = 0
  energy_pos_of_ne : ∀ m, m ≠ zeroIdx → 0 < energy m
  finiteDim_level : ∀ m, FiniteDimensional ℂ (sys.energyEigenspace (energy m))
  eigenspaces_dense : (⨆ m, sys.energyEigenspace (energy m))ᗮ = ⊥

namespace SUSYQuantumSystem

variable (sys : SUSYQuantumSystem n ℋ)

/-- Number of bosonic states at energy `E`. -/
def levelBosonDim (E : ℝ) : ℕ :=
  Module.finrank ℂ (sys.bosonicEigenspace E)

/-- Number of fermionic states at energy `E`. -/
def levelFermionDim (E : ℝ) : ℕ :=
  Module.finrank ℂ (sys.fermionicEigenspace E)

/-- Signed Bose–Fermi difference `n(E) = dim ℋ(E)^B - dim ℋ(E)^F`. -/
def levelWittenDiff (E : ℝ) : ℤ :=
  (sys.levelBosonDim E : ℤ) - (sys.levelFermionDim E : ℤ)

/-- The Witten index `n_0 = dim ℋ(0)^B - dim ℋ(0)^F`. -/
def wittenIndex : ℤ :=
  sys.levelWittenDiff 0

theorem levelWittenDiff_eq_zero_of_pos [NeZero n] {E : ℝ} (hE : 0 < E) :
    sys.levelWittenDiff E = 0 := by
  simp only [levelWittenDiff, levelBosonDim, levelFermionDim]
  rw [sys.nonzero_eigenspace_finrank_eq (0 : Fin n) hE, sub_self]

/-- Thermal supertrace `Tr_s(e^{-βH}) = ∑_m (dim ℋ(E_m)^B - dim ℋ(E_m)^F) e^{-β E_m}`. -/
def thermalSupertrace (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β : ℝ) : ℝ :=
  ∑' m : ι, ((sys.levelWittenDiff (spec.energy m) : ℤ) : ℝ) * Real.exp (-β * spec.energy m)

/-- Bosonic thermal partition sum `∑_m dim ℋ(E_m)^B e^{-β E_m}`. -/
def bosePartitionSum (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β : ℝ) : ℝ :=
  ∑' m : ι, (sys.levelBosonDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m)

/-- Fermionic thermal partition sum `∑_m dim ℋ(E_m)^F e^{-β E_m}`. -/
def fermiPartitionSum (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β : ℝ) : ℝ :=
  ∑' m : ι, (sys.levelFermionDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m)

/-- Theorem 1.2 (Kudinoor): `Tr((-1)^F e^{-βH}) = n_0` for every `β`. -/
theorem witten_index_eq_thermal_supertrace [NeZero n]
    (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β : ℝ) :
    sys.thermalSupertrace spec β = (sys.wittenIndex : ℝ) := by
  unfold thermalSupertrace
  rw [tsum_eq_single spec.zeroIdx]
  · simp [spec.energy_zeroIdx, wittenIndex]
  · intro m hm
    have hpos : 0 < spec.energy m := spec.energy_pos_of_ne m hm
    rw [sys.levelWittenDiff_eq_zero_of_pos hpos]
    simp

/-- Independence of the thermal supertrace from the inverse temperature `β`. -/
theorem witten_index_thermal_independent_of_beta [NeZero n]
    (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β₁ β₂ : ℝ) :
    sys.thermalSupertrace spec β₁ = sys.thermalSupertrace spec β₂ := by
  rw [sys.witten_index_eq_thermal_supertrace spec β₁,
    sys.witten_index_eq_thermal_supertrace spec β₂]

/-- Derivative with respect to `β` of the thermal supertrace is identically `0`. -/
theorem hasDerivAt_thermalSupertrace_zero [NeZero n]
    (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β : ℝ) :
    HasDerivAt (fun t => sys.thermalSupertrace spec t) 0 β := by
  have hfn : (fun t => sys.thermalSupertrace spec t) = fun _ => (sys.wittenIndex : ℝ) := by
    funext t
    exact sys.witten_index_eq_thermal_supertrace spec t
  rw [hfn]
  exact hasDerivAt_const β (sys.wittenIndex : ℝ)

/-- Bose–Fermi partition-function difference equals the Witten index whenever the trace
partition sum converges. -/
theorem bose_partition_sub_fermi_partition_eq_witten_index [NeZero n]
    (spec : DiscreteSUSYSpectrum n ℋ ι sys) (β : ℝ)
    (h_sum : Summable (fun m : ι =>
      (Module.finrank ℂ (sys.energyEigenspace (spec.energy m)) : ℝ) *
        Real.exp (-β * spec.energy m))) :
    sys.bosePartitionSum spec β - sys.fermiPartitionSum spec β = (sys.wittenIndex : ℝ) := by
  have h_bose_le : ∀ m : ι,
      (sys.levelBosonDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m) ≤
        (Module.finrank ℂ (sys.energyEigenspace (spec.energy m)) : ℝ) *
          Real.exp (-β * spec.energy m) := fun m => by
    have := spec.finiteDim_level m
    have h_add := sys.finrank_energyEigenspace_eq_add (spec.energy m)
    have hle : sys.levelBosonDim (spec.energy m) ≤
        Module.finrank ℂ (sys.energyEigenspace (spec.energy m)) := by
      simp only [levelBosonDim, h_add]
      exact Nat.le_add_right _ _
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (le_of_lt (Real.exp_pos _))
  have h_fermi_le : ∀ m : ι,
      (sys.levelFermionDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m) ≤
        (Module.finrank ℂ (sys.energyEigenspace (spec.energy m)) : ℝ) *
          Real.exp (-β * spec.energy m) := fun m => by
    have := spec.finiteDim_level m
    have h_add := sys.finrank_energyEigenspace_eq_add (spec.energy m)
    have hle : sys.levelFermionDim (spec.energy m) ≤
        Module.finrank ℂ (sys.energyEigenspace (spec.energy m)) := by
      simp only [levelFermionDim, h_add]
      exact Nat.le_add_left _ _
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (le_of_lt (Real.exp_pos _))
  have h_bose_sum : Summable (fun m : ι =>
      (sys.levelBosonDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) h_bose_le h_sum
  have h_fermi_sum : Summable (fun m : ι =>
      (sys.levelFermionDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) h_fermi_le h_sum
  unfold bosePartitionSum fermiPartitionSum
  rw [← h_bose_sum.tsum_sub h_fermi_sum]
  have h_term : (fun m : ι =>
      (sys.levelBosonDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m) -
        (sys.levelFermionDim (spec.energy m) : ℝ) * Real.exp (-β * spec.energy m)) =
      (fun m : ι =>
        ((sys.levelWittenDiff (spec.energy m) : ℤ) : ℝ) * Real.exp (-β * spec.energy m)) := by
    funext m
    simp only [levelWittenDiff, Int.cast_sub, Int.cast_natCast, sub_mul]
  rw [h_term]
  exact sys.witten_index_eq_thermal_supertrace spec β

/-- Proposition 1.4 (Kudinoor), unweighted spectral form:
`∑_m (dim ℋ(E_m)^B - dim ℋ(E_m)^F) = n_0`. -/
theorem spectral_supertrace_unweighted_eq_witten_index [NeZero n]
    (spec : DiscreteSUSYSpectrum n ℋ ι sys) :
    (∑' m : ι, sys.levelWittenDiff (spec.energy m)) = sys.wittenIndex := by
  rw [tsum_eq_single spec.zeroIdx]
  · simp [spec.energy_zeroIdx, wittenIndex]
  · intro m hm
    exact sys.levelWittenDiff_eq_zero_of_pos (spec.energy_pos_of_ne m hm)

/-- Proposition 1.4 (Kudinoor), finite-dimensional operator trace form:
`Tr((-1)^F) = dim ℋ_B - dim ℋ_F`. -/
theorem trace_grading_eq_finrank_sub [FiniteDimensional ℂ ℋ] :
    LinearMap.trace ℂ ℋ (sys.K : ℋ →ₗ[ℂ] ℋ) =
      (Module.finrank ℂ sys.bosonicSubspace : ℂ) -
        (Module.finrank ℂ sys.fermionicSubspace : ℂ) := by
  let e : (sys.bosonicSubspace × sys.fermionicSubspace) ≃ₗ[ℂ] ℋ :=
    sys.bosonicSubspace.prodEquivOfIsCompl sys.fermionicSubspace sys.isCompl_bosonic_fermionic
  let blockK : (sys.bosonicSubspace × sys.fermionicSubspace) →ₗ[ℂ]
      (sys.bosonicSubspace × sys.fermionicSubspace) :=
    LinearMap.prodMap LinearMap.id (-LinearMap.id)
  have h_conj : e.conj blockK = (sys.K : ℋ →ₗ[ℂ] ℋ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨⟨u, v⟩, rfl⟩ := e.surjective x
    have hu : sys.K (u : ℋ) = u := (sys.mem_bosonicSubspace_iff _).mp u.2
    have hv : sys.K (v : ℋ) = -v := (sys.mem_fermionicSubspace_iff _).mp v.2
    simp [e, blockK, LinearEquiv.conj_apply, map_add, hu, hv]
  rw [← h_conj, LinearMap.trace_conj' blockK e]
  simp [blockK, LinearMap.trace_prodMap', LinearMap.trace_id, sub_eq_add_neg]

end SUSYQuantumSystem

end WittenIndex

section RepoLinks

open InfoGeometry.Canonical.AtiyahSingerDirac
open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
open InfoGeometry.Algebra.FiniteSUSY

section AtiyahSingerLink

variable {n : ℕ} {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-- Bridge to `InfoGeometry.Canonical.AtiyahSingerDirac.dirac_sq_grading_commutes`:
`Q_i² K - K Q_i² = 0` in the ring `ℋ →L[ℂ] ℋ`. -/
theorem susy_supercharge_sq_grading_commutes (sys : SUSYQuantumSystem n ℋ) (i : Fin n) :
    sys.Q i * sys.Q i * sys.K - sys.K * (sys.Q i * sys.Q i) = 0 := by
  refine dirac_sq_grading_commutes ?_
  change sys.Q i ∘L sys.K + sys.K ∘L sys.Q i = 0
  rw [sys.Q_odd i, neg_add_cancel]

/-- Bridge to `InfoGeometry.Canonical.AtiyahSingerDirac.mckean_singer_algebraic_cancellation`:
in finite dimensions, the cyclic supertrace `Tr(K · {Q_i, X})` vanishes for any even `X`. -/
theorem susy_finite_mckean_singer_cancellation [FiniteDimensional ℂ ℋ]
    (sys : SUSYQuantumSystem n ℋ) (i : Fin n) {X : ℋ →L[ℂ] ℋ}
    (hX : sys.K ∘L X = X ∘L sys.K) :
    gradedTrace
      ((LinearMap.trace ℂ ℋ).toAddMonoidHom.comp
        (ContinuousLinearMap.coeLM ℂ : (ℋ →L[ℂ] ℋ) →ₗ[ℂ] ℋ →ₗ[ℂ] ℋ).toAddMonoidHom)
      sys.K (operatorAnticommutator (sys.Q i) X) = 0 := by
  let τ : (ℋ →L[ℂ] ℋ) →+ ℂ :=
    (LinearMap.trace ℂ ℋ).toAddMonoidHom.comp
      (ContinuousLinearMap.coeLM ℂ : (ℋ →L[ℂ] ℋ) →ₗ[ℂ] ℋ →ₗ[ℂ] ℋ).toAddMonoidHom
  have hτ : IsCyclic τ := fun A B => by
    change LinearMap.trace ℂ ℋ ((A ∘L B : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) =
      LinearMap.trace ℂ ℋ ((B ∘L A : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)
    exact LinearMap.trace_mul_comm ℂ (A : ℋ →ₗ[ℂ] ℋ) (B : ℋ →ₗ[ℂ] ℋ)
  have hγD : sys.K * sys.Q i = -(sys.Q i * sys.K) := by
    change sys.K ∘L sys.Q i = -(sys.Q i ∘L sys.K)
    rw [sys.Q_odd i, neg_neg]
  have hγX : sys.K * X = X * sys.K := hX
  exact mckean_singer_algebraic_cancellation τ hτ hγD hγX

/-- In finite dimensions, `Tr(K H) = 0` when `n ≥ 1`. -/
theorem susy_finite_trace_grading_mul_hamiltonian_eq_zero [FiniteDimensional ℂ ℋ] [NeZero n]
    (sys : SUSYQuantumSystem n ℋ) :
    LinearMap.trace ℂ ℋ ((sys.K ∘L sys.H : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) = 0 := by
  let τ : (ℋ →L[ℂ] ℋ) →+ ℂ :=
    (LinearMap.trace ℂ ℋ).toAddMonoidHom.comp
      (ContinuousLinearMap.coeLM ℂ : (ℋ →L[ℂ] ℋ) →ₗ[ℂ] ℋ →ₗ[ℂ] ℋ).toAddMonoidHom
  have hτ : IsCyclic τ := fun A B => by
    change LinearMap.trace ℂ ℋ ((A ∘L B : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) =
      LinearMap.trace ℂ ℋ ((B ∘L A : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)
    exact LinearMap.trace_mul_comm ℂ (A : ℋ →ₗ[ℂ] ℋ) (B : ℋ →ₗ[ℂ] ℋ)
  have h_odd : sys.K * sys.Q 0 + sys.Q 0 * sys.K = 0 := by
    change sys.K ∘L sys.Q 0 + sys.Q 0 ∘L sys.K = 0
    rw [sys.Q_odd 0, add_neg_cancel]
  have h_no_torsion : ∀ r : ℂ, r + r = 0 → r = 0 := fun r hr => by
    linear_combination (1 / 2 : ℂ) * hr
  have h0 : gradedTrace τ sys.K (sys.Q 0 * sys.Q 0) = 0 :=
    gradedTrace_odd_square_eq_zero τ hτ h_no_torsion h_odd
  have hH : sys.Q 0 * sys.Q 0 = sys.H := (sys.hamiltonian_eq_supercharge_sq 0).symm
  rw [hH] at h0
  exact h0

end AtiyahSingerLink

section FiniteSUSYLink

/-- Construct a genuine Hilbert-space `SUSYQuantumSystem 1` on
`WithLp 2 (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m))` from a `FiniteSUSYSystem m`
with `F.A_dag = F.Aᴴ`. Its Hamiltonian equals `blockDiag (F.H_plus) (F.H_minus)` directly. -/
def ofFiniteSUSYSystem (m : ℕ) (F : FiniteSUSYSystem m) (h_herm : F.A_dag = F.Aᴴ) :
    SUSYQuantumSystem 1 (WithLp 2 (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m))) :=
  let E := EuclideanSpace ℂ (Fin m)
  let ℋ := WithLp 2 (E × E)
  let A_op : E →L[ℂ] E := F.A.toEuclideanLin.toContinuousLinearMap
  let A_dag_op : E →L[ℂ] E := F.A_dag.toEuclideanLin.toContinuousLinearMap
  let K_op : ℋ →L[ℂ] ℋ :=
    { toFun := fun x => WithLp.toLp 2 (x.ofLp.1, -x.ofLp.2)
      map_add' := fun x y => WithLp.ofLp_injective 2 (Prod.ext rfl (neg_add x.ofLp.2 y.ofLp.2))
      map_smul' := fun _ _ => WithLp.ofLp_injective 2 (Prod.ext rfl (smul_neg _ _).symm)
      cont := by
        refine (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.continuous.comp ?_
        exact Continuous.prodMk
          (WithLp.fstL 2 ℂ E E).continuous
          ((WithLp.sndL 2 ℂ E E).continuous.neg) }
  let Q_op : ℋ →L[ℂ] ℋ :=
    { toFun := fun x => WithLp.toLp 2 (A_op x.ofLp.2, A_dag_op x.ofLp.1)
      map_add' := fun x y =>
        WithLp.ofLp_injective 2 (Prod.ext (map_add A_op _ _) (map_add A_dag_op _ _))
      map_smul' := fun c x =>
        WithLp.ofLp_injective 2 (Prod.ext (map_smul A_op c _) (map_smul A_dag_op c _))
      cont := by
        refine (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.continuous.comp ?_
        exact Continuous.prodMk
          (A_op.continuous.comp (WithLp.sndL 2 ℂ E E).continuous)
          (A_dag_op.continuous.comp (WithLp.fstL 2 ℂ E E).continuous) }
  let H_op : ℋ →L[ℂ] ℋ := Q_op ∘L Q_op
  have hAdag_adj : A_dag_op = A_op.adjoint := by
    ext x i
    have hM : F.A_dag.toEuclideanLin = F.A.toEuclideanLin.adjoint := by
      rw [h_herm, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (F.A_dag.toEuclideanLin x).ofLp i = (A_op.adjoint x).ofLp i
    rw [hM]
    rfl
  have hK_symm : ∀ x y : ℋ, ⟪K_op x, y⟫_ℂ = ⟪x, K_op y⟫_ℂ := fun x y => by
    change ⟪WithLp.toLp 2 (x.ofLp.1, -x.ofLp.2), y⟫_ℂ =
      ⟪x, WithLp.toLp 2 (y.ofLp.1, -y.ofLp.2)⟫_ℂ
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    simp only [inner_neg_left, inner_neg_right]
  have hQ_symm : ∀ x y : ℋ, ⟪Q_op x, y⟫_ℂ = ⟪x, Q_op y⟫_ℂ := fun x y => by
    change ⟪WithLp.toLp 2 (A_op x.ofLp.2, A_dag_op x.ofLp.1), y⟫_ℂ =
      ⟪x, WithLp.toLp 2 (A_op y.ofLp.2, A_dag_op y.ofLp.1)⟫_ℂ
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, hAdag_adj]
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_right, add_comm]
  { K := K_op
    K_selfAdjoint := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK_symm
    K_involution := by
      apply ContinuousLinearMap.ext; intro x
      apply WithLp.ofLp_injective 2
      exact Prod.ext rfl (neg_neg _)
    H := H_op
    H_selfAdjoint := by
      have hQ_sa : IsSelfAdjoint Q_op :=
        ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hQ_symm
      rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hQ_sa ⊢
      simp only [H_op, ContinuousLinearMap.adjoint_comp, hQ_sa]
    H_even := by
      apply ContinuousLinearMap.ext; intro x
      apply WithLp.ofLp_injective 2
      exact Prod.ext (by simp [H_op, Q_op, K_op]) (by simp [H_op, Q_op, K_op])
    Q := fun _ => Q_op
    Q_selfAdjoint := fun _ => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hQ_symm
    Q_odd := fun _ => by
      apply ContinuousLinearMap.ext; intro x
      apply WithLp.ofLp_injective 2
      exact Prod.ext (by simp [Q_op, K_op]) (by simp [Q_op, K_op]; exact (neg_neg _).symm)
    superalgebra := fun i j => by
      have hij : i = j := Subsingleton.elim i j
      subst hij
      simp only [↓reduceIte]
      rw [← two_smul ℂ H_op] }

/-- The Hamiltonian of `ofFiniteSUSYSystem m F h_herm` acts block-diagonally as
`F.H_plus = A * A_dag` on the bosonic block and `F.H_minus = A_dag * A` on the fermionic block. -/
theorem ofFiniteSUSYSystem_H_apply (m : ℕ) (F : FiniteSUSYSystem m) (h_herm : F.A_dag = F.Aᴴ)
    (x : WithLp 2 (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m))) :
    (ofFiniteSUSYSystem m F h_herm).H x =
      WithLp.toLp 2 (F.H_plus.toEuclideanLin x.ofLp.1, F.H_minus.toEuclideanLin x.ofLp.2) := by
  apply WithLp.ofLp_injective 2
  refine Prod.ext ?_ ?_
  · change F.A.toEuclideanLin (F.A_dag.toEuclideanLin x.ofLp.1) = F.H_plus.toEuclideanLin x.ofLp.1
    rw [FiniteSUSYSystem.h_plus_is_product, Matrix.toLpLin_mul_same]
    rfl
  · change F.A_dag.toEuclideanLin (F.A.toEuclideanLin x.ofLp.2) = F.H_minus.toEuclideanLin x.ofLp.2
    rw [FiniteSUSYSystem.h_minus_is_product, Matrix.toLpLin_mul_same]
    rfl

/-- Transport a `SUSYQuantumSystem n ℋ₁` along a linear isometry equivalence `e : ℋ₁ ≃ₗᵢ[ℂ] ℋ₂`. -/
def SUSYQuantumSystem.mapIso {n : ℕ} {ℋ₁ ℋ₂ : Type*}
    [NormedAddCommGroup ℋ₁] [InnerProductSpace ℂ ℋ₁] [CompleteSpace ℋ₁]
    [NormedAddCommGroup ℋ₂] [InnerProductSpace ℂ ℋ₂] [CompleteSpace ℋ₂]
    (sys : SUSYQuantumSystem n ℋ₁) (e : ℋ₁ ≃ₗᵢ[ℂ] ℋ₂) :
    SUSYQuantumSystem n ℋ₂ :=
  let conjOp (T : ℋ₁ →L[ℂ] ℋ₁) : ℋ₂ →L[ℂ] ℋ₂ :=
    e.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have conj_symm : ∀ {T : ℋ₁ →L[ℂ] ℋ₁}, IsSelfAdjoint T → IsSelfAdjoint (conjOp T) := by
    intro T hT
    refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
    change ⟪e (T (e.symm x)), y⟫_ℂ = ⟪x, e (T (e.symm y))⟫_ℂ
    calc
      ⟪e (T (e.symm x)), y⟫_ℂ = ⟪e (T (e.symm x)), e (e.symm y)⟫_ℂ := by
        rw [e.apply_symm_apply]
      _ = ⟪T (e.symm x), e.symm y⟫_ℂ := e.inner_map_map _ _
      _ = ⟪e.symm x, T (e.symm y)⟫_ℂ := hT.isSymmetric _ _
      _ = ⟪e (e.symm x), e (T (e.symm y))⟫_ℂ := (e.inner_map_map _ _).symm
      _ = ⟪x, e (T (e.symm y))⟫_ℂ := by rw [e.apply_symm_apply]
  have conj_comp : ∀ A B : ℋ₁ →L[ℂ] ℋ₁, conjOp A ∘L conjOp B = conjOp (A ∘L B) := by
    intro A B
    ext x
    simp [conjOp]
  { K := conjOp sys.K
    K_selfAdjoint := conj_symm sys.K_selfAdjoint
    K_involution := by
      rw [conj_comp, sys.K_involution]
      ext x
      simp [conjOp]
    H := conjOp sys.H
    H_selfAdjoint := conj_symm sys.H_selfAdjoint
    H_even := by
      rw [conj_comp, conj_comp, sys.H_even]
    Q := fun i => conjOp (sys.Q i)
    Q_selfAdjoint := fun i => conj_symm (sys.Q_selfAdjoint i)
    Q_odd := fun i => by
      rw [conj_comp, conj_comp, sys.Q_odd i]
      ext x
      simp [conjOp]
    superalgebra := fun i j => by
      rw [conj_comp, conj_comp]
      ext x
      have h := ContinuousLinearMap.ext_iff.mp (sys.superalgebra i j) (e.symm x)
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply] at h
      change e (sys.Q i (sys.Q j (e.symm x))) + e (sys.Q j (sys.Q i (e.symm x))) =
        (if i = j then (2 : ℂ) else 0) • e (sys.H (e.symm x))
      rw [← map_add, h]
      split_ifs <;> simp [map_smul] }

end FiniteSUSYLink

end RepoLinks

end InfoGeometry.Quantum.SUSYHilbertWittenIndex

/-!
## Closed T17 Constructive Inhabitants and T16 Non-Commutativity Witnesses

Placed outside sections with ambient `variable`s and without `[InnerProductSpace]` binders
so every declared structure has a closed constructive inhabitant and every active operator
and matrix carrier has a closed non-commutativity witness.
-/

namespace InfoGeometry.Quantum.SUSYHilbertWittenIndex

open scoped InnerProductSpace Matrix
open InfoGeometry.Algebra.FiniteSUSY

/-- Pauli X matrix (2×2 complex). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli Y matrix (2×2 complex). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z matrix (2×2 complex). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- T16 matrix non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`: `σ_x * σ_z ≠ σ_z * σ_x`. -/
theorem pauliX_pauliZ_noncomm : pauliX * pauliZ ≠ pauliZ * pauliX := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

private lemma mat2_isSelfAdjoint_of_herm {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A) :
    IsSelfAdjoint A.toEuclideanLin.toContinuousLinearMap := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  ext x i
  have h_adj : A.toEuclideanLin.toContinuousLinearMap.adjoint =
      Aᴴ.toEuclideanLin.toContinuousLinearMap := by
    ext y j
    have hM := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
    change (A.toEuclideanLin.toContinuousLinearMap.adjoint y).ofLp j =
      (Aᴴ.toEuclideanLin y).ofLp j
    rw [hM]
    rfl
  rw [h_adj, hA]

private lemma pauliZ_isSelfAdjoint :
    IsSelfAdjoint pauliZ.toEuclideanLin.toContinuousLinearMap := by
  refine mat2_isSelfAdjoint_of_herm ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

private lemma pauliZ_involution :
    pauliZ.toEuclideanLin.toContinuousLinearMap ∘L pauliZ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) := by
  ext x i
  fin_cases i <;>
    simp [pauliZ, ContinuousLinearMap.comp_apply, Matrix.ofLp_toLpLin,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Closed T17 inhabitant of `SuperHilbertSpace` on `EuclideanSpace ℂ (Fin 2)` via `σ_z`. -/
def canonicalTwoLevelSuperHilbert : SuperHilbertSpace (EuclideanSpace ℂ (Fin 2)) where
  K := pauliZ.toEuclideanLin.toContinuousLinearMap
  K_selfAdjoint := pauliZ_isSelfAdjoint
  K_involution := pauliZ_involution

private lemma pauliX_isSelfAdjoint :
    IsSelfAdjoint pauliX.toEuclideanLin.toContinuousLinearMap := by
  refine mat2_isSelfAdjoint_of_herm ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

private lemma pauliY_isSelfAdjoint :
    IsSelfAdjoint pauliY.toEuclideanLin.toContinuousLinearMap := by
  refine mat2_isSelfAdjoint_of_herm ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY]

private lemma twoLevel_Q_selfAdjoint (i : Fin 2) :
    IsSelfAdjoint ((if i = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap) := by
  fin_cases i
  · exact pauliX_isSelfAdjoint
  · exact pauliY_isSelfAdjoint

private lemma twoLevel_Q_odd (i : Fin 2) :
    (if i = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap ∘L
        pauliZ.toEuclideanLin.toContinuousLinearMap =
      -(pauliZ.toEuclideanLin.toContinuousLinearMap ∘L
        (if i = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap) := by
  fin_cases i <;> ext x j <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, ContinuousLinearMap.comp_apply, Matrix.ofLp_toLpLin,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma twoLevel_superalgebra (i j : Fin 2) :
    (if i = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap ∘L
        (if j = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap +
      (if j = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap ∘L
        (if i = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap =
      (if i = j then (2 : ℂ) else 0) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) := by
  fin_cases i <;> fin_cases j <;> ext x k <;> fin_cases k <;>
    simp [pauliX, pauliY, ContinuousLinearMap.comp_apply, Matrix.ofLp_toLpLin,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, two_smul] <;>
    (try (rw [← mul_assoc, Complex.I_mul_I]; ring))

private lemma id_isSelfAdjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : IsSelfAdjoint (ContinuousLinearMap.id ℂ E) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr ContinuousLinearMap.adjoint_id

/-- Closed T17 inhabitant of `SUSYQuantumSystem 2 (EuclideanSpace ℂ (Fin 2))` with
`K = σ_z`, `Q₀ = σ_x`, `Q₁ = σ_y`, and `H = I`. -/
def canonicalTwoLevelSUSY : SUSYQuantumSystem 2 (EuclideanSpace ℂ (Fin 2)) where
  K := pauliZ.toEuclideanLin.toContinuousLinearMap
  K_selfAdjoint := pauliZ_isSelfAdjoint
  K_involution := pauliZ_involution
  H := ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))
  H_selfAdjoint := id_isSelfAdjoint
  H_even := rfl
  Q i := (if i = 0 then pauliX else pauliY).toEuclideanLin.toContinuousLinearMap
  Q_selfAdjoint := twoLevel_Q_selfAdjoint
  Q_odd := twoLevel_Q_odd
  superalgebra := twoLevel_superalgebra

private lemma twoLevel_energy_pos_of_ne (m : Fin 2) (hm : m ≠ 0) :
    0 < (![(0 : ℝ), 1] : Fin 2 → ℝ) m := by
  fin_cases m
  · exact absurd rfl hm
  · norm_num

private lemma twoLevel_finiteDim_level (m : Fin 2) :
    FiniteDimensional ℂ (canonicalTwoLevelSUSY.energyEigenspace ((![(0 : ℝ), 1] : Fin 2 → ℝ) m)) :=
  inferInstance

private lemma twoLevel_eigenspaces_dense :
    (⨆ m : Fin 2, canonicalTwoLevelSUSY.energyEigenspace ((![(0 : ℝ), 1] : Fin 2 → ℝ) m))ᗮ = ⊥ := by
  have h1 : canonicalTwoLevelSUSY.energyEigenspace 1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    simp [SUSYQuantumSystem.mem_energyEigenspace_iff, canonicalTwoLevelSUSY]
  have hsup : (⨆ m : Fin 2, canonicalTwoLevelSUSY.energyEigenspace ((![(0 : ℝ), 1] : Fin 2 → ℝ) m)) = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    exact le_iSup (fun m : Fin 2 =>
      canonicalTwoLevelSUSY.energyEigenspace ((![(0 : ℝ), 1] : Fin 2 → ℝ) m)) 1 (by simp [h1])
  rw [hsup, Submodule.top_orthogonal_eq_bot]

/-- Closed T17 inhabitant of `DiscreteSUSYSpectrum` on the 2-level Pauli system. -/
def canonicalTwoLevelSpectrum :
    DiscreteSUSYSpectrum 2 (EuclideanSpace ℂ (Fin 2)) (Fin 2) canonicalTwoLevelSUSY where
  energy := ![0, 1]
  zeroIdx := 0
  energy_zeroIdx := rfl
  energy_pos_of_ne := twoLevel_energy_pos_of_ne
  finiteDim_level := twoLevel_finiteDim_level
  eigenspaces_dense := twoLevel_eigenspaces_dense

theorem canonicalTwoLevelSUSY_wittenIndex_eq_zero :
    canonicalTwoLevelSUSY.wittenIndex = 0 := by
  have hbot : canonicalTwoLevelSUSY.energyEigenspace 0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [SUSYQuantumSystem.mem_energyEigenspace_iff] at hx
    simpa [canonicalTwoLevelSUSY] using hx
  have hb : canonicalTwoLevelSUSY.bosonicEigenspace 0 = ⊥ := by
    simp [SUSYQuantumSystem.bosonicEigenspace, hbot]
  have hf : canonicalTwoLevelSUSY.fermionicEigenspace 0 = ⊥ := by
    simp [SUSYQuantumSystem.fermionicEigenspace, hbot]
  rw [SUSYQuantumSystem.wittenIndex, SUSYQuantumSystem.levelWittenDiff,
    SUSYQuantumSystem.levelBosonDim, SUSYQuantumSystem.levelFermionDim, hb, hf]
  simp

theorem canonicalTwoLevelSpectrum_thermalSupertrace_eq_zero (β : ℝ) :
    canonicalTwoLevelSUSY.thermalSupertrace canonicalTwoLevelSpectrum β = 0 := by
  rw [canonicalTwoLevelSUSY.witten_index_eq_thermal_supertrace canonicalTwoLevelSpectrum β,
    canonicalTwoLevelSUSY_wittenIndex_eq_zero, Int.cast_zero]

/-! ### 3-Level `N = 1` Witness with Non-Zero Witten Index `n_0 = 1` -/

private def threeLevelK_op : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  { toFun := fun x => WithLp.toLp 2 ![x 0, x 1, -x 2]
    map_add' := fun x y => by ext i; fin_cases i <;> simp [add_comm]
    map_smul' := fun c x => by ext i; fin_cases i <;> simp
    cont := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 0
      · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 1
      · exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 2).neg }

private def threeLevelQ_op : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  { toFun := fun x => WithLp.toLp 2 ![0, x 2, x 1]
    map_add' := fun x y => by ext i; fin_cases i <;> simp
    map_smul' := fun c x => by ext i; fin_cases i <;> simp
    cont := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact continuous_const
      · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 2
      · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 1 }

private def threeLevelH_op : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  threeLevelQ_op ∘L threeLevelQ_op

private lemma threeLevelK_selfAdjoint : IsSelfAdjoint threeLevelK_op := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  simp only [PiLp.inner_apply, Fin.sum_univ_three, threeLevelK_op,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp [add_assoc]

private lemma threeLevelK_involution :
    threeLevelK_op ∘L threeLevelK_op = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 3)) := by
  ext x i
  fin_cases i <;> simp [threeLevelK_op, ContinuousLinearMap.comp_apply]

private lemma threeLevelQ_selfAdjoint : ∀ _ : Fin 1, IsSelfAdjoint threeLevelQ_op := fun _ => by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  simp only [PiLp.inner_apply, Fin.sum_univ_three, threeLevelQ_op,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp [add_comm]

private lemma threeLevelH_selfAdjoint : IsSelfAdjoint threeLevelH_op := by
  have hQ := threeLevelQ_selfAdjoint 0
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hQ ⊢
  simp [threeLevelH_op, ContinuousLinearMap.adjoint_comp, hQ]

private lemma threeLevelQ_odd :
    ∀ _ : Fin 1, threeLevelQ_op ∘L threeLevelK_op = -(threeLevelK_op ∘L threeLevelQ_op) :=
  fun _ => by
    ext x i
    fin_cases i <;> simp [threeLevelQ_op, threeLevelK_op, ContinuousLinearMap.comp_apply]

private lemma threeLevelH_even :
    threeLevelH_op ∘L threeLevelK_op = threeLevelK_op ∘L threeLevelH_op := by
  ext x i
  fin_cases i <;> simp [threeLevelH_op, threeLevelQ_op, threeLevelK_op, ContinuousLinearMap.comp_apply]

private lemma threeLevel_superalgebra (i j : Fin 1) :
    threeLevelQ_op ∘L threeLevelQ_op + threeLevelQ_op ∘L threeLevelQ_op =
      (if i = j then (2 : ℂ) else 0) • threeLevelH_op := by
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp only [↓reduceIte]
  rw [← two_smul ℂ (threeLevelQ_op ∘L threeLevelQ_op)]
  rfl

/-- Closed 3-level `N = 1` SUSY witness with one unpaired zero-energy bosonic state (`n_0 = 1`). -/
def canonicalThreeLevelIndexOneSUSY : SUSYQuantumSystem 1 (EuclideanSpace ℂ (Fin 3)) where
  K := threeLevelK_op
  K_selfAdjoint := threeLevelK_selfAdjoint
  K_involution := threeLevelK_involution
  H := threeLevelH_op
  H_selfAdjoint := threeLevelH_selfAdjoint
  H_even := threeLevelH_even
  Q _ := threeLevelQ_op
  Q_selfAdjoint := threeLevelQ_selfAdjoint
  Q_odd := threeLevelQ_odd
  superalgebra := threeLevel_superalgebra

theorem canonicalThreeLevelIndexOneSUSY_wittenIndex_eq_one :
    canonicalThreeLevelIndexOneSUSY.wittenIndex = 1 := by
  have h_bose_eq : canonicalThreeLevelIndexOneSUSY.bosonicEigenspace 0 =
      Submodule.span ℂ {PiLp.single 2 (0 : Fin 3) (1 : ℂ)} := by
    apply le_antisymm
    · intro x hx
      rw [SUSYQuantumSystem.mem_bosonicEigenspace_iff] at hx
      have hH0 : threeLevelH_op x = 0 := by simpa [canonicalThreeLevelIndexOneSUSY] using hx.1
      have hx1 : x 1 = 0 := by
        have h := congr_arg (fun v : EuclideanSpace ℂ (Fin 3) => v 1) hH0
        simpa [threeLevelH_op, threeLevelQ_op, ContinuousLinearMap.comp_apply] using h
      have hx2 : x 2 = 0 := by
        have h := congr_arg (fun v : EuclideanSpace ℂ (Fin 3) => v 2) hH0
        simpa [threeLevelH_op, threeLevelQ_op, ContinuousLinearMap.comp_apply] using h
      have hxeq : x = x 0 • PiLp.single 2 (0 : Fin 3) (1 : ℂ) := by
        ext i
        fin_cases i <;> simp [hx1, hx2]
      rw [hxeq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, SUSYQuantumSystem.mem_bosonicEigenspace_iff]
      refine ⟨?_, ?_⟩
      · ext i; fin_cases i <;>
          simp [canonicalThreeLevelIndexOneSUSY, threeLevelH_op, threeLevelQ_op,
            ContinuousLinearMap.comp_apply]
      · ext i; fin_cases i <;>
          simp [canonicalThreeLevelIndexOneSUSY, threeLevelK_op]
  have h_fermi_eq : canonicalThreeLevelIndexOneSUSY.fermionicEigenspace 0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [SUSYQuantumSystem.mem_fermionicEigenspace_iff] at hx
    have hH0 : threeLevelH_op x = 0 := by simpa [canonicalThreeLevelIndexOneSUSY] using hx.1
    have hK0 : threeLevelK_op x = -x := by simpa [canonicalThreeLevelIndexOneSUSY] using hx.2
    have hx0 : x 0 = 0 := by
      have h := congr_arg (fun v : EuclideanSpace ℂ (Fin 3) => v 0) hK0
      simp [threeLevelK_op] at h
      exact CharZero.eq_neg_self_iff.mp h
    have hx1 : x 1 = 0 := by
      have h := congr_arg (fun v : EuclideanSpace ℂ (Fin 3) => v 1) hH0
      simpa [threeLevelH_op, threeLevelQ_op, ContinuousLinearMap.comp_apply] using h
    have hx2 : x 2 = 0 := by
      have h := congr_arg (fun v : EuclideanSpace ℂ (Fin 3) => v 2) hH0
      simpa [threeLevelH_op, threeLevelQ_op, ContinuousLinearMap.comp_apply] using h
    ext i
    fin_cases i <;> simp [hx0, hx1, hx2]
  have h_bose_dim : canonicalThreeLevelIndexOneSUSY.levelBosonDim 0 = 1 := by
    rw [SUSYQuantumSystem.levelBosonDim, h_bose_eq, finrank_span_singleton]
    intro h0
    have h := congr_arg (fun v : EuclideanSpace ℂ (Fin 3) => v 0) h0
    simp at h
  have h_fermi_dim : canonicalThreeLevelIndexOneSUSY.levelFermionDim 0 = 0 := by
    simp [SUSYQuantumSystem.levelFermionDim, h_fermi_eq]
  simp [SUSYQuantumSystem.wittenIndex, SUSYQuantumSystem.levelWittenDiff, h_bose_dim, h_fermi_dim]

/-! ### `2^(k+1)`-Level Fermion Oscillator Family `(k : ℕ)` -/

private def flipParityIdx (k : ℕ) (j : Fin (2 ^ (k + 1))) : Fin (2 ^ (k + 1)) :=
  ⟨if j.val % 2 = 0 then j.val + 1 else j.val - 1, by
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
    have hj : j.val < 2 * 2 ^ k := h2 ▸ j.isLt
    split_ifs with h
    · have : j.val % 2 = 0 := h
      omega
    · omega⟩

private lemma flipParityIdx_invol (k : ℕ) (j : Fin (2 ^ (k + 1))) :
    flipParityIdx k (flipParityIdx k j) = j := by
  ext
  simp only [flipParityIdx]
  split_ifs with h1 h2 h2 <;> omega

private lemma flipParityIdx_mod_two (k : ℕ) (j : Fin (2 ^ (k + 1))) :
    (flipParityIdx k j).val % 2 ≠ j.val % 2 := by
  simp only [flipParityIdx]
  split_ifs with h <;> omega

private def fermionicOscillatorK (k : ℕ) :
    EuclideanSpace ℂ (Fin (2 ^ (k + 1))) →L[ℂ] EuclideanSpace ℂ (Fin (2 ^ (k + 1))) where
  toFun x := WithLp.toLp 2 fun j => (if j.val % 2 = 0 then (1 : ℂ) else -1) * x j
  map_add' x y := by ext j; simp [mul_add]
  map_smul' c x := by ext j; simp [mul_left_comm]
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin (2 ^ (k + 1)) => ℂ)).comp (continuous_pi fun j =>
    continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin (2 ^ (k + 1)) => ℂ) j))

private def fermionicOscillatorQ (k : ℕ) :
    EuclideanSpace ℂ (Fin (2 ^ (k + 1))) →L[ℂ] EuclideanSpace ℂ (Fin (2 ^ (k + 1))) where
  toFun x := WithLp.toLp 2 fun j => x (flipParityIdx k j)
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin (2 ^ (k + 1)) => ℂ)).comp (continuous_pi fun j =>
    PiLp.continuous_apply 2 (fun _ : Fin (2 ^ (k + 1)) => ℂ) (flipParityIdx k j))

private lemma fermionicOscillatorK_selfAdjoint (k : ℕ) :
    IsSelfAdjoint (fermionicOscillatorK k) := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  simp only [PiLp.inner_apply, fermionicOscillatorK, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

private lemma fermionicOscillatorK_involution (k : ℕ) :
    fermionicOscillatorK k ∘L fermionicOscillatorK k =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (2 ^ (k + 1)))) := by
  ext x j
  simp only [fermionicOscillatorK, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  split_ifs <;> simp

private lemma fermionicOscillatorQ_selfAdjoint (k : ℕ) :
    ∀ _ : Fin 1, IsSelfAdjoint (fermionicOscillatorQ k) := fun _ => by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  simp only [PiLp.inner_apply, fermionicOscillatorQ, LinearMap.coe_mk, AddHom.coe_mk]
  let e : Fin (2 ^ (k + 1)) ≃ Fin (2 ^ (k + 1)) :=
    ⟨flipParityIdx k, flipParityIdx k, flipParityIdx_invol k, flipParityIdx_invol k⟩
  refine Finset.sum_equiv e (fun _ => by simp) fun j _ => ?_
  simp [e, flipParityIdx_invol]

private lemma fermionicOscillatorQ_odd (k : ℕ) :
    ∀ _ : Fin 1, fermionicOscillatorQ k ∘L fermionicOscillatorK k =
      -(fermionicOscillatorK k ∘L fermionicOscillatorQ k) := fun _ => by
  ext x j
  simp only [fermionicOscillatorQ, fermionicOscillatorK, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  have hmod := flipParityIdx_mod_two k j
  have h_cases : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  rcases h_cases with h0 | h1
  · have hfp : (flipParityIdx k j).val % 2 = 1 := by omega
    simp [h0, hfp]
  · have hfp : (flipParityIdx k j).val % 2 = 0 := by omega
    simp [h1, hfp]

private lemma fermionicOscillator_superalgebra (k : ℕ) (i j : Fin 1) :
    fermionicOscillatorQ k ∘L fermionicOscillatorQ k +
        fermionicOscillatorQ k ∘L fermionicOscillatorQ k =
      (if i = j then (2 : ℂ) else 0) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (2 ^ (k + 1)))) := by
  have hij : i = j := Subsingleton.elim i j
  subst hij
  have hsq : fermionicOscillatorQ k ∘L fermionicOscillatorQ k =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (2 ^ (k + 1)))) := by
    ext x m
    simp [fermionicOscillatorQ, ContinuousLinearMap.comp_apply, flipParityIdx_invol]
  rw [hsq]
  simp only [↓reduceIte]
  rw [← two_smul ℂ (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (2 ^ (k + 1)))))]

/-- Closed T17 inhabitant family on `EuclideanSpace ℂ (Fin (2 ^ (k + 1)))` (`2^(k+1)`-level
fermion oscillator). -/
def fermionicOscillatorSUSY (k : ℕ) :
    SUSYQuantumSystem 1 (EuclideanSpace ℂ (Fin (2 ^ (k + 1)))) where
  K := fermionicOscillatorK k
  K_selfAdjoint := fermionicOscillatorK_selfAdjoint k
  K_involution := fermionicOscillatorK_involution k
  H := ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (2 ^ (k + 1))))
  H_selfAdjoint := id_isSelfAdjoint
  H_even := rfl
  Q _ := fermionicOscillatorQ k
  Q_selfAdjoint := fermionicOscillatorQ_selfAdjoint k
  Q_odd := fermionicOscillatorQ_odd k
  superalgebra := fermionicOscillator_superalgebra k

/-! ### `FiniteSUSYBlocks` Realization on `EuclideanSpace ℂ (Fin 4)` -/

private lemma canonicalFiniteSUSY_herm :
    canonicalFiniteSUSYSystem.A_dag = canonicalFiniteSUSYSystem.Aᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalFiniteSUSYSystem, superchargeA, superchargeAdag,
      InfoGeometry.Algebra.FiniteSpin.J_minus, InfoGeometry.Algebra.FiniteSpin.J_plus]

private def prodFin2ToFin4 (x : WithLp 2 (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2))) :
    EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 ![x.ofLp.1 0, x.ofLp.1 1, x.ofLp.2 0, x.ofLp.2 1]

private def fin4ToProdFin2 (y : EuclideanSpace ℂ (Fin 4)) :
    WithLp 2 (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :=
  WithLp.toLp 2 (WithLp.toLp 2 ![y 0, y 1], WithLp.toLp 2 ![y 2, y 3])

private def prodFin2EquivFin4 :
    WithLp 2 (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4) where
  toFun := prodFin2ToFin4
  invFun := fin4ToProdFin2
  map_add' x y := by ext i; fin_cases i <;> simp [prodFin2ToFin4]
  map_smul' c x := by ext i; fin_cases i <;> simp [prodFin2ToFin4]
  left_inv x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;>
      · ext i; fin_cases i <;> simp [prodFin2ToFin4, fin4ToProdFin2]
  right_inv y := by ext i; fin_cases i <;> simp [prodFin2ToFin4, fin4ToProdFin2]
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    dsimp [prodFin2ToFin4]
    simp [Fin.sum_univ_four, Fin.sum_univ_two]
    ring

/-- Closed `FiniteSUSYBlocks` realization as a `SUSYQuantumSystem 1` on `EuclideanSpace ℂ (Fin 4)`. -/
def canonicalFiniteSUSYBlockRealization : SUSYQuantumSystem 1 (EuclideanSpace ℂ (Fin 4)) :=
  (ofFiniteSUSYSystem 2 canonicalFiniteSUSYSystem canonicalFiniteSUSY_herm).mapIso prodFin2EquivFin4

/-! ### T16 Non-Commutativity Witnesses -/

/-- Any non-zero supercharge fails to commute with the grading operator (`Q_i ∘L K ≠ K ∘L Q_i`). -/
theorem supercharge_not_commute_grading {n : ℕ} {ℋ : Type*}
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (sys : SUSYQuantumSystem n ℋ) (i : Fin n) (hQ : sys.Q i ≠ 0) :
    sys.Q i ∘L sys.K ≠ sys.K ∘L sys.Q i := by
  intro hcomm
  have hodd : sys.Q i ∘L sys.K = -(sys.K ∘L sys.Q i) := sys.Q_odd i
  rw [hcomm] at hodd
  have h2 : (2 : ℂ) • (sys.K ∘L sys.Q i) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hodd
  have hKQ : sys.K ∘L sys.Q i = 0 :=
    smul_eq_zero.mp h2 |>.resolve_left (by norm_num)
  apply hQ
  calc
    sys.Q i = (sys.K ∘L sys.K) ∘L sys.Q i := by rw [sys.K_involution, ContinuousLinearMap.id_comp]
    _ = sys.K ∘L (sys.K ∘L sys.Q i) := by rw [ContinuousLinearMap.comp_assoc]
    _ = 0 := by rw [hKQ, ContinuousLinearMap.comp_zero]

/-- Multiplicative ring form of `supercharge_not_commute_grading`: `Q_i * K ≠ K * Q_i`. -/
theorem supercharge_mul_grading_ne_commute {n : ℕ} {ℋ : Type*}
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (sys : SUSYQuantumSystem n ℋ) (i : Fin n) (hQ : sys.Q i ≠ 0) :
    sys.Q i * sys.K ≠ sys.K * sys.Q i :=
  supercharge_not_commute_grading sys i hQ

/-- Closed T16 non-commutativity witness for `canonicalTwoLevelSUSY`: `Q₀ ∘L K ≠ K ∘L Q₀`. -/
theorem canonicalTwoLevelSUSY_Q0_K_noncomm :
    canonicalTwoLevelSUSY.Q 0 ∘L canonicalTwoLevelSUSY.K ≠
      canonicalTwoLevelSUSY.K ∘L canonicalTwoLevelSUSY.Q 0 := by
  refine supercharge_not_commute_grading canonicalTwoLevelSUSY 0 ?_
  intro h0
  have h := congr_arg (fun T => T (PiLp.single 2 (1 : Fin 2) (1 : ℂ)) 0) h0
  simp [canonicalTwoLevelSUSY, pauliX, Matrix.ofLp_toLpLin,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h

/-- Closed T16 multiplicative witness for `canonicalTwoLevelSUSY`: `Q₀ * K ≠ K * Q₀`. -/
theorem canonicalTwoLevelSUSY_Q0_K_mul_noncomm :
    canonicalTwoLevelSUSY.Q 0 * canonicalTwoLevelSUSY.K ≠
      canonicalTwoLevelSUSY.K * canonicalTwoLevelSUSY.Q 0 :=
  canonicalTwoLevelSUSY_Q0_K_noncomm

/-- Closed T16 non-commutativity witness between the two supercharges: `Q₀ ∘L Q₁ ≠ Q₁ ∘L Q₀`. -/
theorem canonicalTwoLevelSUSY_Q0_Q1_noncomm :
    canonicalTwoLevelSUSY.Q 0 ∘L canonicalTwoLevelSUSY.Q 1 ≠
      canonicalTwoLevelSUSY.Q 1 ∘L canonicalTwoLevelSUSY.Q 0 := by
  intro h
  have h0 := congr_arg (fun T => T (PiLp.single 2 (0 : Fin 2) (1 : ℂ)) 0) h
  simp [canonicalTwoLevelSUSY, pauliX, pauliY, ContinuousLinearMap.comp_apply,
    Matrix.ofLp_toLpLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  exact Complex.I_ne_zero (by linear_combination (1 / 2 : ℂ) * h0)

end InfoGeometry.Quantum.SUSYHilbertWittenIndex
