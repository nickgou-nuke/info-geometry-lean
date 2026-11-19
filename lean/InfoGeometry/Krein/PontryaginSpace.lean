/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Pontryagin Spaces, Indefinite $\eta$-Metrics, & Spectral Reflection (`S3-18`..`S3-22`)

Formalizes the foundational indefinite-metric operator theory of Pillar 4 (`M5`) in native
Mathlib v4.34.1 while preserving architectural principle `R3.1` (keeping indefinite Krein
pairings native without Wick rotation and keeping `J_Krein`, `Γ_grade`, and `J_real`
strictly distinct):

1. **`S3-21` Krein (1950, 1964)**: Fundamental decomposition `K = K₊ ⊕ K₋` on any real
   `InfoGeometry.Krein.KreinSpace`, orthogonal projectors `P₊, P₋`, `J = P₊ - P₋`,
   Hilbert vs. Krein orthogonality of `K₊` and `K₋`, and the `J`-Hilbertization identity.
2. **`S3-20` Pontryagin (1944)**: `PontryaginSpace` ($\Pi_\kappa$) extending `KreinSpace`
   with `FiniteDimensional ℝ (negSubspace H)`, non-aliased `PontryaginSum H₊ H₋`
   (allowing infinite-dimensional `H₊`), maximal nonpositive dimension bound `dim M ≤ κ`,
   and the real obstruction (`complex_i` on real $\Pi_1$ lacks a 1D real invariant subspace).
3. **`S3-18` Dirac (1942) & `S3-19` Pauli (1943)**: Indefinite ghost-state witness,
   general $\eta$-pseudo-Hermiticity (`η A = A† η`), biorthogonal eigenvector law
   `(star μ₁ - μ₂) * ⟪η v₁, v₂⟫ = 0`, nullness of non-real eigenvectors, and
   `ComplexKreinSpace` conjugate-pair spectral reflection (`σ(A) = star (σ(A))`).
4. **`S3-22` Iokhvidov–Krein (1956–1959)**: Real and complex $J$-unitary groups
   (`σ(U) = (star (σ(U)))⁻¹`), real $J$-Cayley transform, and complex $J$-Cayley transform
   $C_{z,\zeta}(H) = \zeta (H - z \mathbf{1})(H - \bar{z}\mathbf{1})^{-1}$.
5. **`S3-20` Pontryagin Invariant Subspace Theorem**: `ComplexPontryaginSpace`,
   general $\eta$-inertia & Sylvester's Law of Inertia, and a constructive finite-dimensional
   proof that every $J$-self-adjoint operator on $\Pi_\kappa$ admits a $\kappa$-dimensional
   maximal nonpositive invariant subspace.

## Evidence Boundary (`BUCKET 1/2/3`)
- `BUCKET 1/2`: Real & complex fundamental decompositions, bounded `η`-pseudo-Hermitian and
  `J`-unitary spectral symmetry, real & complex `J`-Cayley roundtrips, Sylvester inertia, and
  the finite-dimensional Pontryagin Invariant Subspace Theorem.
- `BUCKET 3` (`O-EXT`): Infinite-dimensional Pontryagin Invariant Subspace Theorem (compact
  corner / Schauder–Tikhonov fixed-point argument) and unbounded `J`-symmetric defect-index
  extensions remain outside the bounded/finite-dimensional scope of this module.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace InfoGeometry.Krein

/-! ## Part 1: Fundamental Decomposition & Real `J`-Cayley Transform (`S3-21`, `S3-22`, `R3.1`) -/

namespace KreinSpace

section FundamentalDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

/-- Positive fundamental subspace `K₊ = ker (J - I)` of a real `KreinSpace` (`S3-21`,
Krein 1950/1964; `R3.1`). -/
def posSubspace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] : Submodule ℝ H :=
  LinearMap.ker ((jCLM (H := H) : H →ₗ[ℝ] H) - LinearMap.id)

/-- Negative fundamental subspace `K₋ = ker (J + I)` of a real `KreinSpace` (`S3-21`,
Krein 1950/1964; `R3.1`). -/
def negSubspace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] : Submodule ℝ H :=
  LinearMap.ker ((jCLM (H := H) : H →ₗ[ℝ] H) + LinearMap.id)

/-- Membership characterization for `posSubspace`: `x ∈ K₊ ↔ J x = x` (`S3-21`, `R3.1`). -/
@[simp] theorem mem_posSubspace_iff (x : H) :
    x ∈ posSubspace H ↔ (J : H ≃ₗᵢ[ℝ] H) x = x := by
  simp [posSubspace, LinearMap.mem_ker, sub_eq_zero, jCLM_apply]

/-- Membership characterization for `negSubspace`: `x ∈ K₋ ↔ J x = -x` (`S3-21`, `R3.1`). -/
@[simp] theorem mem_negSubspace_iff (x : H) :
    x ∈ negSubspace H ↔ (J : H ≃ₗᵢ[ℝ] H) x = -x := by
  simp [negSubspace, LinearMap.mem_ker, add_eq_zero_iff_eq_neg, jCLM_apply]

/-- `posSubspace H` is norm-closed (`S3-21`, `R3.1`). -/
theorem isClosed_posSubspace : IsClosed (posSubspace H : Set H) := by
  have hker : posSubspace H = ((jCLM (H := H) - ContinuousLinearMap.id ℝ H).ker) := rfl
  rw [hker]
  exact (jCLM (H := H) - ContinuousLinearMap.id ℝ H).isClosed_ker

/-- `negSubspace H` is norm-closed (`S3-21`, `R3.1`). -/
theorem isClosed_negSubspace : IsClosed (negSubspace H : Set H) := by
  have hker : negSubspace H = ((jCLM (H := H) + ContinuousLinearMap.id ℝ H).ker) := rfl
  rw [hker]
  exact (jCLM (H := H) + ContinuousLinearMap.id ℝ H).isClosed_ker

instance instCompleteSpace_posSubspace : CompleteSpace (posSubspace H) :=
  (isClosed_posSubspace (H := H)).completeSpace_coe

instance instCompleteSpace_negSubspace : CompleteSpace (negSubspace H) :=
  (isClosed_negSubspace (H := H)).completeSpace_coe

/-- Difference of Krein projectors recovers the fundamental symmetry `P₊ - P₋ = J` (`S3-21`,
`R3.1`). -/
theorem P_plus_sub_P_minus : P_plus (H := H) - P_minus (H := H) = jCLM (H := H) :=
  InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus_sub_peirceMinus (R := ℝ) (jCLM (H := H))

/-- Pointwise decomposition `P₊ x + P₋ x = x` (`S3-21`, `R3.1`). -/
theorem P_plus_add_P_minus_apply (x : H) :
    P_plus (H := H) x + P_minus (H := H) x = x := by
  have h := congrArg (fun T : H →L[ℝ] H => T x) (discharge_completeness (H := H))
  simpa using h

/-- `P₊` is idempotent: `P₊ ∘ P₊ = P₊` (`S3-21`, `R3.1`). -/
@[simp] theorem P_plus_sq : P_plus (H := H) * P_plus (H := H) = P_plus (H := H) :=
  (kreinSplitInvolution (H := H)).P_plus_sq

/-- `P₋` is idempotent: `P₋ ∘ P₋ = P₋` (`S3-21`, `R3.1`). -/
@[simp] theorem P_minus_sq : P_minus (H := H) * P_minus (H := H) = P_minus (H := H) :=
  (kreinSplitInvolution (H := H)).P_minus_sq

/-- Cross-annihilation `P₊ ∘ P₋ = 0` (`S3-21`, `R3.1`). -/
@[simp] theorem P_plus_mul_P_minus : P_plus (H := H) * P_minus (H := H) = 0 :=
  (kreinSplitInvolution (H := H)).P_plus_mul_P_minus

/-- Cross-annihilation `P₋ ∘ P₊ = 0` (`S3-21`, `R3.1`). -/
@[simp] theorem P_minus_mul_P_plus : P_minus (H := H) * P_plus (H := H) = 0 :=
  (kreinSplitInvolution (H := H)).P_minus_mul_P_plus

/-- `P₊` is Hilbert-self-adjoint (`S3-21`, `R3.1`). -/
@[simp] theorem adjoint_P_plus :
    ContinuousLinearMap.adjoint (P_plus (H := H)) = P_plus (H := H) := by
  change ContinuousLinearMap.adjoint
      ((⅟(2 : ℝ)) • (ContinuousLinearMap.id ℝ H + jCLM (H := H))) =
    (⅟(2 : ℝ)) • (ContinuousLinearMap.id ℝ H + jCLM (H := H))
  rw [map_smul, map_add, ContinuousLinearMap.adjoint_id, adjoint_jCLM]

/-- `P₋` is Hilbert-self-adjoint (`S3-21`, `R3.1`). -/
@[simp] theorem adjoint_P_minus :
    ContinuousLinearMap.adjoint (P_minus (H := H)) = P_minus (H := H) := by
  change ContinuousLinearMap.adjoint
      ((⅟(2 : ℝ)) • (ContinuousLinearMap.id ℝ H - jCLM (H := H))) =
    (⅟(2 : ℝ)) • (ContinuousLinearMap.id ℝ H - jCLM (H := H))
  rw [map_smul, map_sub, ContinuousLinearMap.adjoint_id, adjoint_jCLM]

/-- `P₊ x` lies in `posSubspace H` for every `x : H` (`S3-21`, `R3.1`). -/
theorem P_plus_mem_posSubspace (x : H) : P_plus (H := H) x ∈ posSubspace H := by
  rw [mem_posSubspace_iff]
  change (J : H ≃ₗᵢ[ℝ] H) ((⅟(2 : ℝ)) • (x + (J : H ≃ₗᵢ[ℝ] H) x)) =
    (⅟(2 : ℝ)) • (x + (J : H ≃ₗᵢ[ℝ] H) x)
  rw [map_smul, map_add, KreinSpace.J_invol, add_comm]

/-- `P₋ x` lies in `negSubspace H` for every `x : H` (`S3-21`, `R3.1`). -/
theorem P_minus_mem_negSubspace (x : H) : P_minus (H := H) x ∈ negSubspace H := by
  rw [mem_negSubspace_iff]
  change (J : H ≃ₗᵢ[ℝ] H) ((⅟(2 : ℝ)) • (x - (J : H ≃ₗᵢ[ℝ] H) x)) =
    -((⅟(2 : ℝ)) • (x - (J : H ≃ₗᵢ[ℝ] H) x))
  rw [map_smul, map_sub, KreinSpace.J_invol, ← smul_neg, neg_sub]

/-- `P₊ x = x` for every `x ∈ posSubspace H` (`S3-21`, `R3.1`). -/
theorem P_plus_eq_self_of_mem {x : H} (hx : x ∈ posSubspace H) : P_plus (H := H) x = x := by
  rw [mem_posSubspace_iff] at hx
  change (⅟(2 : ℝ)) • (x + (J : H ≃ₗᵢ[ℝ] H) x) = x
  rw [hx, ← two_smul ℝ x, smul_smul, invOf_mul_self, one_smul]

/-- `P₋ x = x` for every `x ∈ negSubspace H` (`S3-21`, `R3.1`). -/
theorem P_minus_eq_self_of_mem {x : H} (hx : x ∈ negSubspace H) : P_minus (H := H) x = x := by
  rw [mem_negSubspace_iff] at hx
  change (⅟(2 : ℝ)) • (x - (J : H ≃ₗᵢ[ℝ] H) x) = x
  rw [hx, sub_neg_eq_add, ← two_smul ℝ x, smul_smul, invOf_mul_self, one_smul]

/-- Fundamental direct-sum decomposition `K = K₊ ⊕ K₋` (`S3-21`, Krein 1950/1964; `R3.1`). -/
theorem posSubspace_isCompl_negSubspace : IsCompl (posSubspace H) (negSubspace H) := by
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨hxPos, hxNeg⟩
    change x ∈ posSubspace H at hxPos
    change x ∈ negSubspace H at hxNeg
    rw [mem_posSubspace_iff] at hxPos
    rw [mem_negSubspace_iff] at hxNeg
    have hneg : x = -x := hxPos.symm.trans hxNeg
    have h2 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rw 2 [hneg]
      exact add_neg_cancel x
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro x
    exact ⟨P_plus x, P_minus x, P_plus_mem_posSubspace x, P_minus_mem_negSubspace x,
      P_plus_add_P_minus_apply x⟩

/-- Hilbert orthogonality of `K₊` and `K₋`: `⟪x, y⟫_ℝ = 0` for `x ∈ K₊`, `y ∈ K₋` (`S3-21`,
`R3.1`). -/
theorem posSubspace_hilbert_orthogonal_negSubspace {x y : H}
    (hx : x ∈ posSubspace H) (hy : y ∈ negSubspace H) : ⟪x, y⟫_ℝ = 0 := by
  rw [mem_posSubspace_iff] at hx
  rw [mem_negSubspace_iff] at hy
  have heq : ⟪x, y⟫_ℝ = -⟪x, y⟫_ℝ := by
    calc
      ⟪x, y⟫_ℝ = ⟪(J : H ≃ₗᵢ[ℝ] H) x, y⟫_ℝ := by rw [hx]
      _ = ⟪x, (J : H ≃ₗᵢ[ℝ] H) y⟫_ℝ := KreinSpace.J_selfAdj x y
      _ = ⟪x, -y⟫_ℝ := by rw [hy]
      _ = -⟪x, y⟫_ℝ := inner_neg_right x y
  linarith

/-- Krein orthogonality of `K₊` and `K₋`: `[x, y]_J = 0` for `x ∈ K₊`, `y ∈ K₋` (`S3-21`,
`R3.1`). -/
theorem posSubspace_krein_orthogonal_negSubspace {x y : H}
    (hx : x ∈ posSubspace H) (hy : y ∈ negSubspace H) : kreinInner x y = 0 := by
  rw [kreinInner_def, (mem_posSubspace_iff x).mp hx]
  exact posSubspace_hilbert_orthogonal_negSubspace hx hy

/-- Strict positivity of the Krein pairing on nonzero vectors in `K₊` (`S3-18`, `S3-21`,
`R3.1`). -/
theorem kreinInner_pos_on_posSubspace {x : H} (hx : x ∈ posSubspace H) (hne : x ≠ 0) :
    0 < kreinInner x x := by
  rw [kreinInner_def, (mem_posSubspace_iff x).mp hx]
  exact real_inner_self_pos.mpr hne

/-- Strict negativity of the Krein pairing on nonzero vectors in `K₋` (`S3-18`, `S3-21`,
`R3.1`). -/
theorem kreinInner_neg_on_negSubspace {y : H} (hy : y ∈ negSubspace H) (hne : y ≠ 0) :
    kreinInner y y < 0 := by
  rw [kreinInner_def, (mem_negSubspace_iff y).mp hy, inner_neg_left]
  exact neg_lt_zero.mpr (real_inner_self_pos.mpr hne)

/-- `J`-Hilbertization identity `(u, v) = [P₊ u, P₊ v]_J - [P₋ u, P₋ v]_J` (`S3-21`,
Krein 1950/1964; `R3.1`). -/
theorem hilbertInner_eq_kreinInner_pos_sub_neg (u v : H) :
    ⟪u, v⟫_ℝ = kreinInner (P_plus u) (P_plus v) - kreinInner (P_minus u) (P_minus v) := by
  have hu : u = P_plus u + P_minus u := (P_plus_add_P_minus_apply u).symm
  have hv : v = P_plus v + P_minus v := (P_plus_add_P_minus_apply v).symm
  have h12 : ⟪P_plus u, P_minus v⟫_ℝ = 0 :=
    posSubspace_hilbert_orthogonal_negSubspace (P_plus_mem_posSubspace u) (P_minus_mem_negSubspace v)
  have h21 : ⟪P_minus u, P_plus v⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact posSubspace_hilbert_orthogonal_negSubspace (P_plus_mem_posSubspace v)
      (P_minus_mem_negSubspace u)
  have hp : kreinInner (P_plus u) (P_plus v) = ⟪P_plus u, P_plus v⟫_ℝ := by
    rw [kreinInner_def, (mem_posSubspace_iff _).mp (P_plus_mem_posSubspace u)]
  have hm : kreinInner (P_minus u) (P_minus v) = -⟪P_minus u, P_minus v⟫_ℝ := by
    rw [kreinInner_def, (mem_negSubspace_iff _).mp (P_minus_mem_negSubspace u), inner_neg_left]
  rw [hp, hm, sub_neg_eq_add]
  conv_lhs => rw [hu, hv]
  rw [inner_add_left, inner_add_right, inner_add_right, h12, h21]
  abel

/-- Orthogonal complement identity `(K₋)ᗮ = K₊` (`S3-21`, `R3.1`). -/
theorem orthogonal_negSubspace_eq_posSubspace : (negSubspace H)ᗮ = posSubspace H := by
  apply le_antisymm
  · intro x hx
    have hPm : P_minus (H := H) x = 0 := by
      have h0 : ⟪P_minus (H := H) x, P_minus (H := H) x⟫_ℝ = 0 := by
        have hmem := hx (P_minus x) (P_minus_mem_negSubspace x)
        rw [real_inner_comm] at hmem
        calc
          ⟪P_minus x, P_minus x⟫_ℝ = ⟪(P_plus x + P_minus x) - P_plus x, P_minus x⟫_ℝ := by
            rw [add_sub_cancel_left]
          _ = ⟪x - P_plus x, P_minus x⟫_ℝ := by rw [P_plus_add_P_minus_apply x]
          _ = ⟪x, P_minus x⟫_ℝ - ⟪P_plus x, P_minus x⟫_ℝ := inner_sub_left _ _ _
          _ = 0 - 0 := by
            rw [hmem, posSubspace_hilbert_orthogonal_negSubspace (P_plus_mem_posSubspace x)
                (P_minus_mem_negSubspace x)]
          _ = 0 := sub_zero 0
      exact inner_self_eq_zero.mp h0
    have hxEq : P_plus (H := H) x = x := by
      have h := P_plus_add_P_minus_apply x
      rw [hPm, add_zero] at h
      exact h
    rw [← hxEq]
    exact P_plus_mem_posSubspace x
  · intro x hx y hy
    rw [real_inner_comm]
    exact posSubspace_hilbert_orthogonal_negSubspace hx hy

/-- Orthogonal complement identity `(K₊)ᗮ = K₋` (`S3-21`, `R3.1`). -/
theorem orthogonal_posSubspace_eq_negSubspace : (posSubspace H)ᗮ = negSubspace H := by
  have hClosed : IsClosed (negSubspace H : Set H) := by
    have hEq : (negSubspace H : Set H) =
        {x : H | (jCLM (H := H) + ContinuousLinearMap.id ℝ H) x = 0} := by
      ext x
      rw [SetLike.mem_coe, mem_negSubspace_iff]
      simp only [Set.mem_ofPred_eq, add_apply, jCLM_apply,
        ContinuousLinearMap.id_apply, add_eq_zero_iff_eq_neg]
    rw [hEq]
    exact isClosed_eq (jCLM (H := H) + ContinuousLinearMap.id ℝ H).continuous continuous_const
  let _ : CompleteSpace (negSubspace H) := hClosed.completeSpace_coe
  let _ : (negSubspace H).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have h1 : ((negSubspace H)ᗮ)ᗮ = negSubspace H :=
    Submodule.orthogonal_orthogonal (negSubspace H)
  rw [← orthogonal_negSubspace_eq_posSubspace (H := H)]
  exact h1

/-- `P₊` coincides with the orthogonal star-projection onto `posSubspace H` (`S3-21`, `R3.1`). -/
theorem P_plus_eq_starProjection :
    P_plus (H := H) = (posSubspace H).starProjection := by
  ext x
  apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (P_plus_mem_posSubspace x) _).symm
  intro y hy
  have hsub : x - P_plus (H := H) x = P_minus (H := H) x := by
    calc
      x - P_plus (H := H) x = (P_plus (H := H) x + P_minus (H := H) x) - P_plus (H := H) x := by
        rw [P_plus_add_P_minus_apply]
      _ = P_minus (H := H) x := add_sub_cancel_left _ _
  rw [hsub, real_inner_comm]
  exact posSubspace_hilbert_orthogonal_negSubspace hy (P_minus_mem_negSubspace x)

/-- `P₋` coincides with the orthogonal star-projection onto `negSubspace H` (`S3-21`, `R3.1`). -/
theorem P_minus_eq_starProjection :
    P_minus (H := H) = (negSubspace H).starProjection := by
  ext x
  apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (P_minus_mem_negSubspace x) _).symm
  intro y hy
  have hsub : x - P_minus (H := H) x = P_plus (H := H) x := by
    calc
      x - P_minus (H := H) x = (P_plus (H := H) x + P_minus (H := H) x) - P_minus (H := H) x := by
        rw [P_plus_add_P_minus_apply]
      _ = P_plus (H := H) x := add_sub_cancel_right _ _
  rw [hsub]
  exact posSubspace_hilbert_orthogonal_negSubspace (P_plus_mem_posSubspace x) hy

/-! ### Real `J`-Unitary Operators & Real `J`-Cayley Transform (`S3-22`, `R3.1`) -/

/-- A bounded operator `U : H →L[ℝ] H` is **`J`-unitary** (Iokhvidov–Krein 1956, `S3-22`,
`R3.1`) when `U♯ ∘ U = 1` and `U ∘ U♯ = 1`. -/
def IsKreinUnitary (U : H →L[ℝ] H) : Prop :=
  (kreinAdjoint U).comp U = ContinuousLinearMap.id ℝ H ∧
    U.comp (kreinAdjoint U) = ContinuousLinearMap.id ℝ H

@[simp] theorem kreinAdjoint_one :
    kreinAdjoint (H := H) (1 : H →L[ℝ] H) = 1 :=
  kreinAdjoint_id (H := H)

/-- Characterization: `U` is `J`-unitary iff `U` is a unit and a Krein isometry (`S3-22`,
`R3.1`). -/
theorem isKreinUnitary_iff_isUnit_isKreinIsometry (U : H →L[ℝ] H) :
    IsKreinUnitary U ↔ IsUnit U ∧ IsKreinIsometry U := by
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨⟨⟨U, kreinAdjoint U, hR, hL⟩, rfl⟩, ?_⟩
    exact (isKreinIsometry_iff_star_comp_self U).mpr hL
  · rintro ⟨hUnit, hIso⟩
    have hL : (kreinAdjoint U).comp U = ContinuousLinearMap.id ℝ H :=
      (isKreinIsometry_iff_star_comp_self U).mp hIso
    refine ⟨hL, ?_⟩
    rcases hUnit with ⟨u, hu⟩
    have hinv : (u⁻¹ : (H →L[ℝ] H)ˣ).val = kreinAdjoint U := by
      have h1 : kreinAdjoint U * U = 1 := hL
      calc
        (u⁻¹ : (H →L[ℝ] H)ˣ).val = 1 * (u⁻¹ : (H →L[ℝ] H)ˣ).val := (one_mul _).symm
        _ = (kreinAdjoint U * U) * (u⁻¹ : (H →L[ℝ] H)ˣ).val := by rw [← h1]
        _ = kreinAdjoint U * (u.val * (u⁻¹ : (H →L[ℝ] H)ˣ).val) := by rw [← hu, mul_assoc]
        _ = kreinAdjoint U := by rw [Units.mul_inv, mul_one]
    rw [← hinv, ← hu]
    exact Units.mul_inv u

/-- Real `J`-Cayley transform `C(A) = (1 + A)(1 - A)⁻¹` mapping `J`-skew-adjoint operators
with `IsUnit (1 - A)` to `J`-unitary operators (`S3-22`, Iokhvidov–Krein 1956–1959; `R3.1`). -/
def realCayley (A : H →L[ℝ] H) (hInv : IsUnit (1 - A)) : H →L[ℝ] H :=
  (1 + A).comp (hInv.unit⁻¹ : (H →L[ℝ] H)ˣ).val

/-- Inverse real `J`-Cayley transform `C⁻¹(U) = (U - 1)(1 + U)⁻¹` (`S3-22`, `R3.1`). -/
def realCayleyInv (U : H →L[ℝ] H) (hInv : IsUnit (1 + U)) : H →L[ℝ] H :=
  (U - 1).comp (hInv.unit⁻¹ : (H →L[ℝ] H)ˣ).val

/-- For `IsKreinSkewAdjoint A` with `IsUnit (1 - A)`, `1 + A` is also a unit (`S3-22`, `R3.1`). -/
theorem isUnit_one_add_of_isKreinSkewAdjoint {A : H →L[ℝ] H}
    (hA : IsKreinSkewAdjoint A) (hInv : IsUnit (1 - A)) : IsUnit (1 + A) := by
  have hEq : kreinAdjoint (1 - A) = 1 + A := by
    rw [kreinAdjoint_sub, kreinAdjoint_one, hA, sub_neg_eq_add]
  rw [← hEq]
  refine ⟨⟨kreinAdjoint hInv.unit.val, kreinAdjoint (hInv.unit⁻¹ : (H →L[ℝ] H)ˣ).val, ?_, ?_⟩, rfl⟩
  · rw [← kreinAdjoint_mul, Units.inv_mul hInv.unit, kreinAdjoint_one]
  · rw [← kreinAdjoint_mul, Units.mul_inv hInv.unit, kreinAdjoint_one]

/-- Real `J`-Cayley transform sends `J`-skew-adjoint operators to `J`-unitary operators, and
satisfies `1 + C(A) = 2(1 - A)⁻¹` and `C⁻¹(C(A)) = A` (`S3-22`, Iokhvidov–Krein; `R3.1`). -/
theorem realCayley_isKreinUnitary_of_skewAdjoint {A : H →L[ℝ] H}
    (hA : IsKreinSkewAdjoint A) (hInv : IsUnit (1 - A)) :
    IsKreinUnitary (realCayley A hInv) ∧
      IsUnit (1 + realCayley A hInv) ∧
      ∀ hInv' : IsUnit (1 + realCayley A hInv),
        realCayleyInv (realCayley A hInv) hInv' = A := by
  let U := realCayley A hInv
  let inv1mA : H →L[ℝ] H := (hInv.unit⁻¹ : (H →L[ℝ] H)ˣ).val
  have hL1 : inv1mA * (1 - A) = 1 := by
    rw [← hInv.unit_spec]
    exact Units.inv_mul hInv.unit
  have hR1 : (1 - A) * inv1mA = 1 := by
    rw [← hInv.unit_spec]
    exact Units.mul_inv hInv.unit
  have hUnit1pA : IsUnit (1 + A) := isUnit_one_add_of_isKreinSkewAdjoint hA hInv
  let inv1pA : H →L[ℝ] H := (hUnit1pA.unit⁻¹ : (H →L[ℝ] H)ˣ).val
  have hL1pA : inv1pA * (1 + A) = 1 := by
    rw [← hUnit1pA.unit_spec]
    exact Units.inv_mul hUnit1pA.unit
  have hR1pA : (1 + A) * inv1pA = 1 := by
    rw [← hUnit1pA.unit_spec]
    exact Units.mul_inv hUnit1pA.unit
  have hAdjInv : kreinAdjoint inv1mA = inv1pA := by
    have hEq : kreinAdjoint (1 - A) = 1 + A := by
      rw [kreinAdjoint_sub, kreinAdjoint_one, hA, sub_neg_eq_add]
    have hL : (1 + A) * kreinAdjoint inv1mA = 1 := by
      rw [← hEq, ← kreinAdjoint_mul, hL1, kreinAdjoint_one]
    calc
      kreinAdjoint inv1mA = (inv1pA * (1 + A)) * kreinAdjoint inv1mA := by rw [hL1pA, one_mul]
      _ = inv1pA * ((1 + A) * kreinAdjoint inv1mA) := mul_assoc _ _ _
      _ = inv1pA := by rw [hL, mul_one]
  have hAdj1pA : kreinAdjoint (1 + A) = 1 - A := by
    rw [kreinAdjoint_add, kreinAdjoint_one, hA, ← sub_eq_add_neg]
  have h12_comm : (1 - A) * (1 + A) = (1 + A) * (1 - A) := by
    calc
      (1 - A) * (1 + A) = (1 + A) - A * (1 + A) := by rw [sub_mul, one_mul]
      _ = 1 + A - (A + A * A) := by rw [mul_add, mul_one]
      _ = 1 - A * A := by abel
      _ = (1 + A) - (A + A * A) := by abel
      _ = (1 + A) * 1 - (1 + A) * A := by rw [mul_one, add_mul, one_mul]
      _ = (1 + A) * (1 - A) := (mul_sub _ _ _).symm
  have hU_def : U = (1 + A) * inv1mA := rfl
  have hU_adj : kreinAdjoint U = (1 - A) * inv1pA := by
    rw [hU_def, kreinAdjoint_mul, hAdj1pA, hAdjInv]
    calc
      inv1pA * (1 - A) = inv1pA * ((1 - A) * ((1 + A) * inv1pA)) := by rw [hR1pA, mul_one]
      _ = inv1pA * (((1 - A) * (1 + A)) * inv1pA) := by rw [mul_assoc (1 - A)]
      _ = inv1pA * (((1 + A) * (1 - A)) * inv1pA) := by rw [h12_comm]
      _ = (inv1pA * (1 + A)) * ((1 - A) * inv1pA) := by simp only [mul_assoc]
      _ = (1 - A) * inv1pA := by rw [hL1pA, one_mul]
  have hUnitary : IsKreinUnitary U := by
    refine ⟨?_, ?_⟩
    · change kreinAdjoint U * U = 1
      rw [hU_adj, hU_def]
      rw [mul_assoc (1 - A), ← mul_assoc inv1pA, hL1pA, one_mul, hR1]
    · change U * kreinAdjoint U = 1
      rw [hU_adj, hU_def]
      rw [mul_assoc (1 + A), ← mul_assoc inv1mA, hL1, one_mul, hR1pA]
  have hSum : 1 + U = (2 : ℝ) • inv1mA := by
    have h2 : (1 - A) + (1 + A) = (2 : ℝ) • (1 : H →L[ℝ] H) := by
      rw [two_smul]; abel
    calc
      1 + U = (1 - A) * inv1mA + (1 + A) * inv1mA := by rw [hR1, hU_def]
      _ = ((1 - A) + (1 + A)) * inv1mA := (add_mul _ _ _).symm
      _ = ((2 : ℝ) • (1 : H →L[ℝ] H)) * inv1mA := by rw [h2]
      _ = (2 : ℝ) • inv1mA := by rw [smul_mul_assoc, one_mul]
  have hUnit1pU : IsUnit (1 + U) := by
    rw [hSum]
    refine ⟨⟨(2 : ℝ) • inv1mA, (2 : ℝ)⁻¹ • (1 - A), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ (by norm_num), one_smul, hL1]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ (by norm_num), one_smul, hR1]
  refine ⟨hUnitary, hUnit1pU, ?_⟩
  intro hInv'
  have hDiff : U - 1 = ((2 : ℝ) • A) * inv1mA := by
    have h2 : (1 + A) - (1 - A) = (2 : ℝ) • A := by
      rw [two_smul]; abel
    calc
      U - 1 = (1 + A) * inv1mA - (1 - A) * inv1mA := by rw [hR1, hU_def]
      _ = ((1 + A) - (1 - A)) * inv1mA := (sub_mul _ _ _).symm
      _ = ((2 : ℝ) • A) * inv1mA := by rw [h2]
  have hInvU : (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val = (2 : ℝ)⁻¹ • (1 - A) := by
    have hmul : (1 + U) * ((2 : ℝ)⁻¹ • (1 - A)) = 1 := by
      rw [hSum, smul_mul_smul_comm, mul_inv_cancel₀ (by norm_num), one_smul, hL1]
    have hL' : (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val * (1 + U) = 1 := by
      have hUinv := Units.inv_mul hInv'.unit
      rw [hInv'.unit_spec] at hUinv
      exact hUinv
    calc
      (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val
          = (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val * ((1 + U) * ((2 : ℝ)⁻¹ • (1 - A))) := by
            rw [hmul, mul_one]
      _ = ((hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val * (1 + U)) * ((2 : ℝ)⁻¹ • (1 - A)) :=
            (mul_assoc _ _ _).symm
      _ = (2 : ℝ)⁻¹ • (1 - A) := by rw [hL', one_mul]
  change (U - 1) * (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val = A
  rw [hDiff, hInvU, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ (by norm_num), one_smul, mul_assoc, hL1, mul_one]

/-- Inverse real `J`-Cayley transform sends `J`-unitary operators with `IsUnit (1 + U)` to
`J`-skew-adjoint operators and satisfies `C(C⁻¹(U)) = U` (`S3-22`, Iokhvidov–Krein; `R3.1`). -/
theorem realCayleyInv_isKreinSkewAdjoint_of_unitary {U : H →L[ℝ] H}
    (hU : IsKreinUnitary U) (hInv : IsUnit (1 + U)) :
    IsKreinSkewAdjoint (realCayleyInv U hInv) ∧
      IsUnit (1 - realCayleyInv U hInv) ∧
      ∀ hInv' : IsUnit (1 - realCayleyInv U hInv),
        realCayley (realCayleyInv U hInv) hInv' = U := by
  let A := realCayleyInv U hInv
  let inv1pU : H →L[ℝ] H := (hInv.unit⁻¹ : (H →L[ℝ] H)ˣ).val
  have hL1 : inv1pU * (1 + U) = 1 := by
    rw [← hInv.unit_spec]
    exact Units.inv_mul hInv.unit
  have hR1 : (1 + U) * inv1pU = 1 := by
    rw [← hInv.unit_spec]
    exact Units.mul_inv hInv.unit
  have hA_def : A = (U - 1) * inv1pU := rfl
  have h12_comm : (1 + U) * (U - 1) = (U - 1) * (1 + U) := by
    calc
      (1 + U) * (U - 1) = (U - 1) + U * (U - 1) := by rw [add_mul, one_mul]
      _ = (U - 1) + (U * U - U) := by rw [mul_sub, mul_one]
      _ = U * U - 1 := by abel
      _ = (U * U + U) - (U + 1) := by abel
      _ = U * (U + 1) - 1 * (U + 1) := by rw [mul_add, mul_one, one_mul]
      _ = (U - 1) * (U + 1) := (sub_mul _ _ _).symm
      _ = (U - 1) * (1 + U) := by rw [add_comm U 1]
  have hComm : (U - 1) * inv1pU = inv1pU * (U - 1) := by
    calc
      (U - 1) * inv1pU = (inv1pU * (1 + U)) * ((U - 1) * inv1pU) := by rw [hL1, one_mul]
      _ = inv1pU * (((1 + U) * (U - 1)) * inv1pU) := by simp only [mul_assoc]
      _ = inv1pU * (((U - 1) * (1 + U)) * inv1pU) := by rw [h12_comm]
      _ = inv1pU * ((U - 1) * ((1 + U) * inv1pU)) := by simp only [mul_assoc]
      _ = inv1pU * (U - 1) := by rw [hR1, mul_one]
  have hU_unit : (kreinAdjoint U) * U = 1 ∧ U * (kreinAdjoint U) = 1 := hU
  have hAdjInv : kreinAdjoint (1 + U) = (1 + U) * kreinAdjoint U := by
    rw [kreinAdjoint_add, kreinAdjoint_one, add_mul, one_mul, hU_unit.2, add_comm]
  have hAdj_inv1pU : kreinAdjoint inv1pU = U * inv1pU := by
    have hR : kreinAdjoint (1 + U) * kreinAdjoint inv1pU = 1 := by
      rw [← kreinAdjoint_mul, hL1, kreinAdjoint_one]
    rw [hAdjInv, mul_assoc] at hR
    have h1pU_inv : inv1pU * ((1 + U) * (kreinAdjoint U * kreinAdjoint inv1pU)) = inv1pU := by
      rw [hR, mul_one]
    rw [← mul_assoc inv1pU, hL1, one_mul] at h1pU_inv
    calc
      kreinAdjoint inv1pU = (U * kreinAdjoint U) * kreinAdjoint inv1pU := by
        rw [hU_unit.2, one_mul]
      _ = U * (kreinAdjoint U * kreinAdjoint inv1pU) := mul_assoc _ _ _
      _ = U * inv1pU := by rw [h1pU_inv]
  have hSkew : IsKreinSkewAdjoint A := by
    change kreinAdjoint A = -A
    rw [hA_def, kreinAdjoint_mul, hAdj_inv1pU, kreinAdjoint_sub, kreinAdjoint_one]
    have h1U_comm : (1 + U) * U = U * (1 + U) := by
      rw [add_mul, mul_add, one_mul, mul_one]
    have hCU : U * inv1pU = inv1pU * U := by
      calc
        U * inv1pU = (inv1pU * (1 + U)) * (U * inv1pU) := by rw [hL1, one_mul]
        _ = inv1pU * (((1 + U) * U) * inv1pU) := by simp only [mul_assoc]
        _ = inv1pU * ((U * (1 + U)) * inv1pU) := by rw [h1U_comm]
        _ = inv1pU * (U * ((1 + U) * inv1pU)) := by simp only [mul_assoc]
        _ = inv1pU * U := by rw [hR1, mul_one]
    calc
      (U * inv1pU) * (kreinAdjoint U - 1)
          = (inv1pU * U) * (kreinAdjoint U - 1) := by rw [hCU]
      _ = inv1pU * (U * (kreinAdjoint U - 1)) := mul_assoc _ _ _
      _ = inv1pU * (1 - U) := by rw [mul_sub, mul_one, hU_unit.2]
      _ = -(inv1pU * (U - 1)) := by rw [← neg_sub U 1, mul_neg]
      _ = -((U - 1) * inv1pU) := by rw [hComm]
  have hOneSubA : 1 - A = (2 : ℝ) • inv1pU := by
    have h2 : (1 + U) - (U - 1) = (2 : ℝ) • (1 : H →L[ℝ] H) := by
      rw [two_smul]; abel
    calc
      1 - A = (1 + U) * inv1pU - (U - 1) * inv1pU := by rw [hR1, hA_def]
      _ = ((1 + U) - (U - 1)) * inv1pU := (sub_mul _ _ _).symm
      _ = ((2 : ℝ) • (1 : H →L[ℝ] H)) * inv1pU := by rw [h2]
      _ = (2 : ℝ) • inv1pU := by rw [smul_mul_assoc, one_mul]
  have hUnit1mA : IsUnit (1 - A) := by
    rw [hOneSubA]
    refine ⟨⟨(2 : ℝ) • inv1pU, (2 : ℝ)⁻¹ • (1 + U), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ (by norm_num), one_smul, hL1]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ (by norm_num), one_smul, hR1]
  refine ⟨hSkew, hUnit1mA, ?_⟩
  intro hInv'
  have hOneAddA : 1 + A = ((2 : ℝ) • U) * inv1pU := by
    have h2 : (1 + U) + (U - 1) = (2 : ℝ) • U := by
      rw [two_smul]; abel
    calc
      1 + A = (1 + U) * inv1pU + (U - 1) * inv1pU := by rw [hR1, hA_def]
      _ = ((1 + U) + (U - 1)) * inv1pU := (add_mul _ _ _).symm
      _ = ((2 : ℝ) • U) * inv1pU := by rw [h2]
  have hInvA : (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val = (2 : ℝ)⁻¹ • (1 + U) := by
    have hmul : (1 - A) * ((2 : ℝ)⁻¹ • (1 + U)) = 1 := by
      rw [hOneSubA, smul_mul_smul_comm, mul_inv_cancel₀ (by norm_num), one_smul, hL1]
    have hL' : (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val * (1 - A) = 1 := by
      have hUinv := Units.inv_mul hInv'.unit
      rw [hInv'.unit_spec] at hUinv
      exact hUinv
    calc
      (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val
          = (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val * ((1 - A) * ((2 : ℝ)⁻¹ • (1 + U))) := by
            rw [hmul, mul_one]
      _ = ((hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val * (1 - A)) * ((2 : ℝ)⁻¹ • (1 + U)) :=
            (mul_assoc _ _ _).symm
      _ = (2 : ℝ)⁻¹ • (1 + U) := by rw [hL', one_mul]
  change (1 + A) * (hInv'.unit⁻¹ : (H →L[ℝ] H)ˣ).val = U
  rw [hOneAddA, hInvA, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ (by norm_num), one_smul, mul_assoc, hL1, mul_one]

end FundamentalDecomposition

end KreinSpace

/-! ## Part 2: Real `PontryaginSpace` ($\Pi_\kappa$) & $\mathcal{H}_+ \oplus \mathcal{H}_-$ Models (`S3-20`, `R3.1`) -/

/-- A **real Pontryagin space** $\Pi_\kappa$ (`S3-20`, Pontryagin 1944; `R3.1`): a real
`InfoGeometry.Krein.KreinSpace` whose negative fundamental subspace `K₋ = ker (J + I)` is
finite-dimensional of index `κ = Module.finrank ℝ (negSubspace H)`. -/
class PontryaginSpace (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    extends KreinSpace H where
  /-- Finite dimensionality of the negative fundamental subspace `K₋`. -/
  finite_neg : FiniteDimensional ℝ (KreinSpace.negSubspace (H := H))

attribute [instance] PontryaginSpace.finite_neg

namespace PontryaginSpace

/-- The negative index `κ = dim K₋` of a real Pontryagin space $\Pi_\kappa$ (`S3-20`, `R3.1`). -/
def negIndex (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [PontryaginSpace H] : ℕ :=
  Module.finrank ℝ (KreinSpace.negSubspace (H := H))

/-- Any complete real Hilbert space is a Pontryagin space $\Pi_0$ (`J = id`, `K₋ = ⊥`, `S3-20`,
`R3.1`; also provides T17 inhabitant on `ℝ`). -/
instance (priority := 100) instPontryaginSpaceOfHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    PontryaginSpace H :=
  { (instKreinSpaceOfHilbert (H := H)) with
    finite_neg := by
      have hbot : KreinSpace.negSubspace (H := H) = ⊥ := by
        ext x
        rw [KreinSpace.mem_negSubspace_iff]
        change x = -x ↔ x = 0
        constructor
        · intro h
          have h2 : (2 : ℝ) • x = 0 := by
            rw [two_smul]
            nth_rw 2 [h]
            exact add_neg_cancel x
          exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
        · intro h
          rw [h, neg_zero]
      rw [hbot]
      infer_instance }

/-- Under the Hilbert $\Pi_0$ instance, the negative index vanishes (`κ = 0`) (`S3-20`, `R3.1`). -/
theorem negIndex_of_hilbert (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    @negIndex H _ _ _ (instPontryaginSpaceOfHilbert (H := H)) = 0 := by
  let _ : PontryaginSpace H := instPontryaginSpaceOfHilbert (H := H)
  have hbot : KreinSpace.negSubspace (H := H) = ⊥ := by
    ext x
    rw [KreinSpace.mem_negSubspace_iff]
    change x = -x ↔ x = 0
    constructor
    · intro h
      have h2 : (2 : ℝ) • x = 0 := by
        rw [two_smul]
        nth_rw 2 [h]
        exact add_neg_cancel x
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    · intro h
      rw [h, neg_zero]
  change Module.finrank ℝ (KreinSpace.negSubspace (H := H)) = 0
  rw [hbot, finrank_bot]

/-- Every finite-dimensional `DoubledSpace E` is a Pontryagin space $\Pi_n$ with `n = dim E`
(`S3-20`, `R3.1`). -/
instance (priority := 1000) instPontryaginSpaceDoubled
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] :
    PontryaginSpace (DoubledSpace E) where
  finite_neg := by
    have heq : KreinSpace.negSubspace (H := DoubledSpace E) ≃ₗ[ℝ] E :=
      { toFun := fun u => WithLp.snd u.1
        invFun := fun ξ => ⟨to_doubled 0 ξ, by
          rw [KreinSpace.mem_negSubspace_iff]
          change signFlipLIE (to_doubled 0 ξ) = -to_doubled 0 ξ
          rw [signFlipLIE_apply]
          apply DoubledSpace.ext <;> simp⟩
        left_inv := fun u => by
          ext
          · have hu := (KreinSpace.mem_negSubspace_iff u.1).mp u.2
            have hfst := congrArg WithLp.fst hu
            change WithLp.fst u.1 = -WithLp.fst u.1 at hfst
            have h2 : (2 : ℝ) • WithLp.fst u.1 = 0 := by
              rw [two_smul]
              nth_rw 2 [hfst]
              exact add_neg_cancel _
            exact ((smul_eq_zero.mp h2).resolve_left (by norm_num)).symm
          · rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact heq.symm.finiteDimensional

/-- On `DoubledSpace E`, `negIndex (DoubledSpace E) = Module.finrank ℝ E` (`S3-20`, `R3.1`). -/
theorem negIndex_doubled (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] :
    negIndex (DoubledSpace E) = Module.finrank ℝ E := by
  have heq : KreinSpace.negSubspace (H := DoubledSpace E) ≃ₗ[ℝ] E :=
    { toFun := fun u => WithLp.snd u.1
      invFun := fun ξ => ⟨to_doubled 0 ξ, by
        rw [KreinSpace.mem_negSubspace_iff]
        change signFlipLIE (to_doubled 0 ξ) = -to_doubled 0 ξ
        rw [signFlipLIE_apply]
        apply DoubledSpace.ext <;> simp⟩
      left_inv := fun u => by
        ext
        · have hu := (KreinSpace.mem_negSubspace_iff u.1).mp u.2
          have hfst := congrArg WithLp.fst hu
          change WithLp.fst u.1 = -WithLp.fst u.1 at hfst
          have h2 : (2 : ℝ) • WithLp.fst u.1 = 0 := by
            rw [two_smul]
            nth_rw 2 [hfst]
            exact add_neg_cancel _
          exact ((smul_eq_zero.mp h2).resolve_left (by norm_num)).symm
        · rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact heq.finrank_eq

/-- Maximal nonpositive dimension bound (`S3-20`, Pontryagin 1944; `R3.1`): any subspace
`M ≤ H` on which `[x, x]_J ≤ 0` satisfies `Module.finrank ℝ M ≤ negIndex H` (via injectivity
of `P₋|_M`). -/
theorem finrank_le_negIndex_of_nonpositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [PontryaginSpace H] (M : Submodule ℝ H) (hM : ∀ x ∈ M, KreinSpace.kreinInner x x ≤ 0) :
    Module.finrank ℝ M ≤ negIndex H := by
  let f : M →ₗ[ℝ] KreinSpace.negSubspace (H := H) :=
    { toFun := fun x => ⟨KreinSpace.P_minus (H := H) x.1, KreinSpace.P_minus_mem_negSubspace x.1⟩
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul _ r x.1) }
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hPm : KreinSpace.P_minus (H := H) x.1 = 0 := congrArg Subtype.val hx
    have hxPos : x.1 ∈ KreinSpace.posSubspace H := by
      have h := KreinSpace.P_plus_add_P_minus_apply x.1
      rw [hPm, add_zero] at h
      rw [← h]
      exact KreinSpace.P_plus_mem_posSubspace x.1
    have hle : KreinSpace.kreinInner x.1 x.1 ≤ 0 := hM x.1 x.2
    have hEq : KreinSpace.kreinInner x.1 x.1 = ‖x.1‖ ^ 2 := by
      rw [KreinSpace.kreinInner_def, (KreinSpace.mem_posSubspace_iff x.1).mp hxPos,
        real_inner_self_eq_norm_sq]
    have h0 : ‖x.1‖ = 0 := by nlinarith [norm_nonneg x.1]
    exact Subtype.ext (norm_eq_zero.mp h0)
  have _ : FiniteDimensional ℝ M := FiniteDimensional.of_injective f hf_inj
  exact LinearMap.finrank_le_finrank_of_injective hf_inj

end PontryaginSpace

/-- Constructive real Hilbert $\Pi_0$ witness for `PontryaginSpace ℝ` (`S3-20`, `R3.1`; T17). -/
@[instance_reducible]
def realLinePontryaginWitness : PontryaginSpace ℝ :=
  PontryaginSpace.instPontryaginSpaceOfHilbert

/-- Non-aliased direct sum `Hpos ⊕ Hneg` carrying an asymmetric fundamental symmetry
`J(x, y) = (x, -y)` (`S3-20`, Pontryagin 1944; `R3.1`). Allows `Hpos` to be arbitrarily
infinite-dimensional while `Hneg` has finite dimension `κ`. Defined as a `structure` (never
`abbrev`) so `instKreinSpaceOfHilbert` never shadows its `KreinSpace` instance. -/
@[ext]
structure PontryaginSum (Hpos Hneg : Type*) where
  /-- Underlying `L²` pair in `WithLp 2 (Hpos × Hneg)`. -/
  toLp : WithLp (2 : ENNReal) (Hpos × Hneg)

namespace PontryaginSum

/-- Constructive zero-model inhabitant for `PontryaginSum ℝ ℝ` (`S3-20`, `R3.1`; T17). -/
def zeroModel : PontryaginSum ℝ ℝ :=
  ⟨WithLp.toLp (2 : ENNReal) ((0 : ℝ), (0 : ℝ))⟩

section Instances

variable {Hpos Hneg : Type*}

lemma toLp_injective : Function.Injective (toLp : PontryaginSum Hpos Hneg → WithLp 2 (Hpos × Hneg)) :=
  fun u v h => by cases u; cases v; cases h; rfl

section NormedGroup

variable [NormedAddCommGroup Hpos] [NormedAddCommGroup Hneg]

instance : Add (PontryaginSum Hpos Hneg) := ⟨fun u v => ⟨u.toLp + v.toLp⟩⟩
instance : Zero (PontryaginSum Hpos Hneg) := ⟨⟨0⟩⟩
instance : Neg (PontryaginSum Hpos Hneg) := ⟨fun u => ⟨-u.toLp⟩⟩
instance : Sub (PontryaginSum Hpos Hneg) := ⟨fun u v => ⟨u.toLp - v.toLp⟩⟩
instance : SMul ℕ (PontryaginSum Hpos Hneg) := ⟨fun n u => ⟨n • u.toLp⟩⟩
instance : SMul ℤ (PontryaginSum Hpos Hneg) := ⟨fun z u => ⟨z • u.toLp⟩⟩

@[simp] lemma toLp_zero : (0 : PontryaginSum Hpos Hneg).toLp = 0 := rfl
@[simp] lemma toLp_add (u v : PontryaginSum Hpos Hneg) : (u + v).toLp = u.toLp + v.toLp := rfl
@[simp] lemma toLp_neg (u : PontryaginSum Hpos Hneg) : (-u).toLp = -u.toLp := rfl
@[simp] lemma toLp_sub (u v : PontryaginSum Hpos Hneg) : (u - v).toLp = u.toLp - v.toLp := rfl

instance : AddCommGroup (PontryaginSum Hpos Hneg) :=
  Function.Injective.addCommGroup toLp toLp_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Additive equivalence `PontryaginSum Hpos Hneg ≃+ WithLp 2 (Hpos × Hneg)`. -/
def toLpAddEquiv : PontryaginSum Hpos Hneg ≃+ WithLp 2 (Hpos × Hneg) where
  toFun := toLp
  invFun := mk
  left_inv u := by cases u; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

instance : NormedAddCommGroup (PontryaginSum Hpos Hneg) :=
  NormedAddCommGroup.induced (PontryaginSum Hpos Hneg) (WithLp 2 (Hpos × Hneg))
    toLpAddEquiv (AddEquiv.injective _)

end NormedGroup

section HilbertAndPontryagin

variable [NormedAddCommGroup Hpos] [InnerProductSpace ℝ Hpos] [CompleteSpace Hpos]
variable [NormedAddCommGroup Hneg] [InnerProductSpace ℝ Hneg] [CompleteSpace Hneg]

instance : SMul ℝ (PontryaginSum Hpos Hneg) := ⟨fun r u => ⟨r • u.toLp⟩⟩

@[simp] lemma toLp_smul (r : ℝ) (u : PontryaginSum Hpos Hneg) :
    (r • u).toLp = r • u.toLp := rfl

instance : Module ℝ (PontryaginSum Hpos Hneg) :=
  Function.Injective.module ℝ toLpAddEquiv.toAddMonoidHom toLp_injective (fun _ _ => rfl)

instance : Inner ℝ (PontryaginSum Hpos Hneg) where
  inner u v := ⟪u.toLp, v.toLp⟫_ℝ

instance : InnerProductSpace ℝ (PontryaginSum Hpos Hneg) where
  norm_smul_le r u := norm_smul_le r u.toLp
  norm_sq_eq_re_inner u := norm_sq_eq_re_inner u.toLp
  conj_inner_symm u v := inner_conj_symm (𝕜 := ℝ) u.toLp v.toLp
  add_left u v w := inner_add_left u.toLp v.toLp w.toLp
  smul_left u v r := by
    change ⟪r • u.toLp, v.toLp⟫_ℝ = (starRingEnd ℝ) r * ⟪u.toLp, v.toLp⟫_ℝ
    simpa using real_inner_smul_left u.toLp v.toLp r

/-- Uniform equivalence `PontryaginSum Hpos Hneg ≃ᵤ WithLp 2 (Hpos × Hneg)`. -/
def toLpUniformEquiv : PontryaginSum Hpos Hneg ≃ᵤ WithLp 2 (Hpos × Hneg) where
  toEquiv := toLpAddEquiv.toEquiv
  uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl
  uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id

instance : CompleteSpace (PontryaginSum Hpos Hneg) :=
  (completeSpace_congr (toLpUniformEquiv (Hpos := Hpos) (Hneg := Hneg)).isUniformEmbedding).mpr
    inferInstance

private def sumSignFlipMap : PontryaginSum Hpos Hneg →ₗ[ℝ] PontryaginSum Hpos Hneg where
  toFun u := ⟨WithLp.toLp 2 (WithLp.fst u.toLp, -WithLp.snd u.toLp)⟩
  map_add' u v := by
    apply PontryaginSum.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp [add_comm]
  map_smul' r u := by
    apply PontryaginSum.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp [smul_neg]

private lemma sumSignFlipMap_invol (u : PontryaginSum Hpos Hneg) :
    sumSignFlipMap (sumSignFlipMap u) = u := by
  apply PontryaginSum.ext
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext
  · rfl
  · simp [sumSignFlipMap]

private lemma sumSignFlipMap_norm (u : PontryaginSum Hpos Hneg) : ‖sumSignFlipMap u‖ = ‖u‖ := by
  have hinner : ⟪sumSignFlipMap u, sumSignFlipMap u⟫_ℝ = ⟪u, u⟫_ℝ := by
    change ⟪(sumSignFlipMap u).toLp, (sumSignFlipMap u).toLp⟫_ℝ = ⟪u.toLp, u.toLp⟫_ℝ
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    have h1 : (sumSignFlipMap u).toLp.ofLp.1 = u.toLp.ofLp.1 := rfl
    have h2 : (sumSignFlipMap u).toLp.ofLp.2 = -u.toLp.ofLp.2 := rfl
    rw [h1, h2, inner_neg_left, inner_neg_right, neg_neg]
  have hsq : ‖sumSignFlipMap u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner]
  nlinarith [norm_nonneg u, norm_nonneg (sumSignFlipMap u)]

private def sumSignFlipLIE : PontryaginSum Hpos Hneg ≃ₗᵢ[ℝ] PontryaginSum Hpos Hneg where
  toLinearEquiv := LinearEquiv.ofLinearMap sumSignFlipMap sumSignFlipMap
    (LinearMap.ext sumSignFlipMap_invol) (LinearMap.ext sumSignFlipMap_invol)
  norm_map' := sumSignFlipMap_norm

/-- Canonical `KreinSpace` instance on `PontryaginSum Hpos Hneg` with `J(x, y) = (x, -y)`
(`S3-20`, `S3-21`, `R3.1`). -/
instance (priority := 1000) instKreinSpace : KreinSpace (PontryaginSum Hpos Hneg) where
  J := sumSignFlipLIE
  J_invol := sumSignFlipMap_invol
  J_selfAdj u v := by
    change ⟪(sumSignFlipMap u).toLp, v.toLp⟫_ℝ = ⟪u.toLp, (sumSignFlipMap v).toLp⟫_ℝ
    rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
    have h1u : (sumSignFlipMap u).toLp.ofLp.1 = u.toLp.ofLp.1 := rfl
    have h2u : (sumSignFlipMap u).toLp.ofLp.2 = -u.toLp.ofLp.2 := rfl
    have h1v : (sumSignFlipMap v).toLp.ofLp.1 = v.toLp.ofLp.1 := rfl
    have h2v : (sumSignFlipMap v).toLp.ofLp.2 = -v.toLp.ofLp.2 := rfl
    rw [h1u, h2u, h1v, h2v, inner_neg_left, inner_neg_right]

/-- Native Krein pairing on `PontryaginSum Hpos Hneg`: `[(x₁, y₁), (x₂, y₂)] = ⟪x₁, x₂⟫ - ⟪y₁, y₂⟫`
(`S3-20`, `R3.1`). -/
theorem kreinInner_eq (u v : PontryaginSum Hpos Hneg) :
    KreinSpace.kreinInner u v =
      ⟪WithLp.fst u.toLp, WithLp.fst v.toLp⟫_ℝ - ⟪WithLp.snd u.toLp, WithLp.snd v.toLp⟫_ℝ := by
  change ⟪(sumSignFlipMap u).toLp, v.toLp⟫_ℝ = _
  rw [WithLp.prod_inner_apply]
  simp [sumSignFlipMap, sub_eq_add_neg]

private def negSubspaceEquiv :
    KreinSpace.negSubspace (H := PontryaginSum Hpos Hneg) ≃ₗ[ℝ] Hneg where
  toFun u := WithLp.snd u.1.toLp
  invFun y := ⟨⟨WithLp.toLp 2 (0, y)⟩, by
    rw [KreinSpace.mem_negSubspace_iff]
    change sumSignFlipMap ⟨WithLp.toLp 2 (0, y)⟩ = -⟨WithLp.toLp 2 (0, y)⟩
    apply PontryaginSum.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext <;> simp [sumSignFlipMap]⟩
  left_inv u := by
    apply Subtype.ext
    apply PontryaginSum.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext
    · have hu := (KreinSpace.mem_negSubspace_iff u.1).mp u.2
      have hfst := congrArg (fun z : PontryaginSum Hpos Hneg => WithLp.fst z.toLp) hu
      change WithLp.fst u.1.toLp = -WithLp.fst u.1.toLp at hfst
      have h2 : (2 : ℝ) • WithLp.fst u.1.toLp = 0 := by
        rw [two_smul]
        nth_rw 2 [hfst]
        exact add_neg_cancel _
      exact ((smul_eq_zero.mp h2).resolve_left (by norm_num)).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- When `Hneg` is finite-dimensional, `PontryaginSum Hpos Hneg` is a real Pontryagin space
$\Pi_\kappa$ (`S3-20`, Pontryagin 1944; `R3.1`), with `Hpos` possibly infinite-dimensional. -/
instance (priority := 1000) instPontryaginSpace [FiniteDimensional ℝ Hneg] :
    PontryaginSpace (PontryaginSum Hpos Hneg) where
  finite_neg := (negSubspaceEquiv (Hpos := Hpos) (Hneg := Hneg)).symm.finiteDimensional

/-- Exact negative index formula `negIndex (PontryaginSum Hpos Hneg) = dim Hneg` (`S3-20`,
`R3.1`). -/
theorem negIndex_eq [FiniteDimensional ℝ Hneg] :
    PontryaginSpace.negIndex (PontryaginSum Hpos Hneg) = Module.finrank ℝ Hneg :=
  (negSubspaceEquiv (Hpos := Hpos) (Hneg := Hneg)).finrank_eq

end HilbertAndPontryagin

end Instances

end PontryaginSum

/-- Concrete Dirac ghost-state & neutral-state witness on `DoubledSpace ℝ` (`S3-18`, Dirac
1942; `R3.1`), refuting Hilbert positivity for `kreinInner` without Wick rotation. -/
theorem doubledReal_negative_and_neutral_witness :
    KreinSpace.kreinInner (H := DoubledSpace ℝ) (to_doubled (1 : ℝ) 0) (to_doubled 1 0) = 1 ∧
    KreinSpace.kreinInner (H := DoubledSpace ℝ) (to_doubled (0 : ℝ) 1) (to_doubled 0 1) = -1 ∧
    to_doubled (1 : ℝ) 1 ≠ 0 ∧
    KreinSpace.kreinInner (H := DoubledSpace ℝ) (to_doubled (1 : ℝ) 1) (to_doubled 1 1) = 0 ∧
    ¬ (∀ v : DoubledSpace ℝ, v ≠ 0 → 0 < KreinSpace.kreinInner v v) := by
  have h1 : KreinSpace.kreinInner (H := DoubledSpace ℝ) (to_doubled (1 : ℝ) 0) (to_doubled 1 0) = 1 := by
    rw [kreinInner_to_doubled]; norm_num
  have h2 : KreinSpace.kreinInner (H := DoubledSpace ℝ) (to_doubled (0 : ℝ) 1) (to_doubled 0 1) = -1 := by
    rw [kreinInner_to_doubled]; norm_num
  have hne : to_doubled (1 : ℝ) 1 ≠ 0 := by
    intro h0
    have hfst := congrArg WithLp.fst h0
    simp [to_doubled] at hfst
  have h3 : KreinSpace.kreinInner (H := DoubledSpace ℝ) (to_doubled (1 : ℝ) 1) (to_doubled 1 1) = 0 := by
    rw [kreinInner_to_doubled]; norm_num
  refine ⟨h1, h2, hne, h3, ?_⟩
  intro hpos
  have hlt := hpos (to_doubled 0 1) (by
    intro h0
    have hsnd := congrArg WithLp.snd h0
    simp [to_doubled] at hsnd)
  rw [h2] at hlt
  linarith

/-- Real obstruction motivating the complex formulation of Pontryagin's Theorem (`S3-20`,
`R3.1`): on real $\Pi_1 = \mathrm{DoubledSpace}\,\mathbb{R}$, `complex_i` is
`IsKreinSelfAdjoint` (`DoubledSpace.isKreinSelfAdjoint_complex_i`) yet admits **no**
1-dimensional real invariant subspace (`c^2 + 1 = 0` has no real root). -/
theorem doubledReal_complex_i_no_one_dim_invariant_subspace :
    PontryaginSpace.negIndex (DoubledSpace ℝ) = 1 ∧
    KreinSpace.IsKreinSelfAdjoint (H := DoubledSpace ℝ) (complex_i (E := ℝ)) ∧
    ¬ ∃ L : Submodule ℝ (DoubledSpace ℝ),
        Module.finrank ℝ L = 1 ∧
        L ∈ Module.End.invtSubmodule (complex_i (E := ℝ) : DoubledSpace ℝ →ₗ[ℝ] DoubledSpace ℝ) := by
  refine ⟨?_, isKreinSelfAdjoint_complex_i, ?_⟩
  · rw [PontryaginSpace.negIndex_doubled, Module.finrank_self]
  · rintro ⟨L, hdim, hinv⟩
    have hnt : Nontrivial L := by
      rw [← Module.finrank_pos_iff (R := ℝ)]
      omega
    obtain ⟨⟨v, hvL⟩, hvne⟩ := exists_ne (0 : L)
    have hv0 : v ≠ 0 := fun h => hvne (Subtype.ext h)
    have hAvL : complex_i (E := ℝ) v ∈ L := hinv hvL
    have hlin : ¬ LinearIndependent ℝ ![v, complex_i (E := ℝ) v] := by
      intro hli
      have hle : 2 ≤ Module.finrank ℝ L := by
        have hsub : Submodule.span ℝ (Set.range ![v, complex_i (E := ℝ) v]) ≤ L := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          fin_cases i
          · exact hvL
          · exact hAvL
        have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![v, complex_i (E := ℝ) v])) = 2 := by
          rw [finrank_span_eq_card hli, Fintype.card_fin]
        rw [← h2]
        exact Submodule.finrank_mono hsub
      omega
    rw [Fintype.linearIndependent_iff] at hlin
    push Not at hlin
    rcases hlin with ⟨c, hsum, i0, hi0⟩
    have hsum' : c 0 • v + c 1 • complex_i (E := ℝ) v = 0 := by
      simpa [Fin.sum_univ_two] using hsum
    have hc1 : c 1 ≠ 0 := by
      intro hc1z
      have h0 : c 0 • v = 0 := by simpa [hc1z] using hsum'
      have hc0z : c 0 = 0 := (smul_eq_zero.mp h0).resolve_right hv0
      fin_cases i0 <;> exact hi0 (by assumption)
    let μ : ℝ := -(c 0) / c 1
    have hEig : complex_i (E := ℝ) v = μ • v := by
      have h1 : c 1 • complex_i (E := ℝ) v = -(c 0) • v := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right hsum'
      calc
        complex_i (E := ℝ) v = (c 1)⁻¹ • (c 1 • complex_i (E := ℝ) v) := by
          rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
        _ = (c 1)⁻¹ • (-(c 0) • v) := by rw [h1]
        _ = μ • v := by
          rw [smul_smul]
          congr 1
          dsimp [μ]
          ring
    have hSq : complex_i (E := ℝ) (complex_i (E := ℝ) v) = -v := by
      have h := congrArg (fun T : DoubledSpace ℝ →L[ℝ] DoubledSpace ℝ => T v) (complex_i_sq ℝ)
      simpa using h
    have hContra : (μ ^ 2 + 1) • v = 0 := by
      calc
        (μ ^ 2 + 1) • v = μ ^ 2 • v + v := by rw [add_smul, one_smul]
        _ = μ • (μ • v) + v := by rw [smul_smul, sq]
        _ = μ • complex_i (E := ℝ) v + v := by rw [hEig]
        _ = complex_i (E := ℝ) (μ • v) + v := by rw [map_smul]
        _ = complex_i (E := ℝ) (complex_i (E := ℝ) v) + v := by rw [hEig]
        _ = -v + v := by rw [hSq]
        _ = 0 := neg_add_cancel v
    have hpos : μ ^ 2 + 1 ≠ 0 := by positivity
    exact hv0 ((smul_eq_zero.mp hContra).resolve_left hpos)

/-! ## Part 3: Dirac–Pauli $\eta$-Pseudo-Hermiticity, `ComplexKreinSpace`, Spectral Reflection, & Complex $J$-Cayley (`S3-18`, `S3-19`, `S3-21`, `S3-22`, `R3.1`) -/

section EtaPseudoHermitian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- General indefinite sesquilinear pairing `[u, v]_η := ⟪η u, v⟫_ℂ` associated to a bounded
metric operator `η : H →L[ℂ] H` (`S3-18` Dirac 1942; `S3-19` Pauli 1943; Mostafazadeh 2002;
`R3.1`). -/
def etaInner (η : H →L[ℂ] H) (u v : H) : ℂ := ⟪η u, v⟫_ℂ

/-- `A` is **`η`-pseudo-Hermitian** (`S3-18`, `S3-19`, `R3.1`) when `A† ∘ η = η ∘ A`. -/
def IsEtaPseudoHermitian (η A : H →L[ℂ] H) : Prop :=
  (ContinuousLinearMap.adjoint A).comp η = η.comp A

/-- `U` is **`η`-unitary** (`S3-19`, `S3-22`, `R3.1`) when `U† ∘ η ∘ U = η` and `U` is bijective. -/
def IsEtaUnitary (η U : H →L[ℂ] H) : Prop :=
  (ContinuousLinearMap.adjoint U).comp (η.comp U) = η ∧ Function.Bijective U

/-- Characterization: `IsEtaPseudoHermitian η A ↔ ∀ u v, [A u, v]_η = [u, A v]_η`
(`S3-18`, `S3-19`, `R3.1`). -/
theorem isEtaPseudoHermitian_iff_etaInner (η A : H →L[ℂ] H) :
    IsEtaPseudoHermitian η A ↔ ∀ u v : H, etaInner η (A u) v = etaInner η u (A v) := by
  constructor
  · intro h u v
    have hu : (ContinuousLinearMap.adjoint A) (η u) = η (A u) := by
      simpa using congrArg (fun T : H →L[ℂ] H => T u) h
    calc
      etaInner η (A u) v = ⟪η (A u), v⟫_ℂ := rfl
      _ = ⟪(ContinuousLinearMap.adjoint A) (η u), v⟫_ℂ := by rw [hu]
      _ = ⟪η u, A v⟫_ℂ := ContinuousLinearMap.adjoint_inner_left A v (η u)
      _ = etaInner η u (A v) := rfl
  · intro h
    ext u
    apply ext_inner_right ℂ
    intro v
    have huv := h u v
    calc
      ⟪((ContinuousLinearMap.adjoint A).comp η) u, v⟫_ℂ
          = ⟪(ContinuousLinearMap.adjoint A) (η u), v⟫_ℂ := rfl
      _ = ⟪η u, A v⟫_ℂ := ContinuousLinearMap.adjoint_inner_left A v (η u)
      _ = ⟪η (A u), v⟫_ℂ := huv.symm
      _ = ⟪(η.comp A) u, v⟫_ℂ := rfl

/-- **Pauli–Mostafazadeh Biorthogonal Law** (`S3-19`, Pauli 1943; Mostafazadeh 2002 Prop. 1;
`R3.1`): for `η`-pseudo-Hermitian `A` with eigenvectors `A v₁ = μ₁ • v₁`, `A v₂ = μ₂ • v₂`,
`(conj μ₁ - μ₂) * [v₁, v₂]_η = 0`. -/
theorem eta_biorthogonal_pairing (η A : H →L[ℂ] H) (hA : IsEtaPseudoHermitian η A)
    {v₁ v₂ : H} {μ₁ μ₂ : ℂ} (hv₁ : A v₁ = μ₁ • v₁) (hv₂ : A v₂ = μ₂ • v₂) :
    (star μ₁ - μ₂) * etaInner η v₁ v₂ = 0 := by
  have hAdj : (ContinuousLinearMap.adjoint A) (η v₁) = η (A v₁) := by
    simpa using congrArg (fun T : H →L[ℂ] H => T v₁) hA
  have h1 : star μ₁ * etaInner η v₁ v₂ = ⟪η (A v₁), v₂⟫_ℂ := by
    calc
      star μ₁ * etaInner η v₁ v₂ = (starRingEnd ℂ) μ₁ * ⟪η v₁, v₂⟫_ℂ := rfl
      _ = ⟪μ₁ • η v₁, v₂⟫_ℂ := (inner_smul_left (η v₁) v₂ μ₁).symm
      _ = ⟪η (μ₁ • v₁), v₂⟫_ℂ := by rw [map_smul]
      _ = ⟪η (A v₁), v₂⟫_ℂ := by rw [hv₁]
  have h2 : ⟪η (A v₁), v₂⟫_ℂ = μ₂ * etaInner η v₁ v₂ := by
    calc
      ⟪η (A v₁), v₂⟫_ℂ = ⟪(ContinuousLinearMap.adjoint A) (η v₁), v₂⟫_ℂ := by rw [hAdj]
      _ = ⟪η v₁, A v₂⟫_ℂ := ContinuousLinearMap.adjoint_inner_left A v₂ (η v₁)
      _ = ⟪η v₁, μ₂ • v₂⟫_ℂ := by rw [hv₂]
      _ = μ₂ * etaInner η v₁ v₂ := inner_smul_right (η v₁) v₂ μ₂
  rw [sub_mul, h1, h2, sub_self]

/-- Any eigenvector of an `η`-pseudo-Hermitian operator with non-real eigenvalue is `η`-null
(`S3-19`, Pauli 1943; `R3.1`). -/
theorem eta_nonreal_eigenvector_null (η A : H →L[ℂ] H) (hA : IsEtaPseudoHermitian η A)
    {v : H} {μ : ℂ} (hv : A v = μ • v) (hμ : μ.im ≠ 0) :
    etaInner η v v = 0 := by
  have hpair := eta_biorthogonal_pairing η A hA hv hv
  have hne : star μ - μ ≠ 0 := by
    intro h0
    have him := congrArg Complex.im (sub_eq_zero.mp h0)
    simp only [RCLike.star_def, Complex.conj_im] at him
    exact hμ (by linarith)
  exact (mul_eq_zero.mp hpair).resolve_left hne

/-- Eigenvectors with `μ₂ ≠ conj μ₁` are `η`-orthogonal (`S3-19`, Pauli 1943; `R3.1`). -/
theorem eta_eigenvectors_orthogonal_of_ne_conj (η A : H →L[ℂ] H) (hA : IsEtaPseudoHermitian η A)
    {v₁ v₂ : H} {μ₁ μ₂ : ℂ} (hv₁ : A v₁ = μ₁ • v₁) (hv₂ : A v₂ = μ₂ • v₂)
    (hne : μ₂ ≠ star μ₁) :
    etaInner η v₁ v₂ = 0 := by
  have hpair := eta_biorthogonal_pairing η A hA hv₁ hv₂
  exact (mul_eq_zero.mp hpair).resolve_left (sub_ne_zero.mpr hne.symm)

/-- Characterization of `η`-unitarity in terms of `etaInner` (`S3-19`, `S3-22`, `R3.1`). -/
theorem isEtaUnitary_iff_etaInner (η U : H →L[ℂ] H) :
    IsEtaUnitary η U ↔ (∀ u v : H, etaInner η (U u) (U v) = etaInner η u v) ∧ Function.Bijective U := by
  constructor
  · rintro ⟨hU, hBij⟩
    refine ⟨fun u v => ?_, hBij⟩
    have hu : (ContinuousLinearMap.adjoint U) (η (U u)) = η u := by
      simpa using congrArg (fun T : H →L[ℂ] H => T u) hU
    calc
      etaInner η (U u) (U v) = ⟪η (U u), U v⟫_ℂ := rfl
      _ = ⟪(ContinuousLinearMap.adjoint U) (η (U u)), v⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_left U v (η (U u))).symm
      _ = ⟪η u, v⟫_ℂ := by rw [hu]
      _ = etaInner η u v := rfl
  · rintro ⟨hIso, hBij⟩
    refine ⟨?_, hBij⟩
    ext u
    apply ext_inner_right ℂ
    intro v
    calc
      ⟪((ContinuousLinearMap.adjoint U).comp (η.comp U)) u, v⟫_ℂ
          = ⟪(ContinuousLinearMap.adjoint U) (η (U u)), v⟫_ℂ := rfl
      _ = ⟪η (U u), U v⟫_ℂ := ContinuousLinearMap.adjoint_inner_left U v (η (U u))
      _ = ⟪η u, v⟫_ℂ := hIso u v

end EtaPseudoHermitian

/-- A **complex Krein space** `(H, [·,·]_J)` (`S3-18`, `S3-21`, `S3-22`, `R3.1`), kept strictly
separate from real `InfoGeometry.Krein.KreinSpace` (`ℝ`) so `ℂ` scalar restriction never
causes typeclass diamonds. -/
class ComplexKreinSpace (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- Fundamental symmetry over `ℂ`: involutive, self-adjoint linear isometry equivalence. -/
  J : H ≃ₗᵢ[ℂ] H
  /-- `J² = id`. -/
  J_invol : ∀ x : H, J (J x) = x
  /-- `⟪J u, v⟫_ℂ = ⟪u, J v⟫_ℂ`. -/
  J_selfAdj : ∀ u v : H, ⟪J u, v⟫_ℂ = ⟪u, J v⟫_ℂ

namespace ComplexKreinSpace

/-- Every complete complex Hilbert space carries a canonical `ComplexKreinSpace` structure
with `J = id` (`S3-21`, `R3.1`; also provides T17 inhabitant on `ℂ`). -/
instance (priority := 100) instOfHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    ComplexKreinSpace H where
  J := LinearIsometryEquiv.refl ℂ H
  J_invol := fun _ => rfl
  J_selfAdj := fun _ _ => rfl

section Operations

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [ComplexKreinSpace H]

/-- Fundamental symmetry as a continuous `ℂ`-linear endomorphism (`S3-21`, `R3.1`). -/
def jCLM : H →L[ℂ] H :=
  (J : H ≃ₗᵢ[ℂ] H).toLinearIsometry.toContinuousLinearMap

@[simp] theorem jCLM_apply (x : H) : jCLM x = (J : H ≃ₗᵢ[ℂ] H) x := rfl

/-- `jCLM ∘ jCLM = 1` (`S3-21`, `R3.1`). -/
@[simp] theorem jCLM_comp_self :
    jCLM.comp (jCLM (H := H)) = ContinuousLinearMap.id ℂ H := by
  ext x; simp [ComplexKreinSpace.J_invol]

/-- `jCLM * jCLM = 1` (`S3-21`, `R3.1`). -/
@[simp] theorem jCLM_mul_self : jCLM (H := H) * jCLM (H := H) = 1 :=
  jCLM_comp_self

/-- `jCLM` is Hilbert-self-adjoint (`S3-21`, `R3.1`). -/
@[simp] theorem adjoint_jCLM :
    ContinuousLinearMap.adjoint (jCLM (H := H)) = jCLM (H := H) := by
  ext x; apply ext_inner_right ℂ; intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [jCLM_apply, ComplexKreinSpace.J_selfAdj]

/-- `jCLM` is a unit in `H →L[ℂ] H` with inverse `jCLM` (`S3-21`, `R3.1`). -/
def jCLMUnit : (H →L[ℂ] H)ˣ where
  val := jCLM (H := H)
  inv := jCLM (H := H)
  val_inv := jCLM_mul_self
  inv_val := jCLM_mul_self

theorem jCLM_isUnit : IsUnit (jCLM (H := H)) := ⟨jCLMUnit, rfl⟩

/-- Native complex indefinite Krein pairing `[u, v]_J = ⟪J u, v⟫_ℂ` (`S3-18`, `S3-21`, `R3.1`). -/
def complexKreinInner (u v : H) : ℂ := ⟪jCLM u, v⟫_ℂ

/-- Complex Krein adjoint `A♯ = J A† J` (`S3-21`, `S3-22`, `R3.1`). -/
def complexKreinAdjoint (A : H →L[ℂ] H) : H →L[ℂ] H :=
  jCLM.comp ((ContinuousLinearMap.adjoint A).comp jCLM)

@[simp] theorem complexKreinAdjoint_id :
    complexKreinAdjoint (H := H) (1 : H →L[ℂ] H) = 1 := by
  change jCLM.comp ((ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ H)).comp jCLM) =
    ContinuousLinearMap.id ℂ H
  rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp, jCLM_comp_self]

@[simp] theorem complexKreinAdjoint_mul (A B : H →L[ℂ] H) :
    complexKreinAdjoint (A * B) = complexKreinAdjoint B * complexKreinAdjoint A := by
  change jCLM.comp ((ContinuousLinearMap.adjoint (A.comp B)).comp jCLM) =
    (jCLM.comp ((ContinuousLinearMap.adjoint B).comp jCLM)).comp
      (jCLM.comp ((ContinuousLinearMap.adjoint A).comp jCLM))
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc jCLM jCLM, jCLM_comp_self, ContinuousLinearMap.id_comp]

/-- `A` is complex Krein-self-adjoint when `A♯ = A` (`S3-19`, `S3-21`, `R3.1`). -/
def IsComplexKreinSelfAdjoint (A : H →L[ℂ] H) : Prop :=
  complexKreinAdjoint A = A

/-- `U` is complex Krein-unitary when `U♯ ∘ U = 1` and `U ∘ U♯ = 1` (`S3-22`, `R3.1`). -/
def IsComplexKreinUnitary (U : H →L[ℂ] H) : Prop :=
  (complexKreinAdjoint U).comp U = 1 ∧ U.comp (complexKreinAdjoint U) = 1

/-- Equivalence between complex Krein-self-adjointness and `jCLM`-pseudo-Hermiticity
(`S3-19`, `S3-21`, `R3.1`). -/
theorem isComplexKreinSelfAdjoint_iff_eta (A : H →L[ℂ] H) :
    IsComplexKreinSelfAdjoint A ↔ IsEtaPseudoHermitian (jCLM (H := H)) A := by
  constructor
  · intro h
    change (ContinuousLinearMap.adjoint A) * jCLM = jCLM * A
    have h1 : jCLM * complexKreinAdjoint A = jCLM * A := congrArg (jCLM * ·) h
    have h2 : jCLM * complexKreinAdjoint A = (ContinuousLinearMap.adjoint A) * jCLM := by
      change jCLM * ((jCLM * ContinuousLinearMap.adjoint A) * jCLM) = _
      rw [← mul_assoc jCLM (jCLM * ContinuousLinearMap.adjoint A),
        ← mul_assoc jCLM jCLM, jCLM_mul_self, one_mul]
    exact h2.symm.trans h1
  · intro h
    change (jCLM * (ContinuousLinearMap.adjoint A)) * jCLM = A
    have h' : (ContinuousLinearMap.adjoint A) * jCLM = jCLM * A := h
    rw [mul_assoc, h', ← mul_assoc, jCLM_mul_self, one_mul]

/-- Positive fundamental subspace `K₊ = ker (J - I)` of a `ComplexKreinSpace` (`S3-21`,
`R3.1`). -/
def posSubspace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ComplexKreinSpace H] : Submodule ℂ H :=
  LinearMap.ker ((jCLM (H := H) : H →ₗ[ℂ] H) - LinearMap.id)

/-- Negative fundamental subspace `K₋ = ker (J + I)` of a `ComplexKreinSpace` (`S3-21`,
`R3.1`). -/
def negSubspace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ComplexKreinSpace H] : Submodule ℂ H :=
  LinearMap.ker ((jCLM (H := H) : H →ₗ[ℂ] H) + LinearMap.id)

@[simp] theorem mem_posSubspace_iff (x : H) :
    x ∈ posSubspace H ↔ (J : H ≃ₗᵢ[ℂ] H) x = x := by
  simp [posSubspace, LinearMap.mem_ker, sub_eq_zero, jCLM_apply]

@[simp] theorem mem_negSubspace_iff (x : H) :
    x ∈ negSubspace H ↔ (J : H ≃ₗᵢ[ℂ] H) x = -x := by
  simp [negSubspace, LinearMap.mem_ker, add_eq_zero_iff_eq_neg, jCLM_apply]

/-- Positive complex Krein projector `P₊ = (1/2)(1 + J)` (`S3-21`, `R3.1`). -/
def P_plus : H →L[ℂ] H := ((2 : ℂ)⁻¹) • (1 + jCLM (H := H))

/-- Negative complex Krein projector `P₋ = (1/2)(1 - J)` (`S3-21`, `R3.1`). -/
def P_minus : H →L[ℂ] H := ((2 : ℂ)⁻¹) • (1 - jCLM (H := H))

/-- `P₊ + P₋ = 1` (`S3-21`, `R3.1`). -/
theorem P_plus_add_P_minus : P_plus (H := H) + P_minus (H := H) = 1 := by
  ext x
  change ((2 : ℂ)⁻¹) • (x + jCLM x) + ((2 : ℂ)⁻¹) • (x - jCLM x) = x
  rw [← smul_add]
  have hsum : (x + jCLM x) + (x - jCLM x) = (2 : ℂ) • x := by
    rw [two_smul]; abel
  rw [hsum, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- `P₊ - P₋ = J` (`S3-21`, `R3.1`). -/
theorem P_plus_sub_P_minus : P_plus (H := H) - P_minus (H := H) = jCLM (H := H) := by
  ext x
  change ((2 : ℂ)⁻¹) • (x + jCLM x) - ((2 : ℂ)⁻¹) • (x - jCLM x) = jCLM x
  rw [← smul_sub]
  have hdiff : (x + jCLM x) - (x - jCLM x) = (2 : ℂ) • jCLM x := by
    rw [two_smul]; abel
  rw [hdiff, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- Complex fundamental decomposition `K = K₊ ⊕ K₋` (`S3-21`, `R3.1`). -/
theorem posSubspace_isCompl_negSubspace : IsCompl (posSubspace H) (negSubspace H) := by
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨hxP, hxN⟩
    change x ∈ posSubspace H at hxP
    change x ∈ negSubspace H at hxN
    rw [mem_posSubspace_iff] at hxP
    rw [mem_negSubspace_iff] at hxN
    have h2 : (2 : ℂ) • x = 0 := by
      rw [two_smul]
      nth_rw 2 [hxP.symm.trans hxN]
      exact add_neg_cancel x
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro x
    refine ⟨P_plus x, P_minus x, ?_, ?_, ?_⟩
    · rw [mem_posSubspace_iff]
      change (J : H ≃ₗᵢ[ℂ] H) (((2 : ℂ)⁻¹) • (x + (J : H ≃ₗᵢ[ℂ] H) x)) =
        ((2 : ℂ)⁻¹) • (x + (J : H ≃ₗᵢ[ℂ] H) x)
      rw [map_smul, map_add, ComplexKreinSpace.J_invol, add_comm]
    · rw [mem_negSubspace_iff]
      change (J : H ≃ₗᵢ[ℂ] H) (((2 : ℂ)⁻¹) • (x - (J : H ≃ₗᵢ[ℂ] H) x)) =
        -(((2 : ℂ)⁻¹) • (x - (J : H ≃ₗᵢ[ℂ] H) x))
      rw [map_smul, map_sub, ComplexKreinSpace.J_invol, ← smul_neg, neg_sub]
    · have h := congrArg (fun T : H →L[ℂ] H => T x) (P_plus_add_P_minus (H := H))
      simpa using h

/-! ### Conjugate-Pair Spectral Reflection (`S3-19`, `S3-22`, `R3.1`) -/

private theorem spectrum_conj_by_jCLM (T : H →L[ℂ] H) :
    spectrum ℂ (jCLM (H := H) * T * jCLM (H := H)) = spectrum ℂ T := by
  ext μ
  simp only [spectrum.mem_iff]
  apply not_congr
  have hEq : algebraMap ℂ (H →L[ℂ] H) μ - jCLM (H := H) * T * jCLM (H := H) =
      jCLM (H := H) * (algebraMap ℂ (H →L[ℂ] H) μ - T) * jCLM (H := H) := by
    rw [Algebra.algebraMap_eq_smul_one, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, ← jCLM_mul_self (H := H)]
  rw [hEq]
  constructor
  · intro hU
    have h1 := (jCLM_isUnit (H := H)).mul (hU.mul (jCLM_isUnit (H := H)))
    have hL : jCLM (H := H) *
        (jCLM (H := H) * (algebraMap ℂ (H →L[ℂ] H) μ - T) * jCLM (H := H) * jCLM (H := H)) =
        algebraMap ℂ (H →L[ℂ] H) μ - T := by
      calc
        jCLM * (jCLM * (algebraMap ℂ (H →L[ℂ] H) μ - T) * jCLM * jCLM)
            = (jCLM * jCLM) * (algebraMap ℂ (H →L[ℂ] H) μ - T) * (jCLM * jCLM) := by
              simp only [mul_assoc]
        _ = algebraMap ℂ (H →L[ℂ] H) μ - T := by rw [jCLM_mul_self, one_mul, mul_one]
    rw [hL] at h1
    exact h1
  · intro hU
    exact ((jCLM_isUnit (H := H)).mul hU).mul (jCLM_isUnit (H := H))

/-- **Conjugate-Pair Spectral Reflection for `J`-Self-Adjoint Operators** (`S3-19`, Pauli 1943;
`S3-22`, Iokhvidov–Krein 1956 Prop. 1; `R3.1`): `μ ∈ σ(A) ↔ star μ ∈ σ(A)` in arbitrary
(possibly infinite) dimension. -/
theorem IsComplexKreinSelfAdjoint.mem_spectrum_conj_iff {A : H →L[ℂ] H}
    (hA : IsComplexKreinSelfAdjoint A) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ star μ ∈ spectrum ℂ A := by
  have hstar : star A = jCLM (H := H) * A * jCLM (H := H) := by
    have hAdj := hA
    change jCLM (H := H) * ContinuousLinearMap.adjoint A * jCLM (H := H) = A at hAdj
    calc
      star A = ContinuousLinearMap.adjoint A := rfl
      _ = (jCLM * jCLM) * ContinuousLinearMap.adjoint A * (jCLM * jCLM) := by
            rw [jCLM_mul_self, one_mul, mul_one]
      _ = jCLM * (jCLM * ContinuousLinearMap.adjoint A * jCLM) * jCLM := by
            simp only [mul_assoc]
      _ = jCLM * A * jCLM := by rw [hAdj]
  have h1 : μ ∈ spectrum ℂ A ↔ star μ ∈ spectrum ℂ (star A) := by
    simp only [spectrum.mem_iff]
    apply not_congr
    have hEq : algebraMap ℂ (H →L[ℂ] H) (star μ) - star A =
        star (algebraMap ℂ (H →L[ℂ] H) μ - A) := by
      simp [Algebra.algebraMap_eq_smul_one, star_smul]
    rw [hEq]
    exact isUnit_star.symm
  rw [h1, hstar, spectrum_conj_by_jCLM]

/-- Conjugate-pair eigenvalue symmetry for finite-dimensional `J`-self-adjoint operators
(`S3-19`, `S3-22`, `R3.1`). -/
theorem IsComplexKreinSelfAdjoint.hasEigenvalue_conj_iff [FiniteDimensional ℂ H]
    {A : H →L[ℂ] H} (hA : IsComplexKreinSelfAdjoint A) (μ : ℂ) :
    Module.End.HasEigenvalue (A : H →ₗ[ℂ] H) μ ↔
      Module.End.HasEigenvalue (A : H →ₗ[ℂ] H) (star μ) := by
  have hspec : ∀ ν : ℂ, ν ∈ spectrum ℂ (A : H →ₗ[ℂ] H) ↔ ν ∈ spectrum ℂ A := fun ν => by
    simp only [spectrum.mem_iff]
    apply not_congr
    have hEq : (algebraMap ℂ (H →ₗ[ℂ] H) ν - (A : H →ₗ[ℂ] H)) =
        ((algebraMap ℂ (H →L[ℂ] H) ν - A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [hEq, Module.End.isUnit_iff, ContinuousLinearMap.isUnit_iff_bijective]
    rfl
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Module.End.hasEigenvalue_iff_mem_spectrum,
    hspec μ, hspec (star μ)]
  exact hA.mem_spectrum_conj_iff μ

/-- `0` is not in the spectrum of a `J`-unitary operator (`S3-22`, `R3.1`). -/
theorem IsComplexKreinUnitary.zero_notMem_spectrum {U : H →L[ℂ] H}
    (hU : IsComplexKreinUnitary U) : (0 : ℂ) ∉ spectrum ℂ U := by
  intro h0
  rw [spectrum.mem_iff, map_zero, zero_sub] at h0
  exact h0 ⟨⟨-U, -(complexKreinAdjoint U), by rw [neg_mul_neg]; exact hU.2,
    by rw [neg_mul_neg]; exact hU.1⟩, rfl⟩

/-- **Conjugate-Reciprocal Spectral Reflection for `J`-Unitary Operators** (`S3-22`,
Iokhvidov–Krein 1956, Schulz-Baldes 2016 Prop. 1(v); `R3.1`):
`μ ∈ σ(U) ↔ (star μ)⁻¹ ∈ σ(U)` for `μ ≠ 0` in arbitrary dimension. -/
theorem IsComplexKreinUnitary.mem_spectrum_conj_inv_iff {U : H →L[ℂ] H}
    (hU : IsComplexKreinUnitary U) {μ : ℂ} (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ U ↔ (star μ)⁻¹ ∈ spectrum ℂ U := by
  let u : (H →L[ℂ] H)ˣ := ⟨U, complexKreinAdjoint U, hU.2, hU.1⟩
  let r : ℂˣ := Units.mk0 μ hμ
  have h1 : (r : ℂ) ∈ spectrum ℂ (u : H →L[ℂ] H) ↔
      ((r⁻¹ : ℂˣ) : ℂ) ∈ spectrum ℂ ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) :=
    spectrum.inv_mem_iff
  have hr : (r : ℂ) = μ := rfl
  have hri : ((r⁻¹ : ℂˣ) : ℂ) = μ⁻¹ := rfl
  have hinv_eq : ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) =
      jCLM (H := H) * star U * jCLM (H := H) := rfl
  have h2 : μ⁻¹ ∈ spectrum ℂ (jCLM (H := H) * star U * jCLM (H := H)) ↔
      μ⁻¹ ∈ spectrum ℂ (star U) := by
    rw [spectrum_conj_by_jCLM]
  have h3 : μ⁻¹ ∈ spectrum ℂ (star U) ↔ star (μ⁻¹) ∈ spectrum ℂ U := by
    simp only [spectrum.mem_iff]
    apply not_congr
    have hEq : algebraMap ℂ (H →L[ℂ] H) (μ⁻¹) - star U =
        star (algebraMap ℂ (H →L[ℂ] H) (star (μ⁻¹)) - U) := by
      simp [Algebra.algebraMap_eq_smul_one, star_smul]
    rw [hEq]
    exact isUnit_star
  have h4 : star (μ⁻¹) = (star μ)⁻¹ := star_inv₀ μ
  rw [hr, hri] at h1
  simpa [u, hinv_eq, h4] using h1.trans (h2.trans h3)

/-- Biorthogonal pairing for eigenvectors of a `J`-unitary operator: `(1 - conj μ₁ * μ₂) *
[v₁, v₂]_J = 0` (`S3-22`, Iokhvidov–Krein; `R3.1`). -/
theorem IsComplexKreinUnitary.eigenvector_pairing {U : H →L[ℂ] H}
    (hU : IsComplexKreinUnitary U) {v₁ v₂ : H} {μ₁ μ₂ : ℂ}
    (hv₁ : U v₁ = μ₁ • v₁) (hv₂ : U v₂ = μ₂ • v₂) :
    (1 - star μ₁ * μ₂) * complexKreinInner v₁ v₂ = 0 := by
  have hIso : complexKreinInner (U v₁) (U v₂) = complexKreinInner v₁ v₂ := by
    have hL : (ContinuousLinearMap.adjoint U) (jCLM (U v₁)) = jCLM v₁ := by
      have hc := congrArg (fun T : H →L[ℂ] H => jCLM (T v₁)) hU.1
      change jCLM (jCLM ((ContinuousLinearMap.adjoint U) (jCLM (U v₁)))) = jCLM v₁ at hc
      simpa [jCLM_apply, ComplexKreinSpace.J_invol] using hc
    calc
      complexKreinInner (U v₁) (U v₂) = ⟪jCLM (U v₁), U v₂⟫_ℂ := rfl
      _ = ⟪(ContinuousLinearMap.adjoint U) (jCLM (U v₁)), v₂⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_left U v₂ (jCLM (U v₁))).symm
      _ = ⟪jCLM v₁, v₂⟫_ℂ := by rw [hL]
  have hLHS : complexKreinInner (U v₁) (U v₂) = (star μ₁ * μ₂) * complexKreinInner v₁ v₂ := by
    rw [hv₁, hv₂]
    calc
      complexKreinInner (μ₁ • v₁) (μ₂ • v₂) = ⟪μ₁ • jCLM v₁, μ₂ • v₂⟫_ℂ := by
        simp [complexKreinInner, map_smul]
      _ = (starRingEnd ℂ) μ₁ * (μ₂ * ⟪jCLM v₁, v₂⟫_ℂ) := by
        rw [inner_smul_left, inner_smul_right]
      _ = (star μ₁ * μ₂) * complexKreinInner v₁ v₂ := by
        change (star μ₁) * (μ₂ * complexKreinInner v₁ v₂) = _
        ring
  rw [sub_mul, one_mul, ← hLHS, hIso, sub_self]

/-- Any eigenvector of a `J`-unitary operator with `‖μ‖ ≠ 1` is `J`-null (`S3-22`, `R3.1`). -/
theorem IsComplexKreinUnitary.nonunit_eigenvector_null {U : H →L[ℂ] H}
    (hU : IsComplexKreinUnitary U) {v : H} {μ : ℂ} (hv : U v = μ • v) (hμ : ‖μ‖ ≠ 1) :
    complexKreinInner v v = 0 := by
  have hpair := hU.eigenvector_pairing hv hv
  have hne : 1 - star μ * μ ≠ 0 := by
    intro h0
    have heq : star μ * μ = 1 := (sub_eq_zero.mp h0).symm
    have hn : ‖μ‖ ^ 2 = 1 := by
      have hconj : star μ * μ = ((‖μ‖ ^ 2 : ℝ) : ℂ) := by
        rw [RCLike.star_def, Complex.conj_mul']
        push_cast; rfl
      rw [hconj] at heq
      have hre := congrArg Complex.re heq
      rw [Complex.ofReal_re, Complex.one_re] at hre
      exact hre
    have hnn : ‖μ‖ = 1 := by nlinarith [norm_nonneg μ]
    exact hμ hnn
  exact (mul_eq_zero.mp hpair).resolve_left hne

/-! ### Complex $J$-Cayley Transform $C_{z,\zeta}$ (`S3-22`, `R3.1`) -/

/-- Complex `J`-Cayley transform `C_{z,ζ}(A) = ζ (A - z 1)(A - z* 1)⁻¹` (`S3-22`,
Iokhvidov–Krein 1956–1959; Schulz-Baldes 2016 §2.4 Prop. 3; `R3.1`). -/
def complexCayley (z ζ : ℂ) (A : H →L[ℂ] H) (hInv : IsUnit (A - star z • 1)) : H →L[ℂ] H :=
  ζ • ((A - z • 1).comp (hInv.unit⁻¹ : (H →L[ℂ] H)ˣ).val)

/-- Inverse complex `J`-Cayley transform `C_{z,ζ}⁻¹(U) = (z ζ 1 - z* U)(ζ 1 - U)⁻¹` (`S3-22`,
Iokhvidov–Krein 1956–1959; Schulz-Baldes 2016 §2.4 Prop. 3; `R3.1`). -/
def complexCayleyInv (z ζ : ℂ) (U : H →L[ℂ] H) (hInv : IsUnit (ζ • 1 - U)) : H →L[ℂ] H :=
  (z • ζ • (1 : H →L[ℂ] H) - star z • U).comp (hInv.unit⁻¹ : (H →L[ℂ] H)ˣ).val

private lemma complexKreinAdjoint_smul (c : ℂ) (A : H →L[ℂ] H) :
    complexKreinAdjoint (H := H) (c • A) = star c • complexKreinAdjoint A := by
  have hAdjSmul : ContinuousLinearMap.adjoint (c • A) = star c • ContinuousLinearMap.adjoint A := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
    simp only [FunLike.coe_smul, Pi.smul_apply, inner_smul_left, inner_smul_right,
      RCLike.star_def, Complex.conj_conj, ContinuousLinearMap.adjoint_inner_left]
  ext x
  simp [complexKreinAdjoint, hAdjSmul]

private lemma complexKreinAdjoint_smul_one (c : ℂ) :
    complexKreinAdjoint (H := H) (c • (1 : H →L[ℂ] H)) = star c • (1 : H →L[ℂ] H) := by
  rw [complexKreinAdjoint_smul, complexKreinAdjoint_id]

private lemma complexKreinAdjoint_add (A B : H →L[ℂ] H) :
    complexKreinAdjoint (H := H) (A + B) = complexKreinAdjoint A + complexKreinAdjoint B := by
  ext x; simp [complexKreinAdjoint, map_add]

private lemma complexKreinAdjoint_sub (A B : H →L[ℂ] H) :
    complexKreinAdjoint (H := H) (A - B) = complexKreinAdjoint A - complexKreinAdjoint B := by
  ext x; simp [complexKreinAdjoint, map_sub]

private lemma isUnit_sub_smul_of_kreinSelfAdj {A : H →L[ℂ] H}
    (hA : IsComplexKreinSelfAdjoint A) {z : ℂ} (hInv : IsUnit (A - star z • 1)) :
    IsUnit (A - z • 1) := by
  have hEq : complexKreinAdjoint (A - star z • 1) = A - z • 1 := by
    rw [complexKreinAdjoint_sub, hA, complexKreinAdjoint_smul_one, star_star]
  rw [← hEq]
  refine ⟨⟨complexKreinAdjoint hInv.unit.val,
    complexKreinAdjoint (hInv.unit⁻¹ : (H →L[ℂ] H)ˣ).val, ?_, ?_⟩, rfl⟩
  · rw [← complexKreinAdjoint_mul, Units.inv_mul, complexKreinAdjoint_id]
  · rw [← complexKreinAdjoint_mul, Units.mul_inv, complexKreinAdjoint_id]

/-- Complex `J`-Cayley transform sends `J`-self-adjoint `A` (with `z* ∈ ρ(A)`, `|ζ| = 1`,
`Im z ≠ 0`) to a `J`-unitary operator `U = C_{z,ζ}(A)` with `ζ 1 - U` invertible and
`C_{z,ζ}⁻¹(U) = A` (`S3-22`, Iokhvidov–Krein; `R3.1`). -/
theorem complexCayley_isComplexKreinUnitary {z ζ : ℂ} (hz : z.im ≠ 0) (hζ : star ζ * ζ = 1)
    {A : H →L[ℂ] H} (hA : IsComplexKreinSelfAdjoint A) (hInv : IsUnit (A - star z • 1)) :
    IsComplexKreinUnitary (complexCayley z ζ A hInv) ∧
      IsUnit (ζ • 1 - complexCayley z ζ A hInv) ∧
      ∀ hInv' : IsUnit (ζ • 1 - complexCayley z ζ A hInv),
        complexCayleyInv z ζ (complexCayley z ζ A hInv) hInv' = A := by
  let U := complexCayley z ζ A hInv
  let invS : H →L[ℂ] H := (hInv.unit⁻¹ : (H →L[ℂ] H)ˣ).val
  have hL1 : invS * (A - star z • 1) = 1 := by
    rw [← hInv.unit_spec]
    exact Units.inv_mul hInv.unit
  have hR1 : (A - star z • 1) * invS = 1 := by
    rw [← hInv.unit_spec]
    exact Units.mul_inv hInv.unit
  have hUnitAz : IsUnit (A - z • 1) := isUnit_sub_smul_of_kreinSelfAdj hA hInv
  let invAz : H →L[ℂ] H := (hUnitAz.unit⁻¹ : (H →L[ℂ] H)ˣ).val
  have hLAz : invAz * (A - z • 1) = 1 := by
    rw [← hUnitAz.unit_spec]
    exact Units.inv_mul hUnitAz.unit
  have hRAz : (A - z • 1) * invAz = 1 := by
    rw [← hUnitAz.unit_spec]
    exact Units.mul_inv hUnitAz.unit
  have hEqAdj : complexKreinAdjoint (A - star z • 1) = A - z • 1 := by
    rw [complexKreinAdjoint_sub, hA, complexKreinAdjoint_smul_one, star_star]
  have hAdjInv : complexKreinAdjoint invS = invAz := by
    have hL : (A - z • 1) * complexKreinAdjoint invS = 1 := by
      rw [← hEqAdj, ← complexKreinAdjoint_mul, hL1, complexKreinAdjoint_id]
    calc
      complexKreinAdjoint invS
          = (invAz * (A - z • 1)) * complexKreinAdjoint invS := by rw [hLAz, one_mul]
      _ = invAz * ((A - z • 1) * complexKreinAdjoint invS) := mul_assoc _ _ _
      _ = invAz := by rw [hL, mul_one]
  have hAdjAz : complexKreinAdjoint (A - z • 1) = A - star z • 1 := by
    rw [complexKreinAdjoint_sub, hA, complexKreinAdjoint_smul_one]
  have h12 : (A - star z • 1) * (A - z • 1) = (A - z • 1) * (A - star z • 1) := by
    have hL : (A - star z • (1 : H →L[ℂ] H)) * (A - z • (1 : H →L[ℂ] H)) =
        A * A - z • A - star z • A + (star z * z) • (1 : H →L[ℂ] H) := by
      rw [sub_mul, mul_sub, mul_sub, mul_smul_comm, mul_one, smul_mul_assoc, one_mul,
        smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
      abel
    have hR : (A - z • (1 : H →L[ℂ] H)) * (A - star z • (1 : H →L[ℂ] H)) =
        A * A - z • A - star z • A + (z * star z) • (1 : H →L[ℂ] H) := by
      rw [sub_mul, mul_sub, mul_sub, mul_smul_comm, mul_one, smul_mul_assoc, one_mul,
        smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
      abel
    rw [hL, hR, mul_comm (star z) z]
  have hU_def : U = ζ • ((A - z • 1) * invS) := rfl
  have hU_adj : complexKreinAdjoint U = star ζ • ((A - star z • 1) * invAz) := by
    rw [hU_def, complexKreinAdjoint_smul, complexKreinAdjoint_mul, hAdjAz, hAdjInv]
    congr 1
    calc
      invAz * (A - star z • 1)
          = invAz * ((A - star z • 1) * ((A - z • 1) * invAz)) := by rw [hRAz, mul_one]
      _ = invAz * (((A - star z • 1) * (A - z • 1)) * invAz) := by rw [mul_assoc (A - star z • 1)]
      _ = invAz * (((A - z • 1) * (A - star z • 1)) * invAz) := by rw [h12]
      _ = (invAz * (A - z • 1)) * ((A - star z • 1) * invAz) := by simp only [mul_assoc]
      _ = (A - star z • 1) * invAz := by rw [hLAz, one_mul]
  have hUnitary : IsComplexKreinUnitary U := by
    refine ⟨?_, ?_⟩
    · change complexKreinAdjoint U * U = 1
      rw [hU_adj, hU_def, smul_mul_smul_comm, hζ, one_smul,
        mul_assoc (A - star z • 1), ← mul_assoc invAz, hLAz, one_mul, hR1]
    · change U * complexKreinAdjoint U = 1
      rw [hU_adj, hU_def, smul_mul_smul_comm, mul_comm ζ (star ζ), hζ, one_smul,
        mul_assoc (A - z • 1), ← mul_assoc invS, hL1, one_mul, hRAz]
  have hDiff : ζ • (1 : H →L[ℂ] H) - U = (ζ * (z - star z)) • invS := by
    have hZ : (A - star z • (1 : H →L[ℂ] H)) - (A - z • (1 : H →L[ℂ] H)) =
        (z - star z) • (1 : H →L[ℂ] H) := by
      rw [sub_smul]; abel
    calc
      ζ • (1 : H →L[ℂ] H) - U
          = ζ • ((A - star z • 1) * invS) - ζ • ((A - z • 1) * invS) := by
            rw [hR1, hU_def]
      _ = ζ • (((A - star z • 1) - (A - z • 1)) * invS) := by
            rw [← smul_sub, ← sub_mul]
      _ = ζ • (((z - star z) • (1 : H →L[ℂ] H)) * invS) := by rw [hZ]
      _ = (ζ * (z - star z)) • invS := by rw [smul_mul_assoc, one_mul, smul_smul]
  have hζne : ζ ≠ 0 := left_ne_zero_of_mul_eq_one (by rw [mul_comm]; exact hζ)
  have hzdiff : z - star z ≠ 0 := by
    intro h0
    have him := congrArg Complex.im (sub_eq_zero.mp h0)
    simp only [RCLike.star_def, Complex.conj_im] at him
    exact hz (by linarith)
  have hcne : ζ * (z - star z) ≠ 0 := mul_ne_zero hζne hzdiff
  have hUnitDiff : IsUnit (ζ • (1 : H →L[ℂ] H) - U) := by
    rw [hDiff]
    refine ⟨⟨(ζ * (z - star z)) • invS, (ζ * (z - star z))⁻¹ • (A - star z • 1), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hcne, one_smul, hL1]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hcne, one_smul, hR1]
  refine ⟨hUnitary, hUnitDiff, ?_⟩
  intro hInv'
  have hNum : z • ζ • (1 : H →L[ℂ] H) - star z • U =
      ((ζ * (z - star z)) • A) * invS := by
    have hZ : z • (A - star z • (1 : H →L[ℂ] H)) - star z • (A - z • (1 : H →L[ℂ] H)) =
        (z - star z) • A := by
      simp only [smul_sub, smul_smul, sub_smul]
      rw [mul_comm (star z) z]
      abel
    calc
      z • ζ • (1 : H →L[ℂ] H) - star z • U
          = z • ζ • ((A - star z • 1) * invS) - star z • ζ • ((A - z • 1) * invS) := by
            rw [hR1, hU_def]
      _ = ζ • (z • ((A - star z • 1) * invS) - star z • ((A - z • 1) * invS)) := by
            rw [smul_comm z ζ, smul_comm (star z) ζ, ← smul_sub]
      _ = ζ • ((z • (A - star z • 1) - star z • (A - z • 1)) * invS) := by
            congr 1
      _ = ζ • (((z - star z) • A) * invS) := by rw [hZ]
      _ = ((ζ * (z - star z)) • A) * invS := by
            rw [smul_mul_assoc, smul_mul_assoc, smul_smul]
  have hInvU : (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val = (ζ * (z - star z))⁻¹ • (A - star z • 1) := by
    have hmul : (ζ • (1 : H →L[ℂ] H) - U) * ((ζ * (z - star z))⁻¹ • (A - star z • 1)) = 1 := by
      rw [hDiff, smul_mul_smul_comm, mul_inv_cancel₀ hcne, one_smul, hL1]
    have hL' : (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val * (ζ • (1 : H →L[ℂ] H) - U) = 1 := by
      have hUinv := Units.inv_mul hInv'.unit
      rw [hInv'.unit_spec] at hUinv
      exact hUinv
    calc
      (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val
          = (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val *
              ((ζ • (1 : H →L[ℂ] H) - U) * ((ζ * (z - star z))⁻¹ • (A - star z • 1))) := by
            rw [hmul, mul_one]
      _ = ((hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val * (ζ • (1 : H →L[ℂ] H) - U)) *
            ((ζ * (z - star z))⁻¹ • (A - star z • 1)) := (mul_assoc _ _ _).symm
      _ = (ζ * (z - star z))⁻¹ • (A - star z • 1) := by rw [hL', one_mul]
  change (z • ζ • (1 : H →L[ℂ] H) - star z • U) * (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val = A
  rw [hNum, hInvU, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ hcne, one_smul, mul_assoc, hL1, mul_one]

/-- Inverse complex `J`-Cayley transform sends `J`-unitary `U` (with `ζ ∈ ρ(U)`, `|ζ| = 1`,
`Im z ≠ 0`) to a `J`-self-adjoint operator `A = C_{z,ζ}⁻¹(U)` with `z* ∈ ρ(A)` and
`C_{z,ζ}(A) = U` (`S3-22`, Iokhvidov–Krein; `R3.1`). -/
theorem complexCayleyInv_isComplexKreinSelfAdjoint {z ζ : ℂ} (hz : z.im ≠ 0) (hζ : star ζ * ζ = 1)
    {U : H →L[ℂ] H} (hU : IsComplexKreinUnitary U) (hInv : IsUnit (ζ • 1 - U)) :
    IsComplexKreinSelfAdjoint (complexCayleyInv z ζ U hInv) ∧
      IsUnit (complexCayleyInv z ζ U hInv - star z • 1) ∧
      ∀ hInv' : IsUnit (complexCayleyInv z ζ U hInv - star z • 1),
        complexCayley z ζ (complexCayleyInv z ζ U hInv) hInv' = U := by
  let A := complexCayleyInv z ζ U hInv
  let invD : H →L[ℂ] H := (hInv.unit⁻¹ : (H →L[ℂ] H)ˣ).val
  have hL1 : invD * (ζ • 1 - U) = 1 := by
    rw [← hInv.unit_spec]
    exact Units.inv_mul hInv.unit
  have hR1 : (ζ • 1 - U) * invD = 1 := by
    rw [← hInv.unit_spec]
    exact Units.mul_inv hInv.unit
  have hA_def : A = (z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD := rfl
  have hζne : ζ ≠ 0 := left_ne_zero_of_mul_eq_one (by rw [mul_comm]; exact hζ)
  have hU_unit : complexKreinAdjoint U * U = 1 ∧ U * complexKreinAdjoint U = 1 := hU
  have hComm : (z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD =
      invD * (z • ζ • (1 : H →L[ℂ] H) - star z • U) := by
    have h12 : (ζ • (1 : H →L[ℂ] H) - U) * (z • ζ • (1 : H →L[ℂ] H) - star z • U) =
        (z • ζ • (1 : H →L[ℂ] H) - star z • U) * (ζ • (1 : H →L[ℂ] H) - U) := by
      have hL : (ζ • (1 : H →L[ℂ] H) - U) * (z • ζ • (1 : H →L[ℂ] H) - star z • U) =
          (ζ * (z * ζ)) • (1 : H →L[ℂ] H) - (z * ζ) • U - (ζ * star z) • U +
            star z • (U * U) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
        module
      have hR : (z • ζ • (1 : H →L[ℂ] H) - star z • U) * (ζ • (1 : H →L[ℂ] H) - U) =
          (z * (ζ * ζ)) • (1 : H →L[ℂ] H) - (z * ζ) • U - (star z * ζ) • U +
            star z • (U * U) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
        module
      rw [hL, hR, mul_left_comm ζ z ζ, mul_comm ζ (star z)]
    calc
      (z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD
          = (invD * (ζ • 1 - U)) * ((z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD) := by
            rw [hL1, one_mul]
      _ = invD * (((ζ • 1 - U) * (z • ζ • (1 : H →L[ℂ] H) - star z • U)) * invD) := by
            simp only [mul_assoc]
      _ = invD * (((z • ζ • (1 : H →L[ℂ] H) - star z • U) * (ζ • 1 - U)) * invD) := by
            rw [h12]
      _ = invD * ((z • ζ • (1 : H →L[ℂ] H) - star z • U) * ((ζ • 1 - U) * invD)) := by
            simp only [mul_assoc]
      _ = invD * (z • ζ • (1 : H →L[ℂ] H) - star z • U) := by rw [hR1, mul_one]
  have hAdjInv : complexKreinAdjoint invD = -((ζ • U) * invD) := by
    have hAdjD : complexKreinAdjoint (ζ • (1 : H →L[ℂ] H) - U) =
        -((star ζ • (ζ • (1 : H →L[ℂ] H) - U)) * complexKreinAdjoint U) := by
      rw [complexKreinAdjoint_sub, complexKreinAdjoint_smul_one, smul_sub, sub_mul,
        smul_mul_assoc, smul_mul_assoc, smul_smul, one_mul, smul_mul_assoc, hU_unit.2, hζ,
        one_smul, neg_sub]
    have hR : complexKreinAdjoint (ζ • 1 - U) * complexKreinAdjoint invD = 1 := by
      rw [← complexKreinAdjoint_mul, hL1, complexKreinAdjoint_id]
    rw [hAdjD, neg_mul, mul_assoc] at hR
    have hDinv : -(invD * ((star ζ • (ζ • (1 : H →L[ℂ] H) - U)) *
        (complexKreinAdjoint U * complexKreinAdjoint invD))) = invD := by
      calc
        -(invD * ((star ζ • (ζ • (1 : H →L[ℂ] H) - U)) *
            (complexKreinAdjoint U * complexKreinAdjoint invD)))
            = invD * (-( (star ζ • (ζ • (1 : H →L[ℂ] H) - U)) *
                (complexKreinAdjoint U * complexKreinAdjoint invD))) := (mul_neg _ _).symm
        _ = invD * 1 := by rw [hR]
        _ = invD := mul_one _
    have hstep : -(star ζ • (complexKreinAdjoint U * complexKreinAdjoint invD)) = invD := by
      simpa [mul_smul_comm, ← mul_assoc, hL1] using hDinv
    have hstep2 : -(complexKreinAdjoint U * complexKreinAdjoint invD) = ζ • invD := by
      calc
        -(complexKreinAdjoint U * complexKreinAdjoint invD)
            = ζ • (-(star ζ • (complexKreinAdjoint U * complexKreinAdjoint invD))) := by
              rw [smul_neg, smul_smul, mul_comm ζ (star ζ), hζ, one_smul]
        _ = ζ • invD := by rw [hstep]
    calc
      complexKreinAdjoint invD = (U * complexKreinAdjoint U) * complexKreinAdjoint invD := by
        rw [hU_unit.2, one_mul]
      _ = U * (complexKreinAdjoint U * complexKreinAdjoint invD) := mul_assoc _ _ _
      _ = -(U * (-(complexKreinAdjoint U * complexKreinAdjoint invD))) := by rw [mul_neg, neg_neg]
      _ = -(U * (ζ • invD)) := by rw [hstep2]
      _ = -((ζ • U) * invD) := by rw [mul_smul_comm, smul_mul_assoc]
  have hSelfAdj : IsComplexKreinSelfAdjoint A := by
    change complexKreinAdjoint A = A
    rw [hA_def, complexKreinAdjoint_mul, hAdjInv, complexKreinAdjoint_sub, complexKreinAdjoint_smul,
      complexKreinAdjoint_smul_one, complexKreinAdjoint_smul, star_star]
    have hUinv : U * invD = invD * U := by
      have h12 : (ζ • (1 : H →L[ℂ] H) - U) * U = U * (ζ • (1 : H →L[ℂ] H) - U) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      calc
        U * invD = (invD * (ζ • 1 - U)) * (U * invD) := by rw [hL1, one_mul]
        _ = invD * (((ζ • 1 - U) * U) * invD) := by simp only [mul_assoc]
        _ = invD * ((U * (ζ • 1 - U)) * invD) := by rw [h12]
        _ = invD * (U * ((ζ • 1 - U) * invD)) := by simp only [mul_assoc]
        _ = invD * U := by rw [hR1, mul_one]
    have hMid : (ζ • U) * (star z • star ζ • (1 : H →L[ℂ] H) - z • complexKreinAdjoint U) =
        star z • U - z • ζ • (1 : H →L[ℂ] H) := by
      rw [smul_mul_assoc, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
        mul_smul_comm, hU_unit.2, smul_sub, smul_smul, smul_smul, smul_smul]
      have hsc1 : ζ * (star z * star ζ) = star z := by
        calc
          ζ * (star z * star ζ) = (star ζ * ζ) * star z := by ring
          _ = star z := by rw [hζ, one_mul]
      rw [mul_assoc ζ (star z) (star ζ), hsc1, mul_comm ζ z, smul_smul]
    calc
      -((ζ • U) * invD) * (star z • star ζ • (1 : H →L[ℂ] H) - z • complexKreinAdjoint U)
          = -(ζ • ((invD * U) * (star z • star ζ • (1 : H →L[ℂ] H) - z • complexKreinAdjoint U))) := by
            rw [neg_mul, smul_mul_assoc, smul_mul_assoc, hUinv]
      _ = -(invD * ((ζ • U) * (star z • star ζ • (1 : H →L[ℂ] H) - z • complexKreinAdjoint U))) := by
            rw [mul_assoc invD U, ← mul_smul_comm, ← smul_mul_assoc]
      _ = -(invD * (star z • U - z • ζ • (1 : H →L[ℂ] H))) := by rw [hMid]
      _ = invD * (z • ζ • (1 : H →L[ℂ] H) - star z • U) := by rw [← mul_neg, neg_sub]
      _ = (z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD := hComm.symm
  have hDiff : A - star z • (1 : H →L[ℂ] H) = ((z - star z) * ζ) • invD := by
    calc
      A - star z • (1 : H →L[ℂ] H)
          = (z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD -
              star z • ((ζ • (1 : H →L[ℂ] H) - U) * invD) := by
            rw [hR1, hA_def]
      _ = ((z • ζ • (1 : H →L[ℂ] H) - star z • U) -
            star z • (ζ • (1 : H →L[ℂ] H) - U)) * invD := by
          rw [← smul_mul_assoc, ← sub_mul]
      _ = (((z - star z) * ζ) • (1 : H →L[ℂ] H)) * invD := by
          congr 1
          rw [smul_sub, smul_smul, smul_smul, sub_sub_sub_cancel_right, ← sub_smul, sub_mul]
      _ = ((z - star z) * ζ) • invD := by rw [smul_mul_assoc, one_mul]
  have hzdiff : z - star z ≠ 0 := by
    intro h0
    have him := congrArg Complex.im (sub_eq_zero.mp h0)
    simp only [RCLike.star_def, Complex.conj_im] at him
    exact hz (by linarith)
  have hcne : (z - star z) * ζ ≠ 0 := mul_ne_zero hzdiff hζne
  have hUnitDiff : IsUnit (A - star z • (1 : H →L[ℂ] H)) := by
    rw [hDiff]
    refine ⟨⟨((z - star z) * ζ) • invD, ((z - star z) * ζ)⁻¹ • (ζ • 1 - U), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, mul_inv_cancel₀ hcne, one_smul, hL1]
    · rw [smul_mul_smul_comm, inv_mul_cancel₀ hcne, one_smul, hR1]
  refine ⟨hSelfAdj, hUnitDiff, ?_⟩
  intro hInv'
  have hAz : A - z • (1 : H →L[ℂ] H) = ((z - star z) • U) * invD := by
    calc
      A - z • (1 : H →L[ℂ] H)
          = (z • ζ • (1 : H →L[ℂ] H) - star z • U) * invD -
              z • ((ζ • (1 : H →L[ℂ] H) - U) * invD) := by
            rw [hR1, hA_def]
      _ = ((z • ζ • (1 : H →L[ℂ] H) - star z • U) -
            z • (ζ • (1 : H →L[ℂ] H) - U)) * invD := by
          rw [← smul_mul_assoc, ← sub_mul]
      _ = ((z - star z) • U) * invD := by
          congr 1
          rw [smul_sub, sub_smul]
          abel
  have hInvA : (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val = ((z - star z) * ζ)⁻¹ • (ζ • 1 - U) := by
    have hmul : (A - star z • (1 : H →L[ℂ] H)) * (((z - star z) * ζ)⁻¹ • (ζ • 1 - U)) = 1 := by
      rw [hDiff, smul_mul_smul_comm, mul_inv_cancel₀ hcne, one_smul, hL1]
    have hL' : (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val * (A - star z • (1 : H →L[ℂ] H)) = 1 := by
      have hUinv := Units.inv_mul hInv'.unit
      rw [hInv'.unit_spec] at hUinv
      exact hUinv
    calc
      (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val
          = (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val *
              ((A - star z • (1 : H →L[ℂ] H)) * (((z - star z) * ζ)⁻¹ • (ζ • 1 - U))) := by
            rw [hmul, mul_one]
      _ = ((hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val * (A - star z • (1 : H →L[ℂ] H))) *
            (((z - star z) * ζ)⁻¹ • (ζ • 1 - U)) := (mul_assoc _ _ _).symm
      _ = ((z - star z) * ζ)⁻¹ • (ζ • 1 - U) := by rw [hL', one_mul]
  change ζ • ((A - z • (1 : H →L[ℂ] H)) * (hInv'.unit⁻¹ : (H →L[ℂ] H)ˣ).val) = U
  rw [hAz, hInvA, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul, smul_smul,
    mul_comm ζ ((z - star z) * ζ)⁻¹, mul_assoc ((z - star z) * ζ)⁻¹ ζ (z - star z),
    mul_comm ζ (z - star z), inv_mul_cancel₀ hcne, one_smul, mul_assoc, hL1, mul_one]

end Operations

end ComplexKreinSpace

/-- Constructive complex Hilbert witness for `ComplexKreinSpace ℂ` (`S3-21`, `R3.1`; T17). -/
@[instance_reducible]
def complexLineKreinWitness : ComplexKreinSpace ℂ where
  J := LinearIsometryEquiv.refl ℂ ℂ
  J_invol := fun _ => rfl
  J_selfAdj := fun _ _ => rfl

/-! ## Part 4: `ComplexPontryaginSpace`, `ComplexPontryaginModel`, `ℂ²` Witnesses, Sylvester Inertia, & Pontryagin Invariant Subspace Theorem (`S3-18`..`S3-20`, `S3-22`, `R3.1`) -/

/-- A **complex Pontryagin space** $\Pi_\kappa$ (`S3-20`, Pontryagin 1944; `R3.1`): a
`ComplexKreinSpace` whose negative fundamental subspace `K₋ = ker (J + I)` has finite
complex dimension `κ`. -/
class ComplexPontryaginSpace (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends ComplexKreinSpace H where
  /-- Finite dimensionality of `negSubspace H` over `ℂ`. -/
  finite_neg : FiniteDimensional ℂ (ComplexKreinSpace.negSubspace (H := H))

attribute [instance] ComplexPontryaginSpace.finite_neg

namespace ComplexPontryaginSpace

/-- The negative index `κ = dim_ℂ K₋` of a complex Pontryagin space $\Pi_\kappa$ (`S3-20`,
`R3.1`). -/
def negIndex (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ComplexPontryaginSpace H] : ℕ :=
  Module.finrank ℂ (ComplexKreinSpace.negSubspace (H := H))

/-- Any complete complex Hilbert space is a complex Pontryagin space $\Pi_0$ (`S3-20`, `R3.1`). -/
instance (priority := 100) instOfHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    ComplexPontryaginSpace H :=
  { (ComplexKreinSpace.instOfHilbert (H := H)) with
    finite_neg := by
      have hbot : ComplexKreinSpace.negSubspace (H := H) = ⊥ := by
        ext x
        rw [ComplexKreinSpace.mem_negSubspace_iff]
        change x = -x ↔ x = 0
        constructor
        · intro h
          have h2 : (2 : ℂ) • x = 0 := by
            rw [two_smul]
            nth_rw 2 [h]
            exact add_neg_cancel x
          exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
        · intro h
          rw [h, neg_zero]
      rw [hbot]
      infer_instance }

end ComplexPontryaginSpace

/-- Constructive complex Hilbert $\Pi_0$ witness for `ComplexPontryaginSpace ℂ` (`S3-20`,
`R3.1`; T17). -/
@[instance_reducible]
def complexLinePontryaginWitness : ComplexPontryaginSpace ℂ :=
  ComplexPontryaginSpace.instOfHilbert

/-- Non-aliased signature `(p, q)` complex Pontryagin model wrapping `EuclideanSpace ℂ (Fin (p + q))`
with diagonal fundamental symmetry `+1` on `i < p` and `-1` on `p ≤ i` (`S3-18`..`S3-20`,
`S3-22`; `R3.1`). Defined as a `structure` (never `abbrev`) so `instOfHilbert` never shadows its
indefinite `ComplexKreinSpace` instance. -/
@[ext]
structure ComplexPontryaginModel (p q : ℕ) where
  /-- Underlying Euclidean vector in `ℂ^(p+q)`. -/
  toVec : EuclideanSpace ℂ (Fin (p + q))

namespace ComplexPontryaginModel

/-- Constructive zero-model inhabitant for `ComplexPontryaginModel 0 0` (`S3-20`, `R3.1`; T17). -/
def zeroModel : ComplexPontryaginModel 0 0 := ⟨0⟩

section Instances

variable {p q : ℕ}

lemma toVec_injective :
    Function.Injective (toVec : ComplexPontryaginModel p q → EuclideanSpace ℂ (Fin (p + q))) :=
  fun u v h => by cases u; cases v; cases h; rfl

instance : Add (ComplexPontryaginModel p q) := ⟨fun u v => ⟨u.toVec + v.toVec⟩⟩
instance : Zero (ComplexPontryaginModel p q) := ⟨⟨0⟩⟩
instance : Neg (ComplexPontryaginModel p q) := ⟨fun u => ⟨-u.toVec⟩⟩
instance : Sub (ComplexPontryaginModel p q) := ⟨fun u v => ⟨u.toVec - v.toVec⟩⟩
instance : SMul ℕ (ComplexPontryaginModel p q) := ⟨fun n u => ⟨n • u.toVec⟩⟩
instance : SMul ℤ (ComplexPontryaginModel p q) := ⟨fun z u => ⟨z • u.toVec⟩⟩
instance : SMul ℂ (ComplexPontryaginModel p q) := ⟨fun c u => ⟨c • u.toVec⟩⟩
instance : SMul ℝ (ComplexPontryaginModel p q) := ⟨fun r u => ⟨r • u.toVec⟩⟩

@[simp] lemma toVec_zero : (0 : ComplexPontryaginModel p q).toVec = 0 := rfl
@[simp] lemma toVec_add (u v : ComplexPontryaginModel p q) :
    (u + v).toVec = u.toVec + v.toVec := rfl
@[simp] lemma toVec_neg (u : ComplexPontryaginModel p q) : (-u).toVec = -u.toVec := rfl
@[simp] lemma toVec_sub (u v : ComplexPontryaginModel p q) :
    (u - v).toVec = u.toVec - v.toVec := rfl
@[simp] lemma toVec_smul (c : ℂ) (u : ComplexPontryaginModel p q) :
    (c • u).toVec = c • u.toVec := rfl

instance : AddCommGroup (ComplexPontryaginModel p q) :=
  Function.Injective.addCommGroup toVec toVec_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Additive equivalence `ComplexPontryaginModel p q ≃+ EuclideanSpace ℂ (Fin (p + q))`. -/
def toVecAddEquiv : ComplexPontryaginModel p q ≃+ EuclideanSpace ℂ (Fin (p + q)) where
  toFun := toVec
  invFun := mk
  left_inv u := by cases u; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

instance : NormedAddCommGroup (ComplexPontryaginModel p q) :=
  NormedAddCommGroup.induced (ComplexPontryaginModel p q) (EuclideanSpace ℂ (Fin (p + q)))
    toVecAddEquiv (AddEquiv.injective _)

instance : Module ℂ (ComplexPontryaginModel p q) :=
  Function.Injective.module ℂ toVecAddEquiv.toAddMonoidHom toVec_injective (fun _ _ => rfl)

instance : NormedSpace ℂ (ComplexPontryaginModel p q) where
  norm_smul_le c u := norm_smul_le c u.toVec

instance : Inner ℂ (ComplexPontryaginModel p q) where
  inner u v := ⟪u.toVec, v.toVec⟫_ℂ

instance : InnerProductSpace ℂ (ComplexPontryaginModel p q) where
  norm_smul_le c u := norm_smul_le c u.toVec
  norm_sq_eq_re_inner u := norm_sq_eq_re_inner u.toVec
  conj_inner_symm u v := inner_conj_symm (𝕜 := ℂ) u.toVec v.toVec
  add_left u v w := inner_add_left u.toVec v.toVec w.toVec
  smul_left u v c := inner_smul_left u.toVec v.toVec c

/-- Uniform equivalence `ComplexPontryaginModel p q ≃ᵤ EuclideanSpace ℂ (Fin (p + q))`. -/
def toVecUniformEquiv : ComplexPontryaginModel p q ≃ᵤ EuclideanSpace ℂ (Fin (p + q)) where
  toEquiv := toVecAddEquiv.toEquiv
  uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl
  uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id

instance : CompleteSpace (ComplexPontryaginModel p q) :=
  (completeSpace_congr (toVecUniformEquiv (p := p) (q := q)).isUniformEmbedding).mpr
    inferInstance

/-- Linear isometry equivalence `ComplexPontryaginModel p q ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (p + q))`. -/
def toVecLIE : ComplexPontryaginModel p q ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (p + q)) where
  toFun := toVec
  invFun := mk
  left_inv u := by cases u; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

instance : FiniteDimensional ℂ (ComplexPontryaginModel p q) :=
  (toVecLIE (p := p) (q := q)).symm.toLinearEquiv.finiteDimensional

/-- Signature sign `(+1 for i < p, -1 for p ≤ i)` on `Fin (p + q)`. -/
def sigSign (p q : ℕ) (i : Fin (p + q)) : ℂ :=
  if (i : ℕ) < p then 1 else -1

@[simp] lemma sigSign_sq (p q : ℕ) (i : Fin (p + q)) : sigSign p q i * sigSign p q i = 1 := by
  unfold sigSign; split_ifs <;> norm_num

@[simp] lemma star_sigSign (p q : ℕ) (i : Fin (p + q)) : star (sigSign p q i) = sigSign p q i := by
  unfold sigSign; split_ifs <;> simp

private def sigFlipMap : ComplexPontryaginModel p q →ₗ[ℂ] ComplexPontryaginModel p q where
  toFun u := ⟨WithLp.toLp 2 (fun i : Fin (p + q) => sigSign p q i * u.toVec.ofLp i)⟩
  map_add' u v := by
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i; simp [mul_add]
  map_smul' c u := by
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    simp only [RingHom.id_apply, toVec_smul, PiLp.smul_apply, smul_eq_mul]
    ring

private lemma sigFlipMap_invol (u : ComplexPontryaginModel p q) :
    sigFlipMap (sigFlipMap u) = u := by
  apply ComplexPontryaginModel.ext
  apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
  ext i
  change sigSign p q i * (sigSign p q i * u.toVec.ofLp i) = u.toVec.ofLp i
  rw [← mul_assoc, sigSign_sq, one_mul]

private lemma sigFlipMap_norm (u : ComplexPontryaginModel p q) : ‖sigFlipMap u‖ = ‖u‖ := by
  have hinner : ⟪sigFlipMap u, sigFlipMap u⟫_ℂ = ⟪u, u⟫_ℂ := by
    change ⟪(sigFlipMap u).toVec, (sigFlipMap u).toVec⟫_ℂ = ⟪u.toVec, u.toVec⟫_ℂ
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (sigSign p q i * u.toVec.ofLp i) * star (sigSign p q i * u.toVec.ofLp i) =
      u.toVec.ofLp i * star (u.toVec.ofLp i)
    rw [star_mul, star_sigSign]
    calc
      (sigSign p q i * u.toVec.ofLp i) * (star (u.toVec.ofLp i) * sigSign p q i)
          = (sigSign p q i * sigSign p q i) * (u.toVec.ofLp i * star (u.toVec.ofLp i)) := by ring
      _ = u.toVec.ofLp i * star (u.toVec.ofLp i) := by rw [sigSign_sq, one_mul]
  have hsq : ‖sigFlipMap u‖ ^ 2 = ‖u‖ ^ 2 := by
    have h1 := congrArg RCLike.re hinner
    rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h1
    exact h1
  nlinarith [norm_nonneg u, norm_nonneg (sigFlipMap u)]

private def sigFlipLIE : ComplexPontryaginModel p q ≃ₗᵢ[ℂ] ComplexPontryaginModel p q where
  toLinearEquiv := LinearEquiv.ofLinearMap sigFlipMap sigFlipMap
    (LinearMap.ext sigFlipMap_invol) (LinearMap.ext sigFlipMap_invol)
  norm_map' := sigFlipMap_norm

/-- Canonical signature-`(p, q)` `ComplexKreinSpace` instance on `ComplexPontryaginModel p q`
(`S3-20`, `S3-21`, `R3.1`). -/
instance (priority := 1000) instComplexKreinSpace :
    ComplexKreinSpace (ComplexPontryaginModel p q) where
  J := sigFlipLIE
  J_invol := sigFlipMap_invol
  J_selfAdj u v := by
    change ⟪(sigFlipMap u).toVec, v.toVec⟫_ℂ = ⟪u.toVec, (sigFlipMap v).toVec⟫_ℂ
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change v.toVec.ofLp i * star (sigSign p q i * u.toVec.ofLp i) =
      (sigSign p q i * v.toVec.ofLp i) * star (u.toVec.ofLp i)
    rw [star_mul, star_sigSign]
    ring

/-- Canonical `ComplexPontryaginSpace` instance on `ComplexPontryaginModel p q` (`S3-20`,
`R3.1`). -/
instance (priority := 1000) instComplexPontryaginSpace :
    ComplexPontryaginSpace (ComplexPontryaginModel p q) where
  finite_neg := inferInstance

private def negSubspaceEquiv :
    ComplexKreinSpace.negSubspace (H := ComplexPontryaginModel p q) ≃ₗ[ℂ] (Fin q → ℂ) where
  toFun u := fun j => u.1.toVec.ofLp (Fin.natAdd p j)
  invFun w := ⟨⟨WithLp.toLp 2 (Fin.append (fun _ : Fin p => (0 : ℂ)) w)⟩, by
    rw [ComplexKreinSpace.mem_negSubspace_iff]
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    change sigSign p q i * (Fin.append (fun _ : Fin p => (0 : ℂ)) w i) =
      -(Fin.append (fun _ : Fin p => (0 : ℂ)) w i)
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp [Fin.append_left]
    · have hge : ¬ ((p + (b : ℕ)) < p) := by omega
      simp [Fin.append_right, sigSign, hge]⟩
  left_inv u := by
    apply Subtype.ext
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    have hu := (ComplexKreinSpace.mem_negSubspace_iff u.1).mp u.2
    have hi := congrArg (fun z : ComplexPontryaginModel p q => z.toVec.ofLp i) hu
    change sigSign p q i * u.1.toVec.ofLp i = -u.1.toVec.ofLp i at hi
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have hlt : (a : ℕ) < p := a.isLt
      have h1 : u.1.toVec.ofLp (Fin.castAdd q a) = -u.1.toVec.ofLp (Fin.castAdd q a) := by
        have hia : sigSign p q (Fin.castAdd q a) * u.1.toVec.ofLp (Fin.castAdd q a) =
            -u.1.toVec.ofLp (Fin.castAdd q a) := by
          have hi' := congrArg (fun z : ComplexPontryaginModel p q =>
            z.toVec.ofLp (Fin.castAdd q a)) hu
          exact hi'
        simpa [sigSign, hlt] using hia
      have h2 : (2 : ℂ) * u.1.toVec.ofLp (Fin.castAdd q a) = 0 := by
        calc
          (2 : ℂ) * u.1.toVec.ofLp (Fin.castAdd q a)
              = u.1.toVec.ofLp (Fin.castAdd q a) + u.1.toVec.ofLp (Fin.castAdd q a) := two_mul _
          _ = u.1.toVec.ofLp (Fin.castAdd q a) + (-u.1.toVec.ofLp (Fin.castAdd q a)) := by
                nth_rw 2 [h1]
          _ = 0 := add_neg_cancel _
      have hz : u.1.toVec.ofLp (Fin.castAdd q a) = 0 :=
        (mul_eq_zero.mp h2).resolve_left (by norm_num)
      simp [Fin.append_left, hz]
    · simp [Fin.append_right]
  right_inv w := by
    ext j
    simp [Fin.append_right]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact negative index formula `negIndex (ComplexPontryaginModel p q) = q` (`S3-20`, `R3.1`). -/
theorem negIndex_eq : ComplexPontryaginSpace.negIndex (ComplexPontryaginModel p q) = q := by
  change Module.finrank ℂ (ComplexKreinSpace.negSubspace (H := ComplexPontryaginModel p q)) = q
  rw [(negSubspaceEquiv (p := p) (q := q)).finrank_eq, Module.finrank_fin_fun]

end Instances

end ComplexPontryaginModel

/-! ### T16 Non-Commutativity & Concrete `ℂ²` Witnesses (`S3-18`, `S3-19`, `S3-22`) -/

/-- Closed T16 non-commutativity witness for `M₂(ℂ)` matrices (`S3-18`, `R3.1`). -/
theorem complex_matrix2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℂ), 1; 0, 0], !![(0 : ℂ), 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add] at h00
  exact one_ne_zero h00

/-- Closed T16 non-commutativity witness for continuous linear endomorphisms on
`ComplexPontryaginModel 1 1` (`S3-18`, `R3.1`). -/
theorem complex_end11_noncommutative :
    ∃ A B : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1, A * B ≠ B * A := by
  let A : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u => ⟨WithLp.toLp 2 ![u.toVec.ofLp 1, 0]⟩
        map_add' := fun u v => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp
        map_smul' := fun c u => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp }
  let B : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u => ⟨WithLp.toLp 2 ![0, u.toVec.ofLp 0]⟩
        map_add' := fun u v => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp
        map_smul' := fun c u => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp }
  refine ⟨A, B, ?_⟩
  intro h
  let e0 : ComplexPontryaginModel 1 1 := ⟨WithLp.toLp 2 ![(1 : ℂ), 0]⟩
  have h0 := congrArg (fun T : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1 =>
    (T e0).toVec.ofLp 0) h
  simp [A, B, e0, ContinuousLinearMap.mul_def] at h0

/-- Concrete `ℂ²` (`ComplexPontryaginModel 1 1`) conjugate-pair spectral witness (`S3-18`,
`S3-19`, `R3.1`): `A = [[0, 1], [-1, 0]]` is `J`-self-adjoint (not Hilbert-self-adjoint) with
complex conjugate eigenvalues `±I` and nonzero `J`-null eigenvectors `(1, ±I)`. -/
theorem pauli_complex_2x2_conjugate_eigenvalues_witness :
    ∃ A : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1,
      ComplexKreinSpace.IsComplexKreinSelfAdjoint A ∧
      ¬ IsSelfAdjoint A ∧
      ∃ vPlus vMinus : ComplexPontryaginModel 1 1,
        vPlus ≠ 0 ∧ vMinus ≠ 0 ∧
        A vPlus = Complex.I • vPlus ∧
        A vMinus = (-Complex.I) • vMinus ∧
        ComplexKreinSpace.complexKreinInner vPlus vPlus = 0 ∧
        ComplexKreinSpace.complexKreinInner vMinus vMinus = 0 := by
  let A : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u => ⟨WithLp.toLp 2 ![u.toVec.ofLp 1, -u.toVec.ofLp 0]⟩
        map_add' := fun u v => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp [add_comm]
        map_smul' := fun c u => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp }
  have hA_app : ∀ (z : ComplexPontryaginModel 1 1),
      (A z).toVec.ofLp 0 = z.toVec.ofLp 1 ∧ (A z).toVec.ofLp 1 = -z.toVec.ofLp 0 :=
    fun _ => ⟨rfl, rfl⟩
  have hAdj : ContinuousLinearMap.adjoint A = -A := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
    change ⟪(-A u).toVec, v.toVec⟫_ℂ = ⟪u.toVec, (A v).toVec⟫_ℂ
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    erw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [ComplexPontryaginModel.toVec_neg, PiLp.neg_apply, star_neg, starRingEnd_apply]
    rw [(hA_app u).1, (hA_app u).2, (hA_app v).1, (hA_app v).2, star_neg]
    ring
  have hKreinSA : ComplexKreinSpace.IsComplexKreinSelfAdjoint A := by
    change ComplexKreinSpace.jCLM.comp ((ContinuousLinearMap.adjoint A).comp
      ComplexKreinSpace.jCLM) = A
    rw [hAdj]
    apply ContinuousLinearMap.ext
    intro u
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    have hJ0 : ∀ z : ComplexPontryaginModel 1 1,
        (ComplexKreinSpace.J z).toVec.ofLp 0 = z.toVec.ofLp 0 := fun z => by
      change ComplexPontryaginModel.sigSign 1 1 0 * z.toVec.ofLp 0 = z.toVec.ofLp 0
      simp [ComplexPontryaginModel.sigSign]
    have hJ1 : ∀ z : ComplexPontryaginModel 1 1,
        (ComplexKreinSpace.J z).toVec.ofLp 1 = -z.toVec.ofLp 1 := fun z => by
      change ComplexPontryaginModel.sigSign 1 1 1 * z.toVec.ofLp 1 = -z.toVec.ofLp 1
      simp [ComplexPontryaginModel.sigSign]
    ext i
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      neg_apply, ComplexKreinSpace.jCLM_apply, map_neg, ComplexKreinSpace.jCLM_apply,
      ComplexPontryaginModel.toVec_neg, PiLp.neg_apply]
    fin_cases i
    · dsimp
      rw [hJ0, (hA_app _).1, hJ1, neg_neg]
      exact (hA_app u).1.symm
    · dsimp
      rw [hJ1, (hA_app _).2, hJ0, neg_neg]
      exact (hA_app u).2.symm
  have hNotHilb : ¬ IsSelfAdjoint A := by
    intro hSA
    rw [ContinuousLinearMap.isSelfAdjoint_iff', hAdj] at hSA
    let e0 : ComplexPontryaginModel 1 1 := ⟨WithLp.toLp 2 ![(1 : ℂ), 0]⟩
    have hpt := congrArg (fun T : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1 =>
      (T e0).toVec.ofLp 1) hSA
    simp [A, e0] at hpt
    norm_num at hpt
  let vPlus : ComplexPontryaginModel 1 1 := ⟨WithLp.toLp 2 ![1, Complex.I]⟩
  let vMinus : ComplexPontryaginModel 1 1 := ⟨WithLp.toLp 2 ![1, -Complex.I]⟩
  have hvPlusNe : vPlus ≠ 0 := by
    intro h0
    have h00 := congrArg (fun z : ComplexPontryaginModel 1 1 => z.toVec.ofLp 0) h0
    simp [vPlus] at h00
  have hvMinusNe : vMinus ≠ 0 := by
    intro h0
    have h00 := congrArg (fun z : ComplexPontryaginModel 1 1 => z.toVec.ofLp 0) h0
    simp [vMinus] at h00
  have hEigPlus : A vPlus = Complex.I • vPlus := by
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    fin_cases i <;> simp [A, vPlus]
  have hEigMinus : A vMinus = (-Complex.I) • vMinus := by
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    fin_cases i <;> simp [A, vMinus]
  have hNullPlus : ComplexKreinSpace.complexKreinInner vPlus vPlus = 0 := by
    have hK := (ComplexKreinSpace.isComplexKreinSelfAdjoint_iff_eta A).mp hKreinSA
    exact eta_nonreal_eigenvector_null ComplexKreinSpace.jCLM A hK hEigPlus (by simp)
  have hNullMinus : ComplexKreinSpace.complexKreinInner vMinus vMinus = 0 := by
    have hK := (ComplexKreinSpace.isComplexKreinSelfAdjoint_iff_eta A).mp hKreinSA
    exact eta_nonreal_eigenvector_null ComplexKreinSpace.jCLM A hK hEigMinus (by simp)
  exact ⟨A, hKreinSA, hNotHilb, vPlus, vMinus, hvPlusNe, hvMinusNe, hEigPlus, hEigMinus,
    hNullPlus, hNullMinus⟩

/-- Concrete `ℂ²` (`ComplexPontryaginModel 1 1`) hyperbolic Lorentz-boost `J`-unitary witness
(`S3-22`, Iokhvidov–Krein; `R3.1`): `U = [[5/4, 3/4], [3/4, 5/4]]` is `J`-unitary with
off-circle conjugate-reciprocal eigenvalues `2` and `1/2 = (star 2)⁻¹` and `J`-null
eigenvectors `(1, 1)` and `(1, -1)`. -/
theorem lorentz_boost_2x2_jUnitary_witness :
    ∃ U : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1,
      ComplexKreinSpace.IsComplexKreinUnitary U ∧
      ∃ v1 v2 : ComplexPontryaginModel 1 1,
        v1 ≠ 0 ∧ v2 ≠ 0 ∧
        U v1 = (2 : ℂ) • v1 ∧
        U v2 = (2⁻¹ : ℂ) • v2 ∧
        ComplexKreinSpace.complexKreinInner v1 v1 = 0 ∧
        ComplexKreinSpace.complexKreinInner v2 v2 = 0 := by
  let U : ComplexPontryaginModel 1 1 →L[ℂ] ComplexPontryaginModel 1 1 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u => ⟨WithLp.toLp 2
          ![((5 / 4 : ℂ) * u.toVec.ofLp 0 + (3 / 4 : ℂ) * u.toVec.ofLp 1),
            ((3 / 4 : ℂ) * u.toVec.ofLp 0 + (5 / 4 : ℂ) * u.toVec.ofLp 1)]⟩
        map_add' := fun u v => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp <;> ring
        map_smul' := fun c u => by
          apply ComplexPontryaginModel.ext
          apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
          ext i; fin_cases i <;> simp <;> ring }
  have hU_app : ∀ (z : ComplexPontryaginModel 1 1),
      (U z).toVec.ofLp 0 = (5 / 4 : ℂ) * z.toVec.ofLp 0 + (3 / 4 : ℂ) * z.toVec.ofLp 1 ∧
      (U z).toVec.ofLp 1 = (3 / 4 : ℂ) * z.toVec.ofLp 0 + (5 / 4 : ℂ) * z.toVec.ofLp 1 :=
    fun _ => ⟨rfl, rfl⟩
  have hAdj : ContinuousLinearMap.adjoint U = U := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
    change ⟪(U u).toVec, v.toVec⟫_ℂ = ⟪u.toVec, (U v).toVec⟫_ℂ
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    erw [Fin.sum_univ_two, Fin.sum_univ_two]
    rw [(hU_app u).1, (hU_app u).2, (hU_app v).1, (hU_app v).2]
    simp only [starRingEnd_apply, star_add, star_mul, star_div₀]
    norm_num
    ring
  have hKreinAdj : ∀ u : ComplexPontryaginModel 1 1,
      ComplexKreinSpace.complexKreinAdjoint U u =
        ⟨WithLp.toLp 2
          ![((5 / 4 : ℂ) * u.toVec.ofLp 0 - (3 / 4 : ℂ) * u.toVec.ofLp 1),
            (-((3 / 4 : ℂ) * u.toVec.ofLp 0) + (5 / 4 : ℂ) * u.toVec.ofLp 1)]⟩ := by
    intro u
    change ComplexKreinSpace.jCLM (ContinuousLinearMap.adjoint U (ComplexKreinSpace.jCLM u)) = _
    rw [hAdj]
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    have hJ0 : ∀ z : ComplexPontryaginModel 1 1,
        (ComplexKreinSpace.J z).toVec.ofLp 0 = z.toVec.ofLp 0 := fun z => by
      change ComplexPontryaginModel.sigSign 1 1 0 * z.toVec.ofLp 0 = z.toVec.ofLp 0
      simp [ComplexPontryaginModel.sigSign]
    have hJ1 : ∀ z : ComplexPontryaginModel 1 1,
        (ComplexKreinSpace.J z).toVec.ofLp 1 = -z.toVec.ofLp 1 := fun z => by
      change ComplexPontryaginModel.sigSign 1 1 1 * z.toVec.ofLp 1 = -z.toVec.ofLp 1
      simp [ComplexPontryaginModel.sigSign]
    ext i
    fin_cases i
    · change (ComplexKreinSpace.J (U (ComplexKreinSpace.J u))).toVec.ofLp 0 = _
      rw [hJ0, (hU_app _).1, hJ0, hJ1]
      simp; ring
    · change (ComplexKreinSpace.J (U (ComplexKreinSpace.J u))).toVec.ofLp 1 = _
      rw [hJ1, (hU_app _).2, hJ0, hJ1]
      simp; ring
  have hUnitary : ComplexKreinSpace.IsComplexKreinUnitary U := by
    refine ⟨?_, ?_⟩
    · apply ContinuousLinearMap.ext; intro u
      apply ComplexPontryaginModel.ext
      apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      ext i
      rw [ContinuousLinearMap.comp_apply, hKreinAdj]
      fin_cases i <;> simp [U] <;> ring
    · apply ContinuousLinearMap.ext; intro u
      apply ComplexPontryaginModel.ext
      apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      ext i
      rw [ContinuousLinearMap.comp_apply, hKreinAdj]
      fin_cases i <;> simp [U] <;> ring
  let v1 : ComplexPontryaginModel 1 1 := ⟨WithLp.toLp 2 ![1, 1]⟩
  let v2 : ComplexPontryaginModel 1 1 := ⟨WithLp.toLp 2 ![1, -1]⟩
  have hv1Ne : v1 ≠ 0 := by
    intro h0
    have h00 := congrArg (fun z : ComplexPontryaginModel 1 1 => z.toVec.ofLp 0) h0
    simp [v1] at h00
  have hv2Ne : v2 ≠ 0 := by
    intro h0
    have h00 := congrArg (fun z : ComplexPontryaginModel 1 1 => z.toVec.ofLp 0) h0
    simp [v2] at h00
  have hv1Eig : U v1 = (2 : ℂ) • v1 := by
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i; fin_cases i <;> simp [U, v1] <;> norm_num
  have hv2Eig : U v2 = (2⁻¹ : ℂ) • v2 := by
    apply ComplexPontryaginModel.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i; fin_cases i <;> simp [U, v2] <;> norm_num
  have hNull1 : ComplexKreinSpace.complexKreinInner v1 v1 = 0 :=
    hUnitary.nonunit_eigenvector_null hv1Eig (by norm_num)
  have hNull2 : ComplexKreinSpace.complexKreinInner v2 v2 = 0 :=
    hUnitary.nonunit_eigenvector_null hv2Eig (by norm_num)
  exact ⟨U, hUnitary, v1, v2, hv1Ne, hv2Ne, hv1Eig, hv2Eig, hNull1, hNull2⟩

/-! ### General $\eta$-Inertia, Sylvester's Law, & Pontryagin Invariant Subspace Theorem (`S3-20`, `R3.1`) -/

section EtaInertiaAndPontryaginTheorem

/-- Positive spectral subspace of a self-adjoint operator `η : V →L[ℂ] V` (`S3-20`, `R3.1`). -/
def etaPosSubspace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (η : V →L[ℂ] V) : Submodule ℂ V :=
  ⨆ (μ : ℝ) (_ : 0 < μ), Module.End.eigenspace (η : V →ₗ[ℂ] V) (μ : ℂ)

/-- Negative spectral subspace of a self-adjoint operator `η : V →L[ℂ] V` (`S3-20`, `R3.1`). -/
def etaNegSubspace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (η : V →L[ℂ] V) : Submodule ℂ V :=
  ⨆ (μ : ℝ) (_ : μ < 0), Module.End.eigenspace (η : V →ₗ[ℂ] V) (μ : ℂ)

/-- Negative inertia index `κ(η) = dim_ℂ (etaNegSubspace η)` (`S3-20`, `R3.1`). -/
def etaNegIndex {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (η : V →L[ℂ] V) : ℕ :=
  Module.finrank ℂ (etaNegSubspace η)

/-- Positive inertia index `π(η) = dim_ℂ (etaPosSubspace η)` (`S3-20`, `R3.1`). -/
def etaPosIndex {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (η : V →L[ℂ] V) : ℕ :=
  Module.finrank ℂ (etaPosSubspace η)

private lemma eta_eigenvector_inner_eq_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) {μ ν : ℝ} (hne : μ ≠ ν)
    {x y : V} (hx : η x = (μ : ℂ) • x) (hy : η y = (ν : ℂ) • y) :
    ⟪x, y⟫_ℂ = 0 := by
  have hAdj : ∀ u v : V, ⟪η u, v⟫_ℂ = ⟪u, η v⟫_ℂ := fun u v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, hη_sa]
  have h1 : (μ : ℂ) * ⟪x, y⟫_ℂ = (ν : ℂ) * ⟪x, y⟫_ℂ := by
    calc
      (μ : ℂ) * ⟪x, y⟫_ℂ = (starRingEnd ℂ (μ : ℂ)) * ⟪x, y⟫_ℂ := by simp
      _ = ⟪(μ : ℂ) • x, y⟫_ℂ := (inner_smul_left x y (μ : ℂ)).symm
      _ = ⟪η x, y⟫_ℂ := by rw [hx]
      _ = ⟪x, η y⟫_ℂ := hAdj x y
      _ = ⟪x, (ν : ℂ) • y⟫_ℂ := by rw [hy]
      _ = (ν : ℂ) * ⟪x, y⟫_ℂ := inner_smul_right x y (ν : ℂ)
  have hdiff : ((μ : ℂ) - (ν : ℂ)) * ⟪x, y⟫_ℂ = 0 := by
    rw [sub_mul, h1, sub_self]
  have hc : (μ : ℂ) - (ν : ℂ) ≠ 0 := by
    intro h0
    exact hne (Complex.ofReal_injective (sub_eq_zero.mp h0))
  exact (mul_eq_zero.mp hdiff).resolve_left hc

private lemma etaPos_repr_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η)
    {x : V} (hx : x ∈ etaPosSubspace η) (i : Fin (Module.finrank ℂ V))
    (h_le : (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvalues rfl i ≤ 0) :
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvectorBasis rfl).repr x i = 0 := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  let ev := hSymm.eigenvalues rfl
  have hmem : x ∈ (Submodule.span ℂ {b i})ᗮ := by
    have hle_ker : etaPosSubspace η ≤ (Submodule.span ℂ {b i})ᗮ := by
      refine iSup₂_le fun μ hμ y hy w hw => ?_
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rw [inner_smul_left]
      have hyEig : η y = (μ : ℂ) • y := Module.End.mem_eigenspace_iff.mp hy
      have hbEig : η (b i) = (ev i : ℂ) • b i := by
        change (η : V →ₗ[ℂ] V) ((hSymm.eigenvectorBasis rfl) i) = _
        exact hSymm.apply_eigenvectorBasis rfl i
      rw [eta_eigenvector_inner_eq_zero hη_sa (ne_of_lt (lt_of_le_of_lt h_le hμ)) hbEig hyEig,
        mul_zero]
    exact hle_ker hx
  have h0 : ⟪b i, x⟫_ℂ = 0 := hmem (b i) (Submodule.mem_span_singleton_self _)
  simpa [b, OrthonormalBasis.repr_apply_apply] using h0

private lemma etaNeg_repr_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η)
    {x : V} (hx : x ∈ etaNegSubspace η) (i : Fin (Module.finrank ℂ V))
    (h_ge : 0 ≤ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvalues rfl i) :
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvectorBasis rfl).repr x i = 0 := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  let ev := hSymm.eigenvalues rfl
  have hmem : x ∈ (Submodule.span ℂ {b i})ᗮ := by
    have hle_ker : etaNegSubspace η ≤ (Submodule.span ℂ {b i})ᗮ := by
      refine iSup₂_le fun μ hμ y hy w hw => ?_
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rw [inner_smul_left]
      have hyEig : η y = (μ : ℂ) • y := Module.End.mem_eigenspace_iff.mp hy
      have hbEig : η (b i) = (ev i : ℂ) • b i := by
        change (η : V →ₗ[ℂ] V) ((hSymm.eigenvectorBasis rfl) i) = _
        exact hSymm.apply_eigenvectorBasis rfl i
      rw [eta_eigenvector_inner_eq_zero hη_sa (ne_of_gt (lt_of_lt_of_le hμ h_ge)) hbEig hyEig,
        mul_zero]
    exact hle_ker hx
  have h0 : ⟪b i, x⟫_ℂ = 0 := hmem (b i) (Submodule.mem_span_singleton_self _)
  simpa [b, OrthonormalBasis.repr_apply_apply] using h0

private lemma eta_eigenvalues_ne_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η)
    (hη_bij : Function.Bijective η) (i : Fin (Module.finrank ℂ V)) :
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvalues rfl i ≠ 0 := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  intro h0
  have hηb : η (b i) = 0 := by
    have hbEig : η (b i) = (hSymm.eigenvalues rfl i : ℂ) • b i := by
      change (η : V →ₗ[ℂ] V) ((hSymm.eigenvectorBasis rfl) i) = _
      exact hSymm.apply_eigenvectorBasis rfl i
    rw [hbEig, h0, Complex.ofReal_zero, zero_smul]
  have hb0 : b i = 0 := hη_bij.injective (hηb.trans (map_zero η).symm)
  exact (b.toBasis.ne_zero i) hb0

private lemma eta_inner_re_formula {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (x y : V) :
    ⟪η x, y⟫_ℂ =
      ∑ i : Fin (Module.finrank ℂ V),
        ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvalues rfl i : ℂ) *
          star (((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvectorBasis rfl).repr x i) *
          ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa).eigenvectorBasis rfl).repr y i := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  let ev := hSymm.eigenvalues rfl
  have hbEig : ∀ i, η (b i) = (ev i : ℂ) • b i := fun i => by
    change (η : V →ₗ[ℂ] V) ((hSymm.eigenvectorBasis rfl) i) = _
    exact hSymm.apply_eigenvectorBasis rfl i
  have hx : η x = ∑ i, (ev i : ℂ) • b.repr x i • b i := by
    calc
      η x = η (∑ i, b.repr x i • b i) := by rw [b.sum_repr x]
      _ = ∑ i, b.repr x i • η (b i) := by simp [map_sum, map_smul]
      _ = ∑ i, (ev i : ℂ) • b.repr x i • b i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hbEig i, smul_comm]
  have hy : y = ∑ j, b.repr y j • b j := (b.sum_repr y).symm
  rw [hx]
  conv_lhs => rhs; rw [hy]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_left, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal i i]
    simp only [↓reduceIte, mul_one, RCLike.star_def, Complex.conj_ofReal]
    ring
  · intro j _ hji
    rw [inner_smul_left, inner_smul_left, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal i j]
    simp [hji.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Spectral splitting `V = etaPosSubspace η ⊕ etaNegSubspace η` for any invertible self-adjoint
`η` on finite-dimensional `V` (`S3-20`, `R3.1`). -/
theorem eta_pos_neg_isCompl {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (hη_bij : Function.Bijective η) :
    IsCompl (etaPosSubspace η) (etaNegSubspace η) := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  let ev := hSymm.eigenvalues rfl
  have hbEig : ∀ i, η (b i) = (ev i : ℂ) • b i := fun i => by
    change (η : V →ₗ[ℂ] V) ((hSymm.eigenvectorBasis rfl) i) = _
    exact hSymm.apply_eigenvectorBasis rfl i
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro x ⟨hxP, hxN⟩
    have hrepr : ∀ i, b.repr x i = 0 := fun i => by
      rcases lt_trichotomy (ev i) 0 with hlt | heq | hgt
      · exact etaPos_repr_zero hη_sa hxP i (le_of_lt hlt)
      · exact absurd heq (eta_eigenvalues_ne_zero hη_sa hη_bij i)
      · exact etaNeg_repr_zero hη_sa hxN i (le_of_lt hgt)
    calc
      x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      _ = 0 := by simp [hrepr]
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro x
    let xP : V := ∑ i : Fin (Module.finrank ℂ V),
      if 0 < ev i then b.repr x i • b i else 0
    let xN : V := ∑ i : Fin (Module.finrank ℂ V),
      if ev i < 0 then b.repr x i • b i else 0
    refine ⟨xP, xN, ?_, ?_, ?_⟩
    · refine Submodule.sum_mem _ fun i _ => ?_
      split_ifs with hgt
      · refine Submodule.smul_mem (etaPosSubspace η) (b.repr x i) ?_
        have hle : Module.End.eigenspace (η : V →ₗ[ℂ] V) (ev i : ℂ) ≤ etaPosSubspace η :=
          le_iSup₂ (f := fun (μ : ℝ) (_ : 0 < μ) =>
            Module.End.eigenspace (η : V →ₗ[ℂ] V) (μ : ℂ)) (ev i) hgt
        exact hle (Module.End.mem_eigenspace_iff.mpr (hbEig i))
      · exact Submodule.zero_mem _
    · refine Submodule.sum_mem _ fun i _ => ?_
      split_ifs with hlt
      · refine Submodule.smul_mem (etaNegSubspace η) (b.repr x i) ?_
        have hle : Module.End.eigenspace (η : V →ₗ[ℂ] V) (ev i : ℂ) ≤ etaNegSubspace η :=
          le_iSup₂ (f := fun (μ : ℝ) (_ : μ < 0) =>
            Module.End.eigenspace (η : V →ₗ[ℂ] V) (μ : ℂ)) (ev i) hlt
        exact hle (Module.End.mem_eigenspace_iff.mpr (hbEig i))
      · exact Submodule.zero_mem _
    · rw [← Finset.sum_add_distrib]
      calc
        ∑ i : Fin (Module.finrank ℂ V),
            ((if 0 < ev i then b.repr x i • b i else 0) +
              (if ev i < 0 then b.repr x i • b i else 0))
            = ∑ i : Fin (Module.finrank ℂ V), b.repr x i • b i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rcases lt_trichotomy (ev i) 0 with hlt | heq | hgt
              · have hnot : ¬ 0 < ev i := not_lt.mpr (le_of_lt hlt)
                simp [hnot, hlt]
              · exact absurd heq (eta_eigenvalues_ne_zero hη_sa hη_bij i)
              · have hnot : ¬ ev i < 0 := not_lt.mpr (le_of_lt hgt)
                simp [hgt, hnot]
        _ = x := b.sum_repr x

/-- `etaPosSubspace η` is strictly `η`-positive definite (`S3-20`, `R3.1`). -/
theorem eta_pos_def {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η)
    {x : V} (hx : x ∈ etaPosSubspace η) (hne : x ≠ 0) :
    0 < (⟪η x, x⟫_ℂ).re := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  let ev := hSymm.eigenvalues rfl
  have hform : (⟪η x, x⟫_ℂ).re = ∑ i : Fin (Module.finrank ℂ V), ev i * ‖b.repr x i‖ ^ 2 := by
    rw [eta_inner_re_formula hη_sa x x, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmul : star (b.repr x i) * b.repr x i = ((‖b.repr x i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, Complex.conj_mul']
      push_cast; rfl
    change ((ev i : ℂ) * star (b.repr x i) * b.repr x i).re = ev i * ‖b.repr x i‖ ^ 2
    rw [mul_assoc, hmul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hform]
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ ev i * ‖b.repr x i‖ ^ 2 := fun i _ => by
    rcases le_or_gt (ev i) 0 with hle | hgt
    · rw [etaPos_repr_zero hη_sa hx i hle, norm_zero, sq, mul_zero, mul_zero]
    · exact mul_nonneg (le_of_lt hgt) (sq_nonneg _)
  have hex : ∃ i ∈ Finset.univ, 0 < ev i * ‖b.repr x i‖ ^ 2 := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ i, b.repr x i = 0 := fun i => by
      rcases le_or_gt (ev i) 0 with hle | hgt
      · exact etaPos_repr_zero hη_sa hx i hle
      · have hle0 := hnone i (Finset.mem_univ i)
        have hns : ‖b.repr x i‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle0 hgt
        have h0 : ‖b.repr x i‖ = 0 := by nlinarith [norm_nonneg (b.repr x i)]
        exact norm_eq_zero.mp h0
    apply hne
    calc
      x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      _ = 0 := by simp [hall]
  exact Finset.sum_pos' hnonneg hex

/-- `etaNegSubspace η` is strictly `η`-negative definite (`S3-20`, `R3.1`). -/
theorem eta_neg_def {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η)
    {y : V} (hy : y ∈ etaNegSubspace η) (hne : y ≠ 0) :
    (⟪η y, y⟫_ℂ).re < 0 := by
  let hSymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hη_sa
  let b := hSymm.eigenvectorBasis rfl
  let ev := hSymm.eigenvalues rfl
  have hform : (⟪η y, y⟫_ℂ).re = ∑ i : Fin (Module.finrank ℂ V), ev i * ‖b.repr y i‖ ^ 2 := by
    rw [eta_inner_re_formula hη_sa y y, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmul : star (b.repr y i) * b.repr y i = ((‖b.repr y i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, Complex.conj_mul']
      push_cast; rfl
    change ((ev i : ℂ) * star (b.repr y i) * b.repr y i).re = ev i * ‖b.repr y i‖ ^ 2
    rw [mul_assoc, hmul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hform, ← neg_pos, ← Finset.sum_neg_distrib]
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ -(ev i * ‖b.repr y i‖ ^ 2) := fun i _ => by
    rcases le_or_gt 0 (ev i) with hge | hlt
    · rw [etaNeg_repr_zero hη_sa hy i hge, norm_zero, sq, mul_zero, mul_zero, neg_zero]
    · rw [← neg_mul]
      exact mul_nonneg (neg_nonneg.mpr (le_of_lt hlt)) (sq_nonneg _)
  have hex : ∃ i ∈ Finset.univ, 0 < -(ev i * ‖b.repr y i‖ ^ 2) := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ i, b.repr y i = 0 := fun i => by
      rcases le_or_gt 0 (ev i) with hge | hlt
      · exact etaNeg_repr_zero hη_sa hy i hge
      · have hle0 := hnone i (Finset.mem_univ i)
        rw [← neg_mul] at hle0
        have hns : ‖b.repr y i‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle0 (neg_pos.mpr hlt)
        have h0 : ‖b.repr y i‖ = 0 := by nlinarith [norm_nonneg (b.repr y i)]
        exact norm_eq_zero.mp h0
    apply hne
    calc
      y = ∑ i, b.repr y i • b i := (b.sum_repr y).symm
      _ = 0 := by simp [hall]
  exact Finset.sum_pos' hnonneg hex

/-- Any `η`-nonpositive subspace `M ≤ V` has `dim_ℂ M ≤ etaNegIndex η` (`S3-20`, Pontryagin
1944; `R3.1`). -/
theorem finrank_le_etaNegIndex_of_nonpositive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (hη_bij : Function.Bijective η)
    (M : Submodule ℂ V) (hM : ∀ x ∈ M, (⟪η x, x⟫_ℂ).re ≤ 0) :
    Module.finrank ℂ M ≤ etaNegIndex η := by
  let hComp := eta_pos_neg_isCompl hη_sa hη_bij
  let projNeg : V →ₗ[ℂ] etaNegSubspace η :=
    Submodule.projectionOnto (etaNegSubspace η) (etaPosSubspace η) hComp.symm
  let f : M →ₗ[ℂ] etaNegSubspace η := projNeg.comp M.subtype
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : x.1 ∈ LinearMap.ker ((etaNegSubspace η).projectionOnto (etaPosSubspace η) hComp.symm) :=
      hx
    rw [Submodule.ker_projectionOnto] at hker
    by_contra hne
    have hx0 : x.1 ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := eta_pos_def hη_sa hker hx0
    have hle := hM x.1 x.2
    linarith
  exact LinearMap.finrank_le_finrank_of_injective hf_inj

/-- Any `η`-nonnegative subspace `M ≤ V` has `dim_ℂ M ≤ etaPosIndex η` (`S3-20`, `R3.1`). -/
theorem finrank_le_etaPosIndex_of_nonnegative {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (hη_bij : Function.Bijective η)
    (M : Submodule ℂ V) (hM : ∀ x ∈ M, 0 ≤ (⟪η x, x⟫_ℂ).re) :
    Module.finrank ℂ M ≤ etaPosIndex η := by
  let hComp := eta_pos_neg_isCompl hη_sa hη_bij
  let projPos : V →ₗ[ℂ] etaPosSubspace η :=
    Submodule.projectionOnto (etaPosSubspace η) (etaNegSubspace η) hComp
  let f : M →ₗ[ℂ] etaPosSubspace η := projPos.comp M.subtype
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : x.1 ∈ LinearMap.ker ((etaPosSubspace η).projectionOnto (etaNegSubspace η) hComp) :=
      hx
    rw [Submodule.ker_projectionOnto] at hker
    by_contra hne
    have hx0 : x.1 ≠ 0 := fun h => hne (Subtype.ext h)
    have hneg := eta_neg_def hη_sa hker hx0
    have hge := hM x.1 x.2
    linarith
  exact LinearMap.finrank_le_finrank_of_injective hf_inj

/-- **Sylvester's Law of Inertia** (`S3-20`, Pontryagin 1944; `R3.1`): any definite
decomposition `V = W₊ ⊕ W₋` with `W₊` `η`-positive definite and `W₋` `η`-negative definite
satisfies `dim_ℂ W₋ = etaNegIndex η`. -/
theorem sylvester_negIndex_eq_of_isCompl {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (hη_bij : Function.Bijective η)
    {Wpos Wneg : Submodule ℂ V} (hCompl : IsCompl Wpos Wneg)
    (hPos : ∀ x ∈ Wpos, x ≠ 0 → 0 < (⟪η x, x⟫_ℂ).re)
    (hNeg : ∀ y ∈ Wneg, y ≠ 0 → (⟪η y, y⟫_ℂ).re < 0) :
    Module.finrank ℂ Wneg = etaNegIndex η := by
  have hleNeg : Module.finrank ℂ Wneg ≤ etaNegIndex η := by
    refine finrank_le_etaNegIndex_of_nonpositive hη_sa hη_bij Wneg fun y hy => ?_
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact le_of_lt (hNeg y hy hy0)
  have hlePos : Module.finrank ℂ Wpos ≤ etaPosIndex η := by
    refine finrank_le_etaPosIndex_of_nonnegative hη_sa hη_bij Wpos fun x hx => ?_
    by_cases hx0 : x = 0
    · simp [hx0]
    · exact le_of_lt (hPos x hx hx0)
  have hsumW : Module.finrank ℂ Wpos + Module.finrank ℂ Wneg = Module.finrank ℂ V :=
    Submodule.finrank_add_eq_of_isCompl hCompl
  have hsumEta : etaPosIndex η + etaNegIndex η = Module.finrank ℂ V :=
    Submodule.finrank_add_eq_of_isCompl (eta_pos_neg_isCompl hη_sa hη_bij)
  omega

/-- For `η = ComplexKreinSpace.jCLM`, `etaNegSubspace jCLM = ComplexKreinSpace.negSubspace V`,
so `etaNegIndex jCLM = ComplexPontryaginSpace.negIndex V` (`S3-20`, `R3.1`). -/
theorem etaNegIndex_jCLM_eq (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] [ComplexPontryaginSpace V] :
    etaNegIndex (ComplexKreinSpace.jCLM (H := V)) = ComplexPontryaginSpace.negIndex V := by
  have hSub : etaNegSubspace (ComplexKreinSpace.jCLM (H := V)) =
      ComplexKreinSpace.negSubspace V := by
    apply le_antisymm
    · refine iSup₂_le fun μ hμ x hx => ?_
      rw [ComplexKreinSpace.mem_negSubspace_iff]
      have hxEig : (ComplexKreinSpace.jCLM (H := V)) x = (μ : ℂ) • x :=
        Module.End.mem_eigenspace_iff.mp hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hsq : (μ : ℂ) ^ 2 • x = x := by
          calc
            (μ : ℂ) ^ 2 • x = (μ : ℂ) • ((μ : ℂ) • x) := by rw [smul_smul, sq]
            _ = (μ : ℂ) • (ComplexKreinSpace.jCLM (H := V) x) := by rw [← hxEig]
            _ = (ComplexKreinSpace.jCLM (H := V)) ((μ : ℂ) • x) := (map_smul _ _ _).symm
            _ = (ComplexKreinSpace.jCLM (H := V)) ((ComplexKreinSpace.jCLM (H := V)) x) := by
                  rw [← hxEig]
            _ = x := ComplexKreinSpace.J_invol x
        have hmu2 : (μ : ℂ) ^ 2 = 1 := by
          have hsub : ((μ : ℂ) ^ 2 - 1) • x = 0 := by rw [sub_smul, one_smul, hsq, sub_self]
          exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hx0)
        have hmuR : μ ^ 2 = 1 := Complex.ofReal_injective (by simpa using hmu2)
        have hmuNeg1 : μ = -1 := by
          rcases sq_eq_one_iff.mp hmuR with h1 | hn1
          · linarith
          · exact hn1
        rw [hmuNeg1] at hxEig
        simp only [ComplexKreinSpace.jCLM_apply, Complex.ofReal_neg, Complex.ofReal_one,
          neg_smul, one_smul] at hxEig
        exact hxEig
    · intro x hx
      rw [ComplexKreinSpace.mem_negSubspace_iff] at hx
      have hxEig : x ∈ Module.End.eigenspace (ComplexKreinSpace.jCLM (H := V) : V →ₗ[ℂ] V)
          ((-1 : ℝ) : ℂ) := by
        rw [Module.End.mem_eigenspace_iff]
        change ComplexKreinSpace.J x = ((-1 : ℝ) : ℂ) • x
        rw [hx, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul]
      exact (le_iSup₂ (f := fun (μ : ℝ) (_ : μ < 0) =>
        Module.End.eigenspace (ComplexKreinSpace.jCLM (H := V) : V →ₗ[ℂ] V) (μ : ℂ))
        (-1 : ℝ) (by norm_num)) hxEig
  change Module.finrank ℂ (etaNegSubspace (ComplexKreinSpace.jCLM (H := V))) =
    Module.finrank ℂ (ComplexKreinSpace.negSubspace V)
  rw [hSub]

private lemma submodule_eta_compression_props {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (hη_bij : Function.Bijective η)
    (H : Submodule ℂ V)
    (hH_nondeg : ∀ h ∈ H, (∀ h' ∈ H, ⟪η h, h'⟫_ℂ = 0) → h = 0) :
    let U : Submodule ℂ V := (H.map (η : V →ₗ[ℂ] V))ᗮ
    IsCompl H U ∧
      ∃ ηU : U →L[ℂ] U,
        ContinuousLinearMap.adjoint ηU = ηU ∧
        Function.Bijective ηU ∧
        (∀ x y : U, ⟪ηU x, y⟫_ℂ = ⟪η x.1, y.1⟫_ℂ) ∧
        (∀ h ∈ H, ∀ u ∈ U, ⟪η h, u⟫_ℂ = 0) := by
  let U : Submodule ℂ V := (H.map (η : V →ₗ[ℂ] V))ᗮ
  let _ : CompleteSpace U := (Submodule.closed_of_finiteDimensional U).completeSpace_coe
  let _ : U.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace U
  let ηU : U →L[ℂ] U := U.orthogonalProjectionOnto.comp (η.comp U.subtypeL)
  have hOrtho : ∀ h ∈ H, ∀ u ∈ U, ⟪η h, u⟫_ℂ = 0 := by
    intro h hh u hu
    have hmem : η h ∈ H.map (η : V →ₗ[ℂ] V) := Submodule.mem_map_of_mem hh
    exact hu (η h) hmem
  have hDisj : Disjoint H U := by
    rw [disjoint_iff_inf_le]
    intro x ⟨hxH, hxU⟩
    refine hH_nondeg x hxH fun h' hh' => ?_
    have h0 : ⟪η h', x⟫_ℂ = 0 := hOrtho h' hh' x hxU
    have hAdj : ⟪η x, h'⟫_ℂ = ⟪x, η h'⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hη_sa]
    rw [hAdj, inner_eq_zero_symm]
    exact h0
  have hCompl : IsCompl H U := by
    have hMapEq : Module.finrank ℂ (H.map (η : V →ₗ[ℂ] V)) = Module.finrank ℂ H :=
      (Submodule.equivMapOfInjective (η : V →ₗ[ℂ] V) hη_bij.injective H).symm.finrank_eq
    let _ : CompleteSpace (H.map (η : V →ₗ[ℂ] V)) :=
      (Submodule.closed_of_finiteDimensional _).completeSpace_coe
    let _ : (H.map (η : V →ₗ[ℂ] V)).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    have hOrthDim : Module.finrank ℂ (H.map (η : V →ₗ[ℂ] V)) + Module.finrank ℂ U =
        Module.finrank ℂ V :=
      Submodule.finrank_add_eq_of_isCompl (Submodule.isCompl_orthogonal _)
    have hSum : Module.finrank ℂ ↥(H ⊔ U) = Module.finrank ℂ V := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq H U
      have hinf : H ⊓ U = ⊥ := hDisj.eq_bot
      rw [hinf, finrank_bot, add_zero] at hsup
      omega
    have hTop : H ⊔ U = ⊤ :=
      Submodule.eq_top_of_finrank_eq hSum
    exact ⟨hDisj, codisjoint_iff.mpr hTop⟩
  have hproj : ∀ (z : V) (w : U), ⟪(U.orthogonalProjectionOnto z : U), w⟫_ℂ = ⟪z, w.1⟫_ℂ := by
    intro z w
    have hz := U.starProjection_inner_eq_zero z w.1 w.2
    rw [← U.coe_orthogonalProjectionOnto_apply z, inner_sub_left, sub_eq_zero] at hz
    exact hz.symm
  have hηU_pair : ∀ x y : U, ⟪ηU x, y⟫_ℂ = ⟪η x.1, y.1⟫_ℂ := fun x y =>
    hproj (η x.1) y
  have hηU_sa : ContinuousLinearMap.adjoint ηU = ηU := by
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
    have hAdj : ⟪η x.1, y.1⟫_ℂ = ⟪x.1, η y.1⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hη_sa]
    calc
      ⟪ηU x, y⟫_ℂ = ⟪η x.1, y.1⟫_ℂ := hηU_pair x y
      _ = ⟪x.1, η y.1⟫_ℂ := hAdj
      _ = star ⟪η y.1, x.1⟫_ℂ := (inner_conj_symm _ _).symm
      _ = star ⟪ηU y, x⟫_ℂ := by rw [hηU_pair y x]
      _ = ⟪x, ηU y⟫_ℂ := inner_conj_symm _ _
  have hηU_inj : Function.Injective ηU := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : η x.1 ∈ LinearMap.ker (U.orthogonalProjectionOnto : V →ₗ[ℂ] U) := hx
    rw [U.ker_orthogonalProjectionOnto] at hker
    let _ : (H.map (η : V →ₗ[ℂ] V)).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    have hUU : Uᗮ = H.map (η : V →ₗ[ℂ] V) :=
      Submodule.orthogonal_orthogonal (H.map (η : V →ₗ[ℂ] V))
    rw [hUU] at hker
    rcases Submodule.mem_map.mp hker with ⟨h, hhH, hhEq⟩
    have hxEq : x.1 = h := hη_bij.injective hhEq.symm
    have hxInf : x.1 ∈ H ⊓ U := ⟨hxEq ▸ hhH, x.2⟩
    rw [hDisj.eq_bot, Submodule.mem_bot] at hxInf
    exact Subtype.ext hxInf
  have hηU_bij : Function.Bijective ηU :=
    ⟨hηU_inj, (LinearMap.injective_iff_surjective (f := (ηU : U →ₗ[ℂ] U))).mp hηU_inj⟩
  exact ⟨hCompl, ηU, hηU_sa, hηU_bij, hηU_pair, hOrtho⟩

private lemma etaNegIndex_split_of_decomp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V] {η : V →L[ℂ] V}
    (hη_sa : ContinuousLinearMap.adjoint η = η) (hη_bij : Function.Bijective η)
    {H U : Submodule ℂ V} (hCompl : IsCompl H U)
    (hOrtho : ∀ h ∈ H, ∀ u ∈ U, ⟪η h, u⟫_ℂ = 0)
    (Hpos Hneg : Submodule ℂ V) (hH_compl : IsCompl (Hpos.comap H.subtype) (Hneg.comap H.subtype))
    (hHpos_le : Hpos ≤ H) (hHneg_le : Hneg ≤ H)
    (hHpos_def : ∀ x ∈ Hpos, x ≠ 0 → 0 < (⟪η x, x⟫_ℂ).re)
    (hHneg_def : ∀ y ∈ Hneg, y ≠ 0 → (⟪η y, y⟫_ℂ).re < 0)
    {ηU : U →L[ℂ] U} (hηU_sa : ContinuousLinearMap.adjoint ηU = ηU)
    (hηU_bij : Function.Bijective ηU) (hηU_inner : ∀ x : U, ⟪ηU x, x⟫_ℂ = ⟪η x.1, x.1⟫_ℂ) :
    etaNegIndex η = Module.finrank ℂ Hneg + etaNegIndex ηU := by
  let _ : CompleteSpace U := (Submodule.closed_of_finiteDimensional U).completeSpace_coe
  let Upos := (etaPosSubspace ηU).map U.subtype
  let Uneg := (etaNegSubspace ηU).map U.subtype
  let Wpos := Hpos ⊔ Upos
  let Wneg := Hneg ⊔ Uneg
  have hDisjHU : H ⊓ U = ⊥ := hCompl.disjoint.eq_bot
  have hDisj_Hpos_Hneg : Hpos ⊓ Hneg = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    have hxH : x ∈ H := hHpos_le hx1
    have hmem : (⟨x, hxH⟩ : H) ∈ Hpos.comap H.subtype ⊓ Hneg.comap H.subtype := ⟨hx1, hx2⟩
    rw [hH_compl.disjoint.eq_bot, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hHU_pos : Hpos ⊓ Upos = ⊥ :=
    eq_bot_iff.mpr fun x ⟨hxH, hxU⟩ => by
      have : x ∈ H ⊓ U := ⟨hHpos_le hxH, Submodule.map_subtype_le _ _ hxU⟩
      rwa [hDisjHU] at this
  have hHU_neg : Hneg ⊓ Uneg = ⊥ :=
    eq_bot_iff.mpr fun x ⟨hxH, hxU⟩ => by
      have : x ∈ H ⊓ U := ⟨hHneg_le hxH, Submodule.map_subtype_le _ _ hxU⟩
      rwa [hDisjHU] at this
  have hDisjW : Disjoint Wpos Wneg := by
    rw [disjoint_iff_inf_le]
    intro x ⟨hxP, hxN⟩
    rcases Submodule.mem_sup.mp hxP with ⟨hp, hHp, up, hUp, rfl⟩
    rcases Submodule.mem_sup.mp hxN with ⟨hn, hHn, un, hUn, heq⟩
    have hH_eq : hp - hn = un - up := by
      calc
        hp - hn = (hp + up) - (hn + up) := by abel
        _ = (hn + un) - (hn + up) := by rw [heq]
        _ = un - up := by abel
    have hmemH : hp - hn ∈ H := H.sub_mem (hHpos_le hHp) (hHneg_le hHn)
    have hmemU : un - up ∈ U := U.sub_mem (Submodule.map_subtype_le _ _ hUn)
      (Submodule.map_subtype_le _ _ hUp)
    have hzeroH : hp - hn = 0 := by
      have hm : hp - hn ∈ H ⊓ U := ⟨hmemH, hH_eq ▸ hmemU⟩
      rwa [hDisjHU, Submodule.mem_bot] at hm
    have hphp : hp = hn := sub_eq_zero.mp hzeroH
    have hupu : up = un := (sub_eq_zero.mp (hH_eq.symm.trans hzeroH)).symm
    have hhp0 : hp = 0 := by
      have hm : hp ∈ Hpos ⊓ Hneg := ⟨hHp, hphp ▸ hHn⟩
      rwa [hDisj_Hpos_Hneg, Submodule.mem_bot] at hm
    have hup0 : up = 0 := by
      rcases Submodule.mem_map.mp hUp with ⟨up', hup'P, rfl⟩
      rcases Submodule.mem_map.mp (hupu ▸ hUn) with ⟨un', hun'N, hun'Eq⟩
      have heqU : up' = un' := (Subtype.ext hun'Eq).symm
      have hdisjU : up' ∈ etaPosSubspace ηU ⊓ etaNegSubspace ηU := ⟨hup'P, heqU ▸ hun'N⟩
      rw [(eta_pos_neg_isCompl hηU_sa hηU_bij).disjoint.eq_bot, Submodule.mem_bot] at hdisjU
      simp [hdisjU]
    simp [hhp0, hup0]
  have hCodisjW : Codisjoint Wpos Wneg := by
    rw [Submodule.codisjoint_iff_exists_add_eq]
    intro x
    have hHU_cod := Submodule.codisjoint_iff_exists_add_eq.mp hCompl.codisjoint x
    rcases hHU_cod with ⟨h, u, hhH, huU, rfl⟩
    have hH_cod := Submodule.codisjoint_iff_exists_add_eq.mp hH_compl.codisjoint ⟨h, hhH⟩
    rcases hH_cod with ⟨⟨hp, hHp⟩, ⟨hn, hHn⟩, hhpMem, hhnMem, hheq⟩
    have hU_cod := Submodule.codisjoint_iff_exists_add_eq.mp
      (eta_pos_neg_isCompl hηU_sa hηU_bij).codisjoint ⟨u, huU⟩
    rcases hU_cod with ⟨up, un, hupP, hunN, hueq⟩
    refine ⟨hp + up.1, hn + un.1,
      Submodule.mem_sup.mpr ⟨hp, hhpMem, up.1, Submodule.mem_map_of_mem hupP, rfl⟩,
      Submodule.mem_sup.mpr ⟨hn, hhnMem, un.1, Submodule.mem_map_of_mem hunN, rfl⟩, ?_⟩
    have h1 : hp + hn = h := congrArg Subtype.val hheq
    have h2 : up.1 + un.1 = u := congrArg Subtype.val hueq
    calc
      (hp + up.1) + (hn + un.1) = (hp + hn) + (up.1 + un.1) := by abel
      _ = h + u := by rw [h1, h2]
  have hW_compl : IsCompl Wpos Wneg := ⟨hDisjW, hCodisjW⟩
  have hWpos_def : ∀ z ∈ Wpos, z ≠ 0 → 0 < (⟪η z, z⟫_ℂ).re := by
    intro z hz hzne
    rcases Submodule.mem_sup.mp hz with ⟨hp, hHp, up, hUp, rfl⟩
    rcases Submodule.mem_map.mp hUp with ⟨up', hup'P, rfl⟩
    have h12 : ⟪η hp, up'.1⟫_ℂ = 0 := hOrtho hp (hHpos_le hHp) up'.1 up'.2
    have h21 : ⟪η up'.1, hp⟫_ℂ = 0 := by
      have hAdj : ⟪η up'.1, hp⟫_ℂ = ⟪up'.1, η hp⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left, hη_sa]
      rw [hAdj, inner_eq_zero_symm]
      exact h12
    have hre : (⟪η (hp + up'.1), hp + up'.1⟫_ℂ).re =
        (⟪η hp, hp⟫_ℂ).re + (⟪ηU up', up'⟫_ℂ).re := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, h12, h21, hηU_inner]
      simp
    simp only [Submodule.coe_subtype]
    rw [hre]
    by_cases hhp0 : hp = 0
    · have hup0 : up' ≠ 0 := fun h => hzne (by simp [hhp0, h])
      simp [hhp0]
      exact eta_pos_def hηU_sa hup'P hup0
    · by_cases hup0 : up' = 0
      · simp [hup0]
        exact hHpos_def hp hHp hhp0
      · exact add_pos (hHpos_def hp hHp hhp0) (eta_pos_def hηU_sa hup'P hup0)
  have hWneg_def : ∀ z ∈ Wneg, z ≠ 0 → (⟪η z, z⟫_ℂ).re < 0 := by
    intro z hz hzne
    rcases Submodule.mem_sup.mp hz with ⟨hn, hHn, un, hUn, rfl⟩
    rcases Submodule.mem_map.mp hUn with ⟨un', hun'N, rfl⟩
    have h12 : ⟪η hn, un'.1⟫_ℂ = 0 := hOrtho hn (hHneg_le hHn) un'.1 un'.2
    have h21 : ⟪η un'.1, hn⟫_ℂ = 0 := by
      have hAdj : ⟪η un'.1, hn⟫_ℂ = ⟪un'.1, η hn⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left, hη_sa]
      rw [hAdj, inner_eq_zero_symm]
      exact h12
    have hre : (⟪η (hn + un'.1), hn + un'.1⟫_ℂ).re =
        (⟪η hn, hn⟫_ℂ).re + (⟪ηU un', un'⟫_ℂ).re := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, h12, h21, hηU_inner]
      simp
    simp only [Submodule.coe_subtype]
    rw [hre]
    by_cases hhn0 : hn = 0
    · have hun0 : un' ≠ 0 := fun h => hzne (by simp [hhn0, h])
      simp [hhn0]
      exact eta_neg_def hηU_sa hun'N hun0
    · by_cases hun0 : un' = 0
      · simp [hun0]
        exact hHneg_def hn hHn hhn0
      · exact add_neg (hHneg_def hn hHn hhn0) (eta_neg_def hηU_sa hun'N hun0)
  have hSyl := sylvester_negIndex_eq_of_isCompl hη_sa hη_bij hW_compl hWpos_def hWneg_def
  rw [← hSyl]
  have hdimW : Module.finrank ℂ ↥Wneg + Module.finrank ℂ ↥(Hneg ⊓ Uneg) =
      Module.finrank ℂ ↥Hneg + Module.finrank ℂ ↥Uneg :=
    Submodule.finrank_sup_add_finrank_inf_eq Hneg Uneg
  rw [hHU_neg, finrank_bot, add_zero] at hdimW
  have hUneg_dim : Module.finrank ℂ Uneg = etaNegIndex ηU :=
    (Submodule.equivMapOfInjective U.subtype Subtype.val_injective (etaNegSubspace ηU)).symm.finrank_eq
  omega

/-- **Pontryagin Invariant Subspace Theorem (General `η`-Formulation)** (`S3-20`, Pontryagin
1944; `R3.1`): on any finite-dimensional complex inner product space `(V, η)` with invertible
self-adjoint metric `η`, every `η`-pseudo-Hermitian operator `A` admits an `A`-invariant,
`η`-nonpositive subspace `M ≤ V` of dimension `etaNegIndex η`. -/
theorem exists_eta_invariant_nonpositive_subspace_of_finiteDim :
    ∀ (n : ℕ) {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [CompleteSpace V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = n →
      ∀ (η A : V →L[ℂ] V),
        ContinuousLinearMap.adjoint η = η →
        Function.Bijective η →
        IsEtaPseudoHermitian η A →
        ∃ M : Submodule ℂ V,
          (∀ x ∈ M, A x ∈ M) ∧
          (∀ x ∈ M, (⟪η x, x⟫_ℂ).re ≤ 0) ∧
          Module.finrank ℂ M = etaNegIndex η := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ _ hfin η A hη_sa hη_bij hA
    by_cases hκ : etaNegIndex η = 0
    · refine ⟨⊥, fun x hx => ?_, fun x hx => ?_, ?_⟩
      · rw [Submodule.mem_bot] at hx; simp [hx]
      · rw [Submodule.mem_bot] at hx; simp [hx]
      · rw [finrank_bot, hκ]
    · have hVpos : 0 < Module.finrank ℂ V := by
        have hle : etaNegIndex η ≤ Module.finrank ℂ V := Submodule.finrank_le _
        omega
      have : Nontrivial V := Module.finrank_pos_iff.mp hVpos
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A : V →ₗ[ℂ] V)
      obtain ⟨v, hvEig, hv0⟩ := hμ.exists_hasEigenvector
      have hvA : A v = μ • v := Module.End.mem_eigenspace_iff.mp hvEig
      have hAdj : ∀ u w : V, ⟪η u, w⟫_ℂ = ⟪u, η w⟫_ℂ := fun u w => by
        rw [← ContinuousLinearMap.adjoint_inner_left, hη_sa]
      have hηv0 : η v ≠ 0 := fun h => hv0 (hη_bij.injective (h.trans (map_zero η).symm))
      by_cases hdef : (⟪η v, v⟫_ℂ).re = 0
      · -- Neutral eigenvector case: build hyperbolic plane H = span{v, u} and project A onto U
        have hηvv_zero : ⟪η v, v⟫_ℂ = 0 := by
          have him : (⟪η v, v⟫_ℂ).im = 0 := by
            have hconj : star ⟪η v, v⟫_ℂ = ⟪η v, v⟫_ℂ := by
              calc
                star ⟪η v, v⟫_ℂ = ⟪v, η v⟫_ℂ := inner_conj_symm _ _
                _ = ⟪η v, v⟫_ℂ := (hAdj v v).symm
            have := congrArg Complex.im hconj
            simp only [RCLike.star_def, Complex.conj_im] at this
            linarith
          exact Complex.ext hdef him
        let w1 : V := ((‖η v‖ ^ 2 : ℝ)⁻¹ : ℂ) • (η v)
        have hnorm2 : ‖η v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hηv0)
        have hηvw1 : ⟪η v, w1⟫_ℂ = 1 := by
          change ⟪η v, (((‖η v‖ ^ 2 : ℝ)⁻¹ : ℂ)) • η v⟫_ℂ = 1
          rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
          have h2 : (‖η v‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hnorm2
          push_cast
          exact inv_mul_cancel₀ h2
        have hηw1v : ⟪η w1, v⟫_ℂ = 1 := by
          have h1 : ⟪η w1, v⟫_ℂ = star ⟪η v, w1⟫_ℂ := by
            rw [hAdj, RCLike.star_def, inner_conj_symm]
          rw [h1, hηvw1, star_one]
        let c0 : ℝ := (⟪η w1, w1⟫_ℂ).re / 2
        let u : V := w1 - (c0 : ℂ) • v
        have hηvu : ⟪η v, u⟫_ℂ = 1 := by
          change ⟪η v, w1 - (c0 : ℂ) • v⟫_ℂ = 1
          rw [inner_sub_right, hηvw1, inner_smul_right, hηvv_zero, mul_zero, sub_zero]
        have hηuv : ⟪η u, v⟫_ℂ = 1 := by
          have h1 : ⟪η u, v⟫_ℂ = star ⟪η v, u⟫_ℂ := by
            rw [hAdj, RCLike.star_def, inner_conj_symm]
          rw [h1, hηvu, star_one]
        have hηuu_real : star ⟪η w1, w1⟫_ℂ = ⟪η w1, w1⟫_ℂ := by
          rw [RCLike.star_def, inner_conj_symm, hAdj]
        have hηuu_im : (⟪η w1, w1⟫_ℂ).im = 0 := by
          have h0 := congrArg Complex.im hηuu_real
          simp only [RCLike.star_def, Complex.conj_im] at h0
          linarith
        have hηw1w1_eq : ⟪η w1, w1⟫_ℂ = ((2 * c0 : ℝ) : ℂ) := by
          apply Complex.ext
          · simp only [Complex.ofReal_re, c0]
            ring
          · simp only [Complex.ofReal_im, hηuu_im]
        have hηuu : ⟪η u, u⟫_ℂ = 0 := by
          have hsub : η u = η w1 - (c0 : ℂ) • η v := by
            change η (w1 - (c0 : ℂ) • v) = _
            simp only [map_sub, map_smul]
          have h1 : ⟪η u, u⟫_ℂ = ⟪η w1 - (c0 : ℂ) • η v, w1 - (c0 : ℂ) • v⟫_ℂ := by
            rw [hsub]
          have hA' : ⟪η w1 - (c0 : ℂ) • η v, w1 - (c0 : ℂ) • v⟫_ℂ =
              (⟪η w1, w1⟫_ℂ - (c0 : ℂ) * ⟪η w1, v⟫_ℂ) -
                ((starRingEnd ℂ) (c0 : ℂ) * ⟪η v, w1⟫_ℂ -
                  (starRingEnd ℂ) (c0 : ℂ) * ((c0 : ℂ) * ⟪η v, v⟫_ℂ)) := by
            simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
            ring
          rw [h1, hA', hηw1w1_eq, hηw1v, hηvw1, hηvv_zero]
          simp only [Complex.conj_ofReal, mul_zero, sub_zero, mul_one]
          push_cast
          ring
        let H : Submodule ℂ V := Submodule.span ℂ {v, u}
        have hH_nondeg : ∀ h ∈ H, (∀ h' ∈ H, ⟪η h, h'⟫_ℂ = 0) → h = 0 := by
          intro h hh h0
          rcases Submodule.mem_span_pair.mp hh with ⟨a, b, rfl⟩
          have hv_orth : ⟪η (a • v + b • u), v⟫_ℂ = 0 :=
            h0 v (Submodule.subset_span (Set.mem_insert v {u}))
          have hu_orth : ⟪η (a • v + b • u), u⟫_ℂ = 0 :=
            h0 u (Submodule.subset_span (Set.mem_insert_of_mem v rfl))
          have hv_exp : η (a • v + b • u) = a • η v + b • η u := by
            rw [map_add, map_smul, map_smul]
          rw [hv_exp, inner_add_left, inner_smul_left, inner_smul_left,
            hηvv_zero, hηuv, mul_zero, zero_add, mul_one, ← RCLike.star_def] at hv_orth
          rw [hv_exp, inner_add_left, inner_smul_left, inner_smul_left,
            hηvu, hηuu, mul_one, mul_zero, add_zero, ← RCLike.star_def] at hu_orth
          have ha0 : a = 0 := star_eq_zero.mp hu_orth
          have hb0 : b = 0 := star_eq_zero.mp hv_orth
          simp [ha0, hb0]
        have hvu_li : LinearIndependent ℂ ![v, u] := by
          rw [Fintype.linearIndependent_iff]
          intro c hc i
          have hsum : c 0 • v + c 1 • u = 0 := by simpa [Fin.sum_univ_two] using hc
          have hv_orth : ⟪η (c 0 • v + c 1 • u), v⟫_ℂ = 0 := by rw [hsum, map_zero, inner_zero_left]
          have hu_orth : ⟪η (c 0 • v + c 1 • u), u⟫_ℂ = 0 := by rw [hsum, map_zero, inner_zero_left]
          have hv_exp : η (c 0 • v + c 1 • u) = c 0 • η v + c 1 • η u := by
            rw [map_add, map_smul, map_smul]
          rw [hv_exp, inner_add_left, inner_smul_left, inner_smul_left,
            hηvv_zero, hηuv, mul_zero, zero_add, mul_one, ← RCLike.star_def] at hv_orth
          rw [hv_exp, inner_add_left, inner_smul_left, inner_smul_left,
            hηvu, hηuu, mul_one, mul_zero, add_zero, ← RCLike.star_def] at hu_orth
          fin_cases i
          · exact star_eq_zero.mp hu_orth
          · exact star_eq_zero.mp hv_orth
        have hH_dim : Module.finrank ℂ H = 2 := by
          have hset : ({v, u} : Set V) = Set.range ![v, u] := by
            ext x
            simp [Set.mem_insert_iff, Set.mem_singleton_iff, Matrix.range_cons,
              Matrix.range_empty]
            tauto
          have hspan : H = Submodule.span ℂ (Set.range ![v, u]) := by
            dsimp [H]
            rw [hset]
          rw [hspan, finrank_span_eq_card hvu_li, Fintype.card_fin]
        let U : Submodule ℂ V := (H.map (η : V →ₗ[ℂ] V))ᗮ
        let _ : CompleteSpace U := (Submodule.closed_of_finiteDimensional U).completeSpace_coe
        obtain ⟨hCompl, ηU, hηU_sa, hηU_bij, hηU_pair, hOrtho⟩ :=
          submodule_eta_compression_props hη_sa hη_bij H hH_nondeg
        have hηU_inner : ∀ x : U, ⟪ηU x, x⟫_ℂ = ⟪η x.1, x.1⟫_ℂ := fun x => hηU_pair x x
        let Hpos : Submodule ℂ V := Submodule.span ℂ {v + u}
        let Hneg : Submodule ℂ V := Submodule.span ℂ {v - u}
        have hHpos_le : Hpos ≤ H := by
          rw [Submodule.span_singleton_le_iff_mem]
          exact H.add_mem (Submodule.subset_span (Set.mem_insert v {u}))
            (Submodule.subset_span (Set.mem_insert_of_mem v rfl))
        have hHneg_le : Hneg ≤ H := by
          rw [Submodule.span_singleton_le_iff_mem]
          exact H.sub_mem (Submodule.subset_span (Set.mem_insert v {u}))
            (Submodule.subset_span (Set.mem_insert_of_mem v rfl))
        have hH_compl : IsCompl (Hpos.comap H.subtype) (Hneg.comap H.subtype) := by
          have hDisj : Disjoint (Hpos.comap H.subtype) (Hneg.comap H.subtype) := by
            rw [disjoint_iff_inf_le]
            intro ⟨x, hxH⟩ ⟨hxP, hxN⟩
            have hxP' : x ∈ Hpos := hxP
            have hxN' : x ∈ Hneg := hxN
            rw [Submodule.mem_span_singleton] at hxP' hxN'
            rcases hxP' with ⟨a, ha⟩
            rcases hxN' with ⟨b, hb⟩
            have hEq : (a - b) • v + (a + b) • u = 0 := by
              have h1 : a • (v + u) - b • (v - u) = 0 := by rw [ha, hb, sub_self]
              calc
                (a - b) • v + (a + b) • u = a • (v + u) - b • (v - u) := by module
                _ = 0 := h1
            have hc := Fintype.linearIndependent_iff.mp hvu_li ![a - b, a + b]
              (by simpa [Fin.sum_univ_two] using hEq)
            have hc0 : a - b = 0 := hc 0
            have hc1 : a + b = 0 := hc 1
            have ha0 : a = 0 := by
              have h2 : (2 : ℂ) * a = 0 := by
                calc
                  (2 : ℂ) * a = (a - b) + (a + b) := by ring
                  _ = 0 := by rw [hc0, hc1, add_zero]
              exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
            have hx0 : x = 0 := by simpa [ha0] using ha.symm
            exact Subtype.ext hx0
          have hCodisj : Codisjoint (Hpos.comap H.subtype) (Hneg.comap H.subtype) := by
            rw [Submodule.codisjoint_iff_exists_add_eq]
            intro ⟨x, hxH⟩
            rcases Submodule.mem_span_pair.mp hxH with ⟨a, b, hxab⟩
            let α : ℂ := (2 : ℂ)⁻¹ * (a + b)
            let β : ℂ := (2 : ℂ)⁻¹ * (a - b)
            refine ⟨⟨α • (v + u), hHpos_le (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))⟩,
              ⟨β • (v - u), hHneg_le (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))⟩,
              ?_, ?_, ?_⟩
            · exact Submodule.mem_span_singleton.mpr ⟨α, rfl⟩
            · exact Submodule.mem_span_singleton.mpr ⟨β, rfl⟩
            · apply Subtype.ext
              change α • (v + u) + β • (v - u) = x
              rw [← hxab]
              have hα : α + β = a := by dsimp [α, β]; ring
              have hβ : α - β = b := by dsimp [α, β]; ring
              rw [← hα, ← hβ]
              module
          exact ⟨hDisj, hCodisj⟩
        have hHpos_def : ∀ z ∈ Hpos, z ≠ 0 → 0 < (⟪η z, z⟫_ℂ).re := by
          intro z hz hzne
          rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
          have ha : a ≠ 0 := fun h => hzne (by simp [h])
          have h1 : ⟪η (a • (v + u)), a • (v + u)⟫_ℂ = ((2 * ‖a‖ ^ 2 : ℝ) : ℂ) := by
            rw [map_smul, inner_smul_left, inner_smul_right, map_add, inner_add_left,
              inner_add_right, inner_add_right, hηvv_zero, hηvu, hηuv, hηuu]
            have hmul : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.conj_mul']; push_cast; rfl
            calc
              (starRingEnd ℂ) a * (a * (0 + 1 + (1 + 0)))
                  = ((starRingEnd ℂ) a * a) * 2 := by ring
              _ = ((2 * ‖a‖ ^ 2 : ℝ) : ℂ) := by rw [hmul]; push_cast; ring
          rw [h1, Complex.ofReal_re]
          exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr ha))
        have hHneg_def : ∀ z ∈ Hneg, z ≠ 0 → (⟪η z, z⟫_ℂ).re < 0 := by
          intro z hz hzne
          rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
          have ha : a ≠ 0 := fun h => hzne (by simp [h])
          have h1 : ⟪η (a • (v - u)), a • (v - u)⟫_ℂ = ((-(2 * ‖a‖ ^ 2) : ℝ) : ℂ) := by
            have hR1 : ⟪η v, v - u⟫_ℂ = ⟪η v, v⟫_ℂ - ⟪η v, u⟫_ℂ := inner_sub_right _ _ _
            have hR2 : ⟪η u, v - u⟫_ℂ = ⟪η u, v⟫_ℂ - ⟪η u, u⟫_ℂ := inner_sub_right _ _ _
            rw [map_smul, inner_smul_left, inner_smul_right, map_sub, inner_sub_left,
              hR1, hR2, hηvv_zero, hηvu, hηuv, hηuu]
            have hmul : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.conj_mul']; push_cast; rfl
            calc
              (starRingEnd ℂ) a * (a * (0 - 1 - (1 - 0)))
                  = ((starRingEnd ℂ) a * a) * (-2) := by ring
              _ = ((-(2 * ‖a‖ ^ 2) : ℝ) : ℂ) := by rw [hmul]; push_cast; ring
          rw [h1, Complex.ofReal_re]
          exact neg_lt_zero.mpr (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr ha)))
        have hNegSplit : etaNegIndex η = Module.finrank ℂ Hneg + etaNegIndex ηU :=
          etaNegIndex_split_of_decomp hη_sa hη_bij hCompl hOrtho Hpos Hneg hH_compl hHpos_le
            hHneg_le hHpos_def hHneg_def hηU_sa hηU_bij hηU_inner
        have hHneg_dim : Module.finrank ℂ Hneg = 1 := by
          apply finrank_span_singleton
          intro hvu
          have hc := Fintype.linearIndependent_iff.mp hvu_li ![1, -1]
            (by simpa [Fin.sum_univ_two, sub_eq_add_neg] using hvu) 0
          norm_num at hc
        have hAx_mem_U : ∀ x : U, A x.1 - ⟪η u, A x.1⟫_ℂ • v ∈ U := by
          intro x
          have hU_eq : ∀ z : V, (⟪η v, z⟫_ℂ = 0 ∧ ⟪η u, z⟫_ℂ = 0) ↔ z ∈ U := fun z => by
            constructor
            · rintro ⟨hzv, hzu⟩ w hw
              rcases Submodule.mem_map.mp hw with ⟨h, hhH, rfl⟩
              rcases Submodule.mem_span_pair.mp hhH with ⟨a, b, rfl⟩
              change ⟪η (a • v + b • u), z⟫_ℂ = 0
              have hexp : η (a • v + b • u) = a • η v + b • η u := by
                rw [map_add, map_smul, map_smul]
              rw [hexp, inner_add_left, inner_smul_left, inner_smul_left,
                hzv, hzu, mul_zero, mul_zero, add_zero]
            · intro hz
              refine ⟨?_, ?_⟩
              · exact hz (η v) (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_insert v {u})))
              · exact hz (η u) (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_insert_of_mem v rfl)))
          rw [← hU_eq]
          have hAv : ⟪η v, A x.1⟫_ℂ = 0 := by
            have hAadj : (ContinuousLinearMap.adjoint A) (η v) = η (A v) := by
              simpa using congrArg (fun T : V →L[ℂ] V => T v) hA
            calc
              ⟪η v, A x.1⟫_ℂ = ⟪(ContinuousLinearMap.adjoint A) (η v), x.1⟫_ℂ :=
                    (ContinuousLinearMap.adjoint_inner_left A x.1 (η v)).symm
              _ = ⟪η (A v), x.1⟫_ℂ := by rw [hAadj]
              _ = ⟪η (μ • v), x.1⟫_ℂ := by rw [hvA]
              _ = (starRingEnd ℂ) μ * ⟪η v, x.1⟫_ℂ := by rw [map_smul, inner_smul_left]
              _ = 0 := by
                    rw [hOrtho v (Submodule.subset_span (Set.mem_insert v {u})) x.1 x.2, mul_zero]
          refine ⟨?_, ?_⟩
          · rw [inner_sub_right, inner_smul_right, hAv, hηvv_zero, mul_zero, sub_zero]
          · rw [inner_sub_right, inner_smul_right, hηuv, mul_one, sub_self]
        let AU_lin : U →ₗ[ℂ] U :=
          { toFun := fun x => ⟨A x.1 - ⟪η u, A x.1⟫_ℂ • v, hAx_mem_U x⟩
            map_add' := fun x y => by
              ext
              simp only [Submodule.coe_add, map_add, inner_add_right, add_smul]
              abel
            map_smul' := fun c x => by
              ext
              simp only [RingHom.id_apply, SetLike.val_smul, map_smul, inner_smul_right,
                smul_smul, smul_sub] }
        let AU : U →L[ℂ] U := LinearMap.toContinuousLinearMap AU_lin
        have hAU_pseudo : IsEtaPseudoHermitian ηU AU := by
          rw [isEtaPseudoHermitian_iff_etaInner ηU AU]
          intro x y
          have hL : ⟪ηU (AU x), y⟫_ℂ = ⟪η (A x.1), y.1⟫_ℂ := by
            rw [hηU_pair]
            change ⟪η (A x.1 - ⟪η u, A x.1⟫_ℂ • v), y.1⟫_ℂ = _
            rw [map_sub, map_smul, inner_sub_left, inner_smul_left,
              hOrtho v (Submodule.subset_span (Set.mem_insert v {u})) y.1 y.2, mul_zero, sub_zero]
          have hR : ⟪ηU x, AU y⟫_ℂ = ⟪η x.1, A y.1⟫_ℂ := by
            rw [hηU_pair]
            change ⟪η x.1, A y.1 - ⟪η u, A y.1⟫_ℂ • v⟫_ℂ = _
            have hxv : ⟪η x.1, v⟫_ℂ = 0 := by
              rw [hAdj, inner_eq_zero_symm]
              exact hOrtho v (Submodule.subset_span (Set.mem_insert v {u})) x.1 x.2
            rw [inner_sub_right, inner_smul_right, hxv, mul_zero, sub_zero]
          unfold etaInner
          rw [hL, hR]
          exact ((isEtaPseudoHermitian_iff_etaInner η A).mp hA) x.1 y.1
        have hdimU_lt : Module.finrank ℂ U < n := by
          have hComplU : IsCompl H U := hCompl
          have hsum := Submodule.finrank_add_eq_of_isCompl hComplU
          rw [hH_dim, hfin] at hsum
          omega
        obtain ⟨M', hM'_inv, hM'_nonpos, hM'_dim⟩ :=
          ih (Module.finrank ℂ U) hdimU_lt rfl ηU AU hηU_sa hηU_bij hAU_pseudo
        let L : Submodule ℂ V := Submodule.span ℂ {v}
        let M : Submodule ℂ V := L ⊔ M'.map U.subtype
        have hDisjLM : Disjoint L (M'.map U.subtype) := by
          rw [disjoint_iff_inf_le]
          intro x ⟨hxL, hxM⟩
          have hxH : x ∈ H := ((Submodule.span_singleton_le_iff_mem v H).2
            (Submodule.subset_span (Set.mem_insert v {u}))) hxL
          have hxU : x ∈ U := Submodule.map_subtype_le _ _ hxM
          have hxHU : x ∈ H ⊓ U := ⟨hxH, hxU⟩
          rwa [hCompl.disjoint.eq_bot] at hxHU
        refine ⟨M, fun x hx => ?_, fun x hx => ?_, ?_⟩
        · rcases Submodule.mem_sup.mp hx with ⟨lv, hlv, m, hm, rfl⟩
          rcases Submodule.mem_span_singleton.mp hlv with ⟨a, rfl⟩
          rcases Submodule.mem_map.mp hm with ⟨m', hm', rfl⟩
          have hAvM : A (a • v) ∈ M := by
            rw [map_smul, hvA]
            exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
              (Submodule.mem_span_singleton_self v)))
          have hAmM : A m'.1 ∈ M := by
            have hEq : A m'.1 = (AU m').1 + ⟪η u, A m'.1⟫_ℂ • v := by
              change A m'.1 = (A m'.1 - ⟪η u, A m'.1⟫_ℂ • v) + ⟪η u, A m'.1⟫_ℂ • v
              abel
            rw [hEq]
            exact M.add_mem
              (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hM'_inv m' hm')))
              (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
          rw [map_add]
          exact M.add_mem hAvM hAmM
        · rcases Submodule.mem_sup.mp hx with ⟨lv, hlv, m, hm, rfl⟩
          rcases Submodule.mem_span_singleton.mp hlv with ⟨a, rfl⟩
          rcases Submodule.mem_map.mp hm with ⟨m', hm', rfl⟩
          have h12 : ⟪η (a • v), m'.1⟫_ℂ = 0 := by
            rw [map_smul, inner_smul_left,
              hOrtho v (Submodule.subset_span (Set.mem_insert v {u})) m'.1 m'.2, mul_zero]
          have h21 : ⟪η m'.1, a • v⟫_ℂ = 0 := by
            rw [hAdj, inner_eq_zero_symm]
            exact h12
          have hvv : ⟪η (a • v), a • v⟫_ℂ = 0 := by
            rw [map_smul, inner_smul_left, inner_smul_right, hηvv_zero, mul_zero, mul_zero]
          have hre : (⟪η (a • v + m'.1), a • v + m'.1⟫_ℂ).re = (⟪ηU m', m'⟫_ℂ).re := by
            rw [map_add, inner_add_left, inner_add_right, inner_add_right, hvv, h12, h21,
              hηU_inner]
            simp
          simp only [Submodule.coe_subtype]
          rw [hre]
          exact hM'_nonpos m' hm'
        · have hsup := Submodule.finrank_sup_add_finrank_inf_eq L (M'.map U.subtype)
          rw [hDisjLM.eq_bot, finrank_bot, add_zero] at hsup
          have hLdim : Module.finrank ℂ L = 1 := finrank_span_singleton hv0
          have hMdim : Module.finrank ℂ (M'.map U.subtype) = Module.finrank ℂ M' :=
            (Submodule.equivMapOfInjective U.subtype Subtype.val_injective M').symm.finrank_eq
          rw [hsup, hLdim, hMdim, hM'_dim, hNegSplit, hHneg_dim]
      · -- Definite eigenvector case: μ is real, H = span{v}, U = (H.map η)ᗮ is A-invariant
        have hμ_real : star μ = μ := by
          have hpair := eta_biorthogonal_pairing η A hA hvA hvA
          have hne0 : etaInner η v v ≠ 0 := fun h0 => hdef (by simp [etaInner] at h0; simp [h0])
          exact sub_eq_zero.mp ((mul_eq_zero.mp hpair).resolve_right hne0)
        let H : Submodule ℂ V := Submodule.span ℂ {v}
        have hηvv_ne : ⟪η v, v⟫_ℂ ≠ 0 := fun h0 => hdef (by simp [h0])
        have hH_nondeg : ∀ h ∈ H, (∀ h' ∈ H, ⟪η h, h'⟫_ℂ = 0) → h = 0 := by
          intro h hh h0
          rcases Submodule.mem_span_singleton.mp hh with ⟨a, rfl⟩
          have hv0' := h0 v (Submodule.mem_span_singleton_self v)
          rw [map_smul, inner_smul_left, mul_eq_zero] at hv0'
          rcases hv0' with ha | hzero
          · simp [star_eq_zero.mp ha]
          · exact absurd hzero hηvv_ne
        let U : Submodule ℂ V := (H.map (η : V →ₗ[ℂ] V))ᗮ
        let _ : CompleteSpace U := (Submodule.closed_of_finiteDimensional U).completeSpace_coe
        obtain ⟨hCompl, ηU, hηU_sa, hηU_bij, hηU_pair, hOrtho⟩ :=
          submodule_eta_compression_props hη_sa hη_bij H hH_nondeg
        have hηU_inner : ∀ x : U, ⟪ηU x, x⟫_ℂ = ⟪η x.1, x.1⟫_ℂ := fun x => hηU_pair x x
        have hU_inv : ∀ x : U, A x.1 ∈ U := by
          intro x w hw
          rcases Submodule.mem_map.mp hw with ⟨h, hhH, rfl⟩
          rcases Submodule.mem_span_singleton.mp hhH with ⟨a, rfl⟩
          have hAadj : (ContinuousLinearMap.adjoint A) (η v) = η (A v) := by
            simpa using congrArg (fun T : V →L[ℂ] V => T v) hA
          change ⟪η (a • v), A x.1⟫_ℂ = 0
          rw [map_smul, inner_smul_left]
          have h0 : ⟪η v, A x.1⟫_ℂ = 0 := by
            calc
              ⟪η v, A x.1⟫_ℂ = ⟪(ContinuousLinearMap.adjoint A) (η v), x.1⟫_ℂ :=
                    (ContinuousLinearMap.adjoint_inner_left A x.1 (η v)).symm
              _ = ⟪η (A v), x.1⟫_ℂ := by rw [hAadj]
              _ = ⟪η (μ • v), x.1⟫_ℂ := by rw [hvA]
              _ = (starRingEnd ℂ) μ * ⟪η v, x.1⟫_ℂ := by rw [map_smul, inner_smul_left]
              _ = 0 := by
                    rw [hOrtho v (Submodule.mem_span_singleton_self v) x.1 x.2, mul_zero]
          rw [h0, mul_zero]
        let AU_lin : U →ₗ[ℂ] U :=
          { toFun := fun x => ⟨A x.1, hU_inv x⟩
            map_add' := fun x y => Subtype.ext (map_add A x.1 y.1)
            map_smul' := fun c x => Subtype.ext (map_smul A c x.1) }
        let AU : U →L[ℂ] U := LinearMap.toContinuousLinearMap AU_lin
        have hAU_pseudo : IsEtaPseudoHermitian ηU AU := by
          rw [isEtaPseudoHermitian_iff_etaInner ηU AU]
          intro x y
          unfold etaInner
          rw [hηU_pair, hηU_pair]
          exact ((isEtaPseudoHermitian_iff_etaInner η A).mp hA) x.1 y.1
        have hdimU_lt : Module.finrank ℂ U < n := by
          have hComplU : IsCompl H U := hCompl
          have hsum := Submodule.finrank_add_eq_of_isCompl hComplU
          have hHdim : Module.finrank ℂ H = 1 := finrank_span_singleton hv0
          rw [hHdim, hfin] at hsum
          omega
        obtain ⟨M', hM'_inv, hM'_nonpos, hM'_dim⟩ :=
          ih (Module.finrank ℂ U) hdimU_lt rfl ηU AU hηU_sa hηU_bij hAU_pseudo
        rcases lt_or_gt_of_ne hdef with hneg | hpos
        · -- Negative eigenvector: take M = H ⊔ M'.map U.subtype
          have hH_compl : IsCompl (⊥ : Submodule ℂ H) (⊤ : Submodule ℂ H) := isCompl_bot_top
          have hH_compl' : IsCompl ((⊥ : Submodule ℂ V).comap H.subtype) (H.comap H.subtype) := by
            simpa [Submodule.comap_bot] using hH_compl
          have hNegSplit : etaNegIndex η = Module.finrank ℂ H + etaNegIndex ηU :=
            etaNegIndex_split_of_decomp hη_sa hη_bij hCompl hOrtho ⊥ H hH_compl'
              bot_le le_rfl (fun _ hx h0 => absurd hx h0)
                (fun z hz hzne => by
                  rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
                  have ha : a ≠ 0 := fun h => hzne (by simp [h])
                  have hmul : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
                    rw [Complex.conj_mul']; push_cast; rfl
                  have h1 : (⟪η (a • v), a • v⟫_ℂ).re = ‖a‖ ^ 2 * (⟪η v, v⟫_ℂ).re := by
                    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hmul,
                      Complex.re_ofReal_mul]
                  rw [h1]
                  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (norm_pos_iff.mpr ha)) hneg)
              hηU_sa hηU_bij hηU_inner
          let M : Submodule ℂ V := H ⊔ M'.map U.subtype
          have hDisjHM : Disjoint H (M'.map U.subtype) := by
            rw [disjoint_iff_inf_le]
            intro x ⟨hxH, hxM⟩
            have hxU : x ∈ U := Submodule.map_subtype_le _ _ hxM
            have hxHU : x ∈ H ⊓ U := ⟨hxH, hxU⟩
            rwa [hCompl.disjoint.eq_bot] at hxHU
          refine ⟨M, fun x hx => ?_, fun x hx => ?_, ?_⟩
          · rcases Submodule.mem_sup.mp hx with ⟨hv', hhv', m, hm, rfl⟩
            rcases Submodule.mem_span_singleton.mp hhv' with ⟨a, rfl⟩
            rcases Submodule.mem_map.mp hm with ⟨m', hm', rfl⟩
            rw [map_add]
            exact M.add_mem
              (Submodule.mem_sup_left (by
                rw [map_smul, hvA]
                exact Submodule.smul_mem _ _
                  (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))))
              (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hM'_inv m' hm')))
          · rcases Submodule.mem_sup.mp hx with ⟨hv', hhv', m, hm, rfl⟩
            rcases Submodule.mem_span_singleton.mp hhv' with ⟨a, rfl⟩
            rcases Submodule.mem_map.mp hm with ⟨m', hm', rfl⟩
            have h12 : ⟪η (a • v), m'.1⟫_ℂ = 0 := by
              rw [map_smul, inner_smul_left,
                hOrtho v (Submodule.mem_span_singleton_self v) m'.1 m'.2, mul_zero]
            have h21 : ⟪η m'.1, a • v⟫_ℂ = 0 := by
              rw [hAdj, inner_eq_zero_symm]
              exact h12
            have hre : (⟪η (a • v + m'.1), a • v + m'.1⟫_ℂ).re =
                ‖a‖ ^ 2 * (⟪η v, v⟫_ℂ).re + (⟪ηU m', m'⟫_ℂ).re := by
              have hmul : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
                rw [Complex.conj_mul']; push_cast; rfl
              rw [map_add, inner_add_left, inner_add_right, inner_add_right, h12, h21,
                hηU_inner, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hmul]
              simp only [Complex.add_re, add_zero, zero_add, Complex.re_ofReal_mul]
            simp only [Submodule.coe_subtype]
            rw [hre]
            exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_lt hneg))
              (hM'_nonpos m' hm')
          · have hsup := Submodule.finrank_sup_add_finrank_inf_eq H (M'.map U.subtype)
            rw [hDisjHM.eq_bot, finrank_bot, add_zero] at hsup
            have hMdim : Module.finrank ℂ (M'.map U.subtype) = Module.finrank ℂ M' :=
              (Submodule.equivMapOfInjective U.subtype Subtype.val_injective M').symm.finrank_eq
            rw [hsup, hMdim, hM'_dim, hNegSplit]
        · -- Positive eigenvector: take M = M'.map U.subtype
          have hH_compl : IsCompl (⊤ : Submodule ℂ H) (⊥ : Submodule ℂ H) := isCompl_top_bot
          have hH_compl' : IsCompl (H.comap H.subtype) ((⊥ : Submodule ℂ V).comap H.subtype) := by
            simpa [Submodule.comap_bot] using hH_compl
          have hNegSplit : etaNegIndex η = Module.finrank ℂ (⊥ : Submodule ℂ V) + etaNegIndex ηU :=
            etaNegIndex_split_of_decomp hη_sa hη_bij hCompl hOrtho H ⊥ hH_compl'
              le_rfl bot_le
              (fun z hz hzne => by
                rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
                have ha : a ≠ 0 := fun h => hzne (by simp [h])
                have hmul : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
                  rw [Complex.conj_mul']; push_cast; rfl
                have h1 : (⟪η (a • v), a • v⟫_ℂ).re = ‖a‖ ^ 2 * (⟪η v, v⟫_ℂ).re := by
                  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hmul,
                    Complex.re_ofReal_mul]
                rw [h1]
                exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr ha)) hpos)
              (fun _ hx h0 => absurd hx h0)
              hηU_sa hηU_bij hηU_inner
          rw [finrank_bot, zero_add] at hNegSplit
          refine ⟨M'.map U.subtype, fun x hx => ?_, fun x hx => ?_, ?_⟩
          · rcases Submodule.mem_map.mp hx with ⟨m', hm', rfl⟩
            exact Submodule.mem_map_of_mem (hM'_inv m' hm')
          · rcases Submodule.mem_map.mp hx with ⟨m', hm', rfl⟩
            simp only [Submodule.coe_subtype]
            rw [← hηU_inner m']
            exact hM'_nonpos m' hm'
          · have hMdim : Module.finrank ℂ (M'.map U.subtype) = Module.finrank ℂ M' :=
              (Submodule.equivMapOfInjective U.subtype Subtype.val_injective M').symm.finrank_eq
            rw [hMdim, hM'_dim, hNegSplit]

/-- **Pontryagin Invariant Subspace Theorem** (`S3-20`, Pontryagin 1944; Kissin 2020 Thm 1.1;
`R3.1`): every `J`-self-adjoint bounded operator `A` on a finite-dimensional complex Pontryagin
space `V` ($\Pi_\kappa$) admits an `A`-invariant, `J`-nonpositive subspace `M ≤ V` of exact
dimension `κ = negIndex V` which is maximal among all `J`-nonpositive subspaces. -/
theorem ComplexPontryaginSpace.exists_invariant_maxNonpositive_subspace
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [FiniteDimensional ℂ V] [ComplexPontryaginSpace V] (A : V →L[ℂ] V)
    (hA : ComplexKreinSpace.IsComplexKreinSelfAdjoint A) :
    ∃ M : Submodule ℂ V,
      (∀ x ∈ M, A x ∈ M) ∧
      (∀ x ∈ M, (ComplexKreinSpace.complexKreinInner x x).re ≤ 0) ∧
      Module.finrank ℂ M = ComplexPontryaginSpace.negIndex V ∧
      (∀ M' : Submodule ℂ V,
        (∀ y ∈ M', (ComplexKreinSpace.complexKreinInner y y).re ≤ 0) →
        M ≤ M' → M = M') := by
  let η : V →L[ℂ] V := ComplexKreinSpace.jCLM (H := V)
  have hη_sa : ContinuousLinearMap.adjoint η = η := ComplexKreinSpace.adjoint_jCLM
  have hη_bij : Function.Bijective η :=
    Function.Involutive.bijective (ComplexKreinSpace.J_invol (H := V))
  have hA_eta : IsEtaPseudoHermitian η A :=
    (ComplexKreinSpace.isComplexKreinSelfAdjoint_iff_eta A).mp hA
  obtain ⟨M, hM_inv, hM_nonpos, hM_dim⟩ :=
    exists_eta_invariant_nonpositive_subspace_of_finiteDim (Module.finrank ℂ V) rfl η A
      hη_sa hη_bij hA_eta
  rw [etaNegIndex_jCLM_eq V] at hM_dim
  refine ⟨M, hM_inv, hM_nonpos, hM_dim, fun M' hM' hle => ?_⟩
  have hM'_le : Module.finrank ℂ M' ≤ ComplexPontryaginSpace.negIndex V := by
    rw [← etaNegIndex_jCLM_eq V]
    exact finrank_le_etaNegIndex_of_nonpositive hη_sa hη_bij M' hM'
  have hM_le_M' : Module.finrank ℂ M ≤ Module.finrank ℂ M' := Submodule.finrank_mono hle
  have hEqDim : Module.finrank ℂ M = Module.finrank ℂ M' := by omega
  exact Submodule.eq_of_le_of_finrank_eq hle hEqDim

end EtaInertiaAndPontryaginTheorem

end InfoGeometry.Krein
