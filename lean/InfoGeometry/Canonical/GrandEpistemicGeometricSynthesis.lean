/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.HodgeGeometricCalculus
import InfoGeometry.Canonical.SuperGrassmannianManifold
import InfoGeometry.Canonical.HolographicColimitContinuum
import InfoGeometry.Epistemology.ChentsovMetricInvariance
import InfoGeometry.Canonical.NaturalGradientSubmersionFlow

/-!
# Grand Epistemic Geometric Synthesis

This module provides cross-module bridge theorems connecting the five algebraic
and information-geometric spine modules:
1. **Hodge Differential-Codifferential Complex (`HodgeGeometricCalculus`)**:
   - `HodgeDifferentialComplex`: Bundles nilpotent linear differential `d` and
     codifferential `delta` operators on an `ℝ`-algebra carrier `A`.
   - Bridges `C.d` and `C.delta` to `HodgeGeometricCalculus.NilpotentDifferential`,
     `HodgeGeometricCalculus.Codifferential`, and `HodgeGeometricCalculus.laplacian`,
     proving Laplacian commutation and harmonic annihilation, alongside the 2D
     Euclidean double Hodge star trace identity (`1 + (-1) + 1 = 1`).
2. **Para-Kähler Super-Grassmannian Spectral Submersion Split
   (`SuperGrassmannianManifold` ↔ `NaturalGradientSubmersionFlow`)**:
   - Proves that the spectral projectors `paraProjectorPlus` and `paraProjectorMinus`
     of any para-complex structure `K` land strictly inside the eigen-sheets
     `InTPlus K` and `InTMinus K`.
   - Deduces that for any compatible `ParaKahlerStructure g omega K`, the projected
     horizontal and vertical subspaces are metric-isotropic (`2 * g (P± v) (P± v) = 0`).
3. **Holographic Colimit Stagewise Submersion Split
   (`HolographicColimitContinuum` ↔ `RiemannianSubmersion`)**:
   - Constructs a `RiemannianSubmersion.SubmersionSplit (T n)` at every stage `n : ℕ`
     of a holographic module tower from a `ProjectorFamily` and its complementary
     projector `complementProjector`, and proves that both horizontal and vertical
     projections intertwine multi-step bonding maps `iotaSeq`.
4. **Chentsov Congruent Partition Functoriality (`ChentsovMetricInvariance`)**:
   - Proves identity Markov kernel Fisher invariance, non-negativity of pushed-forward
     quadratic Fisher energy under `CongruentPartitionEmbedding`, and vanishing Fisher
     energy on the pushed-forward zero tangent vector.
5. **Pinned Submersion Energy & Invariant Geodesic Apex
   (`NaturalGradientSubmersionFlow` ↔ `ChentsovMetricInvariance`)**:
   - Unifies vertical-pinned submersion kinetic energy collapse with Chentsov
     partition-embedding Fisher metric invariance, and establishes simultaneous
     stationarity and global optimality at the critical radius `r* = C / (2K)`.
-/

namespace InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis

open InfoGeometry.Algebra
open InfoGeometry.Canonical
open InfoGeometry.Epistemology

/-! ### 1. Archetype I: Hodge Nilpotent Differential-Codifferential Complex -/

/-- A bundled differential-codifferential complex over a ring module `A`, consisting of
two nilpotent linear operators `d` and `delta` satisfying `d² = 0` and `delta² = 0`. -/
structure HodgeDifferentialComplex (A : Type*) [Ring A] [Module ℝ A] where
  d : A →ₗ[ℝ] A
  delta : A →ₗ[ℝ] A
  d_sq : ∀ x, d (d x) = 0
  delta_sq : ∀ x, delta (delta x) = 0

/-- Canonical zero differential-codifferential complex on any ring module `A`. -/
def zeroHodgeDifferentialComplex (A : Type*) [Ring A] [Module ℝ A] :
    HodgeDifferentialComplex A where
  d := 0
  delta := 0
  d_sq _ := rfl
  delta_sq _ := rfl

/-- Closed concrete witness for `HodgeDifferentialComplex` over `ℝ`. -/
def realZeroHodgeDifferentialComplex : HodgeDifferentialComplex ℝ :=
  zeroHodgeDifferentialComplex ℝ

instance (A : Type*) [Ring A] [Module ℝ A] : Inhabited (HodgeDifferentialComplex A) :=
  ⟨zeroHodgeDifferentialComplex A⟩

/-- The exterior differential `C.d` of a `HodgeDifferentialComplex` satisfies
`HodgeGeometricCalculus.NilpotentDifferential`. -/
theorem hodgeDifferentialComplex_d_nilpotent {A : Type*} [Ring A] [Module ℝ A]
    (C : HodgeDifferentialComplex A) :
    HodgeGeometricCalculus.NilpotentDifferential C.d.toAddMonoidHom :=
  ⟨C.d_sq⟩

/-- The codifferential `C.delta` of a `HodgeDifferentialComplex` satisfies
`HodgeGeometricCalculus.Codifferential`. -/
theorem hodgeDifferentialComplex_delta_codiff {A : Type*} [Ring A] [Module ℝ A]
    (C : HodgeDifferentialComplex A) :
    HodgeGeometricCalculus.Codifferential C.delta.toAddMonoidHom :=
  ⟨C.delta_sq⟩

/-- The Hodge–de Rham Laplacian `Δ = d δ + δ d` associated to a `HodgeDifferentialComplex`. -/
def complexLaplacian {A : Type*} [Ring A] [Module ℝ A]
    (C : HodgeDifferentialComplex A) (x : A) : A :=
  HodgeGeometricCalculus.laplacian C.d.toAddMonoidHom C.delta.toAddMonoidHom x

/-- The differential `C.d` commutes with the complex Laplacian `Δ`. -/
theorem complexLaplacian_comm_d {A : Type*} [Ring A] [Module ℝ A]
    (C : HodgeDifferentialComplex A) (x : A) :
    C.d (complexLaplacian C x) = complexLaplacian C (C.d x) :=
  HodgeGeometricCalculus.laplacian_commutes_d
    C.d.toAddMonoidHom C.delta.toAddMonoidHom (hodgeDifferentialComplex_d_nilpotent C) x

/-- The codifferential `C.delta` commutes with the complex Laplacian `Δ`. -/
theorem complexLaplacian_comm_delta {A : Type*} [Ring A] [Module ℝ A]
    (C : HodgeDifferentialComplex A) (x : A) :
    C.delta (complexLaplacian C x) = complexLaplacian C (C.delta x) :=
  HodgeGeometricCalculus.laplacian_commutes_delta
    C.d.toAddMonoidHom C.delta.toAddMonoidHom (hodgeDifferentialComplex_delta_codiff C) x

/-- Any closed (`d x = 0`) and co-closed (`delta x = 0`) state lies in the kernel of `complexLaplacian`. -/
theorem complexLaplacian_harmonic_zero {A : Type*} [Ring A] [Module ℝ A]
    (C : HodgeDifferentialComplex A) (x : A) (hd : C.d x = 0) (hdelta : C.delta x = 0) :
    complexLaplacian C x = 0 :=
  HodgeGeometricCalculus.harmonic_annihilated_by_laplacian
    C.d.toAddMonoidHom C.delta.toAddMonoidHom x ⟨hd, hdelta⟩

/-- In 2D Euclidean space (`n = 2, s = 0`), the sum of the double Hodge star signs across
0-forms (`+1`), 1-forms (`-1`), and 2-forms (`+1`) equals `1`. -/
theorem hodge_double_star_2d_sum {R : Type*} [CommRing R] :
    HodgeGeometricCalculus.hodgeSign (R := R) 0 2 0 +
      HodgeGeometricCalculus.hodgeSign (R := R) 1 2 0 +
      HodgeGeometricCalculus.hodgeSign (R := R) 2 2 0 = 1 := by
  rw [HodgeGeometricCalculus.hodge_sq_scalar_2d,
      HodgeGeometricCalculus.hodge_sq_vector_2d,
      HodgeGeometricCalculus.hodge_sq_bivector_2d]
  ring

/-! ### 2. Archetype II: Para-Kähler Super-Grassmannian Spectral Submersion Split -/

section ParaKahlerSubmersion

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- For any para-complex structure `K`, the positive spectral projector `paraProjectorPlus K`
maps every vector `v` into the `+1` eigen-sheet `InTPlus K`. -/
theorem paraProjectorPlus_in_TPlus
    (K : V →ₗ[ℝ] V) (hK : SuperGrassmannianManifold.ParaComplexStructure K) (v : V) :
    SuperGrassmannianManifold.InTPlus K (NaturalGradientSubmersionFlow.paraProjectorPlus K v) := by
  dsimp [SuperGrassmannianManifold.InTPlus, NaturalGradientSubmersionFlow.paraProjectorPlus]
  rw [map_add, LinearMap.map_smul, LinearMap.map_smul, hK.involutive v, add_comm]

/-- For any para-complex structure `K`, the negative spectral projector `paraProjectorMinus K`
maps every vector `v` into the `-1` eigen-sheet `InTMinus K`. -/
theorem paraProjectorMinus_in_TMinus
    (K : V →ₗ[ℝ] V) (hK : SuperGrassmannianManifold.ParaComplexStructure K) (v : V) :
    SuperGrassmannianManifold.InTMinus K (NaturalGradientSubmersionFlow.paraProjectorMinus K v) := by
  dsimp [SuperGrassmannianManifold.InTMinus, NaturalGradientSubmersionFlow.paraProjectorMinus]
  rw [map_sub, LinearMap.map_smul, LinearMap.map_smul, hK.involutive v, neg_sub]

/-- Every image vector of the positive spectral projector `paraProjectorPlus K` is
metric-isotropic under a compatible `ParaKahlerStructure`. -/
theorem paraKahler_projPlus_isotropic_two_mul
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : SuperGrassmannianManifold.ParaComplexStructure K)
    (hPK : SuperGrassmannianManifold.ParaKahlerStructure g omega K) (v : V) :
    2 * g (NaturalGradientSubmersionFlow.paraProjectorPlus K v)
      (NaturalGradientSubmersionFlow.paraProjectorPlus K v) = 0 :=
  SuperGrassmannianManifold.tplus_isotropic_two_mul g omega K hK hPK
    (NaturalGradientSubmersionFlow.paraProjectorPlus K v)
    (paraProjectorPlus_in_TPlus K hK v)

/-- Every image vector of the negative spectral projector `paraProjectorMinus K` is
metric-isotropic under a compatible `ParaKahlerStructure`. -/
theorem paraKahler_projMinus_isotropic_two_mul
    {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}
    (hK : SuperGrassmannianManifold.ParaComplexStructure K)
    (hPK : SuperGrassmannianManifold.ParaKahlerStructure g omega K) (v : V) :
    2 * g (NaturalGradientSubmersionFlow.paraProjectorMinus K v)
      (NaturalGradientSubmersionFlow.paraProjectorMinus K v) = 0 :=
  SuperGrassmannianManifold.tminus_isotropic_two_mul g omega K hK hPK
    (NaturalGradientSubmersionFlow.paraProjectorMinus K v)
    (paraProjectorMinus_in_TMinus K hK v)

end ParaKahlerSubmersion

/-! ### 3. Archetype III: Holographic Colimit Projector Tower & Stagewise Submersion Split -/

/-- At each discrete stage `n : ℕ` of a module tower `T`, an idempotent `ProjectorFamily` `PF`
and its complementary projector `complementProjector PF n` form a canonical
`RiemannianSubmersion.SubmersionSplit (T n)`. -/
def colimitStageSubmersionSplit
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module ℝ (T n)]
    (PF : HolographicColimitContinuum.ProjectorFamily (R := ℝ) T) (n : ℕ) :
    RiemannianSubmersion.SubmersionSplit (T n) where
  projH := PF.P n
  projV := HolographicColimitContinuum.complementProjector PF n
  sum_id v := by
    dsimp [HolographicColimitContinuum.complementProjector]
    exact add_sub_cancel (PF.P n v) v
  idemH v := PF.idempotent n v
  idemV v := HolographicColimitContinuum.complement_idempotent PF n v
  orthoHV v := HolographicColimitContinuum.projector_annihilation PF n v
  orthoVH v := by
    dsimp [HolographicColimitContinuum.complementProjector]
    rw [PF.idempotent n v, sub_self]

/-- When `PF` intertwines the bonding maps of a `HolographicTower`, the horizontal
submersion projector `projH` commutes with multi-step bonding maps `iotaSeq`. -/
theorem colimitStageSubmersionSplit_projH_comm_iotaSeq
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module ℝ (T n)]
    (tower : HolographicColimitContinuum.HolographicTower (R := ℝ) T)
    (PF : HolographicColimitContinuum.ProjectorFamily (R := ℝ) T)
    (h_inter : HolographicColimitContinuum.IntertwinesProjector tower PF)
    (n m : ℕ) (x : T n) :
    (colimitStageSubmersionSplit PF (n + m)).projH
        (HolographicColimitContinuum.iotaSeq tower n m x) =
      HolographicColimitContinuum.iotaSeq tower n m
        ((colimitStageSubmersionSplit PF n).projH x) := by
  have h_comm := HolographicColimitContinuum.projector_comm_iotaSeq tower PF h_inter n m
  exact congr_arg (fun f : T n →ₗ[ℝ] T (n + m) => f x) h_comm.symm

/-- When `PF` intertwines the bonding maps of a `HolographicTower`, the vertical
submersion projector `projV` commutes with multi-step bonding maps `iotaSeq`. -/
theorem colimitStageSubmersionSplit_projV_comm_iotaSeq
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module ℝ (T n)]
    (tower : HolographicColimitContinuum.HolographicTower (R := ℝ) T)
    (PF : HolographicColimitContinuum.ProjectorFamily (R := ℝ) T)
    (h_inter : HolographicColimitContinuum.IntertwinesProjector tower PF)
    (n m : ℕ) (x : T n) :
    (colimitStageSubmersionSplit PF (n + m)).projV
        (HolographicColimitContinuum.iotaSeq tower n m x) =
      HolographicColimitContinuum.iotaSeq tower n m
        ((colimitStageSubmersionSplit PF n).projV x) := by
  have h_comm := HolographicColimitContinuum.complement_intertwines_iotaSeq tower PF h_inter n m
  exact congr_arg (fun f : T n →ₗ[ℝ] T (n + m) => f x) h_comm.symm

/-! ### 4. Archetype IV: Chentsov Congruent Partition Functoriality -/

/-- Pushing tangent vectors forward along the identity congruent Markov kernel preserves
the Fisher information metric identically. -/
theorem chentsov_id_fisher_invariance {α : Type*} [Fintype α] [DecidableEq α]
    (P : ChentsovMetricInvariance.ProbInterior α) (u v : α → ℝ) :
    ChentsovMetricInvariance.fisherMetric P
      (ChentsovMetricInvariance.pushforwardTangentVec
        (ChentsovMetricInvariance.idCongruentMarkovKernel α).kernel u)
      (ChentsovMetricInvariance.pushforwardTangentVec
        (ChentsovMetricInvariance.idCongruentMarkovKernel α).kernel v) =
    ChentsovMetricInvariance.fisherMetric P u v := by
  rw [ChentsovMetricInvariance.pushforwardTangentVec_id,
      ChentsovMetricInvariance.pushforwardTangentVec_id]

/-- Under any `CongruentPartitionEmbedding`, the pushed-forward Fisher quadratic form is
non-negative and equals the base Fisher quadratic energy. -/
theorem chentsov_partition_quadratic_energy_nonneg
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (E : ChentsovMetricInvariance.CongruentPartitionEmbedding α β)
    (P : ChentsovMetricInvariance.ProbInterior α) (u : α → ℝ) :
    0 ≤ ChentsovMetricInvariance.fisherMetric
      (ChentsovMetricInvariance.congruentPushforwardInterior
        (ChentsovMetricInvariance.partitionEmbeddingToKernel E) P
        (ChentsovMetricInvariance.partitionEmbedding_weight_pos E))
      (ChentsovMetricInvariance.pushforwardTangentVec
        (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel u)
      (ChentsovMetricInvariance.pushforwardTangentVec
        (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel u) := by
  rw [ChentsovMetricInvariance.chentsov_partition_embedding_fisher_invariance E P u u]
  exact ChentsovMetricInvariance.fisherMetric_nonneg P u

/-- Pushing the zero tangent perturbation forward along a `CongruentPartitionEmbedding`
yields zero Fisher quadratic energy on the target simplex interior. -/
theorem chentsov_partition_preserves_zero_tangent
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (E : ChentsovMetricInvariance.CongruentPartitionEmbedding α β)
    (P : ChentsovMetricInvariance.ProbInterior α) :
    ChentsovMetricInvariance.fisherMetric
      (ChentsovMetricInvariance.congruentPushforwardInterior
        (ChentsovMetricInvariance.partitionEmbeddingToKernel E) P
        (ChentsovMetricInvariance.partitionEmbedding_weight_pos E))
      (ChentsovMetricInvariance.pushforwardTangentVec
        (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel (fun _ => 0))
      (ChentsovMetricInvariance.pushforwardTangentVec
        (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel (fun _ => 0)) = 0 := by
  rw [ChentsovMetricInvariance.chentsov_partition_embedding_fisher_invariance E P (fun _ => 0) (fun _ => 0)]
  exact ChentsovMetricInvariance.fisherMetric_zero_left P (fun _ => 0)

/-! ### 5. Archetype V: Submersion Fiber Collapse & Geodesic Apex Optimality -/

/-- When vertical drift is pinned (`projV velocity = 0`), the joint submersion-plus-Chentsov
quadratic energy reduces to the horizontal base energy plus the base simplex Fisher metric. -/
theorem pinned_submersion_matches_chentsov_invariance
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (sys : NaturalGradientSubmersionFlow.NaturalGradientSubmersionSystem V)
    (velocity : V) (h_pinned : sys.split.projV velocity = 0)
    (E : ChentsovMetricInvariance.CongruentPartitionEmbedding α β)
    (P : ChentsovMetricInvariance.ProbInterior α) (u : α → ℝ) :
    sys.g velocity velocity +
      ChentsovMetricInvariance.fisherMetric
        (ChentsovMetricInvariance.congruentPushforwardInterior
          (ChentsovMetricInvariance.partitionEmbeddingToKernel E) P
          (ChentsovMetricInvariance.partitionEmbedding_weight_pos E))
        (ChentsovMetricInvariance.pushforwardTangentVec
          (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel u)
        (ChentsovMetricInvariance.pushforwardTangentVec
          (ChentsovMetricInvariance.partitionEmbeddingToKernel E).kernel u) =
    sys.g (sys.split.projH velocity) (sys.split.projH velocity) +
      ChentsovMetricInvariance.fisherMetric P u u := by
  rw [NaturalGradientSubmersionFlow.kinetic_energy_fiber_collapse sys velocity h_pinned]
  rw [ChentsovMetricInvariance.chentsov_partition_embedding_fisher_invariance E P u u]

/-- For positive curvature penalty `K > 0`, the critical radius `r* = C / (2K)` is simultaneously
a stationary point of `apexGradient` and a global maximizer attaining `invariantApex C K`. -/
theorem apex_stationary_and_maximal (C K r : ℝ) (hK : 0 < K) :
    NaturalGradientSubmersionFlow.apexGradient C K
        (NaturalGradientSubmersionFlow.criticalRadius C K) = 0 ∧
      NaturalGradientSubmersionFlow.apexObjective C K r ≤
        NaturalGradientSubmersionFlow.invariantApex C K :=
  ⟨NaturalGradientSubmersionFlow.apexGradient_zero_at_criticalRadius C K (ne_of_gt hK),
   NaturalGradientSubmersionFlow.apexObjective_le_invariantApex C K r hK⟩

end InfoGeometry.Canonical.GrandEpistemicGeometricSynthesis
