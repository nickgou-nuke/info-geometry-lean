/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockInfinityPairing
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Real Hilbert completion of the existing algebraic Fock tower

The positive native pairing installs a metric on the existing root FockInfinity.
All named metric instances are local here. The only completed carrier is its
Mathlib uniform completion. Individual stage ranges need not be dense; their
union is dense. No completed creation/contraction operator is asserted.
-/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- The actual descended pairing satisfies the native positive inner-product core. -/
local instance fockInfinityInnerProductCore : InnerProductSpace.Core ℝ FockInfinity where
  inner := fun x y => fockInfinityPairing x y
  conj_inner_symm := by
    intro x y
    simpa using fockInfinityPairing_symm y x
  re_inner_nonneg := fockInfinityPairing_self_nonneg
  add_left := by
    intro x y z
    exact LinearMap.congr_fun (fockInfinityPairing.map_add x y) z
  smul_left := by
    intro x y r
    change fockInfinityPairing (r • x) y = r * fockInfinityPairing x y
    exact LinearMap.congr_fun (fockInfinityPairing.map_smul r x) y
  definite := by
    intro x hx
    exact (fockInfinityPairing_self_eq_zero x).mp hx


/-- Named pre-core uses exactly the same pairing as the definite core. -/
local instance fockInfinityPreInnerProductCore : PreInnerProductSpace.Core ℝ FockInfinity :=
  fockInfinityInnerProductCore.toCore

/-- The norm is derived from the proved positive definite pairing. -/
local instance fockInfinityNormedAddCommGroup : NormedAddCommGroup FockInfinity :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

/-- The real inner-product structure on the original algebraic direct limit. -/
local instance fockInfinityInnerProductSpace : InnerProductSpace ℝ FockInfinity :=
  InnerProductSpace.ofCore fockInfinityInnerProductCore.toCore

/-- The constructed inner product supplies the normed real scalar action. -/
local instance fockInfinityNormedSpace : NormedSpace ℝ FockInfinity :=
  fockInfinityInnerProductSpace.toNormedSpace

/-- Fixed scalar multiplication is uniformly continuous by its actual norm bound. -/
local instance fockInfinityUniformContinuousConstSMul :
    UniformContinuousConstSMul ℝ FockInfinity where
  uniformContinuous_const_smul r :=
    (lipschitzWith_smul (β := FockInfinity) r).uniformContinuous

/-- The installed inner product is the descended pairing, definitionally. -/
theorem fockInfinity_inner_eq (x y : FockInfinity) :
    inner ℝ x y = fockInfinityPairing x y := rfl

/-- The native finite-stage injection, with its derived isometry property. -/
def fockStageToInfinityIsometry (n : ℕ) : FockStage n →ₗᵢ[ℝ] FockInfinity :=
  (DirectLimit.Module.of ℝ ℕ FockStage (fun i j h => fockStageMap i j h) n).isometryOfInner (by
      intro x y
      change fockInfinityPairing (fockToInfinity n x) (fockToInfinity n y) =
        inner ℝ x y
      exact fockInfinityPairing_same_stage n x y)

/-- The bundled isometry has the existing algebraic injection as its function. -/
theorem fockStageToInfinityIsometry_apply (n : ℕ) (x : FockStage n) :
    fockStageToInfinityIsometry n x = fockToInfinity n x := rfl

/-- Finite-stage norm preservation on the actual algebraic carrier. -/
theorem fockToInfinity_norm (n : ℕ) (x : FockStage n) :
    ‖fockToInfinity n x‖ = ‖x‖ :=
  (fockStageToInfinityIsometry n).norm_map x

/-- No finite vector is lost by the native injection. -/
theorem fockToInfinity_injective (n : ℕ) : Function.Injective (fockToInfinity n) :=
  (fockStageToInfinityIsometry n).injective

/-- The exact original transition relation survives metric installation. -/
theorem fockToInfinity_transition {m n : ℕ} (hmn : m ≤ n) (x : FockStage m) :
    fockToInfinity n (fockStageMap m n hmn x) = fockToInfinity m x :=
  DirectLimit.Module.of_f

/-- Only the uniform completion of the original algebraic Fock carrier. -/
abbrev RealFockCompletion := UniformSpace.Completion FockInfinity

/-- Completeness is inherited from Mathlib's uniform completion. -/
theorem realFockCompletion_complete : CompleteSpace RealFockCompletion := inferInstance

/-- Compose the actual stage inclusion with Mathlib's canonical completion isometry. -/
def fockStageToCompletion (n : ℕ) : FockStage n →ₗᵢ[ℝ] RealFockCompletion :=
  (UniformSpace.Completion.toComplₗᵢ : FockInfinity →ₗᵢ[ℝ] RealFockCompletion).comp
    (fockStageToInfinityIsometry n)

/-- Completed stage readback uses the same finite representative. -/
theorem fockStageToCompletion_apply (n : ℕ) (x : FockStage n) :
    fockStageToCompletion n x = (fockToInfinity n x : RealFockCompletion) := rfl

/-- Completed inclusions preserve the actual finite real metric. -/
theorem fockStageToCompletion_inner (n : ℕ) (x y : FockStage n) :
    inner ℝ (fockStageToCompletion n x) (fockStageToCompletion n y) = inner ℝ x y :=
  (fockStageToCompletion n).inner_map_map x y

/-- Each finite-stage inclusion is an isometric embedding in the completion. -/
theorem fockStageToCompletion_norm (n : ℕ) (x : FockStage n) :
    ‖fockStageToCompletion n x‖ = ‖x‖ := (fockStageToCompletion n).norm_map x

/-- The completed inclusions retain the actual tower transition maps. -/
theorem fockStageToCompletion_transition {m n : ℕ} (hmn : m ≤ n) (x : FockStage m) :
    fockStageToCompletion n (fockStageMap m n hmn x) = fockStageToCompletion m x := by
  rw [fockStageToCompletion_apply, fockStageToCompletion_apply,
    fockToInfinity_transition hmn]

/-- The algebraic colimit is dense in its actual completion. -/
theorem fockInfinity_denseRange_completion :
    DenseRange (fun x : FockInfinity => (x : RealFockCompletion)) :=
  UniformSpace.Completion.denseRange_coe

/-- Finite-stage images jointly form a dense subset of the real Fock completion. -/
theorem dense_iUnion_range_fockStageToCompletion :
    Dense (⋃ n : ℕ, Set.range (fockStageToCompletion n)) := by
  apply fockInfinity_denseRange_completion.mono
  rintro y ⟨z, rfl⟩
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) z
  have hx' : z = fockToInfinity n x := hx
  refine Set.mem_iUnion.mpr ⟨n, x, ?_⟩
  rw [fockStageToCompletion_apply, hx']

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
