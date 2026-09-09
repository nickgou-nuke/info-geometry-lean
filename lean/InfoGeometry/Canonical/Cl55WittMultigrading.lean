import InfoGeometry.Canonical.Cl55WittWeightReadout
import Mathlib.Data.ZMod.Basic

/-! The intrinsic `ℤ⁵` weight readout and its degree/parity coarsenings for the
concrete five-mode Witt--CAR matrix carrier.  This is a readout of the
existing operators, not an identification with a separately named Lie
algebra. -/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittMultigrading

open scoped BigOperators
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting

abbrev WittWeight := Fin 5 → ℤ

def cartanAdjoint (k : Fin 5) : MatStage 5 →ₗ[ℝ] MatStage 5 where
  toFun X := bracket (E k k) X
  map_add' X Y := bracket_add_right (E k k) X Y
  map_smul' c X := bracket_smul_right c (E k k) X

@[simp] theorem cartanAdjoint_apply (k : Fin 5) (X : MatStage 5) :
    cartanAdjoint k X = bracket (E k k) X := rfl

theorem cartanAdjoint_bracket (k : Fin 5) (X Y : MatStage 5) :
    cartanAdjoint k (bracket X Y) =
      bracket (cartanAdjoint k X) Y + bracket X (cartanAdjoint k Y) := by
  change bracket (E k k) (bracket X Y) =
    bracket (bracket (E k k) X) Y + bracket X (bracket (E k k) Y)
  simp only [bracket]
  noncomm_ring

def weightSpace (μ : WittWeight) : Submodule ℝ (MatStage 5) :=
  ⨅ k, LinearMap.ker
    (cartanAdjoint k - (μ k : ℝ) • (LinearMap.id : MatStage 5 →ₗ[ℝ] MatStage 5))

theorem mem_weightSpace_iff {μ : WittWeight} {X : MatStage 5} :
    X ∈ weightSpace μ ↔ ∀ k, cartanAdjoint k X = (μ k : ℝ) • X := by
  simp [weightSpace, LinearMap.mem_ker, sub_eq_zero]

theorem weightSpace_bracket_mem {μ ν : WittWeight} {X Y : MatStage 5}
    (hX : X ∈ weightSpace μ) (hY : Y ∈ weightSpace ν) :
    bracket X Y ∈ weightSpace (μ + ν) := by
  rw [mem_weightSpace_iff] at hX hY ⊢
  intro k
  rw [cartanAdjoint_bracket, hX k, hY k, bracket_smul_left, bracket_smul_right]
  simp only [Pi.add_apply, Int.cast_add, add_smul]

def totalDegree : WittWeight →+ ℤ where
  toFun μ := ∑ k, μ k
  map_zero' := by simp
  map_add' μ ν := by simp [Finset.sum_add_distrib]

def weightParity (μ : WittWeight) : ZMod 2 := (totalDegree μ : ZMod 2)

@[simp] theorem weightParity_add (μ ν : WittWeight) :
    weightParity (μ + ν) = weightParity μ + weightParity ν := by
  simp [weightParity]

theorem creation_mem_weightSpace (i : Fin 5) :
    creation i ∈ weightSpace (creationWeight i) := by
  rw [mem_weightSpace_iff]
  exact fun k => diagonal_creation_weight k i

theorem annihilation_mem_weightSpace (i : Fin 5) :
    annihilation i ∈ weightSpace (annihilationWeight i) := by
  rw [mem_weightSpace_iff]
  exact fun k => diagonal_annihilation_weight k i

theorem totalDegree_creationWeight (i : Fin 5) :
    totalDegree (creationWeight i) = 1 := by
  simp [totalDegree, creationWeight]

theorem totalDegree_annihilationWeight (i : Fin 5) :
    totalDegree (annihilationWeight i) = -1 := by
  simp [totalDegree, annihilationWeight]

theorem cl55_witt_multigrading_packet (i : Fin 5) :
    creation i ∈ weightSpace (creationWeight i) ∧
    annihilation i ∈ weightSpace (annihilationWeight i) ∧
    totalDegree (creationWeight i) = 1 ∧
    totalDegree (annihilationWeight i) = -1 := by
  exact ⟨creation_mem_weightSpace i, annihilation_mem_weightSpace i,
    totalDegree_creationWeight i, totalDegree_annihilationWeight i⟩

end InfoGeometry.Canonical.Cl55WittMultigrading
