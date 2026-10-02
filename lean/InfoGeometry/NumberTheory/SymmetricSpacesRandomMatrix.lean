import InfoGeometry.Cartan.Involution
import InfoGeometry.Architecture.CartanLieBracket
import InfoGeometry.Core.SymmetricLieGeneric
import InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.NumberTheory.SymmetricSpacesRandomMatrix

open InfoGeometry.Cartan
open Filter Topology

section SymmetricPair

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

variable (σ : L →ₗ⁅ℝ⁆ L)

def fixedSpace : Submodule ℝ L :=
  Module.End.eigenspace σ.toLinearMap 1

def negatedSpace : Submodule ℝ L :=
  Module.End.eigenspace σ.toLinearMap (-1)

@[simp] theorem mem_fixedSpace (vector : L) :
    vector ∈ fixedSpace σ ↔ σ vector = vector := by
  simp [fixedSpace, Module.End.mem_eigenspace_iff]

@[simp] theorem mem_negatedSpace (vector : L) :
    vector ∈ negatedSpace σ ↔ σ vector = -vector := by
  simp [negatedSpace, Module.End.mem_eigenspace_iff]

theorem bracket_eigenvectors {first second : L} {firstValue secondValue : ℝ}
    (hfirst : σ first = firstValue • first)
    (hsecond : σ second = secondValue • second) :
    σ ⁅first, second⁆ = (firstValue * secondValue) • ⁅first, second⁆ := by
  rw [σ.map_lie, hfirst, hsecond, smul_lie, lie_smul, smul_smul]

theorem symmetric_pair_grading :
    InfoGeometry.Architecture.CartanGrading
      (fun first second : L => ⁅first, second⁆) (fixedSpace σ) (negatedSpace σ) := by
  constructor
  · intro first second hfirst hsecond
    simp only [mem_fixedSpace] at hfirst hsecond ⊢
    rw [σ.map_lie, hfirst, hsecond]
  · intro first second hfirst hsecond
    simp only [mem_fixedSpace, mem_negatedSpace] at hfirst hsecond ⊢
    rw [σ.map_lie, hfirst, hsecond, lie_neg]
  · intro first second hfirst hsecond
    simp only [mem_fixedSpace, mem_negatedSpace] at hfirst hsecond ⊢
    rw [σ.map_lie, hfirst, hsecond, neg_lie, lie_neg, neg_neg]

theorem involution_end (hinv : Function.Involutive σ) :
    IsCartanInvolution σ.toLinearMap := by
  ext vector
  exact hinv vector

theorem plus_fixed (hinv : Function.Involutive σ) (vector : L) :
    σ (Pplus σ.toLinearMap vector) = Pplus σ.toLinearMap vector := by
  simp only [Pplus_apply, map_smul, map_add]
  change (⅟(2 : ℝ)) • (σ vector + σ (σ vector)) =
    (⅟(2 : ℝ)) • (vector + σ vector)
  rw [hinv vector, add_comm]

theorem minus_negated (hinv : Function.Involutive σ) (vector : L) :
    σ (Pminus σ.toLinearMap vector) = -Pminus σ.toLinearMap vector := by
  simp only [Pminus_apply, map_smul, map_sub]
  change (⅟(2 : ℝ)) • (σ vector - σ (σ vector)) =
    -((⅟(2 : ℝ)) • (vector - σ vector))
  rw [hinv vector, ← smul_neg, neg_sub]

theorem decomposition_unique {vector fixed negated : L}
    (hfixed : σ fixed = fixed) (hnegated : σ negated = -negated)
    (hsum : vector = fixed + negated) :
    fixed = Pplus σ.toLinearMap vector ∧
      negated = Pminus σ.toLinearMap vector := by
  rw [hsum]
  simp only [Pplus_apply, Pminus_apply, LinearMap.map_add]
  rw [hfixed, hnegated]
  simp only [invOf_eq_inv]
  constructor <;> module

theorem symmetric_pair_decomposition (hinv : Function.Involutive σ) (vector : L) :
    ∃! parts : L × L,
      parts.1 ∈ fixedSpace σ ∧ parts.2 ∈ negatedSpace σ ∧
        vector = parts.1 + parts.2 := by
  refine ⟨(Pplus σ.toLinearMap vector, Pminus σ.toLinearMap vector), ?_, ?_⟩
  · exact ⟨(mem_fixedSpace σ _).mpr (plus_fixed σ hinv vector),
      (mem_negatedSpace σ _).mpr (minus_negated σ hinv vector),
      decompose σ.toLinearMap (involution_end σ hinv) vector⟩
  · intro parts hparts
    obtain ⟨hfirst, hsecond⟩ := decomposition_unique σ
      ((mem_fixedSpace σ _).mp hparts.1)
      ((mem_negatedSpace σ _).mp hparts.2.1) hparts.2.2
    exact Prod.ext hfirst hsecond

end SymmetricPair

section OwnerCompatibility

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

variable (symmetric : InfoGeometry.Core.Generic.SymmetricLieAlgebra ℝ L)

theorem fixedSpace_eq_generic :
    fixedSpace symmetric.θ.toLieHom = symmetric.𝔨 := by
  ext vector
  exact (mem_fixedSpace _ vector).trans (symmetric.mem_𝔨_iff vector).symm

theorem negatedSpace_eq_generic :
    negatedSpace symmetric.θ.toLieHom = symmetric.𝔭 := by
  ext vector
  exact (mem_negatedSpace _ vector).trans (symmetric.mem_𝔭_iff vector).symm

theorem symmetric_pair_isCompl :
    IsCompl (fixedSpace symmetric.θ.toLieHom) (negatedSpace symmetric.θ.toLieHom) := by
  rw [fixedSpace_eq_generic, negatedSpace_eq_generic]
  exact symmetric.isCompl_𝔨_𝔭

def symmetricPairLinearEquiv :
    L ≃ₗ[ℝ] fixedSpace symmetric.θ.toLieHom × negatedSpace symmetric.θ.toLieHom :=
  (Submodule.prodEquivOfIsCompl _ _ (symmetric_pair_isCompl symmetric)).symm

@[simp] theorem symmetricPairLinearEquiv_symm_apply
    (parts : fixedSpace symmetric.θ.toLieHom × negatedSpace symmetric.θ.toLieHom) :
    (symmetricPairLinearEquiv symmetric).symm parts = (parts.1 : L) + parts.2 := rfl

theorem symmetricPairLinearEquiv_apply (vector : L) :
    symmetricPairLinearEquiv symmetric vector =
      (⟨Pplus symmetric.θ.toLinearMap vector,
        (mem_fixedSpace _ _).mpr
          (plus_fixed _ symmetric.involution_apply vector)⟩,
       ⟨Pminus symmetric.θ.toLinearMap vector,
        (mem_negatedSpace _ _).mpr
          (minus_negated _ symmetric.involution_apply vector)⟩) := by
  apply (symmetricPairLinearEquiv symmetric).symm.injective
  rw [LinearEquiv.symm_apply_apply, symmetricPairLinearEquiv_symm_apply]
  exact decompose _ (involution_end _ symmetric.involution_apply) vector

end OwnerCompatibility

abbrev AZLabel := InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge.AZClass

def azLabelEquiv : AZLabel ≃ Fin 10 where
  toFun
    | .A => 0
    | .AIII => 1
    | .AI => 2
    | .BDI => 3
    | .D => 4
    | .DIII => 5
    | .AII => 6
    | .CII => 7
    | .C => 8
    | .CI => 9
  invFun index := ![.A, .AIII, .AI, .BDI, .D, .DIII, .AII, .CII, .C, .CI] index
  left_inv label := by cases label <;> rfl
  right_inv index := by fin_cases index <;> rfl

inductive DysonLabel
  | unitary
  | orthogonal
  | symplectic
  deriving DecidableEq, Fintype

inductive ArithmeticCompactGroupLabel
  | unitary
  | compactSymplectic
  | specialOrthogonalEven
  | specialOrthogonalOdd
  deriving DecidableEq, Fintype

theorem dyson_label_count : Fintype.card DysonLabel = 3 := by decide

theorem arithmetic_label_count : Fintype.card ArithmeticCompactGroupLabel = 4 := by decide

def PointwiseSpacingLimit (empirical : ℝ → ℝ → ℝ) (target : ℝ → ℝ) : Prop :=
  ∀ location, Tendsto (fun height => empirical height location) atTop (𝓝 (target location))

theorem spacing_limit_unique {empirical : ℝ → ℝ → ℝ} {first second : ℝ → ℝ}
    (hfirst : PointwiseSpacingLimit empirical first)
    (hsecond : PointwiseSpacingLimit empirical second) : first = second := by
  funext location
  exact tendsto_nhds_unique (hfirst location) (hsecond location)

theorem constant_spacing_limit_iff (constant target : ℝ → ℝ) :
    PointwiseSpacingLimit (fun _ => constant) target ↔ constant = target := by
  constructor
  · intro hlimit
    exact spacing_limit_unique (fun _ => tendsto_const_nhds) hlimit
  · rintro rfl
    intro location
    exact tendsto_const_nhds

theorem no_universal_spacing_limit (target : ℝ → ℝ) :
    ¬ ∀ empirical : ℝ → ℝ → ℝ, PointwiseSpacingLimit empirical target := by
  intro hall
  have hzero := (constant_spacing_limit_iff (fun _ => 0) target).mp (hall (fun _ _ => 0))
  have hone := (constant_spacing_limit_iff (fun _ => 1) target).mp (hall (fun _ _ => 1))
  have hcontradiction := congrFun (hzero.trans hone.symm) 0
  norm_num at hcontradiction

end InfoGeometry.NumberTheory.SymmetricSpacesRandomMatrix
