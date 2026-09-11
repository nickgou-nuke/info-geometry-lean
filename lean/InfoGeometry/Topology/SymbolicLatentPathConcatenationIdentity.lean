import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction
import InfoGeometry.Topology.SymbolicLatentPathReparametrization
import InfoGeometry.Topology.SymbolicLatentPath
import InfoGeometry.Topology.SymbolicLatentLoop
import InfoGeometry.Topology.SymbolicLatentPathHomotopyComposition

namespace InfoGeometry.Topology

/-!
# Constant-path identity witnesses for canonical concatenation

The canonical midpoint gluing with a constant path is an explicit endpoint
preserving reparametrization.  This is the path-level input for quotient
identity laws.
-/

noncomputable def leftConstantConcatenationReparametrization :
    SymbolicLatentPathReparametrization :=
  ⟨symbolicConcatenationSecondParameter, by
    constructor
    · apply Subtype.ext
      norm_num [symbolicConcatenationSecondParameter]
    · apply Subtype.ext
      norm_num [symbolicConcatenationSecondParameter]⟩

theorem canonicalSymbolicConcatenation_constant_left_eq_reparametrized
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentPath X) (hstart : γ.start = x) :
    canonicalSymbolicConcatenation
        (show (constantSymbolicLatentPath x).finish = γ.start from hstart.symm)
      = reparametrizeSymbolicLatentPath
          leftConstantConcatenationReparametrization γ := by
  ext t
  change Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
      ((constantSymbolicLatentPath x).comp symbolicConcatenationFirstParameter)
      (γ.comp symbolicConcatenationSecondParameter) t =
    γ (symbolicConcatenationSecondParameter t)
  by_cases ht : t ∈ Set.Iic symbolicConcatenationMidpoint
  · have hp := Set.piecewise_eq_of_mem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := (constantSymbolicLatentPath x).comp symbolicConcatenationFirstParameter)
      (g := γ.comp symbolicConcatenationSecondParameter) ht
    rw [hp]
    have hzero : symbolicConcatenationSecondParameter t =
        (0 : SymbolicPathDomain) := by
      apply Subtype.ext
      rw [symbolicConcatenationSecondParameter]
      change max (2 * (t : ℝ) - 1) 0 = 0
      rw [max_eq_right]
      have htle : (t : ℝ) ≤ (1 : ℝ) / 2 := by
        exact ht
      linarith
    rw [hzero]
    exact hstart.symm
  · have hp := Set.piecewise_eq_of_notMem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := (constantSymbolicLatentPath x).comp symbolicConcatenationFirstParameter)
      (g := γ.comp symbolicConcatenationSecondParameter) ht
    rw [hp]
    rfl

theorem canonicalSymbolicConcatenation_constant_left_homotopic
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentPath X) (hstart : γ.start = x) :
    SymbolicLatentPathHomotopic
      (canonicalSymbolicConcatenation
        (show (constantSymbolicLatentPath x).finish = γ.start from hstart.symm))
      γ := by
  rw [canonicalSymbolicConcatenation_constant_left_eq_reparametrized γ hstart]
  exact SymbolicLatentPathHomotopic.symm
    (reparametrizeSymbolicLatentPath_homotopic
      leftConstantConcatenationReparametrization γ)

noncomputable def rightConstantConcatenationReparametrization :
    SymbolicLatentPathReparametrization :=
  ⟨symbolicConcatenationFirstParameter, by
    constructor
    · apply Subtype.ext
      norm_num [symbolicConcatenationFirstParameter]
    · apply Subtype.ext
      norm_num [symbolicConcatenationFirstParameter]⟩

theorem canonicalSymbolicConcatenation_constant_right_eq_reparametrized
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentPath X) (hfinish : γ.finish = x) :
    canonicalSymbolicConcatenation
        (show γ.finish = (constantSymbolicLatentPath x).start from hfinish)
      = reparametrizeSymbolicLatentPath
          rightConstantConcatenationReparametrization γ := by
  ext t
  change Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
      (γ.comp symbolicConcatenationFirstParameter)
      ((constantSymbolicLatentPath x).comp symbolicConcatenationSecondParameter) t =
    γ (symbolicConcatenationFirstParameter t)
  by_cases ht : t ∈ Set.Iic symbolicConcatenationMidpoint
  · rw [Set.piecewise_eq_of_mem
      (Set.Iic symbolicConcatenationMidpoint) _ _ ht]
    rfl
  · rw [Set.piecewise_eq_of_notMem
      (Set.Iic symbolicConcatenationMidpoint) _ _ ht]
    have hone : symbolicConcatenationFirstParameter t =
        (1 : SymbolicPathDomain) := by
      apply Subtype.ext
      rw [symbolicConcatenationFirstParameter]
      change min (2 * (t : ℝ)) 1 = 1
      rw [min_eq_right]
      have htle : (1 : ℝ) / 2 ≤ (t : ℝ) := by
        by_contra hlt
        have hmem : (t : ℝ) ≤ (1 : ℝ) / 2 := le_of_lt (lt_of_not_ge hlt)
        exact ht hmem
      linarith
    rw [hone]
    exact hfinish.symm

theorem canonicalSymbolicConcatenation_constant_right_homotopic
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentPath X) (hfinish : γ.finish = x) :
    SymbolicLatentPathHomotopic
      (canonicalSymbolicConcatenation
        (show γ.finish = (constantSymbolicLatentPath x).start from hfinish))
      γ := by
  rw [canonicalSymbolicConcatenation_constant_right_eq_reparametrized γ hfinish]
  exact SymbolicLatentPathHomotopic.symm
    (reparametrizeSymbolicLatentPath_homotopic
      rightConstantConcatenationReparametrization γ)

end InfoGeometry.Topology
