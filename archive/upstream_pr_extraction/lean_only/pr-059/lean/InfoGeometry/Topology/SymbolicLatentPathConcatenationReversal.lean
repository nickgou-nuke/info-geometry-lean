import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentPathReversal

namespace InfoGeometry.Topology

/-!
# Reversal of a canonical concatenation

The explicit midpoint gluing is compatible with reversal: reversing a glued
path agrees pointwise with gluing the reversed second path to the reversed
first path.  The midpoint is handled explicitly because the piecewise
definition uses the left branch there.
-/

theorem reverseSymbolicLatentPath_canonicalSymbolicConcatenation
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    let hend' : (reverseSymbolicLatentPath γ₁).finish =
        (reverseSymbolicLatentPath γ₀).start := by
      rw [reverseSymbolicLatentPath_finish,
        reverseSymbolicLatentPath_start]
      exact hend.symm
    reverseSymbolicLatentPath (canonicalSymbolicConcatenation hend) =
      canonicalSymbolicConcatenation hend' := by
  ext t
  change symbolicConcatenationFunction γ₀ γ₁
      (symbolicPathReversalParameter t) =
    symbolicConcatenationFunction
      (reverseSymbolicLatentPath γ₁)
      (reverseSymbolicLatentPath γ₀) t
  dsimp [symbolicConcatenationFunction]
  by_cases ht : (t : ℝ) ≤ (1 : ℝ) / 2
  · have hright : t ∈ Set.Iic symbolicConcatenationMidpoint := by
      change (t : ℝ) ≤ (1 : ℝ) / 2
      exact ht
    rw [Set.piecewise_eq_of_mem
      (s := Set.Iic symbolicConcatenationMidpoint) (f := _) (g := _) hright]
    by_cases hteq : (t : ℝ) = (1 : ℝ) / 2
    · have ht' : t = symbolicConcatenationMidpoint := by
        apply Subtype.ext
        exact hteq
      subst t
      rw [Set.piecewise_eq_of_mem
        (s := Set.Iic symbolicConcatenationMidpoint) (f := _) (g := _)]
      · change γ₀ (symbolicConcatenationFirstParameter
          (symbolicPathReversalParameter symbolicConcatenationMidpoint)) =
          γ₁ (symbolicPathReversalParameter
            (symbolicConcatenationFirstParameter symbolicConcatenationMidpoint))
        have hfirst : symbolicConcatenationFirstParameter
            symbolicConcatenationMidpoint = (1 : SymbolicPathDomain) := by
          apply Subtype.ext
          norm_num [symbolicConcatenationFirstParameter,
            symbolicConcatenationMidpoint]
        have hrev : symbolicPathReversalParameter
            symbolicConcatenationMidpoint = symbolicConcatenationMidpoint := by
          apply Subtype.ext
          norm_num [symbolicPathReversalParameter,
            symbolicConcatenationMidpoint]
        rw [hrev, hfirst, symbolicPathReversalParameter_one]
        change γ₀.finish = γ₁.start
        exact hend
      · change (symbolicPathReversalParameter symbolicConcatenationMidpoint : ℝ) ≤
          (symbolicConcatenationMidpoint : ℝ)
        norm_num [symbolicPathReversalParameter,
          symbolicConcatenationMidpoint]
    · have hlt : (t : ℝ) < (1 : ℝ) / 2 := lt_of_le_of_ne ht hteq
      have hleft : ¬ symbolicPathReversalParameter t ∈
          Set.Iic symbolicConcatenationMidpoint := by
        change ¬ (1 - (t : ℝ) ≤ (1 : ℝ) / 2)
        linarith
      rw [Set.piecewise_eq_of_notMem
        (s := Set.Iic symbolicConcatenationMidpoint) (f := _) (g := _) hleft]
      change γ₁ (symbolicConcatenationSecondParameter
          (symbolicPathReversalParameter t)) =
        γ₁ (symbolicPathReversalParameter
          (symbolicConcatenationFirstParameter t))
      congr 1
      apply Subtype.ext
      change max (2 * (1 - (t : ℝ)) - 1) 0 =
        1 - min (2 * (t : ℝ)) 1
      rw [max_eq_left (by linarith)]
      rw [min_eq_left (by linarith [t.property.2])]
      ring
  · have hright : ¬ t ∈ Set.Iic symbolicConcatenationMidpoint := by
      change ¬ (t : ℝ) ≤ (1 : ℝ) / 2
      exact ht
    rw [Set.piecewise_eq_of_notMem
      (s := Set.Iic symbolicConcatenationMidpoint) (f := _) (g := _) hright]
    have hgt : (1 : ℝ) / 2 < (t : ℝ) := lt_of_not_ge ht
    have hleft : symbolicPathReversalParameter t ∈
        Set.Iic symbolicConcatenationMidpoint := by
      change 1 - (t : ℝ) ≤ (1 : ℝ) / 2
      linarith
    rw [Set.piecewise_eq_of_mem
      (s := Set.Iic symbolicConcatenationMidpoint) (f := _) (g := _) hleft]
    change γ₀ (symbolicConcatenationFirstParameter
        (symbolicPathReversalParameter t)) =
      γ₀ (symbolicPathReversalParameter
        (symbolicConcatenationSecondParameter t))
    congr 1
    apply Subtype.ext
    change min (2 * (1 - (t : ℝ))) 1 =
      1 - max (2 * (t : ℝ) - 1) 0
    rw [min_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]
    ring

theorem reverseSymbolicLatentPath_canonicalSymbolicConcatenation_quotient
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    let hend' : (reverseSymbolicLatentPath γ₁).finish =
        (reverseSymbolicLatentPath γ₀).start := by
      rw [reverseSymbolicLatentPath_finish,
        reverseSymbolicLatentPath_start]
      exact hend.symm
    symbolicLatentPathHomotopyQuotientMap
        (reverseSymbolicLatentPath (canonicalSymbolicConcatenation hend)) =
      symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicConcatenation hend') := by
  exact congrArg symbolicLatentPathHomotopyQuotientMap
    (reverseSymbolicLatentPath_canonicalSymbolicConcatenation hend)

end InfoGeometry.Topology
