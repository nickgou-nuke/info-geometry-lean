import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopHomotopyQuotientIdentity
import InfoGeometry.Topology.SymbolicLatentBasedLoopConcatenationQuotient

namespace InfoGeometry.Topology

/-!
# Associativity of representative-based based-loop quotient concatenation

The operation is defined using `Quotient.out`, so associativity is not
definitional.  We transport the selected representatives back to the
canonical concatenations by quotient exactness, then use the explicit
associativity reparametrisation at path level.
-/

theorem basedLoopHomotopyQuotientConcatenation_eq_mk_representatives
    {X : Type} [TopologicalSpace X] {x : X}
    (q₀ q₁ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    basedLoopHomotopyQuotientConcatenation q₀ q₁ =
      basedLoopHomotopyQuotient_mk
        (canonicalSymbolicLatentBasedLoopConcatenation
          (basedLoopHomotopyQuotientRepresentativeLoop q₀)
          (basedLoopHomotopyQuotientRepresentativeLoop q₁)) := by
  apply Subtype.ext
  rfl

theorem basedLoopHomotopyQuotientConcatenation_associative
    {X : Type} [TopologicalSpace X] {x : X}
    (q₀ q₁ q₂ : SymbolicLatentBasedLoopHomotopyQuotient x) :
    basedLoopHomotopyQuotientConcatenation
        (basedLoopHomotopyQuotientConcatenation q₀ q₁) q₂ =
      basedLoopHomotopyQuotientConcatenation q₀
        (basedLoopHomotopyQuotientConcatenation q₁ q₂) := by
  let γ₀ := basedLoopHomotopyQuotientRepresentativeLoop q₀
  let γ₁ := basedLoopHomotopyQuotientRepresentativeLoop q₁
  let γ₂ := basedLoopHomotopyQuotientRepresentativeLoop q₂
  have h₀₁ : SymbolicLatentPathHomotopic
      (basedLoopHomotopyQuotientRepresentativeLoop
        (basedLoopHomotopyQuotientConcatenation q₀ q₁)).1
      (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1 := by
    have hq : symbolicLatentPathHomotopyQuotientMap
        (basedLoopHomotopyQuotientRepresentative
          (basedLoopHomotopyQuotientConcatenation q₀ q₁)) =
        symbolicLatentPathHomotopyQuotientMap
          (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1 := by
      exact (basedLoopHomotopyQuotientRepresentative_quotient_eq
        (basedLoopHomotopyQuotientConcatenation q₀ q₁)).trans (by
          simpa using congrArg Subtype.val
            (basedLoopHomotopyQuotientConcatenation_eq_mk_representatives q₀ q₁))
    exact Quotient.exact hq
  have h₁₂ : SymbolicLatentPathHomotopic
      (basedLoopHomotopyQuotientRepresentativeLoop
        (basedLoopHomotopyQuotientConcatenation q₁ q₂)).1
      (canonicalSymbolicLatentBasedLoopConcatenation γ₁ γ₂).1 := by
    have hq : symbolicLatentPathHomotopyQuotientMap
        (basedLoopHomotopyQuotientRepresentative
          (basedLoopHomotopyQuotientConcatenation q₁ q₂)) =
        symbolicLatentPathHomotopyQuotientMap
          (canonicalSymbolicLatentBasedLoopConcatenation γ₁ γ₂).1 := by
      exact (basedLoopHomotopyQuotientRepresentative_quotient_eq
        (basedLoopHomotopyQuotientConcatenation q₁ q₂)).trans (by
          simpa using congrArg Subtype.val
            (basedLoopHomotopyQuotientConcatenation_eq_mk_representatives q₁ q₂))
    exact Quotient.exact hq
  have hleft : SymbolicLatentPathHomotopic
      (canonicalSymbolicLatentBasedLoopConcatenation
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotientConcatenation q₀ q₁)) γ₂).1
      (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
    exact concatenatedSymbolicPathHomotopic_of_homotopies
      ((basedLoopHomotopyQuotientRepresentativeLoop
        (basedLoopHomotopyQuotientConcatenation q₀ q₁)).2.2.trans γ₂.2.1.symm)
      ((canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).2.2.trans
        γ₂.2.1.symm)
      h₀₁.some (SymbolicLatentPathHomotopic.refl γ₂.1).some
  have hright : SymbolicLatentPathHomotopic
      (canonicalSymbolicLatentBasedLoopConcatenation γ₀
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotientConcatenation q₁ q₂))).1
      (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
    exact concatenatedSymbolicPathHomotopic_of_homotopies
      (γ₀.2.2.trans
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotientConcatenation q₁ q₂)).2.1.symm)
      (γ₀.2.2.trans
        (canonicalSymbolicLatentBasedLoopConcatenation γ₁ γ₂).2.1.symm)
      (SymbolicLatentPathHomotopic.refl γ₀.1).some h₁₂.some
  apply Subtype.ext
  rw [basedLoopHomotopyQuotientConcatenation_eq_mk_representatives,
    basedLoopHomotopyQuotientConcatenation_eq_mk_representatives]
  have hleftQ : symbolicLatentPathHomotopyQuotientMap
      (canonicalSymbolicLatentBasedLoopConcatenation
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotientConcatenation q₀ q₁)) γ₂).1 =
      symbolicLatentPathHomotopyQuotientMap
        (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
    apply Quotient.sound
    exact hleft
  have hrightQ : symbolicLatentPathHomotopyQuotientMap
      (canonicalSymbolicLatentBasedLoopConcatenation γ₀
        (basedLoopHomotopyQuotientRepresentativeLoop
          (basedLoopHomotopyQuotientConcatenation q₁ q₂))).1 =
      symbolicLatentPathHomotopyQuotientMap
        (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
    apply Quotient.sound
    exact hright
  exact (hleftQ.trans
    (basedLoopConcatenation_associative_quotient_readout γ₀ γ₁ γ₂).symm).trans
    hrightQ.symm

end InfoGeometry.Topology
