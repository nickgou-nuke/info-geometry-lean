import Mathlib
import InfoGeometry.Topology.SymbolicLatentBasedLoopConcatenationAssociativity
import InfoGeometry.Topology.SymbolicLatentPathConcatenationHomotopy
import InfoGeometry.Topology.SymbolicLatentPathConcatenationReparametrization
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient

namespace InfoGeometry.Topology

/-!
# Quotient readouts for based-loop concatenation

These lemmas establish the quotient-level congruence and associativity
readouts that follow from endpoint-preserving homotopies and the explicit
associativity reparametrization.  They deliberately stop short of declaring a
group operation on the quotient.
-/

theorem basedLoopConcatenation_quotient_congr
    {X : Type*} [TopologicalSpace X] {x : X}
    {γ₀ γ₀' γ₁ γ₁' : SymbolicLatentBasedLoopPath x}
    (H₀ : SymbolicLatentPathHomotopy γ₀.1 γ₀'.1)
    (H₁ : SymbolicLatentPathHomotopy γ₁.1 γ₁'.1) :
    symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁).1 =
      symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀' γ₁').1 := by
  apply Quotient.sound
  exact concatenatedSymbolicPathHomotopic_of_homotopies
    (γ₀.2.2.trans γ₁.2.1.symm)
    (γ₀'.2.2.trans γ₁'.2.1.symm)
    H₀ H₁

theorem basedLoopConcatenation_associative_quotient_readout
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ γ₂ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentPathHomotopyQuotientMap
        (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 =
      symbolicLatentPathHomotopyQuotientMap
        (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
  apply Quotient.sound
  have hrepr :=
    reparametrizeSymbolicLatentPath_homotopic
      associativityReparametrization
      (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1
  simpa [rightAssociativeBasedLoopConcatenation_eq_reparametrized_left
    γ₀ γ₁ γ₂] using hrepr.symm

end InfoGeometry.Topology
