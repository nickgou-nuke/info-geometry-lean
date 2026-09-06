import InfoGeometry.Canonical.CliffordCausalBridge
import InfoGeometry.Canonical.ModularEvolution

open CategoryTheory Limits

namespace InfoGeometry.Canonical

/--
  The discrete shift operator representing a single discrete unit
  of algorithmic "time" in the Clifford hierarchy.
-/
def discreteTimeShift : CausalSpacetime ℕ ⥤ CausalSpacetime ℕ where
  obj n := Nat.succ n
  map h := homOfLE (Nat.succ_le_succ (leOfHom h))

/--
  A structural declaration that the continuous modular flow `σ_t`
  perfectly interpolates the discrete temporal shifts of the Clifford hierarchy.
  
  In this compatibility class, we assert that the modular evolution evaluated 
  at discrete integer times generates exact lattice automorphisms of the 
  Universal Causal Future.
-/
class DiscreteContinuousTimeCompatibility
    (F : CausalFunctor ℕ) [HasColimit F]
    (σ : ModularAutomorphismGroup F) : Prop where
  /-- At integer times, the continuous flow generates an exact discrete 
      automorphism of the algebra. -/
  integer_flow_compatibility : 
    ∀ (n : ℕ), ∃ (iso : UniversalCausalFuture F ≅ UniversalCausalFuture F),
      (σ (Multiplicative.ofAdd (n : ℝ))).hom = iso.hom

end InfoGeometry.Canonical
