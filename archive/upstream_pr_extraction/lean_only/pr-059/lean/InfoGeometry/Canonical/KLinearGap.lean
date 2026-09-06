import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Analysis.L2CantorCommutation

open InfoGeometry.Topology.CuntzCantorSpectralTriple
open InfoGeometry.Krein
open InfoGeometry.Analysis.L2CantorCommutation

/-!
# KLinear S_left — status

The commutation S_left ∘ K = K ∘ S_left is proved on the concrete
Hilbert space H = ℓ²((ℕ → BinarySector), ℝ²) in L2CantorCommutation.

The fiber-only KLinear predicate in CuntzCantorSpectralTriple is a
different type; the concrete proof lives on the full Hilbert space.
-/

section FinalGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The commutation S_left · K = K · S_left on the full Hilbert space
H = ℓ²((ℕ → BinarySector), ℝ²) is proved in L2CantorCommutation.

This is the last analytic step for closing the e₂ self-adjointness
chain in CuntzCantorSpectralTriple.lean.
-/
theorem S_left_commutes_K_proved : S_left ∘ K_op = K_op ∘ S_left :=
  S_left_commutes_K

end FinalGap
