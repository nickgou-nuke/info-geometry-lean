import InfoGeometry.OperatorAlgebra.CrossoverResidue
import InfoGeometry.Canonical.LogCftMonodromyBridge

namespace InfoGeometry.Integration.AeonCrossoverChiralMonodromyBridge

open InfoGeometry.OperatorAlgebra.CrossoverResidue
open InfoGeometry.Canonical.LogCftMonodromyBridge
open InfoGeometry.OperatorAlgebra.ConformalCrossover

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {C : ConformalCrossoverDatum V}
variable (D : HawkingPointDivisor C)

/--
The Aeonic Conformal Crossover Bridge.
The Aeon crossover boundary flips the chiral charge,
allowing the nilpotent monodromy to reset/transition to the new aeon.
-/
theorem aeon_crossover_chiral_monodromy_bridge :
    D.crossover.chiralCharge = -D.chiralCharge ∧
    hadjiivanovMonodromy (D.crossover.chiralCharge : ℂ) =
      lcftPhase (D.crossover.chiralCharge : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        InfoGeometry.Clifford.LogCftMonodromy.monodromyNilpotentPart (D.crossover.chiralCharge : ℂ) := by
  refine ⟨?_, ?_⟩
  · exact D.chiralCharge_crossover
  · exact monodromy_decomposition (D.crossover.chiralCharge : ℂ)

end InfoGeometry.Integration.AeonCrossoverChiralMonodromyBridge
