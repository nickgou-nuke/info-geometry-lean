import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylDiagonalAction

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

variable {State W : Type*} [Fintype State] [Nonempty State] [Group W]

theorem inverse_diagonal_energy_invariant
    (D : WeylEquivariantEnsembleDatum (State := State) (W := W))
    (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realPairingEnergy D.base
        (parameterLeftAction (D := D) w⁻¹ beta) (w⁻¹ • m) =
      realPairingEnergy D.base beta m := by
  exact energy_diagonal_invariant (D := D) w⁻¹ beta m

theorem inverse_diagonal_weight_invariant
    (D : WeylEquivariantEnsembleDatum (State := State) (W := W))
    (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realGibbsWeight D.base
        (parameterLeftAction (D := D) w⁻¹ beta) (w⁻¹ • m) =
      realGibbsWeight D.base beta m := by
  exact probability_diagonal_invariant (D := D) w⁻¹ beta m

end InfoGeometry.Lie.CanonicalZornG2CartanWeylDiagonalAction
