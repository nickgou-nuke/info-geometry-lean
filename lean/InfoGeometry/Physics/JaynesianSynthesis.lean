import InfoGeometry.Inference.RegularizedPoissonDeviance
import InfoGeometry.Physics.JaynesMaxEntKMSBridge
import InfoGeometry.Physics.ThermodynamicAlgebraicCenter
import InfoGeometry.Physics.TomitaTakesakiModularFlow

namespace InfoGeometry.Physics.JaynesianSynthesis

open InfoGeometry.Physics
open InfoGeometry.Inference

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [Ring A]

/--
Jaynesian synthesis hub.

This is a thin, theorem-honest packaging layer that re-exports already-checked
facts from the Jaynes/KMS, Poisson-deviance, thermodynamic-center, and Tomita
branches without introducing new mathematics.
-/
theorem jaynesian_synthesis_hub
    (rho rhoInv X Y : TraceOperatorSpace n)
    (hInv : rhoInv * rho = 1)
    (x ε : ℝ)
    (z1 z2 : A)
    (hz1 : z1 ∈ ThermodynamicCenter A)
    (hz2 : z2 ∈ ThermodynamicCenter A)
    (J_op : TomitaConjugationData A)
    (S : Set A)
    (hT : TomitaCommutantData A J_op S)
    (F : ModularFlowData A)
    (t s : ℝ)
    (a : A) :
    jaynesGibbsState (rho := rho) (X * modularImaginaryFlow rho rhoInv Y) =
        jaynesGibbsState (rho := rho) (Y * X) ∧
    poissonDeviance x x = 0 ∧
    poissonDevianceGibbsFactor x x ε = 1 ∧
    (1 : A) ∈ ThermodynamicCenter A ∧
    z1 * z2 ∈ ThermodynamicCenter A ∧
    (∀ S : Set A, S ⊆ Commutant A (Commutant A S)) ∧
    ThermodynamicCenter A = Commutant A (Set.univ : Set A) ∧
    tomitaImage A J_op S = Commutant A S ∧
    Function.Bijective (F.sigma t) ∧
    F.sigma (t + s) a = F.sigma t (F.sigma s a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jaynesian_synthesis_kms rho rhoInv X Y hInv
  · exact poissonDeviance_self_eq_zero x
  · exact poissonDevianceGibbsFactor_self_eq_one x ε
  · exact center_contains_vacuum_background A
  · exact center_closed_under_multiplication A z1 z2 hz1 hz2
  · exact double_commutant_emergence A
  · exact center_is_global_commutant A
  · exact tomita_image_eq_commutant A J_op S hT
  · exact modular_flow_is_bijective A F t
  · exact modular_flow_group_law A F t s a

end InfoGeometry.Physics.JaynesianSynthesis
