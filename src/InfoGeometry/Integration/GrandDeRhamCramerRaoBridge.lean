import InfoGeometry.Integration.CramerRaoMaurerCartanBridge
import InfoGeometry.Capstone.GrandIdentityDeRhamModular
import InfoGeometry.Canonical.LogCftMonodromyBridge

namespace InfoGeometry.Integration.GrandDeRhamCramerRaoBridge

open InfoGeometry.Integration.CramerRaoMaurerCartanBridge
open InfoGeometry.Capstone.GrandIdentityDeRhamModular
open InfoGeometry.Canonical.LogCftMonodromyBridge

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem grand_de_rham_cramer_rao_bridge
    (v F dξ dθ : ℝ) (K : A) (u : Aˣ)
    (data : CramerRaoMaurerCartanData v F dξ dθ K u)
    (Q Kexp : ℝ → ℝ) (β : ℝ)
    (hB : DifferentiableAt ℝ (boltzmannEntropy Q) β)
    (hK : DifferentiableAt ℝ Kexp β)
    (hBoltzFlat : deriv (boltzmannEntropy Q) β = 0) :
    (v * F ≥ 1) ∧
    (deriv (vonNeumannEntropy Q Kexp) β = Kexp β + β * deriv Kexp β) ∧
    (hadjiivanovMonodromy (v : ℂ) =
      lcftPhase (v : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        InfoGeometry.Clifford.LogCftMonodromy.monodromyNilpotentPart (v : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (bridge_synthesis v F dξ dθ K u data).1
  · exact first_law_modular_thermodynamics Q Kexp β hB hK hBoltzFlat
  · exact monodromy_decomposition (v : ℂ)

end InfoGeometry.Integration.GrandDeRhamCramerRaoBridge
