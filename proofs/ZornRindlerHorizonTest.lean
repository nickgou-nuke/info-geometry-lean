import proofs.ZornCliffordParityAPI
import proofs.ZornChiralLightcone
import proofs.ZornLightconeCAR

noncomputable section

open CliffordAlgebra LinearMap
open SplitOctonionBraidSU3 CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation ZornCliffordParityAPI
open ZornChiralLightcone ZornLightconeCAR

namespace ZornRindlerHorizon

def rindlerModularHamiltonian : Module.End ℂ DiracSpinor16 :=
  chiralityOperator

theorem causal_order_proof (r : Fin 3) :
    rindlerModularHamiltonian * lightconeSigmaPlus r - lightconeSigmaPlus r * rindlerModularHamiltonian = 
    (2 : ℂ) • lightconeSigmaPlus r := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  apply Prod.ext <;> simp [rindlerModularHamiltonian, lightconeSigmaPlus, diracGamma, cliffordMinus, cliffordPlus, zornConj]
  · ring_nf

end ZornRindlerHorizon
