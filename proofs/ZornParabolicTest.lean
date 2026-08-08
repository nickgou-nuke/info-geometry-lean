import proofs.ZornCliffordParityAPI
import proofs.ZornChiralLightcone
import proofs.ZornLightconeCAR
import proofs.ZornQuasiHopfCocycle
import proofs.ZornGromovWitten
import proofs.ZornMajoranaBraiding

noncomputable section

open CliffordAlgebra LinearMap
open SplitOctonionBraidSU3 CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation ZornCliffordParityAPI
open ZornChiralLightcone ZornLightconeCAR ZornGromovWitten

namespace ZornParabolicHolography

def parabolicBoundaryProjector (r : Fin 3) : Module.End ℂ DiracSpinor16 :=
  peirceProjectorPlus * gromovJStructure * lightconeChannelProjector r

def holographicAnyonBraid (γ_i γ_j : Module.End ℂ DiracSpinor16) (X Y Z : Zorn) : 
    Module.End ℂ DiracSpinor16 :=
  diracGamma ⟨zorn3Cocycle X Y Z⟩ * majoranaBraidOperator γ_i γ_j

theorem diracGamma_zero : diracGamma 0 = 0 := by
  apply LinearMap.ext
  rintro ⟨S, C⟩
  apply Prod.ext <;> simp [diracGamma, cliffordMinus, cliffordPlus, zornConj]

theorem holographic_braid_abelian_sector (γ_i γ_j : Module.End ℂ DiracSpinor16) (X Y Z : Zorn) 
    (h : zorn3Cocycle X Y Z = 0) :
    holographicAnyonBraid γ_i γ_j X Y Z = 0 := by
  have hz : (⟨zorn3Cocycle X Y Z⟩ : Vector8) = 0 := Subtype.ext h
  rw [holographicAnyonBraid, hz, diracGamma_zero, zero_mul]

end ZornParabolicHolography
