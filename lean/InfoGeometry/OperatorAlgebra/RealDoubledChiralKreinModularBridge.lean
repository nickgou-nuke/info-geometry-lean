import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

/-!
# Modular sign/CPT bridge for the doubled real chiral Krein carrier

This file instantiates the repository's existing finite modular sign datum on
the canonical real doubled carrier.  It records the exact linear reflection,
grading, and phase-axis identities.  It does not assert anti-linearity,
standard-pair cyclicity/separatingness, or an algebra/commutant theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinModularBridge

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.ModularSignCPT
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev H₂ := DoubledSpace E

/-- The existing modular sign/CPT relation instantiated by the doubled carrier. -/
noncomputable def doubledModularSignCPTDatum : ModularSignCPTDatum (H₂ (E := E)) where
  eps := gamma5 (E := E)
  J := etaChiral (E := E)
  Kmod := complex_i (E := E)
  eps_square := by
    simpa [gamma5] using spectral_epsilon_involution E
  J_square := by
    simpa [etaChiral] using modular_j_involution E
  J_eps_anticomm := by
    simpa [etaChiral, gamma5] using modular_j_spectral_epsilon_anticommute E
  Kmod_eq := by
    rfl
  Kmod_square := by
    exact complex_i_sq E

theorem doubledModularSignCPTDatum_Kmod_eq_complex_i :
    (doubledModularSignCPTDatum (E := E)).Kmod = complex_i (E := E) := rfl

theorem doubledModularSignCPTDatum_Kmod_square :
    (doubledModularSignCPTDatum (E := E)).Kmod.comp
        (doubledModularSignCPTDatum (E := E)).Kmod =
      -(ContinuousLinearMap.id ℝ (H₂ (E := E))) := by
  exact (doubledModularSignCPTDatum (E := E)).Kmod_square

theorem doubledModularSignCPTDatum_J_Kmod_anticommute :
    (doubledModularSignCPTDatum (E := E)).J.comp
        (doubledModularSignCPTDatum (E := E)).Kmod =
      -((doubledModularSignCPTDatum (E := E)).Kmod.comp
        (doubledModularSignCPTDatum (E := E)).J) := by
  let M := doubledModularSignCPTDatum (E := E)
  rw [M.Kmod_eq]
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun T : H₂ (E := E) →L[ℝ] H₂ (E := E) => T u) M.J_eps_anticomm
  have h' : M.J (M.eps u) = -(M.eps (M.J u)) := by
    simpa [ContinuousLinearMap.comp_apply] using h
  change M.J (M.J (M.eps u)) = -(M.J (M.eps (M.J u)))
  rw [h']
  simp

/-- The `Γ ∘ R` orientation is the negative of the canonical `R ∘ Γ` phase axis. -/
theorem chiralComplexStructure_eq_neg_complex_i :
    chiralComplexStructure (E := E) = -(complex_i (E := E)) := by
  calc
    chiralComplexStructure (E := E) =
        -((etaChiral (E := E)).comp (gamma5 (E := E))) := by
          unfold chiralComplexStructure
          rw [etaChiral_gamma5_anticommute]
          simp
    _ = -(complex_i (E := E)) := by
          rfl

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinModularBridge
