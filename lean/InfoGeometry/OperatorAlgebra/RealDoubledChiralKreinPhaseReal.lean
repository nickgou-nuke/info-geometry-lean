import InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint

/-!
# Phase-axis/Real-structure data for the doubled chiral carrier

This file connects the finite doubled construction to the repository's
existing `PhaseAxis` and `PhaseRealStructure` interfaces.  The `J` here is
real-linear; complex anti-linearity belongs to a later complexification.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPhaseReal

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
open InfoGeometry.OperatorAlgebra.RealPhaseSpectralTriple

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev H₂ := DoubledSpace E
abbrev ChiralPhaseAxis := PhaseAxis (H₂ (E := E))

noncomputable def chiralPhaseAxis : ChiralPhaseAxis (E := E) where
  K := chiralComplexStructure (E := E)
  K_sq := chiralComplexStructure_sq (E := E)

theorem gamma5_reverses_chiral_phase :
    (gamma5 (E := E)).comp (chiralComplexStructure (E := E)) =
      -((chiralComplexStructure (E := E)).comp (gamma5 (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [chiralComplexStructure, gamma5, etaChiral, spectral_epsilon,
      modular_j]

noncomputable def gamma5PhaseRealStructure :
    PhaseRealStructure (H₂ (E := E)) (chiralPhaseAxis (E := E)) where
  J := gamma5 (E := E)
  J_square := gamma5_involution (E := E)
  J_reverses_phase := gamma5_reverses_chiral_phase (E := E)

@[simp] theorem gamma5PhaseRealStructure_J :
    (gamma5PhaseRealStructure (E := E)).J = gamma5 (E := E) := rfl

theorem gamma5PhaseRealStructure_reverses_phase :
    (gamma5PhaseRealStructure (E := E)).J.comp
        (chiralPhaseAxis (E := E)).K =
      -((chiralPhaseAxis (E := E)).K.comp
        (gamma5PhaseRealStructure (E := E)).J) :=
  gamma5_reverses_chiral_phase (E := E)

theorem etaChiral_reverses_chiral_phase :
    (etaChiral (E := E)).comp (chiralComplexStructure (E := E)) =
      -((chiralComplexStructure (E := E)).comp (etaChiral (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [chiralComplexStructure, gamma5, etaChiral, spectral_epsilon,
      modular_j]

noncomputable def etaChiralPhaseRealStructure :
    PhaseRealStructure (H₂ (E := E)) (chiralPhaseAxis (E := E)) where
  J := etaChiral (E := E)
  J_square := etaChiral_involution (E := E)
  J_reverses_phase := etaChiral_reverses_chiral_phase (E := E)

@[simp] theorem etaChiralPhaseRealStructure_J :
    (etaChiralPhaseRealStructure (E := E)).J = etaChiral (E := E) := rfl

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPhaseReal
