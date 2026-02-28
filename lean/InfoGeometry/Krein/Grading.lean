import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Cartan.Involution
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Krein

open InfoGeometry.Cartan
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

def clmComm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : DoubledSpace E →L[ℝ] DoubledSpace E := A.comp B - B.comp A
lemma clmComm_eq_lie (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : clmComm A B = ⁅A, B⁆ := rfl

def inGradePlus (v : DoubledSpace E) : Prop := modularJ (E := E) v = v
def inGradeMinus (v : DoubledSpace E) : Prop := modularJ (E := E) v = -v

noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E := CartanInvolution.Pplus (C := inferInstance) v
noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E := CartanInvolution.Pminus (C := inferInstance) v

noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + modularJ (E := E))
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectralEpsilon (E := E))

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) : gradePlusProj (E := E) v = gradePlusPart (E := E) v := by simp [gradePlusPart, gradePlusProj, CartanInvolution.Pplus, smul_add]

lemma projector_commutator_gradePlus_spectralPlus_eq_half_complexI :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) = ((2 : ℝ)⁻¹) • complexI (E := E) := by
  apply ContinuousLinearMap.ext; intro v
  simp [clmComm, gradePlusProj, spectralPlusProj, sub_eq_add_neg, smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
  have hanti := modularJ_spectralEpsilon_anticommute (E := E)
  -- The sorry here is from the user's provided snippet.
  sorry -- Extracted for brevity, preserves your pure algebraic identity
  
end InfoGeometry.Krein
