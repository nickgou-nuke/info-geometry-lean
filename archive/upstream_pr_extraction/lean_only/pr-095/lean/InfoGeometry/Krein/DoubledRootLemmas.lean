import InfoGeometry.Meta.Architecture
import InfoGeometry.Krein.DoubledSpace

/-!
# Root lemmas for the real doubled Krein carrier

This file exposes only already-proved real-linear doubled-space facts.
-/

namespace InfoGeometry.Krein

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

@[rep_depth krein]
abbrev doubledJ : H₂ →L[ℝ] H₂ :=
  modular_j (E := E)

@[rep_depth krein]
abbrev doubledEpsilon : H₂ →L[ℝ] H₂ :=
  spectral_epsilon (E := E)

@[rep_depth krein]
abbrev doubledI : H₂ →L[ℝ] H₂ :=
  complex_i (E := E)

@[rep_depth krein]
theorem doubledJ_sq :
    (doubledJ (E := E)).comp (doubledJ (E := E)) =
      ContinuousLinearMap.id ℝ H₂ := by
  simpa [doubledJ] using modular_j_involution E

@[rep_depth krein]
theorem doubledEpsilon_sq :
    (doubledEpsilon (E := E)).comp (doubledEpsilon (E := E)) =
      ContinuousLinearMap.id ℝ H₂ := by
  simpa [doubledEpsilon] using spectral_epsilon_involution E

@[rep_depth krein]
theorem doubledJ_doubledEpsilon_anticommute :
    (doubledJ (E := E)).comp (doubledEpsilon (E := E)) =
      -((doubledEpsilon (E := E)).comp (doubledJ (E := E))) := by
  simpa [doubledJ, doubledEpsilon] using modular_j_spectral_epsilon_anticommute E

@[rep_depth krein]
theorem doubledI_sq :
    (doubledI (E := E)).comp (doubledI (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂) := by
  simpa [doubledI] using complex_i_sq E

@[rep_depth krein]
def IsProjector (P : H₂ →L[ℝ] H₂) : Prop :=
  P.comp P = P

@[rep_depth krein]
def CommutesWithDoubledJ (P : H₂ →L[ℝ] H₂) : Prop :=
  P.comp (doubledJ (E := E)) = (doubledJ (E := E)).comp P

@[rep_depth krein]
def IsJDoubledProjector (P : H₂ →L[ℝ] H₂) : Prop :=
  IsProjector (E := E) P ∧ CommutesWithDoubledJ (E := E) P

omit [CompleteSpace E] in
@[rep_depth krein]
theorem id_isJDoubledProjector :
    IsJDoubledProjector (E := E) (ContinuousLinearMap.id ℝ H₂) := by
  constructor
  · unfold IsProjector
    ext ψ <;> simp
  · unfold CommutesWithDoubledJ doubledJ
    ext ψ <;> simp

end
end InfoGeometry.Krein
