import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# Canonical doubled-core Majorana lift

The Majorana operators are the canonical maps already owned by
`InfoGeometry.Krein.DoubledSpace`.  No structure stores copies of the operators
or their defining laws.
-/

namespace InfoGeometry.Core

open InfoGeometry.Krein

noncomputable section

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Canonical Majorana conjugation. -/
abbrev canonicalMajoranaJ := modular_j (E := E)

/-- Canonical Majorana spectral sign. -/
abbrev canonicalMajoranaEps := spectral_epsilon (E := E)

/-- Canonical Majorana phase axis `J ∘ ε`. -/
abbrev canonicalMajoranaK := complex_i (E := E)

/-- The canonical Majorana conjugation is involutive. -/
theorem canonicalMajoranaJ_sq :
    (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaJ (E := E)) =
      ContinuousLinearMap.id ℝ H₂ :=
  modular_j_involution (E := E)

/-- The canonical Majorana spectral sign is involutive. -/
theorem canonicalMajoranaEps_sq :
    (canonicalMajoranaEps (E := E)).comp (canonicalMajoranaEps (E := E)) =
      ContinuousLinearMap.id ℝ H₂ :=
  spectral_epsilon_involution (E := E)

/-- The two canonical Majorana involutions anticommute. -/
theorem canonicalMajoranaJ_Eps_anticommute :
    (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaEps (E := E)) =
      -((canonicalMajoranaEps (E := E)).comp (canonicalMajoranaJ (E := E))) :=
  modular_j_spectral_epsilon_anticommute (E := E)

/-- The canonical Majorana phase axis is the composite `J ∘ ε`. -/
theorem canonicalMajoranaK_eq_J_comp_Eps :
    canonicalMajoranaK (E := E) =
      (canonicalMajoranaJ (E := E)).comp
        (canonicalMajoranaEps (E := E)) :=
  rfl

/-- The canonical Majorana phase axis squares to `-Id`. -/
theorem canonicalMajoranaK_sq_eq_neg_id :
    (canonicalMajoranaK (E := E)).comp (canonicalMajoranaK (E := E)) =
      -(ContinuousLinearMap.id ℝ H₂) :=
  complex_i_sq (E := E)

/-- Complete canonical doubled-core Majorana root laws. -/
theorem canonicalMajorana_root_laws :
    (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaJ (E := E)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (canonicalMajoranaEps (E := E)).comp (canonicalMajoranaEps (E := E)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaEps (E := E)) =
        -((canonicalMajoranaEps (E := E)).comp (canonicalMajoranaJ (E := E)))
      ∧
    (canonicalMajoranaK (E := E)).comp (canonicalMajoranaK (E := E)) =
        -(ContinuousLinearMap.id ℝ H₂) :=
  ⟨modular_j_involution (E := E),
    spectral_epsilon_involution (E := E),
    modular_j_spectral_epsilon_anticommute (E := E),
    complex_i_sq (E := E)⟩

/-- Complete canonical doubled-core Majorana laws, including the phase-axis
factorization that was formerly stored as a packet field. -/
theorem canonicalMajorana_complete_root_laws :
    (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaJ (E := E)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (canonicalMajoranaEps (E := E)).comp (canonicalMajoranaEps (E := E)) =
        ContinuousLinearMap.id ℝ H₂
      ∧
    (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaEps (E := E)) =
        -((canonicalMajoranaEps (E := E)).comp (canonicalMajoranaJ (E := E)))
      ∧
    canonicalMajoranaK (E := E) =
        (canonicalMajoranaJ (E := E)).comp
          (canonicalMajoranaEps (E := E))
      ∧
    (canonicalMajoranaK (E := E)).comp (canonicalMajoranaK (E := E)) =
        -(ContinuousLinearMap.id ℝ H₂) :=
  ⟨canonicalMajoranaJ_sq (E := E),
    canonicalMajoranaEps_sq (E := E),
    canonicalMajoranaJ_Eps_anticommute (E := E),
    canonicalMajoranaK_eq_J_comp_Eps (E := E),
    canonicalMajoranaK_sq_eq_neg_id (E := E)⟩

end

end InfoGeometry.Core
