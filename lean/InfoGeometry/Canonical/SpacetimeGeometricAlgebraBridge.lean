import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.NoncommutativeModularSignum

namespace SpacetimeGeometricAlgebraBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.NoncommutativeModularSignum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
The Pseudoscalar Isomorphism:
The geometric pseudoscalar i of Spacetime Algebra maps exactly to the chiral grading / phase axis K
in the Hestenes-Krein doubled space.
-/
@[rep_depth krein]
noncomputable def pseudoscalar_K [CompleteSpace E] : EndH :=
  complex_i (E := E)

/-- The volume form K squares to -1 (the involution property of the pseudoscalar). -/
theorem pseudoscalar_K_sq [CompleteSpace E] :
    (pseudoscalar_K (E := E)).comp (pseudoscalar_K (E := E)) = -(1 : EndH) := by
  simpa [pseudoscalar_K] using (complex_i_sq (E := E))

/--
Tomita conjugation flips the pseudoscalar phase axis.

This is the operator-level readback of the real doubled `i = Jε` relation:
`J K J = -K`.
-/
theorem J_K_anticommute [CompleteSpace E] :
    modular_j (E := E) * pseudoscalar_K (E := E) * modular_j (E := E) =
      -pseudoscalar_K (E := E) := by
  have hJK :
      modular_j (E := E) * pseudoscalar_K (E := E) =
        spectral_epsilon (E := E) := by
    simpa [pseudoscalar_K] using (modular_j_comp_complex_i (E := E))
  calc
    modular_j (E := E) * pseudoscalar_K (E := E) * modular_j (E := E)
        = spectral_epsilon (E := E) * modular_j (E := E) := by
            rw [hJK]
    _ = -pseudoscalar_K (E := E) := by
          simpa [pseudoscalar_K] using (spectral_epsilon_comp_modular_j (E := E))

/-- The discrete Dirac-Hodge Operator D on the Cuntz algebra.
D = S_L + J S_L J
where S_L is the left shift operator (annihilation operator).
-/
noncomputable def discrete_dirac_hodge (S_L J_op : EndH) : EndH :=
  S_L + J_op.comp (S_L.comp J_op)

/-- Maxwell's vacuum equation analogue: D * rho = 0 -/
def maxwell_vacuum_conservation (D rho : EndH) : Prop :=
  D.comp rho = 0

/--
Spinor Rotors on the Critical Line.
A relativistic Dirac spinor is ψ = ρ^(1/2) e^{iβ} R.
On the critical line (Re(s) = 1/2), the scale-normal inflation β vanishes.
We represent the spinor purely as a geometric rotor in the doubled space.
-/
@[rep_depth krein]
noncomputable def spinor_rotor [CompleteSpace E] (rho_sqrt : EndH) (gamma_lnx : ℝ) : EndH :=
  (Real.cos gamma_lnx) • rho_sqrt + (Real.sin gamma_lnx) • ((pseudoscalar_K (E := E)).comp rho_sqrt)

/--
The Biquaternion-Tomita Isomorphism.
The Tomita-Takesaki modular evolution Δ^{it} J matches the spinor rotor dynamics.
-/
def tomita_biquaternion_isomorphism (Delta_it J_op R_rotor : EndH) : Prop :=
  Delta_it.comp J_op = R_rotor

end SpacetimeGeometricAlgebraBridge
