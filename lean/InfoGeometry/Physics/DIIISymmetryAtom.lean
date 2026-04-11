import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Krein.Superphysics
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Physics.DIIISymmetryAtom

Formalization of Class DIII Symmetries (TRS and PHS) on the fundamental 
split-Cl(1,1) informational atom.

This file provides the local symmetry package required for the future 
macroscopic symmetry lift. 

- Time-Reversal Symmetry (T): T² = -1
- Particle-Hole Symmetry (C): C² = 1
- Chiral Symmetry (S = TC): S² = 1
-/

namespace InfoGeometry.Physics.DIIISymmetryAtom

open InfoGeometry.Quantum
open InfoGeometry.Krein

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
The Class DIII Symmetry Package for a real carrier.
This structure defines the anti-linear operators and their relations.
(Note: Real implementations use linear proxies for the anti-linear action).
-/
structure ClassDIIISymmetry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  T : H →L[ℝ] H
  C : H →L[ℝ] H
  T_sq : T.comp T = -(ContinuousLinearMap.id ℝ H)
  C_sq : C.comp C = ContinuousLinearMap.id ℝ H
  TC_anticommute : T.comp C = -(C.comp T)

/--
The DIII Symmetry for the doubled split-Cl(1,1) atom.
In the informational Spire, these are derived from the spectral involutions.
-/
@[rep_depth transport]
noncomputable def cl11DIIIPackage : ClassDIIISymmetry H₂ where
  T := complex_i (E := E) -- T acting as the phase-volume axis K
  C := modular_j (E := E)  -- C acting as the modular mirror J
  T_sq := complex_i_sq (E := E)
  C_sq := modular_j_involution (E := E)
  TC_anticommute := by
    -- K and J anti-commute in the Cl(1,1) algebra
    simpa using (InfoGeometry.Krein.complex_i_comp_modular_j (E := E))

/--
Theorem: Chiral Symmetry of the Atom.
The composite S = TC serves as the chiral symmetry (eps) of the DIII package.
-/
@[rep_depth transport]
theorem chiral_symmetry_eq_epsilon :
    (cl11DIIIPackage (E := E)).T.comp (cl11DIIIPackage (E := E)).C 
      = -(spectral_epsilon (E := E)) := by
  simp [cl11DIIIPackage]
  simpa using (InfoGeometry.Krein.complex_i_comp_modular_j (E := E))

end InfoGeometry.Physics.DIIISymmetryAtom
