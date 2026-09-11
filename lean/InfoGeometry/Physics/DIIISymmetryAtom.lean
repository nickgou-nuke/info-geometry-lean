import InfoGeometry.Canonical.RealBdGDIIIAtom
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Physics.DIIISymmetryAtom

Compatibility translator for the local DIII symmetry API.

This file does not own a second DIII ontology. It translates the historical
`Physics` namespace surface to the canonical owner
`InfoGeometry.Canonical.RealBdGDIIIAtom`.
-/

namespace InfoGeometry.Physics.DIIISymmetryAtom

open InfoGeometry.Canonical.RealBdGDIIIAtom
open InfoGeometry.Krein

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Legacy physics-facing DIII package.

`TC_anticommute` is transported from the canonical proxy laws.
-/
structure ClassDIIISymmetry (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  T : H →L[ℝ] H
  C : H →L[ℝ] H
  T_sq : T.comp T = -(ContinuousLinearMap.id ℝ H)
  C_sq : C.comp C = ContinuousLinearMap.id ℝ H
  TC_anticommute : T.comp C = -(C.comp T)

/--
Translator surface: the historical `cl11DIIIPackage` is induced from the
canonical DIII proxy owner.
-/
@[rep_depth transport]
noncomputable def cl11DIIIPackage : ClassDIIISymmetry H₂ where
  T := (canonicalDIIIProxy (E := E)).T
  C := (canonicalDIIIProxy (E := E)).C
  T_sq := (canonicalDIIIProxy (E := E)).T_sq
  C_sq := (canonicalDIIIProxy (E := E)).C_sq
  TC_anticommute := by
    have hRoot := canonicalDIIIProxy_root_laws (E := E)
    rcases hRoot with ⟨_, _, _, _, _, hTC, hCT⟩
    calc
      (canonicalDIIIProxy (E := E)).T.comp (canonicalDIIIProxy (E := E)).C
          = -(spectral_epsilon (E := E)) := hTC
      _ = -((canonicalDIIIProxy (E := E)).C.comp (canonicalDIIIProxy (E := E)).T) := by
            simpa [hCT]

/--
Chiral readout on the historical physics surface, transported from the
canonical root-law package.
-/
@[rep_depth transport]
theorem chiral_symmetry_eq_epsilon :
    (cl11DIIIPackage (E := E)).T.comp (cl11DIIIPackage (E := E)).C
      = -(spectral_epsilon (E := E)) := by
  have hRoot := canonicalDIIIProxy_root_laws (E := E)
  rcases hRoot with ⟨_, _, _, _, _, hTC, _⟩
  simpa [cl11DIIIPackage] using hTC

/-- Root-name companion: the physics translator uses `T = complex_i`. -/
@[rep_depth transport, simp]
theorem cl11DIIIPackage_T_eq_complex_i :
    (cl11DIIIPackage (E := E)).T = complex_i (E := E) := by
  change (canonicalDIIIProxy (E := E)).T = complex_i (E := E)
  exact canonicalDIIIProxy_T_eq_complex_i (E := E)

/-- Root-name companion: the physics translator uses `C = modular_j`. -/
@[rep_depth transport, simp]
theorem cl11DIIIPackage_C_eq_modular_j :
    (cl11DIIIPackage (E := E)).C = modular_j (E := E) := by
  change (canonicalDIIIProxy (E := E)).C = modular_j (E := E)
  exact canonicalDIIIProxy_C_eq_modular_j (E := E)

/--
Packaged root-name law surface for the physics translator.
-/
@[rep_depth transport]
theorem cl11DIIIPackage_root_laws :
    let P := cl11DIIIPackage (E := E)
    P.T = complex_i (E := E)
      ∧ P.C = modular_j (E := E)
      ∧ P.T.comp P.T = -(ContinuousLinearMap.id ℝ H₂)
      ∧ P.C.comp P.C = ContinuousLinearMap.id ℝ H₂
      ∧ P.T.comp P.C = -(spectral_epsilon (E := E)) := by
  refine ⟨cl11DIIIPackage_T_eq_complex_i (E := E), cl11DIIIPackage_C_eq_modular_j (E := E), ?_, ?_, ?_⟩
  · change (canonicalDIIIProxy (E := E)).T.comp (canonicalDIIIProxy (E := E)).T =
      -(ContinuousLinearMap.id ℝ H₂)
    exact (canonicalDIIIProxy (E := E)).T_sq
  · change (canonicalDIIIProxy (E := E)).C.comp (canonicalDIIIProxy (E := E)).C =
      ContinuousLinearMap.id ℝ H₂
    exact (canonicalDIIIProxy (E := E)).C_sq
  · exact chiral_symmetry_eq_epsilon (E := E)

end InfoGeometry.Physics.DIIISymmetryAtom
