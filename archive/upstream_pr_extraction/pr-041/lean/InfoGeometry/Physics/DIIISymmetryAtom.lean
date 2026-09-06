import InfoGeometry.Canonical.RealBdGDIIIAtom
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
structure ClassDIIISymmetryData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  T : H →L[ℝ] H
  C : H →L[ℝ] H

def ClassDIIISymmetryLaws
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (P : ClassDIIISymmetryData H) : Prop :=
  P.T.comp P.T = -(ContinuousLinearMap.id ℝ H) ∧
  P.C.comp P.C = ContinuousLinearMap.id ℝ H ∧
  P.T.comp P.C = -(P.C.comp P.T)

def ClassDIIISymmetry
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :=
  { P : ClassDIIISymmetryData H // ClassDIIISymmetryLaws P }

/--
Translator surface: the historical `cl11DIIIPackage` is induced from the
canonical DIII proxy owner.
-/
@[rep_depth transport]
noncomputable def cl11DIIIPackage : ClassDIIISymmetry H₂ := by
  let P := canonicalDIIIProxy (E := E)
  exact ⟨
    { T := P.T, C := P.C },
    ⟨P.T_sq, P.C_sq, by
      rw [P.TC_eq_S, P.CT_eq_neg_S]
      simp⟩⟩

-- Root laws are owned by `ClassDIIISymmetryLaws` and the canonical proxy.

end InfoGeometry.Physics.DIIISymmetryAtom
