import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Krein.KreinSpace

/-!
# Category of Real Krein Spaces

This module defines the categorical structure for real Krein spaces:
- `Krein`: A bundled object containing the carrier Hilbert space and its fundamental symmetry.
- `Category Krein`: Morphisms are continuous linear maps preserving the Krein inner product.
-/

open CategoryTheory
open scoped InnerProductSpace

/-- Bundled object for the category of real Krein spaces. -/
structure Krein where
  H : Type*
  [instN : NormedAddCommGroup H]
  [instI : InnerProductSpace ℝ H]
  [instC : CompleteSpace H]
  [instK : KreinSpace H]

attribute [instance] Krein.instN Krein.instI Krein.instC Krein.instK

namespace Krein

/-- Morphisms in the category of Krein spaces. -/
noncomputable def Hom (X Y : Krein) := KreinHom X.H Y.H

noncomputable instance : Category Krein where
  Hom X Y := Hom X Y
  id X :=
    { hom := ContinuousLinearMap.id ℝ X.H
      isometric := by intro u v; simp [KreinSpace.kreinInner_def] }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      isometric := fun u v => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, g.isometric, f.isometric] }

end Krein
