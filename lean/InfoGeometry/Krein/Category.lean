import Mathlib.CategoryTheory.Category.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.KreinSpace

/-!
# Category of Bundled Real Krein Spaces

This module defines the categorical structure for real Krein spaces:
- `RealKreinSpace`: A bundled object containing the carrier Hilbert space and its fundamental symmetry.
- `Category RealKreinSpace`: Morphisms are continuous linear maps preserving the Krein inner product.
-/

open CategoryTheory
open scoped InnerProductSpace

namespace InfoGeometry.Krein

/-- Bundled object for the category of real Krein spaces. -/
structure RealKreinSpace where
  H : Type*
  [instN : NormedAddCommGroup H]
  [instI : InnerProductSpace ℝ H]
  [instC : CompleteSpace H]
  [instK : KreinSpace H]

attribute [instance] RealKreinSpace.instN RealKreinSpace.instI RealKreinSpace.instC RealKreinSpace.instK

namespace RealKreinSpace

/-- Morphisms in the category of Krein spaces. -/
noncomputable def Hom (X Y : RealKreinSpace) := KreinHom X.H Y.H

noncomputable instance : Category RealKreinSpace where
  Hom X Y := Hom X Y
  id X :=
    { hom := ContinuousLinearMap.id ℝ X.H
      isometric := by intro u v; simp [KreinSpace.kreinInner_def] }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      isometric := fun u v => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, g.isometric, f.isometric] }

end RealKreinSpace

end InfoGeometry.Krein
