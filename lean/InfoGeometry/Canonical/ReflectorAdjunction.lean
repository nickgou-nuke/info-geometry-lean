import Mathlib.Tactic

namespace InfoGeometry.Canonical

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

variable (R : C ⥤ D)
variable (i : D ⥤ C)

/-- The reflector adjunction R ⊣ i mirroring the "nearest" collapse functor projection. -/
class ReflectorAdjunction (R : C ⥤ D) (i : D ⥤ C) where
  adjunction : R ⊣ i

end InfoGeometry.Canonical
