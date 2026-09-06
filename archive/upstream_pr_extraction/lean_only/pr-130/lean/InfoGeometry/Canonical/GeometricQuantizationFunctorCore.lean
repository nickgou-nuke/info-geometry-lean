import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Constructive finite geometric-quantization functor

The source category records a classical carrier, a quantum carrier, and a
quantization map.  A morphism consists of maps on both carriers commuting with
that quantization map.  The native Mathlib functor below forgets the classical
carrier and sends a morphism to its quantum map.

This is the finite categorical core; it does not claim a smooth geometric
quantization theorem or a canonical Hilbert-space completion.
-/

universe u v

namespace InfoGeometry.Canonical

open CategoryTheory

structure QuantizationObject where
  classical : Type u
  quantum : Type v
  quantize : classical → quantum

structure QuantizationMorphism (X Y : QuantizationObject) where
  classicalMap : X.classical → Y.classical
  quantumMap : X.quantum → Y.quantum
  commutes : ∀ x, quantumMap (X.quantize x) = Y.quantize (classicalMap x)

namespace QuantizationMorphism

def id (X : QuantizationObject) :
    QuantizationMorphism X X where
  classicalMap := _root_.id
  quantumMap := _root_.id
  commutes := by intro x; rfl

def comp {X Y Z : QuantizationObject}
    (f : QuantizationMorphism X Y) (g : QuantizationMorphism Y Z) :
    QuantizationMorphism X Z where
  classicalMap := g.classicalMap ∘ f.classicalMap
  quantumMap := g.quantumMap ∘ f.quantumMap
  commutes := by
    intro x
    change g.quantumMap (f.quantumMap (X.quantize x)) =
      Z.quantize (g.classicalMap (f.classicalMap x))
    rw [f.commutes x, g.commutes]

@[ext] theorem ext {X Y : QuantizationObject}
    (f g : QuantizationMorphism X Y)
    (hc : f.classicalMap = g.classicalMap)
    (hq : f.quantumMap = g.quantumMap) :
    f = g := by
  cases f
  cases g
  simp only at hc hq
  cases hc
  cases hq
  rfl

end QuantizationMorphism

instance : Category QuantizationObject where
  Hom X Y := QuantizationMorphism X Y
  id := QuantizationMorphism.id
  comp f g := QuantizationMorphism.comp f g
  id_comp := by
    intro X Y f
    apply QuantizationMorphism.ext
    · funext x
      simp [QuantizationMorphism.comp, QuantizationMorphism.id]
    · funext x
      simp [QuantizationMorphism.comp, QuantizationMorphism.id]
  comp_id := by
    intro X Y f
    apply QuantizationMorphism.ext
    · funext x
      simp [QuantizationMorphism.comp, QuantizationMorphism.id]
    · funext x
      simp [QuantizationMorphism.comp, QuantizationMorphism.id]
  assoc := by
    intro W X Y Z f g h
    apply QuantizationMorphism.ext
    · funext x
      simp [QuantizationMorphism.comp]
    · funext x
      simp [QuantizationMorphism.comp]

/-! A small native category of types at the quantum universe level. -/
instance : Category (Type v) where
  Hom X Y := X → Y
  id X := _root_.id
  comp f g := g ∘ f
  id_comp := by
    intro X Y f
    funext x
    rfl
  comp_id := by
    intro X Y f
    funext x
    rfl
  assoc := by
    intro W X Y Z f g h
    funext x
    rfl

/-- The constructive finite geometric-quantization functor. -/
def geometricQuantizationFunctor :
    QuantizationObject ⥤ Type v where
  obj X := X.quantum
  map f := f.quantumMap
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

@[simp] theorem geometricQuantizationFunctor_obj
    (X : QuantizationObject) :
    geometricQuantizationFunctor.obj X = X.quantum :=
  rfl

@[simp] theorem geometricQuantizationFunctor_map
    {X Y : QuantizationObject}
    (f : X ⟶ Y) :
    geometricQuantizationFunctor.map f = f.quantumMap :=
  rfl

end InfoGeometry.Canonical
