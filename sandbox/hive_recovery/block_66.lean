import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

open CategoryTheory

noncomputable section

namespace InfoGeometry.Epistemology

/-- 
  The category of raw, unverified mathematical skeletons.
  Objects are raw signatures; morphisms are partial mappings.
-/
variable (RawType : Type*) [Category RawType]

/-- 
  The category of sound, verified mathematical structures.
  Objects are verified algebra structures; morphisms are strict homomorphisms.
-/
variable (SoundType : Type*) [Category SoundType]

/-- The canonical inclusion functor mapping sound structures to their raw signatures. -/
variable (Inclusion : SoundType ⥤ RawType)

/-- 
  The Left Adjoint "Repair" (Reflector) Functor.
  Takes a raw signature and constructs the minimal, sound algebraic type.
-/
variable (Repair : RawType ⥤ SoundType)

/-- 
  The Reflective Adjunction: Repair ⊣ Inclusion.
  This formally secures the universal property of the semantic repair.
-/
variable (ReflectiveRepair : Repair ⊣ Inclusion)

/--
  THE CATEGORICAL REPAIR THEOREM:
  Proves that any sound realization 'f' of a raw specification 'X' 
  factors uniquely through the repaired structure 'Repair.obj X'.
  This guarantees that 'Repair.obj X' is the minimal supporting type.
-/
theorem repaired_type_is_minimal_and_sound
    (X : RawType) (T : SoundType)
    (f : X ⟶ Inclusion.obj T) :
    ∃! (f' : Repair.obj X ⟶ T), f = ReflectiveRepair.homEquiv X T f' := by
  -- 1. The homEquiv of the adjunction provides the unique bijection of morphisms
  use (ReflectiveRepair.homEquiv X T).symm f
  constructor
  · -- Prove the factoring equality: f = homEquiv(f')
    simp only [Adjunction.homEquiv_symm_apply, Equiv.apply_symm_apply]
  · -- Prove uniqueness: any other factoring map must equal f'
    intro g h_eq
    rw [h_eq]
    simp only [Adjunction.homEquiv_symm_apply, Equiv.symm_apply_apply]

end InfoGeometry.Epistemology