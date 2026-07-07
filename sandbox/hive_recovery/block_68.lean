import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

open CategoryTheory

noncomputable section

namespace InfoGeometry.Epistemology

/- The category of raw, unverified mathematical skeletons. -/
variable (RawType : Type*) [Category RawType]

/- The category of sound, verified mathematical structures. -/
variable (SoundType : Type*) [Category SoundType]

/- The canonical inclusion functor mapping sound structures to their raw signatures. -/
variable (Inclusion : SoundType ⥤ RawType)

/- The Left Adjoint "Repair" (Reflector) Functor. -/
variable (Repair : RawType ⥤ SoundType)

/- The Reflective Adjunction: Repair ⊣ Inclusion. -/
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
  refine ⟨(ReflectiveRepair.homEquiv X T).symm f, ?_, ?_⟩
  · exact ((ReflectiveRepair.homEquiv X T).apply_symm_apply f).symm
  · intro g h_eq
    rw [h_eq]
    exact ((ReflectiveRepair.homEquiv X T).symm_apply_apply g).symm

end InfoGeometry.Epistemology