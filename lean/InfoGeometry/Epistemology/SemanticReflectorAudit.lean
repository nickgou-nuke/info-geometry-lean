import InfoGeometry.Epistemology.SemanticReflector

open CategoryTheory

universe u v

namespace InfoGeometry.Epistemology

variable (RawType : Type u) [Category.{v, u} RawType]
variable (SoundType : Type u) [Category.{v, u} SoundType]
variable (Inclusion : SoundType ⥤ RawType)
variable (Repair : RawType ⥤ SoundType)

#check repaired_type_is_minimal
#check repairUnit
#check repairCounit
#check repair_unit_counit_triangle
#check repair_counit_unit_triangle
#check repair_unit_naturality
#check repair_counit_naturality

#print axioms repaired_type_is_minimal
#print axioms repair_unit_counit_triangle
#print axioms repair_counit_unit_triangle
#print axioms repair_unit_naturality
#print axioms repair_counit_naturality

end InfoGeometry.Epistemology
