import InfoGeometry.External.Auto.InfinityFilteredColimits

open CategoryTheory CategoryTheory.Limits SSet Opposite

universe u

namespace InfoGeometry.External.Auto.InfinityFilteredColimitsAudit

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable (F : J ⥤ SSet.{u}) (c : SSet.{u})

#check rozenblyum_mapping_space_commutes_colimit

#print axioms rozenblyum_mapping_space_commutes_colimit

end InfoGeometry.External.Auto.InfinityFilteredColimitsAudit
