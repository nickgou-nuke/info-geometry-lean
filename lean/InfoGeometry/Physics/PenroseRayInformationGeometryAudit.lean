import InfoGeometry.Physics.PenroseRayInformationGeometry

open InfoGeometry.Physics.PenroseRayInformationGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (M : PenroseMinkowski V)
variable (F : GammaFieldTensor M)

#print axioms field_confinement_to_penrose_rays
#print axioms gamma_field_pure_projection
#print axioms penrose_null_ray_krein_zero
#print axioms penrose_minkowski_symmetry
#print axioms penrose_minkowski_involutive
#print axioms certified_penrose_ray_information_geometry_synthesis
