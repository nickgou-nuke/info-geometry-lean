import InfoGeometry.LightCone.ApolloniusCylinder

namespace InfoGeometry.Canonical.ApolloniusCylinderCapstone

open InfoGeometry.LightCone.ApolloniusCylinder

theorem capstone_apollonius_cylinder_synthesis (dξ dθ : ℝ) :
    cylinderMetric dξ dθ = dξ ^ 2 + dθ ^ 2 :=
  grand_apollonius_cylinder_synthesis dξ dθ

end InfoGeometry.Canonical.ApolloniusCylinderCapstone
