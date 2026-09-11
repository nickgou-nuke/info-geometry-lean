import InfoGeometry.Physics.FluidBRSTGaugeDecoupling

/-!
# Audit for Fluid BRST Gauge Decoupling (Section 5.87)
-/

open InfoGeometry.Physics.FluidBRSTGaugeDecoupling
open InfoGeometry.Physics.FluidBRSTGaugeDecoupling.FluidBRSTState

#print axioms ghost_variation_zero
#print axioms brst_ghost_nilpotent
#print axioms brst_antighost_nilpotent
#print axioms brst_pressure_nilpotent
#print axioms brst_velocity_nilpotent
#print axioms brst_nilpotent
#print axioms exact_is_physical
#print axioms solenoidal_flow_is_physical
#print axioms certified_fluid_brst_gauge_decoupling_synthesis
