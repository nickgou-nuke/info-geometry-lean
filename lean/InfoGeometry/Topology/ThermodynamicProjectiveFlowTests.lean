import InfoGeometry.Topology.ThermodynamicProjectiveFlow

noncomputable section

namespace InfoGeometry.Topology.ThermodynamicProjectiveFlowTests

open ThermodynamicSL2MobiusFlow ThermodynamicProjectiveFlow

example (variation : ThermodynamicSL2Variation) (point : RiemannSphere) :
    globalOrbit variation 0 point = point :=
  globalOrbit_zero variation point

example (variation : ThermodynamicSL2Variation) (time : ℂ) (point : RiemannSphere) :
    globalOrbit variation (-time) (globalOrbit variation time point) = point :=
  globalOrbit_neg variation time point

example (variation : ThermodynamicSL2Variation) (time point : ℂ)
    (denominator_ne : variation.finiteOrbitDenominator time point ≠ 0) :
    globalOrbit variation time (some point) = some (variation.finiteOrbit time point) :=
  globalOrbit_some_of_den_ne_zero variation time point denominator_ne

example (variation : ThermodynamicSL2Variation) (time point : ℂ)
    (denominator_zero : variation.finiteOrbitDenominator time point = 0) :
    globalOrbit variation time (some point) = none :=
  globalOrbit_some_of_den_zero variation time point denominator_zero

example (variation : ThermodynamicSL2Variation) (time point : ℂ)
    (denominator_ne : variation.finiteOrbitDenominator time point ≠ 0) :
    HasDerivAt (fun parameter => variation.finiteOrbit parameter point)
      (variation.vectorField (variation.finiteOrbit time point)) time :=
  (globalOrbit_affine_ode variation time point denominator_ne).2

#print axioms flowRepresentative_add
#print axioms globalOrbit_add
#print axioms globalOrbit_affine_ode

end InfoGeometry.Topology.ThermodynamicProjectiveFlowTests
