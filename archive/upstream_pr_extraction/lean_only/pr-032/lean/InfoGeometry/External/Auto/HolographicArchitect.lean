namespace HolographicArchitect

/-- The discrete optical bench with stimulated scattering. -/
abbrev OpticalBench := Nat × (Float → Float)

namespace OpticalBench

def scatteringModes (bench : OpticalBench) : Nat := bench.1

def phaseConjugation (bench : OpticalBench) : Float → Float := bench.2

end OpticalBench

/-- The continuous black hole horizon. -/
abbrev BlackHoleHorizon := Float × (Float → Float)

namespace BlackHoleHorizon

def area (horizon : BlackHoleHorizon) : Float := horizon.1

def causalBoundary (horizon : BlackHoleHorizon) : Float → Float := horizon.2

end BlackHoleHorizon

def AndreevReflectionCompatible (bench : OpticalBench) (horizon : BlackHoleHorizon) : Prop :=
  bench.phaseConjugation = horizon.causalBoundary

end HolographicArchitect
