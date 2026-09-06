import Mathlib
import InfoGeometry.Topology.CuntzCantorSpectralTriple

open InfoGeometry.Topology.CuntzCantorSpectralTriple

variable {Op H : Type*} [Ring Op] [StarRing Op]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]

theorem boundedCommutator_tilt_dirac
    (T : CuntzCantorSpectralTriple Op H) (j : ℕ) :
    T.boundedCommutatorWitness :=
  T.boundedCommutatorCertified
