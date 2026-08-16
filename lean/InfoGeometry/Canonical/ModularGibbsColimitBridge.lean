/-!
# Retired modular/Gibbs colimit compatibility surface

The former file transported an equality between tuple fields called
`negativeLogDensity`, `gibbsHamiltonian`, and `logPartitionScalar`.  The
transport was algebraically valid but the tuple carried no modular operator,
state, trace, or noncommutative Gibbs law.  It therefore did not establish a
relative modular theorem on a colimit.

The maintained owners are:

* `InfoGeometry.Canonical.OperatorThermodynamics` for operator-first modular
  and exponential-family data;
* `InfoGeometry.Canonical.ModularSurprisalThermoPacket` for supplied negative
  logarithm/readout laws;
* `InfoGeometry.Canonical.TensorTowerColimit` and the categorical colimit
  owners for actual stage-to-limit transport.

This file remains only as a stable docs-only import path.  A future genuine
colimit theorem must carry typed operator maps and their multiplicative/state
compatibility, rather than reintroducing the old tuple socket.
-/
