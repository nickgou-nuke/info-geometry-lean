import Mathlib

/-!
QMS isolated proof targets for purifying the `QuantumOperatorialSouriauFamily`
sockets in `InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

Mathematical context:
- `LieAlgebra` is the parameter / Lie algebra carrier.
- `Obs` is an abstract operator/observable carrier.
- `Jhat β` is the quantum moment observable at parameter `β`.
- `Khat_beta` is the operatorial Souriau Hamiltonian source.
- `untracedExponential` is the unnormalized exponential operator.
- `partitionFunction` is the scalar partition function `Zβ`.
- `partitionPotential` is the scalar Massieu/log-partition potential `Φβ`.
- `rho_beta` is the normalized operatorial state proxy.
- `modularHamiltonian` is the source plus scalar log-partition correction.

Existing mathlib/literature context:
- Mathlib supplies equality and real positivity over `ℝ`.
- In operator-algebra/Souriau/KMS theory, trace-class and KMS state readouts
  require concrete operator topology, trace/state, positivity, and domain data.
- This abstract owner surface does not define a trace-class predicate, trace
  functional, von Neumann algebra, or KMS state. Therefore those analytic claims
  cannot be proved natively here.

QMS purification move:
- Replace impossible analytic sockets by positive readbacks of the explicit data
  already carried by the structure:
  1. partition function positivity `0 < Zβ`;
  2. normalized-state equation `ρβ = Zβ⁻¹ • exp(-Kβ)`.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialQuantumReadout

structure QuantumOperatorialSouriauFamily (LieAlgebra Obs : Type*) where
  Jhat : LieAlgebra → Obs
  beta : LieAlgebra
  Khat_beta : Obs
  untracedExponential : Obs
  opAdd : Obs → Obs → Obs
  opScale : ℝ → Obs → Obs
  opIdentity : Obs
  partitionFunction : ℝ
  partitionPotential : ℝ
  rho_beta : Obs
  modularHamiltonian : Obs
  partitionFunction_pos : 0 < partitionFunction
  Khat_beta_eq : Khat_beta = Jhat beta
  partitionPotential_eq_log_trace : partitionPotential = Real.log partitionFunction
  rho_beta_eq_normalized_exp : rho_beta = opScale (partitionFunction⁻¹) untracedExponential
  modularHamiltonian_eq : modularHamiltonian = opAdd Khat_beta (opScale partitionPotential opIdentity)

/-- Positive partition-function readback from the supplied quantum operatorial family. -/
theorem quantumTraceClass_as_partition_pos
    {LieAlgebra Obs : Type*}
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    0 < Q.partitionFunction := by
  exact Q.partitionFunction_pos

/-- Normalized-state readback from the supplied operatorial exponential data. -/
theorem traceStateKMSReadout_as_normalized_state
    {LieAlgebra Obs : Type*}
    (Q : QuantumOperatorialSouriauFamily LieAlgebra Obs) :
    Q.rho_beta = Q.opScale (Q.partitionFunction⁻¹) Q.untracedExponential := by
  exact Q.rho_beta_eq_normalized_exp

end InfoGeometry.QMS.SouriauOperatorialLogPotentialQuantumReadout
