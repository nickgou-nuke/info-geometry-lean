import InfoGeometry.Canonical.SouriauOperatorialLogPotential

/-!
# Spectral thermal normalization: owner exports

The former version of this module stored analytic claims as `Type*` property
fields.  Such fields do not state, and cannot prove, a normalization identity,
a KMS condition, or a Type-III modular theorem.  The native owner is
`Canonical.SouriauOperatorialLogPotential`: it keeps the statewise logarithmic
generator and its positive partition readout in typed data and proves the
available identities directly.

This module intentionally exports the operator-valued Souriau family without
introducing a scalar surrogate for the missing measure-theoretic construction.
-/

namespace InfoGeometry.GrandUnification

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

abbrev SpectralThermalNormalizationData (LieAlgebra Obs : Type*)
    [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs] :=
  QuantumOperatorialSouriauFamily LieAlgebra Obs

theorem spectralThermalNormalization_partition_pos
    {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (D : SpectralThermalNormalizationData LieAlgebra Obs) :
    0 < D.partitionFunction :=
  QuantumOperatorialSouriauFamily.partitionFunction_pos D

theorem spectralThermalNormalization_partitionPotential_eq_logZ
    {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (D : SpectralThermalNormalizationData LieAlgebra Obs) :
    D.partitionPotential = Real.log D.partitionFunction :=
  QuantumOperatorialSouriauFamily.partitionPotential_eq_log_trace D

theorem spectralThermalNormalization_modularHamiltonian_eq_bare_add_logZ
    {LieAlgebra Obs : Type*} [AddMonoid LieAlgebra]
    [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]
    (D : SpectralThermalNormalizationData LieAlgebra Obs) :
    D.modularHamiltonian =
      D.Khat_beta + D.partitionPotential • (1 : Obs) :=
  QuantumOperatorialSouriauFamily.modularHamiltonian_eq_Khat_add_logZ D

end InfoGeometry.GrandUnification
