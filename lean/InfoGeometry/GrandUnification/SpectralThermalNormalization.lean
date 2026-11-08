import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Spectral thermal normalization: owner exports

The former version of this module stored analytic claims as `Type*` witness
fields.  Such fields do not state, and cannot prove, a normalization identity,
a KMS condition, or a Type-III modular theorem.  The native owner is
`Canonical.SouriauOperatorialLogPotential`: it keeps the statewise logarithmic
generator and its positive partition readout in typed data and proves the
available identities directly.

This module intentionally exports that owner without introducing a second
packet or a scalar surrogate for the missing measure-theoretic construction.
-/

namespace InfoGeometry.GrandUnification

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

abbrev SpectralThermalNormalizationData (State LieAlgebra LieDual : Type*) :=
  SouriauLieThermoData State LieAlgebra LieDual

theorem spectralThermalNormalization_partition_pos
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual) :
    0 < D.partitionFunction :=
  D.partitionFunction_pos

theorem spectralThermalNormalization_partitionPotential_eq_logZ
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual) :
    D.partitionPotential = Real.log D.partitionFunction :=
  D.partitionPotential_eq_logZ

theorem spectralThermalNormalization_negativeLogGibbsDensity
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual)
    (x : State) :
    -Real.log (D.gibbsDensity x) =
      D.K_beta x + D.partitionPotential :=
  D.negativeLogGibbsDensity_eq_K_beta_add_Phi x

theorem spectralThermalNormalization_statewise_log_generator
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual)
    (x : State) :
    D.K_beta x = -Real.log (D.gibbsDensity x) - D.partitionPotential :=
  D.modularHamiltonian_statewise_neg_log_gibbs_sub_PartitionPotential x

end InfoGeometry.GrandUnification
