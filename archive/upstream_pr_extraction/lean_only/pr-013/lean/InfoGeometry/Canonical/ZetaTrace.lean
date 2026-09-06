import InfoGeometry.Canonical.Arithmetic.ZetaEulerProductBridge
import InfoGeometry.Canonical.ZetaTraceBridge

namespace InfoGeometry.Canonical.ZetaTrace

abbrev PrimeGasPartition := InfoGeometry.Canonical.Arithmetic.PrimeGasPartition
abbrev PrimeWeightSpecialization := InfoGeometry.Canonical.Arithmetic.PrimeWeightSpecialization
abbrev AnalyticGate := InfoGeometry.Canonical.Arithmetic.AnalyticGate

theorem zeta_trace_bridge
    {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = riemannZeta s :=
  InfoGeometry.Canonical.zeta_trace_bridge hs

theorem weyl_denominator_limit_eq_zeta
    {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  InfoGeometry.Canonical.weyl_denominator_limit_eq_zeta hs

theorem zetaPrimeGas_partitionFunction_eq_riemannZeta
    {P : PrimeGasPartition}
    (W : PrimeWeightSpecialization P)
    {s : ℂ}
    (hs : 1 < s.re) :
    P.partitionFunction s = riemannZeta s :=
  InfoGeometry.Canonical.Arithmetic.PrimeWeightSpecialization.partitionFunction_eq_riemannZeta W hs

end InfoGeometry.Canonical.ZetaTrace
