import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

open InfoGeometry.Canonical.SouriauThermodynamics

/-- The finite prime occupation observables as a Souriau moment-map shadow. -/
def primeSouriauMomentMap
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (energyWeight : ℕ → ℝ) :
    SouriauMomentMap (PrimeState P) where
  energy := stateEnergy energyWeight
  number := stateNumber

theorem primeSouriauMomentMap_toGrandCanonicalTwoParam
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (energyWeight : ℕ → ℝ) :
    toGrandCanonicalTwoParam (primeSouriauMomentMap P energyWeight) =
      primeGrandCanonicalParams P energyWeight := by
  rfl

theorem primeSouriauPartition_eq_finiteEulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (energyWeight : ℕ → ℝ) (T : GeometricTemperature) :
    souriauPartition (primeSouriauMomentMap P energyWeight) T =
      finiteEulerProduct P energyWeight T.beta T.mu := by
  rw [souriauPartition_eq_partitionGC]
  rw [primeSouriauMomentMap_toGrandCanonicalTwoParam]
  exact partition_eq_finiteEulerProduct P energyWeight T.beta T.mu

end InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
