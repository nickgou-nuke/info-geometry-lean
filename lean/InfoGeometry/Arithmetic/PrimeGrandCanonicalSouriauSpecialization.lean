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
  energy := stateEnergy (P := P) energyWeight
  number := stateNumber (P := P)

theorem primeSouriauMomentMap_toGrandCanonicalTwoParam
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (energyWeight : ℕ → ℝ) :
    toGrandCanonicalTwoParam (primeSouriauMomentMap P energyWeight) =
      (PrimeGrandCanonicalPacket.mk P energyWeight).params := by
  rfl

theorem primeSouriauPartition_eq_finiteEulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (energyWeight : ℕ → ℝ) (T : GeometricTemperature) :
    souriauPartition (primeSouriauMomentMap P energyWeight) T =
      (PrimeGrandCanonicalPacket.mk P energyWeight).finiteEulerProduct T.beta T.mu := by
  rw [souriauPartition_eq_partitionGC]
  rw [primeSouriauMomentMap_toGrandCanonicalTwoParam]
  exact PrimeGrandCanonicalPacket.partition_eq_finiteEulerProduct
    (PrimeGrandCanonicalPacket.mk P energyWeight) T.beta T.mu

end InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
