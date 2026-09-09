import InfoGeometry.Canonical.SouriauKaehlerKleinBottleBridge

namespace InfoGeometry.Canonical.SouriauKaehlerKleinBottleCapstone

open InfoGeometry.Canonical.SouriauKaehlerKleinBottle

theorem souriau_kaehler_klein_bottle_canonical_capstone
    (theta : SouriauTemperature) (u v : OrbitVector) (t : ℝ) :
    ((complexTemperature theta).re = theta.beta ∧
      (complexTemperature theta).im = theta.time) ∧
    (complexStructure * complexStructure = -1) ∧
    (symplectic u (actComplex v) = metric u v) ∧
    (modularTwist (modularTwist theta) = theta) ∧
    ((modularTwist ⟨1 / 2, t⟩).beta = 1 / 2) ∧
    ((modularTwist ⟨1 / 2, t⟩).time = -t) :=
  ⟨complexTemperature_parts theta, complexStructure_sq,
    kahler_compatibility u v, modularTwist_involutive theta,
    modularTwist_fixed_beta t, modularTwist_reverses_time t⟩

end InfoGeometry.Canonical.SouriauKaehlerKleinBottleCapstone
