import InfoGeometry.Canonical.BerryRotorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ModularBerryBridge

universe u v w

export InfoGeometry.Canonical.BerryRotorBridge (
  Γ H modularFD modularFDo BivectorPhaseAlgebra
  AbelianModularBerryData
  NonAbelianSpinBerryData
)

theorem modularBerryRotor_eq_curvatureIntegral_plus_anomaly
    {M : Type u} {Biv : Type v} {Rotor : Type w}
    [AddCommGroup Biv] [Module ℝ Biv]
    [LieRing Biv] [LieAlgebra ℝ Biv]
    [Group Rotor] [InfoGeometry.Canonical.BerryRotorBridge.BivectorPhaseAlgebra Biv Rotor]
    (data : InfoGeometry.Canonical.BerryRotorBridge.AbelianModularBerryData M Biv Rotor)
    (D : data.Chain2) :
    data.holonomy (data.boundary D) =
      InfoGeometry.Canonical.BerryRotorBridge.BivectorPhaseAlgebra.expBiv
        (-(data.surfaceIntegral D data.F + data.residue D)) :=
  InfoGeometry.Canonical.BerryRotorBridge.AbelianModularBerryData.modularBerryRotor_eq_curvatureIntegral_plus_anomaly
    data D

theorem modularSpinHolonomy_eq_surfaceOrderedCurvature_mul_anomaly
    {M : Type u} {Spin : Type v} {Curv2 : Type u}
    [Group Spin] [HAdd Curv2 Curv2 Curv2]
    (data : InfoGeometry.Canonical.BerryRotorBridge.NonAbelianSpinBerryData M Spin Curv2)
    (D : data.Surface) :
    data.holonomy (data.boundary D) =
      data.surfaceOrderedExp D * data.anomaly D :=
  InfoGeometry.Canonical.BerryRotorBridge.NonAbelianSpinBerryData.modularSpinHolonomy_eq_surfaceOrderedCurvature_mul_anomaly
    data D

end InfoGeometry.Canonical.ModularBerryBridge
