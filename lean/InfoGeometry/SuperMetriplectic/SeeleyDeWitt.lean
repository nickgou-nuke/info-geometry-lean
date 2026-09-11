import InfoGeometry.SuperMetriplectic.CasimirZeta
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Seeley-DeWitt / Weyl-Anomaly Layer

Lean-only scalar/body-level packet for the heat-kernel statement used by the
Casimir-zeta supervolume model.

In the intended `Cl(4,4)`/`D₄` picture the effective dimension is `8`, so the
Weyl anomaly is controlled by the `a₄` Seeley-DeWitt coefficient, i.e. the
`t⁰` term in the heat-kernel expansion.  This module records the theorem
interface:

* `ζ(0)` is the Seeley-DeWitt/a₄ readout;
* `a₄` splits into Euler/Pontryagin/central-curvature channels;
* the Euler density is represented by a curvature Pfaffian readout;
* the Pfaffian/topological index regulates the central-charge Casimir lane.

No heat-kernel analysis, manifold integration, or concrete curvature tensor is
constructed here.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Heat-kernel zeta-zero packet.

`dimensionReadout` is included so the `D = 8` specialization is explicit.
-/
structure HeatKernelZetaZeroPacket where
  dimensionReadout : ℕ
  seeleyDeWittA4 : ℝ
  zetaZero : ℝ
  anomalyIntegral : ℝ
  dimensionReadout_eq_eight :
    dimensionReadout = 8
  zetaZero_eq_seeleyDeWittA4 :
    zetaZero = seeleyDeWittA4
  seeleyDeWittA4_eq_anomalyIntegral :
    seeleyDeWittA4 = anomalyIntegral

namespace HeatKernelZetaZeroPacket

/-- The effective dimension of the `Cl(4,4)` heat-kernel shadow is eight. -/
theorem dimension_eq_eight
    (H : HeatKernelZetaZeroPacket) :
    H.dimensionReadout = 8 :=
  H.dimensionReadout_eq_eight

/-- Zeta-zero equals the `a₄` Seeley-DeWitt readout. -/
theorem zetaZero_eq_a4
    (H : HeatKernelZetaZeroPacket) :
    H.zetaZero = H.seeleyDeWittA4 :=
  H.zetaZero_eq_seeleyDeWittA4

/-- The `a₄` readout is the integrated Weyl-anomaly density. -/
theorem a4_eq_anomalyIntegral
    (H : HeatKernelZetaZeroPacket) :
    H.seeleyDeWittA4 = H.anomalyIntegral :=
  H.seeleyDeWittA4_eq_anomalyIntegral

/-- Zeta-zero directly reads the anomaly integral. -/
theorem zetaZero_eq_anomalyIntegral
    (H : HeatKernelZetaZeroPacket) :
    H.zetaZero = H.anomalyIntegral := by
  rw [H.zetaZero_eq_a4, H.a4_eq_anomalyIntegral]

end HeatKernelZetaZeroPacket

/--
`D₄`/8D `a₄` density split.

The intended expression is
`a₄ = c₁χ₈(R) + c₂P₂(R) + c₃ Tr(F_Z⁴)`.
-/
structure SeeleyDeWittA4D4Packet where
  eulerDensity : ℝ
  pontryaginDensity : ℝ
  centralCurvatureFourth : ℝ
  cEuler : ℝ
  cPontryagin : ℝ
  cCentral : ℝ
  a4Density : ℝ
  a4Density_eq :
    a4Density =
      cEuler * eulerDensity
        + cPontryagin * pontryaginDensity
        + cCentral * centralCurvatureFourth

namespace SeeleyDeWittA4D4Packet

/-- Public `a₄` density decomposition into topological and central-charge lanes. -/
theorem a4Density_eq_split
    (A : SeeleyDeWittA4D4Packet) :
    A.a4Density =
      A.cEuler * A.eulerDensity
        + A.cPontryagin * A.pontryaginDensity
        + A.cCentral * A.centralCurvatureFourth :=
  A.a4Density_eq

end SeeleyDeWittA4D4Packet

/--
Euler/Pfaffian/topological-index bridge.

The Euler density is represented by a curvature Pfaffian readout; the resulting
topological index is identified with the protected central-charge regulator.
-/
structure PfaffianEulerIndexBridge where
  curvaturePfaffian : ℝ
  eulerDensity : ℝ
  topologicalIndex : ℝ
  centralChargeRegulator : ℝ
  eulerDensity_eq_curvaturePfaffian :
    eulerDensity = curvaturePfaffian
  topologicalIndex_eq_curvaturePfaffian :
    topologicalIndex = curvaturePfaffian
  topologicalIndex_eq_centralChargeRegulator :
    topologicalIndex = centralChargeRegulator

namespace PfaffianEulerIndexBridge

/-- Euler density is the curvature Pfaffian readout. -/
theorem euler_eq_pfaffian
    (P : PfaffianEulerIndexBridge) :
    P.eulerDensity = P.curvaturePfaffian :=
  P.eulerDensity_eq_curvaturePfaffian

/-- Topological index is the curvature Pfaffian readout. -/
theorem index_eq_pfaffian
    (P : PfaffianEulerIndexBridge) :
    P.topologicalIndex = P.curvaturePfaffian :=
  P.topologicalIndex_eq_curvaturePfaffian

/-- Topological index is the central-charge regulator. -/
theorem index_eq_centralRegulator
    (P : PfaffianEulerIndexBridge) :
    P.topologicalIndex = P.centralChargeRegulator :=
  P.topologicalIndex_eq_centralChargeRegulator

end PfaffianEulerIndexBridge

/--
Final Seeley-DeWitt capstone over the Casimir-zeta supervolume packet.
-/
structure SeeleyDeWittCasimirCapstone (ι : Type*) [Fintype ι] where
  casimirCapstone : SupervolumeCasimirZetaCapstone ι
  heatKernel : HeatKernelZetaZeroPacket
  a4 : SeeleyDeWittA4D4Packet
  pfaffianIndex : PfaffianEulerIndexBridge
  heatKernel_a4_matches_density :
    heatKernel.seeleyDeWittA4 = a4.a4Density
  a4_euler_matches_pfaffian :
    a4.eulerDensity = pfaffianIndex.eulerDensity
  pfaffian_regulator_matches_casimir :
    pfaffianIndex.centralChargeRegulator =
      casimirCapstone.pfaffianRegulator.centralCharge

namespace SeeleyDeWittCasimirCapstone

variable {ι : Type*} [Fintype ι]

/-- Zeta-zero is the `a₄` density readout. -/
theorem zetaZero_eq_a4Density
    (C : SeeleyDeWittCasimirCapstone ι) :
    C.heatKernel.zetaZero = C.a4.a4Density := by
  rw [C.heatKernel.zetaZero_eq_a4, C.heatKernel_a4_matches_density]

/-- The Euler lane of `a₄` is represented by the curvature Pfaffian. -/
theorem a4Euler_eq_curvaturePfaffian
    (C : SeeleyDeWittCasimirCapstone ι) :
    C.a4.eulerDensity = C.pfaffianIndex.curvaturePfaffian := by
  rw [C.a4_euler_matches_pfaffian, C.pfaffianIndex.euler_eq_pfaffian]

/-- The Pfaffian central regulator matches the Casimir-flow central charge. -/
theorem pfaffianRegulator_eq_casimirCentralCharge
    (C : SeeleyDeWittCasimirCapstone ι) :
    C.pfaffianIndex.centralChargeRegulator =
      C.casimirCapstone.pfaffianRegulator.centralCharge :=
  C.pfaffian_regulator_matches_casimir

/--
Final Seeley-DeWitt theorem:
`ζ(0)` is the `a₄` density, `a₄` splits into Euler/Pontryagin/central lanes,
Euler is Pfaffian, and the Pfaffian regulator is the Casimir central charge.
-/
theorem seeleyDeWitt_casimir_capstone
    (C : SeeleyDeWittCasimirCapstone ι) :
    C.heatKernel.dimensionReadout = 8
      ∧ C.heatKernel.zetaZero = C.a4.a4Density
      ∧ C.a4.a4Density =
          C.a4.cEuler * C.a4.eulerDensity
            + C.a4.cPontryagin * C.a4.pontryaginDensity
            + C.a4.cCentral * C.a4.centralCurvatureFourth
      ∧ C.a4.eulerDensity = C.pfaffianIndex.curvaturePfaffian
      ∧ C.pfaffianIndex.centralChargeRegulator =
          C.casimirCapstone.pfaffianRegulator.centralCharge := by
  exact ⟨C.heatKernel.dimension_eq_eight,
    C.zetaZero_eq_a4Density,
    C.a4.a4Density_eq_split,
    C.a4Euler_eq_curvaturePfaffian,
    C.pfaffianRegulator_eq_casimirCentralCharge⟩

end SeeleyDeWittCasimirCapstone

end InfoGeometry.SuperMetriplectic
