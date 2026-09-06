import InfoGeometry.Algebraic.CartanExponentialFamily
import InfoGeometry.Physics.BoundaryMajoranaMassGap
import InfoGeometry.Physics.FreeEntropyDiffusionFunctional
import InfoGeometry.Physics.HolographicPressureFunctional
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-!
# Explicit Souriau free-entropy bridge

This file bundles the already-proved scalar readouts into a concrete
`S_free`-style functional.  It does not introduce a new vacuum carrier, a
new boundary state, or any unproved interface fields.

The layer is purely compositional:

* Massieu / surprisal / Boltzmann readouts from `SouriauMassieuPlanckFunctional`;
* free-entropy and `c = 8` readouts from `FreeEntropyDiffusionFunctional`;
* boundary entropy readout from the same finite free-entropy layer;
* chiral Majorana central charge bookkeeping from `BoundaryMajoranaMassGap`;
* holographic pressure readout from `HolographicPressureFunctional`.
-/

noncomputable section

namespace InfoGeometry.Physics.FreeEntropySouriauBridge

/-- The explicit combined free-entropy functional `S_free`. -/
def S_free
    (massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree : ℝ) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.souriauFreeEntropyAction
    massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree

/-- `S_free` expands to the explicit Souriau action formula. -/
theorem S_free_eq
    (massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree : ℝ) :
    S_free massieu kl incidenceFriction freeEnergy lambdaInc lambdaFree =
      massieu - kl - lambdaInc * incidenceFriction - lambdaFree * freeEnergy := by
  rfl

/--
Concrete finite-Cartan specialization of `S_free`.

The Massieu and KL inputs are not arbitrary scalars here: they are computed from
the finite Cartan exponential family.  The free layer is the explicit `c = 8`
free-entropy energy readout.
-/
def cartanSFree
    {ι : Type*} [Fintype ι]
    (theta eta : ι → ℝ)
    (incidenceFriction secondMoment freeEntropy lambdaInc lambdaFree : ℝ) : ℝ :=
  S_free
    (InfoGeometry.Algebraic.CartanExponentialFamily.massieu theta)
    (InfoGeometry.Algebraic.CartanExponentialFamily.kl theta eta)
    incidenceFriction
    (InfoGeometry.Physics.FreeEntropyDiffusionFunctional.freeEntropyEnergy
      8 secondMoment freeEntropy)
    lambdaInc
    lambdaFree

/-- Expanding the concrete finite-Cartan `S_free` specialization. -/
theorem cartanSFree_eq
    {ι : Type*} [Fintype ι]
    (theta eta : ι → ℝ)
    (incidenceFriction secondMoment freeEntropy lambdaInc lambdaFree : ℝ) :
    cartanSFree theta eta incidenceFriction secondMoment freeEntropy lambdaInc lambdaFree =
      InfoGeometry.Algebraic.CartanExponentialFamily.massieu theta
        - InfoGeometry.Algebraic.CartanExponentialFamily.kl theta eta
        - lambdaInc * incidenceFriction
        - lambdaFree *
          InfoGeometry.Physics.FreeEntropyDiffusionFunctional.freeEntropyEnergy
            8 secondMoment freeEntropy := by
  rfl

/--
Using the proved finite-Cartan KL/Bregman identity, the same `S_free`
specialization can be written with the Massieu-Bregman divergence.
-/
theorem cartanSFree_eq_massieu_sub_bregman
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (theta eta : ι → ℝ)
    (incidenceFriction secondMoment freeEntropy lambdaInc lambdaFree : ℝ)
    (hZ : 0 < InfoGeometry.Algebraic.CartanExponentialFamily.Z theta) :
    cartanSFree theta eta incidenceFriction secondMoment freeEntropy lambdaInc lambdaFree =
      InfoGeometry.Algebraic.CartanExponentialFamily.massieu theta
        - InfoGeometry.Algebraic.CartanExponentialFamily.bregmanPhi theta eta
        - lambdaInc * incidenceFriction
        - lambdaFree *
          InfoGeometry.Physics.FreeEntropyDiffusionFunctional.freeEntropyEnergy
            8 secondMoment freeEntropy := by
  rw [cartanSFree_eq]
  rw [InfoGeometry.Algebraic.CartanExponentialFamily.kl_eq_bregmanPhi theta eta hZ]

/-- First variation of the explicit combined free-entropy functional. -/
def S_freeFirstVariation
    (dMassieu dKL dIncidenceFriction dFreeEnergy lambdaInc lambdaFree : ℝ) : ℝ :=
  InfoGeometry.Physics.SouriauMassieuPlanckFunctional.souriauFreeEntropyFirstVariation
    dMassieu dKL dIncidenceFriction dFreeEnergy lambdaInc lambdaFree

/-- Expanding the first variation of `S_free`. -/
theorem S_freeFirstVariation_eq
    (dMassieu dKL dIncidenceFriction dFreeEnergy lambdaInc lambdaFree : ℝ) :
    S_freeFirstVariation dMassieu dKL dIncidenceFriction dFreeEnergy lambdaInc lambdaFree =
      dMassieu - dKL - lambdaInc * dIncidenceFriction - lambdaFree * dFreeEnergy := by
  rfl

/--
Finite-Cartan first variation of `S_free` with the free-probability layer
specialized to central charge `c = 8`.
-/
def cartanSFreeFirstVariation
    (dMassieu dKL dIncidenceFriction dSecondMoment dFreeEntropy
      lambdaInc lambdaFree : ℝ) : ℝ :=
  S_freeFirstVariation
    dMassieu
    dKL
    dIncidenceFriction
    (InfoGeometry.Physics.FreeEntropyDiffusionFunctional.freeEntropyFirstVariation
      8 dSecondMoment dFreeEntropy)
    lambdaInc
    lambdaFree

/-- Expanding the finite-Cartan `S_free` first-variation readout. -/
theorem cartanSFreeFirstVariation_eq
    (dMassieu dKL dIncidenceFriction dSecondMoment dFreeEntropy
      lambdaInc lambdaFree : ℝ) :
    cartanSFreeFirstVariation
        dMassieu dKL dIncidenceFriction dSecondMoment dFreeEntropy lambdaInc lambdaFree =
      dMassieu
        - dKL
        - lambdaInc * dIncidenceFriction
        - lambdaFree *
          ((1 / 2) * dSecondMoment - 8 * dFreeEntropy) := by
  rfl

/-- Stationarity of the explicit first variation is exactly vanishing of the readout. -/
theorem cartanSFree_stationary_iff_firstVariation_zero
    (dMassieu dKL dIncidenceFriction dSecondMoment dFreeEntropy
      lambdaInc lambdaFree : ℝ) :
    cartanSFreeFirstVariation
        dMassieu dKL dIncidenceFriction dSecondMoment dFreeEntropy lambdaInc lambdaFree = 0
      ↔
    dMassieu
        - dKL
        - lambdaInc * dIncidenceFriction
        - lambdaFree * ((1 / 2) * dSecondMoment - 8 * dFreeEntropy) = 0 := by
  rw [cartanSFreeFirstVariation_eq]

/--
Effective stress readout with the four scalar layers kept explicit:
incidence, Wick/anomaly, free-entropy, and Souriau/Massieu.
-/
def effectiveStressTensorReadout
    (incidence anomaly free souriau : ℝ) : ℝ :=
  incidence + anomaly + free + souriau

/-- Expanding the effective stress tensor readout. -/
theorem effectiveStressTensorReadout_eq
    (incidence anomaly free souriau : ℝ) :
    effectiveStressTensorReadout incidence anomaly free souriau =
      incidence + anomaly + free + souriau := by
  rfl

/-- Scalar residual for the effective Einstein balance readout. -/
def effectiveEinsteinResidual
    (einsteinTensor newtonG incidence anomaly free souriau : ℝ) : ℝ :=
  einsteinTensor
    - (8 * Real.pi * newtonG) *
      effectiveStressTensorReadout incidence anomaly free souriau

/-- Zero residual is exactly the scalar effective Einstein balance. -/
theorem effectiveEinsteinResidual_eq_zero_iff
    (einsteinTensor newtonG incidence anomaly free souriau : ℝ) :
    effectiveEinsteinResidual einsteinTensor newtonG incidence anomaly free souriau = 0 ↔
      einsteinTensor =
        (8 * Real.pi * newtonG) *
          effectiveStressTensorReadout incidence anomaly free souriau := by
  unfold effectiveEinsteinResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Bekenstein-Hawking area-law readout in units where the entropy is dimensionless. -/
def bekensteinHawkingEntropy (area newtonG : ℝ) : ℝ :=
  area / (4 * newtonG)

/-- Boundary calibration residual for the area law `S_BH = A / (4G)`. -/
def boundaryBHCalibrationResidual
    (boundaryEntropy area newtonG : ℝ) : ℝ :=
  boundaryEntropy - bekensteinHawkingEntropy area newtonG

/--
The boundary calibration residual vanishes exactly when the boundary entropy
matches the Bekenstein-Hawking area readout.  This is a calibration theorem,
not a derivation of the area law.
-/
theorem boundaryBHCalibrationResidual_eq_zero_iff
    (boundaryEntropy area newtonG : ℝ) :
    boundaryBHCalibrationResidual boundaryEntropy area newtonG = 0 ↔
      boundaryEntropy = bekensteinHawkingEntropy area newtonG := by
  unfold boundaryBHCalibrationResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith

/--
Boundary calibration specialized to the Hawking-type entropy readout
`S_boundary = -dF_boundary/dT`.
-/
theorem boundaryEntropyReadout_eq_bekensteinHawkingEntropy_iff
    (dFreeEnergy_dTemperature area newtonG : ℝ) :
    InfoGeometry.Physics.FreeEntropyDiffusionFunctional.boundaryEntropyReadout
        dFreeEnergy_dTemperature =
        bekensteinHawkingEntropy area newtonG
      ↔
    boundaryBHCalibrationResidual
        (InfoGeometry.Physics.FreeEntropyDiffusionFunctional.boundaryEntropyReadout
          dFreeEnergy_dTemperature)
        area
        newtonG = 0 := by
  rw [boundaryBHCalibrationResidual_eq_zero_iff]

/-- The 16-channel Majorana central charge is `8`. -/
theorem majoranaCentralCharge_sixteen_eq_eight :
    InfoGeometry.Physics.FreeEntropyDiffusionFunctional.majoranaCentralCharge 16 = 8 :=
  InfoGeometry.Physics.FreeEntropyDiffusionFunctional.majoranaCentralCharge_sixteen

/-- The 16-channel free-entropy energy is the `c = 8` readout. -/
theorem majoranaFreeEntropyEnergy_sixteen_eq_c8
    (secondMoment freeEntropy : ℝ) :
    InfoGeometry.Physics.FreeEntropyDiffusionFunctional.majoranaFreeEntropyEnergy
        16 secondMoment freeEntropy =
      InfoGeometry.Physics.FreeEntropyDiffusionFunctional.freeEntropyEnergy
        8 secondMoment freeEntropy :=
  InfoGeometry.Physics.FreeEntropyDiffusionFunctional.majoranaFreeEntropyEnergy_sixteen
    secondMoment freeEntropy

/-- The Hawking-type boundary entropy readout is the negative free-energy derivative. -/
theorem boundaryEntropyReadout_eq_neg_dFreeEnergy
    (dFreeEnergy_dTemperature : ℝ) :
    InfoGeometry.Physics.FreeEntropyDiffusionFunctional.boundaryEntropyReadout
        dFreeEnergy_dTemperature =
      -dFreeEnergy_dTemperature :=
  InfoGeometry.Physics.FreeEntropyDiffusionFunctional.boundaryEntropyReadout_eq
    dFreeEnergy_dTemperature

/-- The boundary entropy readout is the explicit Hawking-type negative derivative. -/
theorem hawkingBoundaryEntropyReadout_eq
    (dFreeEnergy_dTemperature : ℝ) :
    InfoGeometry.Physics.FreeEntropyDiffusionFunctional.boundaryEntropyReadout
        dFreeEnergy_dTemperature =
      -dFreeEnergy_dTemperature := by
  exact boundaryEntropyReadout_eq_neg_dFreeEnergy dFreeEnergy_dTemperature

/-- The holographic pressure coefficient remains an explicit scalar readout. -/
theorem holographicPressure_coeff_eq
    (A0 q F0 z Neff chi : ℝ) :
    InfoGeometry.Physics.HolographicPressureFunctional.outwardPressure
      A0 q F0 z Neff chi =
        z * Neff / (2 * q * InfoGeometry.Physics.HolographicPressureFunctional.weylBoundaryArea A0 q chi) :=
  InfoGeometry.Physics.HolographicPressureFunctional.holographicPressure_coeff
    A0 q F0 z Neff chi

end InfoGeometry.Physics.FreeEntropySouriauBridge
