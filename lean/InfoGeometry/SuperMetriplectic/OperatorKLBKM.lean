import InfoGeometry.SuperMetriplectic.CriticalStiffness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermo.ModularKLDivergence
import InfoGeometry.Jordan.LogDet

/-!
# Operator KL/Bregman Lift and BKM Hessian Packets

Lean-only scalar/body-level formalization of the operatorial route:

* start from an unnormalized Gaussian/grand-canonical KL split;
* separate covariance/Itakura-Saito shape from scale;
* lift the logarithmic generator to an operator/modular Hamiltonian readout;
* take the second-order expansion as a BKM/Kubo-Mori Hessian bilinear form;
* express the Type III super-volume through expectation ratios and Fierz
  channel extraction, not traces of density matrices.

No Type III trace, spectral integral, or analytic functional-calculus theorem is
claimed here.  Those are carried as explicit fields; the compiled theorems only
check the algebraic bridge relations between the supplied readouts.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Unnormalized Gaussian/grand-canonical KL split.

`shapeItakuraSaito` is the covariance/shape part; `scaleItakuraSaito` is the
mass/intensity/particle-number scale part.  This is the scalar shadow of the
projective/radial generalized-KL decomposition used before operator lifting.
-/
structure UnnormalizedGaussianKLSplit where
  generalizedKL : ℝ
  shapeItakuraSaito : ℝ
  scaleItakuraSaito : ℝ
  generalizedKL_eq_shape_add_scale :
    generalizedKL = shapeItakuraSaito + scaleItakuraSaito
  shape_nonneg :
    0 ≤ shapeItakuraSaito
  scale_nonneg :
    0 ≤ scaleItakuraSaito

namespace UnnormalizedGaussianKLSplit

/-- Generalized KL is the covariance/IS shape term plus the scale term. -/
theorem kl_eq_shape_add_scale
    (G : UnnormalizedGaussianKLSplit) :
    G.generalizedKL = G.shapeItakuraSaito + G.scaleItakuraSaito :=
  G.generalizedKL_eq_shape_add_scale

/-- The supplied split makes the unnormalized Gaussian KL nonnegative. -/
theorem generalizedKL_nonneg
    (G : UnnormalizedGaussianKLSplit) :
    0 ≤ G.generalizedKL := by
  rw [G.kl_eq_shape_add_scale]
  exact add_nonneg G.shape_nonneg G.scale_nonneg

end UnnormalizedGaussianKLSplit

/--
Trace-free expectation carrier for a Type III-style operator layer.

The carrier has only expectation values and ratios against a reference vacuum
functional; it deliberately has no trace or density-matrix field.
-/
structure TypeIIIExpectationCarrier (Op : Type*) where
  vacuumExpectation : Op → ℝ
  perturbedExpectation : Op → ℝ
  referenceVacuumWeight : ℝ
  expectationRatio : Op → ℝ
  referenceVacuumWeight_pos :
    0 < referenceVacuumWeight
  expectationRatio_eq :
    ∀ A : Op, expectationRatio A = perturbedExpectation A / referenceVacuumWeight

namespace TypeIIIExpectationCarrier

/-- Expectation ratios are normalized only by the reference vacuum weight. -/
theorem expectationRatio_eq_perturbed_div_reference
    {Op : Type*} (E : TypeIIIExpectationCarrier Op) (A : Op) :
    E.expectationRatio A = E.perturbedExpectation A / E.referenceVacuumWeight :=
  E.expectationRatio_eq A

end TypeIIIExpectationCarrier

/--
Operatorial logarithmic generator / modular Hamiltonian lift.

The intended interpretation is that `logGenerator` is the logarithmic inverse of
the operator exponential chart, while `modularHamiltonianReadout` is the
expectation-level Araki/Tomita modular potential.
-/
structure OperatorLogBregmanLift (Op : Type*) where
  logGenerator : Op → ℝ
  modularHamiltonianReadout : Op → ℝ
  operatorBregmanDivergence : Op → Op → ℝ
  generator_matches_modularHamiltonian :
    ∀ A : Op, logGenerator A = modularHamiltonianReadout A
  divergence_eq_generator_gap :
    ∀ A B : Op,
      operatorBregmanDivergence A B =
        logGenerator A - logGenerator B

namespace OperatorLogBregmanLift

/-- The operator log-generator is the modular Hamiltonian readout. -/
theorem logGenerator_eq_modularHamiltonian
    {Op : Type*} (L : OperatorLogBregmanLift Op) (A : Op) :
    L.logGenerator A = L.modularHamiltonianReadout A :=
  L.generator_matches_modularHamiltonian A

/-- Operatorial Bregman divergence is the logarithmic generator gap. -/
theorem divergence_eq_logGenerator_gap
    {Op : Type*} (L : OperatorLogBregmanLift Op) (A B : Op) :
    L.operatorBregmanDivergence A B =
      L.logGenerator A - L.logGenerator B :=
  L.divergence_eq_generator_gap A B

end OperatorLogBregmanLift

/--
Second-order expansion of the exponential KL kernel.

This records the local Taylor readout for `exp (-D/ε)` through the quadratic
term.  The analytic remainder estimate is intentionally an explicit field.
-/
structure OperatorKLExponentialSecondOrderPacket where
  epsilon : ℝ
  divergence : ℝ
  expKernelReadout : ℝ
  secondOrderTaylor : ℝ
  remainder : ℝ
  secondOrderTaylor_eq :
    secondOrderTaylor =
      1 - divergence / epsilon + divergence ^ 2 / (2 * epsilon ^ 2)
  expKernel_eq_taylor_add_remainder :
    expKernelReadout = secondOrderTaylor + remainder

namespace OperatorKLExponentialSecondOrderPacket

/-- The second-order readout of `exp(-D/ε)` in the supplied local chart. -/
theorem secondOrderTaylor_eq_readout
    (K : OperatorKLExponentialSecondOrderPacket) :
    K.secondOrderTaylor =
      1 - K.divergence / K.epsilon + K.divergence ^ 2 / (2 * K.epsilon ^ 2) :=
  K.secondOrderTaylor_eq

/-- The kernel readout is the second-order Taylor part plus the supplied remainder. -/
theorem expKernel_eq_secondOrder_add_remainder
    (K : OperatorKLExponentialSecondOrderPacket) :
    K.expKernelReadout = K.secondOrderTaylor + K.remainder :=
  K.expKernel_eq_taylor_add_remainder

end OperatorKLExponentialSecondOrderPacket

/--
BKM/Kubo-Mori Hessian packet.

The bilinear map is indexed by operator generators rather than coordinates.
`hessian_eq_bkm` is the precise body-level statement that the second variation
of the lifted KL/Bregman divergence is the BKM form.
-/
structure OperatorBKMHessianPacket (Op : Type*) where
  bkm : Op → Op → ℝ
  hessian : Op → Op → ℝ
  modularIntegralReadout : Op → Op → ℝ
  bkm_eq_modularIntegral :
    ∀ A B : Op, bkm A B = modularIntegralReadout A B
  hessian_eq_bkm :
    ∀ A B : Op, hessian A B = bkm A B
  bkm_symm :
    ∀ A B : Op, bkm A B = bkm B A
  bkm_nonneg :
    ∀ A : Op, 0 ≤ bkm A A

namespace OperatorBKMHessianPacket

/-- The Hessian of the operatorial KL/Bregman lift is the BKM bilinear form. -/
theorem hessian_eq_bkm_form
    {Op : Type*} (H : OperatorBKMHessianPacket Op) (A B : Op) :
    H.hessian A B = H.bkm A B :=
  H.hessian_eq_bkm A B

/-- BKM is represented by the supplied modular-flow integral readout. -/
theorem bkm_eq_modularIntegralReadout
    {Op : Type*} (H : OperatorBKMHessianPacket Op) (A B : Op) :
    H.bkm A B = H.modularIntegralReadout A B :=
  H.bkm_eq_modularIntegral A B

/-- The BKM Hessian is symmetric on the supplied operator generator lanes. -/
theorem hessian_symm
    {Op : Type*} (H : OperatorBKMHessianPacket Op) (A B : Op) :
    H.hessian A B = H.hessian B A := by
  rw [H.hessian_eq_bkm_form, H.hessian_eq_bkm_form, H.bkm_symm]

/-- The diagonal BKM Hessian is nonnegative. -/
theorem hessian_nonneg
    {Op : Type*} (H : OperatorBKMHessianPacket Op) (A : Op) :
    0 ≤ H.hessian A A := by
  rw [H.hessian_eq_bkm_form]
  exact H.bkm_nonneg A

end OperatorBKMHessianPacket

/--
Fierz extraction packet for the spin-2 channel.

The bridge records that the stress/linearized-gravity potential is extracted
from expectation-level operator products via Fierz channel decomposition.
-/
structure FierzSpinTwoExtractionPacket (Op : Type*) where
  bilinearOperatorProduct : Op → Op → ℝ
  scalarChannel : Op → Op → ℝ
  vectorChannel : Op → Op → ℝ
  spinTwoChannel : Op → Op → ℝ
  linearizedGravityPotential : Op → Op → ℝ
  fierz_decomposition :
    ∀ A B : Op,
      bilinearOperatorProduct A B =
        scalarChannel A B + vectorChannel A B + spinTwoChannel A B
  gravityPotential_eq_spinTwo :
    ∀ A B : Op,
      linearizedGravityPotential A B = spinTwoChannel A B

namespace FierzSpinTwoExtractionPacket

/-- Fierz decomposition isolates the spin-2 channel. -/
theorem gravityPotential_eq_spinTwoChannel
    {Op : Type*} (F : FierzSpinTwoExtractionPacket Op) (A B : Op) :
    F.linearizedGravityPotential A B = F.spinTwoChannel A B :=
  F.gravityPotential_eq_spinTwo A B

end FierzSpinTwoExtractionPacket

/--
Type III super-volume readout.

The expression is expectation-ratio/BKM based.  It is not a trace of a density
matrix, which is the point of the Type III lift.
-/
structure TypeIIIOperatorSupervolumePacket (Op : Type*) where
  expectation : TypeIIIExpectationCarrier Op
  bkm : OperatorBKMHessianPacket Op
  logPfaffianReadout : ℝ
  bkmLogBerezinianReadout : ℝ
  superVolumeReadout : ℝ
  superVolume_eq :
    superVolumeReadout =
      logPfaffianReadout - (1 / 2 : ℝ) * bkmLogBerezinianReadout

namespace TypeIIIOperatorSupervolumePacket

/-- Type III super-volume is Pfaffian topology minus half the BKM/Berezinian scale readout. -/
theorem superVolume_eq_pfaffian_sub_half_bkmBerezinian
    {Op : Type*} (V : TypeIIIOperatorSupervolumePacket Op) :
    V.superVolumeReadout =
      V.logPfaffianReadout - (1 / 2 : ℝ) * V.bkmLogBerezinianReadout :=
  V.superVolume_eq

end TypeIIIOperatorSupervolumePacket

/--
Capstone tying the whole route together.
-/
structure OperatorKLBKMCapstone (Op : Type*) where
  gaussianSplit : UnnormalizedGaussianKLSplit
  logLift : OperatorLogBregmanLift Op
  kernelExpansion : OperatorKLExponentialSecondOrderPacket
  bkmHessian : OperatorBKMHessianPacket Op
  fierz : FierzSpinTwoExtractionPacket Op
  superVolume : TypeIIIOperatorSupervolumePacket Op
  kernelDivergence_matches_gaussianKL :
    kernelExpansion.divergence = gaussianSplit.generalizedKL
  superVolume_bkm_matches :
    superVolume.bkm = bkmHessian

namespace OperatorKLBKMCapstone

/-- The Gaussian unnormalized KL split is nonnegative. -/
theorem gaussianKL_nonneg
    {Op : Type*} (C : OperatorKLBKMCapstone Op) :
    0 ≤ C.gaussianSplit.generalizedKL :=
  C.gaussianSplit.generalizedKL_nonneg

/-- The exponential kernel expands to second order in the lifted KL divergence. -/
theorem kernel_secondOrder_expansion
    {Op : Type*} (C : OperatorKLBKMCapstone Op) :
    C.kernelExpansion.expKernelReadout =
      C.kernelExpansion.secondOrderTaylor + C.kernelExpansion.remainder :=
  C.kernelExpansion.expKernel_eq_secondOrder_add_remainder

/-- The operatorial Hessian is the BKM bilinear form on operator generators. -/
theorem operator_hessian_eq_bkm
    {Op : Type*} (C : OperatorKLBKMCapstone Op) (A B : Op) :
    C.bkmHessian.hessian A B = C.bkmHessian.bkm A B :=
  C.bkmHessian.hessian_eq_bkm_form A B

/-- The spin-2 linearized-gravity potential is the Fierz spin-two channel. -/
theorem linearizedGravityPotential_eq_spinTwo
    {Op : Type*} (C : OperatorKLBKMCapstone Op) (A B : Op) :
    C.fierz.linearizedGravityPotential A B = C.fierz.spinTwoChannel A B :=
  C.fierz.gravityPotential_eq_spinTwoChannel A B

/-- The Type III super-volume is expressed without a density-matrix trace. -/
theorem typeIII_superVolume_eq
    {Op : Type*} (C : OperatorKLBKMCapstone Op) :
    C.superVolume.superVolumeReadout =
      C.superVolume.logPfaffianReadout
        - (1 / 2 : ℝ) * C.superVolume.bkmLogBerezinianReadout :=
  C.superVolume.superVolume_eq_pfaffian_sub_half_bkmBerezinian

/--
Operator KL/BKM capstone:
the unnormalized Gaussian KL split is nonnegative, its exponential kernel has
the supplied second-order expansion, the operator Hessian is BKM, Fierz
extracts the spin-2 channel, and the Type III super-volume is the
Pfaffian/BKM-Berezinian readout.
-/
theorem operator_kl_bkm_capstone
    {Op : Type*} (C : OperatorKLBKMCapstone Op) (A B : Op) :
    0 ≤ C.gaussianSplit.generalizedKL
      ∧ C.kernelExpansion.expKernelReadout =
          C.kernelExpansion.secondOrderTaylor + C.kernelExpansion.remainder
      ∧ C.bkmHessian.hessian A B = C.bkmHessian.bkm A B
      ∧ C.fierz.linearizedGravityPotential A B = C.fierz.spinTwoChannel A B
      ∧ C.superVolume.superVolumeReadout =
          C.superVolume.logPfaffianReadout
            - (1 / 2 : ℝ) * C.superVolume.bkmLogBerezinianReadout := by
  exact ⟨C.gaussianKL_nonneg,
    C.kernel_secondOrder_expansion,
    C.operator_hessian_eq_bkm A B,
    C.linearizedGravityPotential_eq_spinTwo A B,
    C.typeIII_superVolume_eq⟩

end OperatorKLBKMCapstone

end InfoGeometry.SuperMetriplectic
