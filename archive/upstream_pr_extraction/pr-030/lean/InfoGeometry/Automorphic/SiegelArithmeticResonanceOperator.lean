/-
InfoGeometry/Automorphic/SiegelArithmeticResonanceOperator.lean

Siegel operator as an arithmetic-resonance filter.

The analytic Siegel operator is already owned by `SiegelResonance.lean` as the
boundary/constant-term map

  𝔖_P : Bulk → Boundary.

Given a split Eisenstein section, the repository has the constructive projector

  ℜ_P = I - ℰ_P ∘ 𝔖_P,

which kills the Siegel boundary component and lands exactly in `ker 𝔖_P`.

This file adds the arithmetic-resonance interpretation layer:

* boundary/Eisenstein range = removable scattering/noise component;
* cuspidal projector = pure internal arithmetic resonance component;
* finite zeta-trace readouts may be attached as proof-carrying calibration
  data.

It does not claim the Riemann hypothesis, analytic continuation, an actual
E8 lattice theorem, or a full Siegel modular-form construction.
-/

import InfoGeometry.Automorphic.SiegelResonance
import InfoGeometry.Arithmetic.ZetaTraceSpecialization

noncomputable section

namespace InfoGeometry.Automorphic.SiegelArithmeticResonanceOperator

open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Arithmetic.ZetaTraceSpecialization
open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.SouriauThermalEvaluation
open scoped BigOperators

universe uBulk uBoundary uReadout

/-! ## 1. Siegel filter packet -/

/-!
The arithmetic resonance filter is the existing Siegel/Eisenstein owner
itself.  The same split exact sequence supplies the boundary/Eisenstein and
cuspidal components; the former one-field witness packet added no mathematical
content.
-/
abbrev SiegelArithmeticResonanceFilter
    (Bulk : Type uBulk) (Boundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary] :=
  SiegelEisensteinWitness Bulk Boundary

namespace SiegelArithmeticResonanceFilter

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable (F : SiegelArithmeticResonanceFilter Bulk Boundary)

/-- The Siegel boundary operator. -/
def siegelOperator : Bulk →ₗ[ℝ] Boundary :=
  F.siegel

/-- Boundary/Eisenstein component, interpreted as removable boundary noise. -/
def boundaryNoise : Bulk →ₗ[ℝ] Bulk :=
  F.boundaryProjector

/-- Pure arithmetic resonance component. -/
def pureResonance : Bulk →ₗ[ℝ] Bulk :=
  F.cuspidalProjector

/-- The pure resonance component is killed by the Siegel operator. -/
theorem siegel_pureResonance_eq_zero
    (X : Bulk) :
    F.siegelOperator (F.pureResonance X) = 0 :=
  F.siegel_cuspidalProjector_apply X

/-- The pure resonance component lies in the kernel of the Siegel operator. -/
theorem pureResonance_mem_kernel
    (X : Bulk) :
    F.pureResonance X ∈ LinearMap.ker F.siegelOperator := by
  rw [LinearMap.mem_ker]
  exact F.siegel_pureResonance_eq_zero X

/-- Boundary noise has no pure resonance component. -/
theorem pureResonance_boundaryNoise_eq_zero
    (X : Bulk) :
    F.pureResonance (F.boundaryNoise X) = 0 := by
  have h :=
    congrArg (fun T : Bulk →ₗ[ℝ] Bulk => T X)
      F.cuspidalProjector_mul_boundaryProjector
  simpa [pureResonance, boundaryNoise] using h

/-- The boundary component is unchanged by the Siegel operator. -/
theorem siegel_boundaryNoise_eq_siegel
    (X : Bulk) :
    F.siegelOperator (F.boundaryNoise X) = F.siegelOperator X := by
  have h :=
    congrArg (fun T : Bulk →ₗ[ℝ] Boundary => T X)
      F.siegel_comp_boundaryProjector
  simpa [siegelOperator, boundaryNoise, LinearMap.comp_apply] using h

/--
Every bulk state decomposes into boundary noise plus pure resonance.
-/
theorem boundaryNoise_add_pureResonance
    (X : Bulk) :
    F.boundaryNoise X + F.pureResonance X = X := by
  have h :=
    congrArg (fun T : Bulk →ₗ[ℝ] Bulk => T X)
      F.projector_sum
  simpa [boundaryNoise, pureResonance, LinearMap.add_apply] using h

/--
The pure resonance projector is idempotent.
-/
theorem pureResonance_idempotent
    (X : Bulk) :
    F.pureResonance (F.pureResonance X) = F.pureResonance X := by
  have h :=
    congrArg (fun T : Bulk →ₗ[ℝ] Bulk => T X)
      F.cuspidalProjector_idempotent
  simpa [pureResonance] using h

end SiegelArithmeticResonanceFilter

/-! ## 2. Arithmetic readout calibration -/

/--
Arithmetic readout attached to a Siegel filter.

`rawReadout` measures the original bulk state, while `resonanceReadout`
measures the purified cuspidal component.  The calibration law says that the
resonance readout is exactly the raw readout after applying the Siegel
resonance projector.
-/
structure SiegelArithmeticReadoutCalibration
    (Bulk : Type uBulk) (Boundary : Type uBoundary) (Readout : Type uReadout)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    [AddCommGroup Readout] [Module ℝ Readout]
    (F : SiegelArithmeticResonanceFilter Bulk Boundary) where
  /-- Raw arithmetic readout on the bulk state. -/
  rawReadout : Bulk →ₗ[ℝ] Readout

  /-- Purified arithmetic readout after the Siegel filter. -/
  resonanceReadout : Bulk →ₗ[ℝ] Readout

  /-- The purified readout is the raw readout of the pure resonance component. -/
  resonanceReadout_eq_raw_pure :
    resonanceReadout = rawReadout.comp F.pureResonance

namespace SiegelArithmeticReadoutCalibration

variable {Bulk : Type uBulk} {Boundary : Type uBoundary} {Readout : Type uReadout}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable [AddCommGroup Readout] [Module ℝ Readout]
variable {F : SiegelArithmeticResonanceFilter Bulk Boundary}
variable (C : SiegelArithmeticReadoutCalibration Bulk Boundary Readout F)

/-- Pointwise purified readout law. -/
theorem resonanceReadout_apply
    (X : Bulk) :
    C.resonanceReadout X = C.rawReadout (F.pureResonance X) := by
  have h := congrArg (fun T : Bulk →ₗ[ℝ] Readout => T X) C.resonanceReadout_eq_raw_pure
  simpa [LinearMap.comp_apply] using h

/-- Boundary noise contributes zero to the purified readout. -/
theorem resonanceReadout_boundaryNoise_eq_zero
    (X : Bulk) :
    C.resonanceReadout (F.boundaryNoise X) = 0 := by
  rw [C.resonanceReadout_apply]
  rw [F.pureResonance_boundaryNoise_eq_zero]
  exact map_zero C.rawReadout

end SiegelArithmeticReadoutCalibration

/-! ## 3. Finite zeta-trace calibration socket -/

/--
Finite zeta-trace calibration for a Siegel-purified arithmetic state.

The finite zeta-trace side is deliberately finite/cutoff: no infinite product,
analytic continuation, or Riemann-zero theorem is asserted here.
-/
structure SiegelZetaTraceCalibration
    (Bulk : Type uBulk) (Boundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (L : FormalPrimeRootLattice)
    (F : SiegelArithmeticResonanceFilter Bulk Boundary) where
  /-- Finite prime/root thermal evaluation. -/
  evaluation : SouriauThermalEvaluation L

  /-- Real-valued arithmetic amplitude on bulk states. -/
  arithmeticAmplitude : Bulk →ₗ[ℝ] ℝ

  /-- Distinguished bulk state being filtered. -/
  bulkState : Bulk

  /--
  The Siegel-purified arithmetic amplitude agrees with the finite zeta
  supertrace readout.
  -/
  pure_amplitude_eq_zeta_supertrace :
    arithmeticAmplitude (F.pureResonance bulkState)
      = finiteZetaTraceSupertrace evaluation

namespace SiegelZetaTraceCalibration

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable {L : FormalPrimeRootLattice}
variable {F : SiegelArithmeticResonanceFilter Bulk Boundary}
variable (Z : SiegelZetaTraceCalibration Bulk Boundary L F)

/-- The purified arithmetic amplitude is the finite zeta supertrace. -/
theorem pure_amplitude_eq_supertrace :
    Z.arithmeticAmplitude (F.pureResonance Z.bulkState)
      = finiteZetaTraceSupertrace Z.evaluation :=
  Z.pure_amplitude_eq_zeta_supertrace

/-- The purified arithmetic amplitude is also the finite Euler/Weyl denominator. -/
theorem pure_amplitude_eq_denominator :
    Z.arithmeticAmplitude (F.pureResonance Z.bulkState)
      = finiteZetaTraceDenominator Z.evaluation := by
  rw [Z.pure_amplitude_eq_supertrace]
  exact primeFockSupertrace_eq_finiteEulerDenominator Z.evaluation

end SiegelZetaTraceCalibration

/-! ## 4. Jordan boundary norm reduction -/

/--
Jordan-Siegel norm reduction.

This is the norm-level abstraction of

`N₃([[A,0],[0,t]]) / t = N₂(A)`.

The analytic limit and split-octonionic construction are not proved here.
Instead, a concrete model supplies the boundary lift and the exact
renormalized norm law.
-/
structure JordanSiegelNormReduction
    (Cubic Boundary : Type*) where
  /-- Cubic/Jordan bulk norm, morally `N₃`. -/
  cubicNorm : Cubic → ℝ

  /-- Boundary quadratic norm, morally `N₂`. -/
  boundaryNorm : Boundary → ℝ

  /-- Boundary embedding along the diverging cusp parameter. -/
  boundaryLift : Boundary → ℝ → Cubic

  /-- Exact renormalized norm law for the supplied boundary model. -/
  cubicNorm_boundaryLift :
    ∀ A : Boundary × ℝ,
      cubicNorm (boundaryLift A.1 A.2) = A.2 * boundaryNorm A.1

namespace JordanSiegelNormReduction

variable {Cubic Boundary : Type*}
variable (J : JordanSiegelNormReduction Cubic Boundary)

/-- Renormalized cubic norm after dividing by the cusp scale. -/
def renormalizedNorm
    (A : Boundary)
    (t : ℝ) : ℝ :=
  t⁻¹ * J.cubicNorm (J.boundaryLift A t)

/--
The supplied Jordan-Siegel norm law: `N₃(boundaryLift A t) = t * N₂(A)`.
-/
theorem cubicNorm_boundaryLift_eq
    (A : Boundary)
    (t : ℝ) :
    J.cubicNorm (J.boundaryLift A t) = t * J.boundaryNorm A := by
  simpa using J.cubicNorm_boundaryLift (A, t)

/--
For nonzero cusp scale, the renormalized cubic norm is the boundary norm.
-/
theorem renormalizedNorm_eq_boundaryNorm
    (A : Boundary)
    {t : ℝ}
    (ht : t ≠ 0) :
    J.renormalizedNorm A t = J.boundaryNorm A := by
  dsimp [renormalizedNorm]
  rw [J.cubicNorm_boundaryLift_eq A t]
  field_simp [ht]

end JordanSiegelNormReduction

/-! ## 5. Jordan potential reduction -/

/--
Jordan-Siegel potential reduction.

This is the potential-level abstraction of

`-log |N₃| + log t → -log |N₂|`.

The limit and logarithmic regularity hypotheses remain model-dependent; the
renormalized boundary potential is supplied with an explicit equality to the
quadratic boundary potential.
-/
structure JordanSiegelPotentialReduction
    (Cubic Boundary : Type*) where
  /-- Bulk cubic potential, morally `-log |N₃|`. -/
  cubicPotential : Cubic → ℝ

  /-- Boundary quadratic potential, morally `-log |N₂|`. -/
  boundaryPotential : Boundary → ℝ

  /-- Boundary embedding along the diverging cusp parameter. -/
  boundaryLift : Boundary → ℝ → Cubic

  /-- Renormalized boundary potential after subtracting the divergent scale. -/
  renormalizedPotential : Boundary → ℝ

  /-- The renormalized potential equals the boundary quadratic potential. -/
  renormalizedPotential_eq_boundary :
    ∀ A : Boundary,
      renormalizedPotential A = boundaryPotential A

namespace JordanSiegelPotentialReduction

variable {Cubic Boundary : Type*}
variable (J : JordanSiegelPotentialReduction Cubic Boundary)

/--
Jordan-Siegel potential extraction gives the boundary quadratic potential.
-/
theorem siegelPotential_eq_boundaryPotential
    (A : Boundary) :
    J.renormalizedPotential A = J.boundaryPotential A :=
  J.renormalizedPotential_eq_boundary A

end JordanSiegelPotentialReduction

/-! ## 6. Exceptional constant-term layer -/

/--
Exceptional Siegel constant-term layer.

This identifies a parabolic constant-term operator with the abstract Siegel
operator already carried by `SiegelArithmeticResonanceFilter`.

Group names such as `E₈(8)`, `E₇(7)`, and `E₆(6)` remain calibration labels;
no exceptional classification theorem is asserted in this socket.
-/
structure ExceptionalSiegelConstantTermLayer
    (Bulk : Type uBulk) (Boundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (F : SiegelArithmeticResonanceFilter Bulk Boundary) where
  /-- Model-specific parabolic constant-term operator. -/
  constantTerm : Bulk →ₗ[ℝ] Boundary

  /-- The constant-term operator is the chosen Siegel operator. -/
  constantTerm_eq_siegel :
    constantTerm = F.siegelOperator

namespace ExceptionalSiegelConstantTermLayer

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable {F : SiegelArithmeticResonanceFilter Bulk Boundary}
variable (E : ExceptionalSiegelConstantTermLayer Bulk Boundary F)

/-- Pointwise constant-term/Siegel equality. -/
theorem constantTerm_apply
    (X : Bulk) :
    E.constantTerm X = F.siegelOperator X := by
  rw [E.constantTerm_eq_siegel]

/-- The exceptional constant term kills the pure resonance component. -/
theorem constantTerm_pureResonance_eq_zero
    (X : Bulk) :
    E.constantTerm (F.pureResonance X) = 0 := by
  rw [E.constantTerm_apply]
  exact F.siegel_pureResonance_eq_zero X

end ExceptionalSiegelConstantTermLayer

/-! ## 7. Zeta sign convention and primitive-prime filter -/

/--
Zeta surprisal sign convention.

`eulerLog` represents `Σ_p log(1 - p^{-s})`.
`logZeta` represents `log ζ(s)`.

The convention stored here is

`log ζ(s) = - eulerLog(s)`.

Thus the positive zeta surprisal is `log ζ(s)`, while `eulerLog` is the
opposite-sign free-energy convention.
-/
structure ZetaSurprisalSignConvention
    (Parameter : Type*) where
  eulerLog : Parameter → ℂ
  logZeta : Parameter → ℂ
  surprisal : Parameter → ℂ
  freeEnergy : Parameter → ℂ
  logZeta_eq_neg_eulerLog :
    ∀ s : Parameter,
      logZeta s = - eulerLog s
  surprisal_eq_logZeta :
    ∀ s : Parameter,
      surprisal s = logZeta s
  freeEnergy_eq_eulerLog :
    ∀ s : Parameter,
      freeEnergy s = eulerLog s

namespace ZetaSurprisalSignConvention

variable {Parameter : Type*}
variable (Z : ZetaSurprisalSignConvention Parameter)

/-- The Euler-log free-energy convention is the negative zeta surprisal. -/
theorem freeEnergy_eq_neg_surprisal
    (s : Parameter) :
    Z.freeEnergy s = - Z.surprisal s := by
  rw [Z.freeEnergy_eq_eulerLog, Z.surprisal_eq_logZeta, Z.logZeta_eq_neg_eulerLog]
  simp

end ZetaSurprisalSignConvention

/--
Finite Möbius/prime-zeta filter.

This is the finite/cutoff form of the primitive-prime extraction

`P(s) = Σ_m μ(m)/m · log ζ(ms)`.

The coefficient system is supplied by the model.  This file does not assert
the analytic infinite-series theorem.
-/
structure FiniteMobiusPrimeFilter
    (Signal : Type*) where
  /-- Finite cutoff of positive integer modes. -/
  modes : Finset ℕ

  /-- Mode coefficient, morally `μ(m)/m`. -/
  coefficient : ℕ → ℂ

  /-- Log-zeta readout at mode `m`. -/
  logZetaMode : ℕ → Signal → ℂ

  /-- Primitive-prime readout. -/
  primeResonance : Signal → ℂ

  /-- Finite Möbius inversion law. -/
  primeResonance_eq_mobius_sum :
    ∀ X : Signal,
      primeResonance X =
        ∑ m ∈ modes, coefficient m * logZetaMode m X

namespace FiniteMobiusPrimeFilter

variable {Signal : Type*}
variable (M : FiniteMobiusPrimeFilter Signal)

/-- The primitive-prime readout is the finite Möbius-filtered log-zeta readout. -/
theorem primeResonance_eq_filtered_logZeta
    (X : Signal) :
    M.primeResonance X =
      ∑ m ∈ M.modes, M.coefficient m * M.logZetaMode m X :=
  M.primeResonance_eq_mobius_sum X

end FiniteMobiusPrimeFilter

/-! ## 8. Three-layer Siegel resonance operator -/

/--
Three-layer Siegel resonance operator.

The pipeline is:

1. Jordan-Siegel potential reduction: cubic norm potential to quadratic
   boundary potential;
2. automorphic Siegel constant term: boundary/constant mode extraction;
3. Möbius prime filter: primitive prime harmonic extraction.

The composition is proof-carrying and deliberately finite/cutoff on the prime
filter side.
-/
structure ThreeLayerSiegelResonanceOperator
    (Cubic JordanBoundary : Type*)
    (Bulk : Type uBulk) (AutoBoundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup AutoBoundary] [Module ℝ AutoBoundary] where
  /-- Jordan norm-level boundary reduction. -/
  jordanNorm : JordanSiegelNormReduction Cubic JordanBoundary

  /-- Jordan potential-level boundary reduction. -/
  jordanPotential : JordanSiegelPotentialReduction Cubic JordanBoundary

  /-- Map from Jordan boundary data to the automorphic bulk model. -/
  boundaryToBulk : JordanBoundary → Bulk

  /-- Automorphic Siegel filter. -/
  automorphic : SiegelArithmeticResonanceFilter Bulk AutoBoundary

  /-- Exceptional constant-term interpretation of the same Siegel operator. -/
  exceptional :
    ExceptionalSiegelConstantTermLayer Bulk AutoBoundary automorphic

  /-- Primitive-prime filter on the automorphic bulk signal. -/
  primeFilter : FiniteMobiusPrimeFilter Bulk

namespace ThreeLayerSiegelResonanceOperator

variable
    {Cubic JordanBoundary : Type*}
    {Bulk : Type uBulk} {AutoBoundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup AutoBoundary] [Module ℝ AutoBoundary]

variable (S : ThreeLayerSiegelResonanceOperator Cubic JordanBoundary Bulk AutoBoundary)

/-- Automorphic signal obtained from the Jordan boundary input. -/
def automorphicSignal
    (A : JordanBoundary) : Bulk :=
  S.automorphic.pureResonance (S.boundaryToBulk A)

/-- Final primitive-prime resonance readout. -/
def primitivePrimeReadout
    (A : JordanBoundary) : ℂ :=
  S.primeFilter.primeResonance (S.automorphicSignal A)

/-- The final readout is the Möbius-filtered log-zeta readout of the Siegel signal. -/
theorem primitivePrimeReadout_eq_mobius_filtered_logZeta
    (A : JordanBoundary) :
    S.primitivePrimeReadout A =
      ∑ m ∈ S.primeFilter.modes,
        S.primeFilter.coefficient m *
          S.primeFilter.logZetaMode m (S.automorphicSignal A) :=
  S.primeFilter.primeResonance_eq_filtered_logZeta (S.automorphicSignal A)

/-- The exceptional constant term kills the automorphic pure-resonance signal. -/
theorem exceptional_constantTerm_automorphicSignal_eq_zero
    (A : JordanBoundary) :
    S.exceptional.constantTerm (S.automorphicSignal A) = 0 :=
  S.exceptional.constantTerm_pureResonance_eq_zero (S.boundaryToBulk A)

end ThreeLayerSiegelResonanceOperator

/-! ## 9. Owner targets -/

/-- Owner target for installing a Siegel arithmetic resonance filter. -/
def SiegelArithmeticResonanceFilterOwnerTarget
    (Bulk : Type uBulk) (Boundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary] : Prop :=
  Nonempty (SiegelArithmeticResonanceFilter Bulk Boundary)

/-- Owner target for attaching a readout to a Siegel arithmetic resonance filter. -/
def SiegelArithmeticReadoutOwnerTarget
    (Bulk : Type uBulk) (Boundary : Type uBoundary) (Readout : Type uReadout)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    [AddCommGroup Readout] [Module ℝ Readout]
    (F : SiegelArithmeticResonanceFilter Bulk Boundary) : Prop :=
  Nonempty (SiegelArithmeticReadoutCalibration Bulk Boundary Readout F)

/-- Owner target for finite zeta-trace calibration of a Siegel-purified state. -/
def SiegelZetaTraceCalibrationOwnerTarget
    (Bulk : Type uBulk) (Boundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (L : FormalPrimeRootLattice)
    (F : SiegelArithmeticResonanceFilter Bulk Boundary) : Prop :=
  Nonempty (SiegelZetaTraceCalibration Bulk Boundary L F)

/-- Owner target for a Jordan-Siegel norm reduction. -/
def JordanSiegelNormReductionOwnerTarget
    (Cubic Boundary : Type*) : Prop :=
  Nonempty (JordanSiegelNormReduction Cubic Boundary)

/-- Owner target for the three-layer Siegel resonance operator. -/
def ThreeLayerSiegelResonanceOperatorOwnerTarget
    (Cubic JordanBoundary : Type*)
    (Bulk : Type uBulk) (AutoBoundary : Type uBoundary)
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup AutoBoundary] [Module ℝ AutoBoundary] : Prop :=
  Nonempty (ThreeLayerSiegelResonanceOperator Cubic JordanBoundary Bulk AutoBoundary)

end InfoGeometry.Automorphic.SiegelArithmeticResonanceOperator
