import Mathlib
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.ZetaStandardRealizations
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SouriauTomitaZetaCenteredBridge

Honest bridge file tying together four tracked surfaces already owned by the repo:

1. centered zeta symmetry coordinates,
2. centered completed-`Ξ` parity,
3. Souriau negative-log Radon-Nikodym / modular-potential readback,
4. the Souriau/Tomita logarithmic modular generator.

Scope discipline:
- This file formalizes only algebraic / definitional consequences of tracked owner files.
- It does NOT claim that the untracked `Arithmetic/ZetaSymmetryAdaptedDefinitions.lean`
  currently compiles.
- It does NOT prove analytic continuation, Euler products, Ramanujan's full
  odd-zeta transform, or an operator-level theorem `exp (-s H) = exp (-H/2) exp (-u H) exp (-iv H)`.
- The Ramanujan/Lambert lane is kept witness-gated on purpose.
-/

noncomputable section

namespace SouriauTomitaZetaCenteredBridge

open Complex
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Canonical.ZetaStandardRealizations
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Canonical.SouriauTomitaModularFlowBridge

abbrev CenteredChart :=
  InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-- Centered complex parameter `s = 1/2 + u + iv`. -/
def centeredParameter (x : CenteredChart) : ℂ :=
  ((x.u + (1 / 2 : ℝ) : ℝ) : ℂ) + (x.v : ℂ) * Complex.I

@[simp] theorem centeredParameter_re (x : CenteredChart) :
    (centeredParameter x).re = x.u + (1 / 2 : ℝ) := by
  simp [centeredParameter]

@[simp] theorem centeredParameter_im (x : CenteredChart) :
    (centeredParameter x).im = x.v := by
  simp [centeredParameter]

/-- Critical-line predicate in centered coordinates. -/
def centeredCriticalLine (x : CenteredChart) : Prop :=
  x.u = 0

/-- The half-density / critical-line channel. -/
def criticalLineWeight (L : ℝ) : ℂ :=
  (Real.exp (-(1 / 2 : ℝ) * L) : ℂ)

/-- The scale-normal channel. -/
def scaleEnvelope (L u : ℝ) : ℂ :=
  (Real.exp (-u * L) : ℂ)

/-- The tangential phase / modular-time channel. -/
def phaseWave (L v : ℝ) : ℂ :=
  Complex.exp (-(v * L : ℝ) * Complex.I)

/-- Scalar centered Dirichlet mode in the `s = 1/2 + u + iv` chart. -/
def centeredDirichletMode (L : ℝ) (x : CenteredChart) : ℂ :=
  criticalLineWeight L * scaleEnvelope L x.u * phaseWave L x.v

theorem centeredDirichletMode_eq_three_channels (L : ℝ) (x : CenteredChart) :
    centeredDirichletMode L x =
      criticalLineWeight L * scaleEnvelope L x.u * phaseWave L x.v :=
  rfl

@[simp] theorem scaleEnvelope_zero (L : ℝ) :
    scaleEnvelope L 0 = 1 := by
  simp [scaleEnvelope]

@[simp] theorem phaseWave_zero (L : ℝ) :
    phaseWave L 0 = 1 := by
  simp [phaseWave]

/-- On the centered critical line, the dissipative channel collapses to `1`. -/
theorem scaleEnvelope_eq_one_of_centeredCriticalLine
    {L : ℝ} {x : CenteredChart} (hx : centeredCriticalLine x) :
    scaleEnvelope L x.u = 1 := by
  rw [centeredCriticalLine] at hx
  rw [hx]
  exact scaleEnvelope_zero L

/-- Critical-line readback: only the half-density and phase channels remain. -/
theorem centeredDirichletMode_of_centeredCriticalLine
    {L : ℝ} {x : CenteredChart} (hx : centeredCriticalLine x) :
    centeredDirichletMode L x = criticalLineWeight L * phaseWave L x.v := by
  calc
    centeredDirichletMode L x
        = criticalLineWeight L * scaleEnvelope L x.u * phaseWave L x.v := rfl
    _ = criticalLineWeight L * 1 * phaseWave L x.v := by
          rw [scaleEnvelope_eq_one_of_centeredCriticalLine hx]
    _ = criticalLineWeight L * phaseWave L x.v := by ring

/-- `J`-even projector for centered `Ξ`-style scalar readouts. -/
def JEvenProjection (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((1 / 2 : ℂ) * (F z + F (-z)))

/-- `J`-odd projector for centered `Ξ`-style scalar readouts. -/
def JOddProjection (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((1 / 2 : ℂ) * (F z - F (-z)))

theorem JOddProjection_eq_zero_of_even
    (F : ℂ → ℂ) (hF : ∀ z : ℂ, F z = F (-z)) (z : ℂ) :
    JOddProjection F z = 0 := by
  unfold JOddProjection
  rw [hF z]
  ring

theorem JEvenProjection_eq_of_even
    (F : ℂ → ℂ) (hF : ∀ z : ℂ, F z = F (-z)) (z : ℂ) :
    JEvenProjection F z = F z := by
  unfold JEvenProjection
  rw [hF z]
  ring

/-- Tracked centered completed-`Ξ` is `J`-even, hence its `J`-odd projection vanishes. -/
theorem centeredXi_JOddProjection_eq_zero
    (X : CompletedXiRealization) (z : ℂ) :
    JOddProjection X.centeredXi z = 0 := by
  exact JOddProjection_eq_zero_of_even X.centeredXi (fun w => X.centeredXi_even w) z

/-- The `J`-even projector fixes centered completed `Ξ`. -/
theorem centeredXi_JEvenProjection_eq_self
    (X : CompletedXiRealization) (z : ℂ) :
    JEvenProjection X.centeredXi z = X.centeredXi z := by
  exact JEvenProjection_eq_of_even X.centeredXi (fun w => X.centeredXi_even w) z

section SouriauReadback

variable {State LieAlgebra LieDual : Type*}

/-- The Souriau modular potential reads back as the moment pairing plus Massieu shift. -/
@[rep_depth thermo]
theorem modularPotential_eq_pairing_add_partitionPotential
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) (x : State) :
    D.modularPotential x =
      D.souriau.pairing (D.souriau.momentMap x) D.souriau.beta +
        D.souriau.partitionPotential := by
  rw [D.modularPotential_eq_K_beta_add_Phi, D.souriau.K_beta_eq_pairing x]

/-- Entropy is the expectation of the pairing-plus-shift modular potential. -/
@[rep_depth thermo]
theorem entropy_eq_expectation_pairing_add_partitionPotential
    (D : SouriauNegativeLogRNDerivative State LieAlgebra LieDual) :
    D.entropy =
      D.expectationBeta
        (fun x =>
          D.souriau.pairing (D.souriau.momentMap x) D.souriau.beta +
            D.souriau.partitionPotential) := by
  rw [D.entropy_eq_expectation_modularPotential]
  congr 1
  funext x
  exact modularPotential_eq_pairing_add_partitionPotential D x

end SouriauReadback

section TomitaReadback

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Symmetry : Type v}

/-- In the tracked bridge, Tomita logarithm data is exactly the Souriau thermal moment. -/
@[rep_depth operator]
theorem tomita_deltaLog_eq_souriau_moment_geometricTemperature
    (C : SouriauTomitaLogContext (H := H) (Symmetry := Symmetry)) :
    C.toRealModularLogData =
      C.souriauMoment.momentOperator C.souriauMoment.geometricTemperature := by
  rw [C.tomita_deltaLog_eq_thermalGenerator,
    C.souriauModularGenerator_eq_moment_geometricTemperature]

end TomitaReadback

/--
Witness-gated Ramanujan/Lambert socket.

This is intentionally a socket, not an analytic theorem: the tracked repo already
uses the same discipline for Ramanujan's odd-zeta transform.
-/
def RamanujanLambertTransform
    (oddZetaReadout lambertSeriesSide bernoulliCorrectionSide : ℕ → ℂ) : Prop :=
  ∀ m, oddZetaReadout m = lambertSeriesSide m + bernoulliCorrectionSide m

structure RamanujanLambertSocket where
  oddZetaReadout : ℕ → ℂ
  lambertSeriesSide : ℕ → ℂ
  bernoulliCorrectionSide : ℕ → ℂ
  transform :
    RamanujanLambertTransform oddZetaReadout lambertSeriesSide bernoulliCorrectionSide

namespace RamanujanLambertSocket

theorem oddZeta_eq_lambert_plus_bernoulli
    (R : RamanujanLambertSocket) (m : ℕ) :
    R.oddZetaReadout m = R.lambertSeriesSide m + R.bernoulliCorrectionSide m :=
  R.transform m

end RamanujanLambertSocket

end SouriauTomitaZetaCenteredBridge
