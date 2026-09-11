import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.WeylGaugeOperatorLift
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Topology.TwistedCohomologyWeyl
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Abel

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.BerryPhase

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.WeylGaugeOperatorLift
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Quantum.GeometricQuantumTensor
open scoped InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Real doubled super-Hestenes-Kaehler datum on the canonical carrier.

This is the explicit geometric package behind the repository's real doubled QGT
reading:

- `metric` is the symmetric transport/variance sector;
- `phase` is the `(Jε)`-sensitive Berry/symplectic sector;
- `J`, `ε`, and `K = J ∘ ε` are the concrete split-`Cl(1,1)` axes;
- the compatibility law is the Hestenes-Kaehler relation
  `phase u v = metric (K u) v`.
-/
structure SuperHestenesKaehlerDatum where
  metric : LinearMap.BilinForm ℝ H₂
  phase : LinearMap.BilinForm ℝ H₂
  J : EndH
  epsilon : EndH
  K : EndH
  metric_symm : metric.IsSymm
  phase_alt : phase.IsAlt
  compat : ∀ u v, phase u v = metric (K u) v
  J_sq : J.comp J = ContinuousLinearMap.id ℝ H₂
  epsilon_sq : epsilon.comp epsilon = ContinuousLinearMap.id ℝ H₂
  J_anticomm_epsilon : J.comp epsilon = -(epsilon.comp J)
  K_eq_J_comp_epsilon : K = J.comp epsilon
  K_eq_modularComplexI : K = InfoGeometry.Krein.clockAxis (E := E)
  K_sq_neg : K.comp K = -(ContinuousLinearMap.id ℝ H₂)

namespace SuperHestenesKaehlerDatum

@[simp] theorem K_eq_complex_i
    (S : SuperHestenesKaehlerDatum (E := E)) :
    S.K = InfoGeometry.Krein.clockAxis (E := E) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    S.K_eq_modularComplexI

/-- Recover the QGT owner surface from the explicit Hestenes-Kaehler datum. -/
noncomputable def toQGT
    (S : SuperHestenesKaehlerDatum (E := E)) : QGT E where
  metric := S.metric
  berry := S.phase
  metric_symm := S.metric_symm
  berry_alt := S.phase_alt
  compat := by
    intro u v
    simpa [S.K_eq_modularComplexI] using S.compat u v

@[simp] theorem toQGT_compat_complex_i
    (S : SuperHestenesKaehlerDatum (E := E)) (u v : H₂) :
    S.toQGT.berry u v = S.toQGT.metric (InfoGeometry.Krein.clockAxis (E := E) u) v := by
  exact S.toQGT.compat u v

/-- Canonical constructor from the maintained real doubled QGT owner surface. -/
noncomputable def ofQGT
    (Q : QGT E) : SuperHestenesKaehlerDatum (E := E) where
  metric := Q.metric
  phase := Q.berry
  J := InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)
  epsilon := InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := E)
  K := InfoGeometry.Krein.clockAxis (E := E)
  metric_symm := Q.metric_symm
  phase_alt := Q.berry_alt
  compat := Q.compat
  J_sq := InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_sq (E := E)
  epsilon_sq := InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_sq (E := E)
  J_anticomm_epsilon :=
    InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_anticommutes_modularSign (E := E)
  K_eq_J_comp_epsilon := rfl
  K_eq_modularComplexI := rfl
  K_sq_neg := InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_sq (E := E)

@[simp] theorem ofQGT_K_eq_complex_i
    (Q : QGT E) :
    (ofQGT (E := E) Q).K = InfoGeometry.Krein.clockAxis (E := E) := by
  change InfoGeometry.Krein.clockAxis (E := E) =
      InfoGeometry.Krein.clockAxis (E := E)
  exact InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := E)

@[simp] theorem toQGT_metric
    (S : SuperHestenesKaehlerDatum (E := E)) :
    S.toQGT.metric = S.metric := rfl

@[simp] theorem toQGT_berry
    (S : SuperHestenesKaehlerDatum (E := E)) :
    S.toQGT.berry = S.phase := rfl

@[simp] theorem ofQGT_metric
    (Q : QGT E) :
    (ofQGT (E := E) Q).metric = Q.metric := rfl

@[simp] theorem ofQGT_phase
    (Q : QGT E) :
    (ofQGT (E := E) Q).phase = Q.berry := rfl

@[simp] theorem ofQGT_J
    (Q : QGT E) :
    (ofQGT (E := E) Q).J =
      InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) := rfl

@[simp] theorem ofQGT_J_eq_modular_j
    (Q : QGT E) :
    (ofQGT (E := E) Q).J =
      InfoGeometry.Krein.modular_j (E := E) := by
  exact ofQGT_J (E := E) Q

@[simp] theorem ofQGT_epsilon
    (Q : QGT E) :
    (ofQGT (E := E) Q).epsilon =
      InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := E) := rfl

@[simp] theorem ofQGT_epsilon_eq_spectral_epsilon
    (Q : QGT E) :
    (ofQGT (E := E) Q).epsilon =
      InfoGeometry.Krein.spectral_epsilon (E := E) := by
  exact ofQGT_epsilon (E := E) Q

@[simp] theorem ofQGT_K
    (Q : QGT E) :
    (ofQGT (E := E) Q).K =
      InfoGeometry.Krein.clockAxis (E := E) := rfl

/-- The native `ℤ₂` parity surface attached to the doubled super-Hestenes datum. -/
abbrev Parity :=
  InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity

/-- Canonical super-bracket on doubled endomorphisms carried by the datum. -/
noncomputable abbrev superBracket
    (p q : Parity) (A B : EndH) : EndH :=
  InfoGeometry.Canonical.BogoliubovFockSuper.fockSuperBracket p q A B

/-- Even-even commutator channel carried by the datum. -/
noncomputable abbrev commutator
    (A B : EndH) : EndH :=
  InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator A B

/-- Odd-odd anticommutator channel carried by the datum. -/
noncomputable abbrev anticommutator
    (A B : EndH) : EndH :=
  InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator A B

/-- The Hestenes phase grading induced by `K = Jε`. -/
inductive PhaseParity where
  | even
  | odd

/-- Predicate attaching the phase grading to an endomorphism. -/
def HasPhaseParity : PhaseParity → EndH → Prop
  | .even, A => IsPhaseLinear (E := E) A
  | .odd,  A => IsPhaseAntilinear (E := E) A

/--
The fermionic surface compatibility datum.
The super algebra branch is explicitly non-identical to the underlying Hestenes
metric geometry; it sits on top of it as either a projector-super or a CAR surface.
-/
inductive FermionicSurface (aMinus aPlus : EndH) : Prop
  | projectorSuper :
      InfoGeometry.Canonical.BogoliubovFockSuper.IsProjectorSuperPair (E := E) aMinus aPlus
      → FermionicSurface aMinus aPlus
  | car :
      InfoGeometry.Canonical.BogoliubovFockSuper.IsCARPair (E := E) aMinus aPlus
      → FermionicSurface aMinus aPlus

/--
Real doubled bi-graded super-Hestenes datum.
This is the full reconciliation package carrying both the Hestenes phase grading
from `K = Jε` and the super/Fock grading from the `ℤ₂` bracket.
-/
structure BigradedSuperHestenesDatum
    extends SuperHestenesKaehlerDatum (E := E) where
  aMinus : EndH
  aPlus : EndH
  fermionic_surface : FermionicSurface aMinus aPlus
  J_phase_odd : HasPhaseParity (E := E) PhaseParity.odd J
  epsilon_phase_odd : HasPhaseParity (E := E) PhaseParity.odd epsilon
  K_phase_even : HasPhaseParity (E := E) PhaseParity.even K

/-- Canonical one-parameter Bogoliubov mixing boost generated by `J`. -/
noncomputable def JBoost
    (_S : SuperHestenesKaehlerDatum (E := E)) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.BogoliubovTransport.JBoost (E := E) t

/-- Canonical one-parameter sheet/signature boost generated by `ε`. -/
noncomputable def epsilonBoost
    (_S : SuperHestenesKaehlerDatum (E := E)) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost (E := E) t

/-- Canonical one-parameter Hestenes phase rotation generated by `K = Jε`. -/
noncomputable def KRotation
    (_S : SuperHestenesKaehlerDatum (E := E)) (t : ℝ) : EndH :=
  InfoGeometry.Canonical.BogoliubovTransport.KRotation (E := E) t

@[simp] theorem JBoost_zero
    (S : SuperHestenesKaehlerDatum (E := E)) :
    S.JBoost 0 = (1 : EndH) := by
  simp [JBoost]

@[simp] theorem epsilonBoost_zero
    (S : SuperHestenesKaehlerDatum (E := E)) :
    S.epsilonBoost 0 = (1 : EndH) := by
  simp [epsilonBoost]

@[simp] theorem KRotation_zero
    (S : SuperHestenesKaehlerDatum (E := E)) :
    S.KRotation 0 = (1 : EndH) := by
  simp [KRotation]

theorem JBoost_add
    (S : SuperHestenesKaehlerDatum (E := E))
    (s t : ℝ) :
    S.JBoost (s + t) = S.JBoost s * S.JBoost t := by
  simpa [JBoost] using
    (InfoGeometry.Canonical.BogoliubovTransport.JBoost_add (E := E) s t)

theorem epsilonBoost_add
    (S : SuperHestenesKaehlerDatum (E := E))
    (s t : ℝ) :
    S.epsilonBoost (s + t) = S.epsilonBoost s * S.epsilonBoost t := by
  simpa [epsilonBoost] using
    (InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_add (E := E) s t)

theorem KRotation_add
    (S : SuperHestenesKaehlerDatum (E := E))
    (s t : ℝ) :
    S.KRotation (s + t) = S.KRotation s * S.KRotation t := by
  simpa [KRotation] using
    (InfoGeometry.Canonical.BogoliubovTransport.KRotation_add (E := E) s t)

@[simp] theorem phase_eq_metric_of_K
    (S : SuperHestenesKaehlerDatum (E := E))
    (u v : H₂) :
    S.phase u v = S.metric (S.K u) v :=
  S.compat u v

end SuperHestenesKaehlerDatum

/--
Hestenes modular connection generator on doubled real space:
the transported operator channel induced by the relative modular axis `K = Jε`.
-/
noncomputable def hestenesModularConnectionGenerator
    (hMod A : EndH) : EndH :=
  relativeModularDeriv (E := E) hMod A

/--
Symmetric readout associated to the Hestenes modular connection generator.
-/
noncomputable def hestenesMetricTwoForm
    (hMod A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  GeometricQuantumTensor.metricOfOperator (E := E) (hestenesModularConnectionGenerator hMod A)

/--
Skew/phase readout associated to the Hestenes modular connection generator.
This is the real doubled-space Berry 2-form channel.
-/
noncomputable def hestenesBerryTwoForm
    (hMod A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  GeometricQuantumTensor.berryOfOperator (E := E) (hestenesModularConnectionGenerator hMod A)

@[simp] theorem hestenesBerryTwoForm_apply
    (hMod A : EndH) (u v : H₂) :
    hestenesBerryTwoForm hMod A u v
      =
    hestenesMetricTwoForm hMod A
      (InfoGeometry.Krein.clockAxis (E := E) u) v := by
  rfl

@[simp] theorem hestenesBerryTwoForm_apply_complex_i
    (hMod A : EndH) (u v : H₂) :
    hestenesBerryTwoForm hMod A u v
      =
    hestenesMetricTwoForm hMod A
      (InfoGeometry.Krein.clockAxis (E := E) u) v := by
  exact hestenesBerryTwoForm_apply (E := E) hMod A u v

/-- Chiral-sheet Berry-curvature readout on the doubled real space. -/
@[simp] theorem hestenesBerryTwoForm_chiralSheet_readout
    (hMod A : EndH) (u v : H₂) :
    hestenesBerryTwoForm hMod A u v
      =
    hestenesMetricTwoForm hMod A
      (InfoGeometry.Krein.clockAxis (E := E) u) v := by
  exact hestenesBerryTwoForm_apply_complex_i (E := E) hMod A u v

/--
Operator Maurer-Cartan curvature bracket on doubled real space.
-/
noncomputable def hestenesMaurerCartanCurvature
    (X Y : EndH) : EndH :=
  transportCommutator (E := E) X Y

theorem hestenesMaurerCartanCurvature_skew
    (X Y : EndH) :
    hestenesMaurerCartanCurvature X Y
      =
    -hestenesMaurerCartanCurvature Y X := by
  unfold hestenesMaurerCartanCurvature transportCommutator
  abel

/--
Generic Berry transport law under exponential conjugation:
the derivative at `t = 0` is the Berry readout of the Maurer-Cartan commutator.
-/
theorem deriv_berryOfOperator_expTransport_at_zero
    (X A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t)
          u v)
      0
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (hestenesMaurerCartanCurvature X A) u v := by
  simpa [GeometricQuantumTensor.berryOfOperator, hestenesMaurerCartanCurvature] using
    GeometricQuantumTensor.deriv_metricOfOperator_expTransport_at_zero
      (E := E) X A (InfoGeometry.Krein.clockAxis (E := E) u) v

/--
Infinitesimal phase-axis Berry transport law:
transporting the internal axis `K = Jε` under the generator `X` produces
exactly the Berry readout of the phase-axis response `[X, K]`.
-/
theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse
    (X : EndH) (u v : H₂) :
    deriv
      (fun t =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            X
            (InfoGeometry.Krein.clockAxis (E := E))
            t)
          u v)
      0
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (phaseAxisResponse (E := E) X) u v := by
  simpa [hestenesMaurerCartanCurvature, phaseAxisResponse, phaseAxisForce] using
    deriv_berryOfOperator_expTransport_at_zero
      (E := E)
      (X := X)
      (A := InfoGeometry.Krein.clockAxis (E := E))
      u v

theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse_complex_i
    (X : EndH) (u v : H₂) :
    deriv
      (fun t =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            X
            (InfoGeometry.Krein.clockAxis (E := E))
            t)
          u v)
      0
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (phaseAxisResponse (E := E) X) u v := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse
      (E := E) (X := X) u v

/--
Source-channel specialization of the infinitesimal phase-axis Berry transport
law for phase-antilinear generators.
-/
theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_two_smul_comp_modularComplexI_of_IsPhaseAntilinear
    (X : EndH)
    (hX : IsPhaseAntilinear (E := E) X)
    (u v : H₂) :
    deriv
      (fun t =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            X
            (InfoGeometry.Krein.clockAxis (E := E))
            t)
          u v)
      0
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      ((2 : ℝ) • (X.comp (InfoGeometry.Krein.clockAxis (E := E)))) u v := by
  rw [deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse
    (E := E) (X := X) u v]
  rw [phaseAxisResponse_antilinear_source (E := E) X hX]

theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_two_smul_comp_complex_i_of_IsPhaseAntilinear
    (X : EndH)
    (hX : IsPhaseAntilinear (E := E) X)
    (u v : H₂) :
    deriv
      (fun t =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            X
            (InfoGeometry.Krein.clockAxis (E := E))
            t)
          u v)
      0
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      ((2 : ℝ) • (X.comp (InfoGeometry.Krein.clockAxis (E := E)))) u v := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_two_smul_comp_modularComplexI_of_IsPhaseAntilinear
      (E := E) X hX u v

/--
Global noncommuting Berry-flow equation (arbitrary `t`):
the derivative of the exponential-transported Berry channel is the Berry readout
of the Maurer-Cartan commutator with the transported operator.
-/
theorem deriv_berryOfOperator_expTransport_at
    (X A : EndH) (t : ℝ) (u v : H₂) :
    deriv
      (fun s =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A s)
          u v)
      t
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        X
        (hestenesMaurerCartanCurvature X A)
        t)
      u v := by
  let ω : EndH →L[ℝ] ℝ :=
    (innerSL ℝ v).comp
      (ContinuousLinearMap.apply ℝ H₂
        (InfoGeometry.Krein.clockAxis (E := E) u))
  have hωEval :
      ∀ B : EndH,
        ω B = GeometricQuantumTensor.berryOfOperator (E := E) B u v := by
    intro B
    simp [ω, GeometricQuantumTensor.berryOfOperator, real_inner_comm]
  have hExp :
      HasDerivAt
        (fun s => InfoGeometry.Canonical.expTransport (A := EndH) X A s)
        (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t)
        t := by
    simpa using (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) X A t)
  have hω : HasDerivAt (fun _ : ℝ => ω) (0 : EndH →L[ℝ] ℝ) t := by
    simpa using (hasDerivAt_const (x := t) (c := ω))
  have hApply :
      HasDerivAt
        (fun s =>
          (fun _ : ℝ => ω) s
            (InfoGeometry.Canonical.expTransport (A := EndH) X A s))
        ((0 : EndH →L[ℝ] ℝ)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t)
          + ω (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t))
        t :=
    hω.clm_apply hExp
  have hMain :
      HasDerivAt
        (fun s =>
          GeometricQuantumTensor.berryOfOperator
            (E := E)
            (InfoGeometry.Canonical.expTransport (A := EndH) X A s)
            u v)
        (GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t)
          u v)
        t := by
    simpa [hωEval] using hApply
  simpa [hestenesMaurerCartanCurvature] using hMain.deriv

section WeylModular

variable [FiniteDimensional ℝ E]

/--
Weyl contribution to the doubled-space connection axis (lifted logarithmic
generator).
-/
noncomputable def hestenesWeylConnectionAxis
    (g : LiftedSheetAut (E := E)) : EndH :=
  LiftedSheetAut.logarithmicGenerator (E := E) g

/--
Combined Weyl + modular connection axis on doubled real space.
-/
noncomputable def hestenesWeylModularConnectionAxis
    (g : LiftedSheetAut (E := E)) (hMod : EndH) : EndH :=
  hestenesWeylConnectionAxis g
    + relativeModularKGenerator (E := E) hMod

/-- Maurer-Cartan transport generator induced by the combined Weyl/modular axis. -/
noncomputable def hestenesWeylModularConnectionGenerator
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) : EndH :=
  hestenesMaurerCartanCurvature
    (hestenesWeylModularConnectionAxis g hMod) A

/-- Pure Weyl contribution to the Maurer-Cartan transport generator. -/
noncomputable def hestenesWeylConnectionGenerator
    (g : LiftedSheetAut (E := E)) (A : EndH) : EndH :=
  hestenesMaurerCartanCurvature (hestenesWeylConnectionAxis g) A

lemma hestenesMaurerCartanCurvature_add_left
    (X Y A : EndH) :
    hestenesMaurerCartanCurvature (X + Y) A
      =
    hestenesMaurerCartanCurvature X A
      +
    hestenesMaurerCartanCurvature Y A := by
  apply ContinuousLinearMap.ext
  intro x
  unfold hestenesMaurerCartanCurvature transportCommutator
  simp [sub_eq_add_neg]
  abel

theorem hestenesWeylModularConnectionGenerator_eq_hestenesWeylConnectionGenerator_add_relativeModularDeriv
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) :
    hestenesWeylModularConnectionGenerator g hMod A
      =
    hestenesWeylConnectionGenerator g A
      +
    relativeModularDeriv (E := E) hMod A := by
  unfold hestenesWeylModularConnectionGenerator hestenesWeylModularConnectionAxis
  rw [hestenesMaurerCartanCurvature_add_left]
  unfold hestenesWeylConnectionGenerator hestenesWeylConnectionAxis
  simp [hestenesMaurerCartanCurvature, relativeModularKGenerator, relativeModularDeriv, modularDeriv]

theorem hestenesWeylModularConnectionGenerator_eq_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart
    (g : LiftedSheetAut (E := E)) (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod)) :
    hestenesWeylModularConnectionGenerator g hMod A
      =
    hestenesWeylConnectionGenerator g A
      +
    relativeModularSourceDeriv (E := E) hMod A := by
  rw [hestenesWeylModularConnectionGenerator_eq_hestenesWeylConnectionGenerator_add_relativeModularDeriv
      g hMod A]
  rw [relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge]

/-- Combined Weyl/modular Berry 2-form generated by the Maurer-Cartan channel. -/
noncomputable def hestenesWeylModularBerryTwoForm
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  GeometricQuantumTensor.berryOfOperator (E := E) (hestenesWeylModularConnectionGenerator g hMod A)

theorem deriv_hestenesWeylModularBerryTransport_at_zero_eq_hestenesWeylModularBerryTwoForm
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (hestenesWeylModularConnectionAxis g hMod)
            A
            t)
          u v)
      0
      =
    hestenesWeylModularBerryTwoForm g hMod A u v := by
  simpa [hestenesWeylModularBerryTwoForm, hestenesWeylModularConnectionGenerator,
    hestenesWeylModularConnectionAxis] using
    deriv_berryOfOperator_expTransport_at_zero
      (E := E) (X := hestenesWeylModularConnectionAxis g hMod) (A := A) u v

/--
Global Weyl/modular Berry-flow equation (arbitrary `t`) on doubled real space.
-/
theorem deriv_hestenesWeylModularBerryTransport_at_eq_hestenesWeylModularBerryTwoForm
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) (t : ℝ) (u v : H₂) :
    deriv
      (fun s =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (hestenesWeylModularConnectionAxis g hMod)
            A
            s)
          u v)
      t
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (hestenesWeylModularConnectionAxis g hMod)
        (hestenesWeylModularConnectionGenerator g hMod A)
        t) u v := by
  simpa [hestenesWeylModularConnectionAxis] using
    deriv_berryOfOperator_expTransport_at
      (E := E)
      (X := hestenesWeylModularConnectionAxis g hMod)
      (A := A) t u v

/--
Cartan-channel decomposition at arbitrary `t`:
the global Weyl/modular Berry flow splits into Weyl-gauge transport plus
relative-modular transport channels on the same exponential orbit.
-/
theorem deriv_hestenesWeylModularBerryTransport_at_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularDeriv
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) (t : ℝ) (u v : H₂) :
    deriv
      (fun s =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (hestenesWeylModularConnectionAxis g hMod)
            A
            s)
          u v)
      t
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
          (A := EndH)
          (hestenesWeylModularConnectionAxis g hMod)
          (hestenesWeylConnectionGenerator g A)
          t) u v
      +
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (hestenesWeylModularConnectionAxis g hMod)
        (relativeModularDeriv (E := E) hMod A)
        t) u v := by
  have hSplit :
      hestenesWeylModularConnectionGenerator g hMod A
        =
      hestenesWeylConnectionGenerator g A
        +
      relativeModularDeriv (E := E) hMod A :=
    hestenesWeylModularConnectionGenerator_eq_hestenesWeylConnectionGenerator_add_relativeModularDeriv
      (E := E) g hMod A
  rw [deriv_hestenesWeylModularBerryTransport_at_eq_hestenesWeylModularBerryTwoForm
      (E := E) g hMod A t u v]
  rw [hSplit]
  rw [InfoGeometry.Canonical.expTransport_add_seed (A := EndH)
    (X := hestenesWeylModularConnectionAxis g hMod)
    (A₁ := hestenesWeylConnectionGenerator g A)
    (A₂ := relativeModularDeriv (E := E) hMod A)]
  rw [GeometricQuantumTensor.berryOfOperator_add]
  simp

/--
Volume-preserving vs volume-changing split at arbitrary `t`:
if the gauge channel commutes with the seed, the relative-modular part reduces
to the source (dilation/anomaly) channel.
-/
theorem deriv_hestenesWeylModularBerryTransport_at_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart
    (g : LiftedSheetAut (E := E)) (hMod A : EndH) (t : ℝ)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun s =>
        GeometricQuantumTensor.berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (hestenesWeylModularConnectionAxis g hMod)
            A
            s)
          u v)
      t
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
          (A := EndH)
          (hestenesWeylModularConnectionAxis g hMod)
          (hestenesWeylConnectionGenerator g A)
          t) u v
      +
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (hestenesWeylModularConnectionAxis g hMod)
        (relativeModularSourceDeriv (E := E) hMod A)
        t) u v := by
  rw [deriv_hestenesWeylModularBerryTransport_at_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularDeriv
      (E := E) g hMod A t u v]
  rw [relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (E := E) hMod A hCommGauge]

theorem hestenesWeylModularBerryTwoForm_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart
    (g : LiftedSheetAut (E := E)) (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    hestenesWeylModularBerryTwoForm g hMod A u v
      =
    GeometricQuantumTensor.berryOfOperator
      (E := E)
      (hestenesWeylConnectionGenerator g A
        + relativeModularSourceDeriv (E := E) hMod A) u v := by
  unfold hestenesWeylModularBerryTwoForm
  simpa using congrArg (fun T : EndH => GeometricQuantumTensor.berryOfOperator (E := E) T u v)
    (hestenesWeylModularConnectionGenerator_eq_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart
      g hMod A hCommGauge)

end WeylModular

section StarCertifiedWeld

/--
Synthesis-facing Hestenes weld closure:
under projector agreement on the star-certified conformal surface, the Berry
sector of the `K = Jε`-twisted Einstein-anomaly QGT is exactly the metric
readout of the lifted projector obstruction.
-/
theorem starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement
    (SCI : StarCertifiedConformalInference E)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    (InfoGeometry.Quantum.GeometricQuantumTensor.starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator (E := E)
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
  exact
    InfoGeometry.Quantum.GeometricQuantumTensor.starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement
      (E := E) SCI hProj

end StarCertifiedWeld

section TopologicalSheetGlideReadout

/--
Forwarder to the topological owner: a constructed sheet/glide Berry connection generated from
a base potential satisfies the odd potential law, without taking that law as a free hypothesis.
-/
theorem sheetGlideOddBerryConnection_owner_odd
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : InfoGeometry.Topology.Weyl.GlideBrillouinZone BZ) (φ : BZ → ℝ) :
    ∀ s k,
      (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ).potential s.swap (gbz.glide k) =
        -(InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ).potential s k := by
  exact InfoGeometry.Topology.Weyl.oddSheetConnection_owner_odd gbz φ

/--
Forwarder to the topological owner: the finite glide-difference curvature induced by the
constructed sheet/glide-odd connection is itself strictly odd under sheet/glide.
-/
theorem inducedSheetGlideOddBerryCurvature_owner_odd
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : InfoGeometry.Topology.Weyl.GlideBrillouinZone BZ) (φ : BZ → ℝ)
    (s : InfoGeometry.Topology.Weyl.ChiralSheet) (k : BZ) :
    (InfoGeometry.Topology.Weyl.inducedSheetBerryCurvature gbz
      (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ)).curvature s.swap (gbz.glide k) =
      -(InfoGeometry.Topology.Weyl.inducedSheetBerryCurvature gbz
        (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ)).curvature s k := by
  exact InfoGeometry.Topology.Weyl.induced_oddSheetBerryCurvature_owner_odd gbz φ s k

/--
Forwarder to the topological owner: the constructed sheet/glide-odd Berry curvature cancels on
each sheet/glide pair.
-/
theorem inducedSheetGlideOddBerryCurvature_owner_odd_cancellation
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : InfoGeometry.Topology.Weyl.GlideBrillouinZone BZ) (φ : BZ → ℝ)
    (s : InfoGeometry.Topology.Weyl.ChiralSheet) (k : BZ) :
    (InfoGeometry.Topology.Weyl.inducedSheetBerryCurvature gbz
      (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ)).curvature s k +
      (InfoGeometry.Topology.Weyl.inducedSheetBerryCurvature gbz
        (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ)).curvature s.swap
          (gbz.glide k) = 0 := by
  exact InfoGeometry.Topology.Weyl.induced_oddSheetBerryCurvature_owner_odd_cancellation gbz φ s k

end TopologicalSheetGlideReadout

section Legacy

variable [FiniteDimensional ℝ E]

/--
Legacy scalar determinant readout.
Prefer the operatorial doubled-space forms above for new developments.
-/
noncomputable def berryConnection (CI : ConformalInference E) (dCI : ConformalInference E) : ℝ :=
  Real.log (|LinearMap.det (CI.chiralAnomaly * dCI.chiralAnomaly).toLinearMap|)

end Legacy

end InfoGeometry.Canonical.BerryPhase
