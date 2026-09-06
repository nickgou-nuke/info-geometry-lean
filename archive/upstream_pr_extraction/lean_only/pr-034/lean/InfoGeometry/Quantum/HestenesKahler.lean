import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Convex.ProjectiveRays
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.BerryConnection
import InfoGeometry.Canonical.StateDependentTransport
import InfoGeometry.Canonical.PolarizedMadelungBridge
import InfoGeometry.Canonical.EinsteinAnomalyOperator
import InfoGeometry.Canonical.TwistorOperatorialIncidence
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.SuperchargeCentralChargeClosure

/-!
# Projective Polarized Bi-graded Hestenes Geometry

This file formalizes the fused owner surface latent in the repository:

- projective rays are the physical carrier,
- a `K`-polarization organizes the doubled carrier into `plus/minus` sectors,
- the transport algebra is bi-graded by Hestenes phase parity and Fock super parity,
- and everything is kept in the full noncommuting operator representation on
  `DoubledSpace E`.

No scalar or diagonal proxy model is introduced here.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Convex
open InfoGeometry.Canonical
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ConformalAlgebra
open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Quantum.GeometricQuantumTensor
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.PolarizedMadelungBridge
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Hestenes phase grading relative to the internal axis `K = Jε`. -/
inductive PhaseParity where
  | even
  | odd
deriving DecidableEq, Repr

/-- The full bi-degree carried by the noncommuting operator algebra. -/
abbrev Bidegree := PhaseParity × SuperParity

/-- Predicate asserting the phase parity of a doubled-space endomorphism. -/
def HasPhaseParity : PhaseParity → EndH → Prop
  | .even, A => IsPhaseLinear (E := E) A
  | .odd, A => IsPhaseAntilinear (E := E) A

/--
Operator together with a property Hestenes phase parity.

The phase grade is a genuine property of the noncommuting operator.
-/
structure PhaseGradedOperator where
  op : EndH
  parity : PhaseParity
  hasParity : HasPhaseParity (E := E) parity op

/--
Operator together with a chosen Fock/super parity label.

The super grade is the algebra label used by the graded bracket.
-/
structure SuperGradedOperator where
  op : EndH
  parity : SuperParity

/--
Operator carrying both the Hestenes phase grade and the super/Fock grade.

The super label chooses the bracket sector; the phase property certifies how the
operator interacts with the internal axis `K = Jε`.
-/
structure BigradedOperator where
  op : EndH
  phaseParity : PhaseParity
  superParity : SuperParity
  hasPhaseParity : HasPhaseParity (E := E) phaseParity op

namespace BigradedOperator

/-- The explicit `ℤ₂ × ℤ₂` degree of a noncommuting doubled-space operator. -/
def bidegree (A : BigradedOperator (E := E)) : Bidegree :=
  (A.phaseParity, A.superParity)

end BigradedOperator

/--
Projective, polarized, bi-graded Bogoliubov datum on the doubled real carrier.

This is the fused owner surface for:
- Goutev's Principle (`ray` / projective content),
- polarization (`plus/minus` splitting),
- Hestenes phase grading (`K`-linear / `K`-antilinear),
- and the noncommuting super/Fock operator branch.
-/
structure ProjectivePolarizedBigradedBogoliubovDatum where
  representative : NonzeroDoubledState (E := E)
  qgt : QGT E
  majorana : RealMajoranaDatum (S := H₂)
  polarization : KPolarization (S := H₂) majorana
  J_eq_modularConjugationJ :
    majorana.J = modularConjugationJ (E := E)
  eps_eq_modularSignEpsilon :
    majorana.eps = modularSignEpsilon (E := E)

namespace ProjectivePolarizedBigradedBogoliubovDatum

/-- The physical ray carried by the datum. -/
noncomputable def ray
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    ProjectiveState (E := E) :=
  projectivize' (E := E) D.representative

/-- The canonical mixing axis. -/
abbrev J
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : EndH :=
  D.majorana.J

/-- The canonical signature/sheet axis. -/
abbrev eps
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : EndH :=
  D.majorana.eps

/-- The Hestenes phase axis `K = Jε`. -/
noncomputable abbrev K
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : EndH :=
  D.majorana.K

/-- The `+` polarization sector. -/
noncomputable def plus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : Submodule ℝ H₂ :=
  D.polarization.plus

/-- The `-` polarization sector. -/
noncomputable def minus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : Submodule ℝ H₂ :=
  D.polarization.minus

/-- The canonical projector split induced by the polarization. -/
noncomputable def split
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    KPolarization.PolarizationSplit (S := H₂) :=
  KPolarization.splitOfPolarization (M := D.majorana) D.polarization

/-- The odd annihilation/projector branch induced by the polarization split. -/
noncomputable def aMinus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : EndH :=
  D.split.Pminus

/-- The odd creation/projector branch induced by the polarization split. -/
noncomputable def aPlus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) : EndH :=
  D.split.Pplus

/-- Ray invariance under nonzero rescaling of the chosen representative. -/
theorem ray_eq_of_smul_representative
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (a : ℝ) (ha : a ≠ 0) :
    projectivize' (E := E) ⟨a • D.representative.1, smul_ne_zero ha D.representative.2⟩
      = D.ray := by
  simpa [ray] using projectivize'_smul (E := E) a ha D.representative

/-- The stored Majorana phase axis also coincides with the root owner `complex_i`. -/
theorem K_eq_complex_i
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    D.K = InfoGeometry.Krein.clockAxis (E := E) := by
  calc
    D.K = InfoGeometry.Krein.clockAxis (E := E) := by
      unfold ProjectivePolarizedBigradedBogoliubovDatum.K RealMajoranaDatum.K
      rw [D.J_eq_modularConjugationJ, D.eps_eq_modularSignEpsilon]
      rfl
    _ = InfoGeometry.Krein.clockAxis (E := E) := by
      exact InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := E)

/-- The stored Majorana phase axis coincides with the canonical doubled-space `K = Jε`. -/
theorem K_eq_modularComplexI
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    D.K = InfoGeometry.Krein.clockAxis (E := E) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    D.K_eq_complex_i

/-- The stored Majorana mixing axis coincides with the root owner `modular_j`. -/
theorem J_eq_modular_j
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    D.J = modular_j (E := E) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    D.J_eq_modularConjugationJ

/-- The stored Majorana signature axis coincides with the root owner `spectral_epsilon`. -/
theorem eps_eq_spectral_epsilon
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    D.eps = spectral_epsilon (E := E) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    D.eps_eq_modularSignEpsilon

/-- The QGT carried by the datum is compatible with the stored Hestenes axis. -/
theorem compat
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (u v : H₂) :
    D.qgt.berry u v = D.qgt.metric (D.K u) v := by
  rw [D.K_eq_modularComplexI]
  exact D.qgt.compat u v

/-- Root-owner form of the stored Hestenes/QGT compatibility law. -/
theorem compat_complex_i
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (u v : H₂) :
    D.qgt.berry u v = D.qgt.metric (InfoGeometry.Krein.clockAxis (E := E) u) v := by
  calc
    D.qgt.berry u v = D.qgt.metric (D.K u) v := D.compat u v
    _ = D.qgt.metric (InfoGeometry.Krein.clockAxis (E := E) u) v := by rw [D.K_eq_complex_i]

/-- The phase axis swaps the `+` polarization sector into the `-` sector. -/
theorem K_maps_plus_to_minus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (x : H₂) (hx : x ∈ D.plus) :
    D.K x ∈ D.minus := by
  simpa [plus, minus, K] using
    KPolarization.K_maps_plus_to_minus (M := D.majorana) (P0 := D.polarization) x hx

/-- The phase axis swaps the `-` polarization sector into the `+` sector. -/
theorem K_maps_minus_to_plus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (x : H₂) (hx : x ∈ D.minus) :
    D.K x ∈ D.plus := by
  simpa [plus, minus, K] using
    KPolarization.K_maps_minus_to_plus (M := D.majorana) (P0 := D.polarization) x hx

/-- The polarization involution is recovered from the noncommuting split operators. -/
theorem aPlus_sub_aMinus_eq_polarization
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    D.aPlus - D.aMinus = D.polarization.P := by
  simpa [aPlus, aMinus, split] using
    KPolarization.plus_sub_minus_eq_P (M := D.majorana) D.polarization

/--
The polarization split always yields the canonical projector-super odd pair.

This stays entirely in the noncommuting operator representation.
-/
theorem isProjectorSuperPair_aMinus_aPlus
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    IsProjectorSuperPair (E := E) D.aMinus D.aPlus := by
  simpa [aMinus, aPlus, split] using
    projectorSuperPair_of_ladderOfPolarization (E := E) D.majorana D.polarization

/-- The canonical mixing axis `J` is Hestenes phase-odd. -/
theorem J_phase_odd
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    HasPhaseParity (E := E) PhaseParity.odd D.J := by
  unfold HasPhaseParity IsPhaseAntilinear ProjectivePolarizedBigradedBogoliubovDatum.J
  rw [D.J_eq_modularConjugationJ]
  exact modularConjugationJ_anticommutes_modularComplexI (E := E)

/-- The canonical signature axis `ε` is Hestenes phase-odd. -/
theorem eps_phase_odd
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    HasPhaseParity (E := E) PhaseParity.odd D.eps := by
  unfold HasPhaseParity IsPhaseAntilinear ProjectivePolarizedBigradedBogoliubovDatum.eps
  rw [D.eps_eq_modularSignEpsilon]
  calc
    (modularSignEpsilon (E := E)).comp (InfoGeometry.Krein.clockAxis (E := E))
      = -(modularConjugationJ (E := E)) := by
          simpa [TomitaTakesaki.modularSignEpsilon, TomitaTakesaki.modularComplexI,
            TomitaTakesaki.modularConjugationJ] using
            (InfoGeometry.Krein.spectral_epsilon_comp_complex_i (E := E))
    _ = -((InfoGeometry.Krein.clockAxis (E := E)).comp (modularSignEpsilon (E := E))) := by
          congr 1
          simpa [TomitaTakesaki.modularSignEpsilon, TomitaTakesaki.modularComplexI,
            TomitaTakesaki.modularConjugationJ] using
            (InfoGeometry.Krein.complex_i_comp_spectral_epsilon (E := E)).symm

/-- The Hestenes axis `K = Jε` is phase-even. -/
theorem K_phase_even
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    HasPhaseParity (E := E) PhaseParity.even D.K := by
  unfold HasPhaseParity IsPhaseLinear
  rw [D.K_eq_modularComplexI]

/-- Canonical Bogoliubov mixing generator as a bi-graded operator. -/
noncomputable def JAxis
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    BigradedOperator (E := E) where
  op := D.J
  phaseParity := .odd
  superParity := .even
  hasPhaseParity := D.J_phase_odd

/-- Canonical sheet/signature generator as a bi-graded operator. -/
noncomputable def epsAxis
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    BigradedOperator (E := E) where
  op := D.eps
  phaseParity := .odd
  superParity := .even
  hasPhaseParity := D.eps_phase_odd

/-- Canonical phase-axis generator as a bi-graded operator. -/
noncomputable def KAxis
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    BigradedOperator (E := E) where
  op := D.K
  phaseParity := .even
  superParity := .even
  hasPhaseParity := D.K_phase_even

/-- The odd annihilation/projector branch as a super-graded operator. -/
noncomputable def aMinusOdd
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    SuperGradedOperator (E := E) where
  op := D.aMinus
  parity := .odd

/-- The odd creation/projector branch as a super-graded operator. -/
noncomputable def aPlusOdd
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    SuperGradedOperator (E := E) where
  op := D.aPlus
  parity := .odd

/-- Canonical Bogoliubov mixing boost. -/
noncomputable def JBoost
    (_D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (t : ℝ) : EndH :=
  BogoliubovTransport.JBoost (E := E) t

/-- Canonical sheet/signature boost. -/
noncomputable def epsBoost
    (_D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (t : ℝ) : EndH :=
  BogoliubovTransport.epsilonBoost (E := E) t

/-- Canonical Hestenes phase rotation. -/
noncomputable def KRotation
    (_D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (t : ℝ) : EndH :=
  BogoliubovTransport.KRotation (E := E) t

end ProjectivePolarizedBigradedBogoliubovDatum

section AnomalyPlacement

/--
The canonical lifted projector obstruction is an even-even operator:
phase-even on the Hestenes side and bosonic/even on the super side.
-/
noncomputable def propertyProjectorObstructionAxis
    (CCI : CertifiedConformalInference E) :
    BigradedOperator (E := E) where
  op := CCI.liftedProjectorObstructionOperator
  phaseParity := .even
  superParity := .even
  hasPhaseParity := by
    show IsPhaseLinear (E := E)
      (InfoGeometry.Canonical.MongeAmpereDualSheetBridge.dualSheetLift
        (E := E) CCI.chiralAnomalyOperator)
    exact
      CertifiedConformalInference.dualSheetLift_isPhaseLinear
        (E := E) (A := CCI.chiralAnomalyOperator)

@[simp] theorem propertyProjectorObstructionAxis_bidegree
    (CCI : CertifiedConformalInference E) :
    (propertyProjectorObstructionAxis (E := E) CCI).bidegree
      =
    (PhaseParity.even, SuperParity.even) := rfl

/--
The welded projector obstruction is the phase-axis response of the lifted
projector obstruction. It sits in the (phase-odd, super-even) sector.
-/
lemma comp_modularComplexI_isPhaseAntilinear
    (A : EndH) (hA : IsPhaseAntilinear (E := E) A) :
    IsPhaseAntilinear (E := E) (A.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
  unfold IsPhaseAntilinear at hA ⊢
  let K : EndH := InfoGeometry.Krein.clockAxis (E := E)
  have hK2 : K.comp K = -(ContinuousLinearMap.id ℝ H₂) := by
    simp [K]
  calc
    (A.comp K).comp K = A.comp (K.comp K) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (-(ContinuousLinearMap.id ℝ H₂)) := by
      rw [hK2]
    _ = -A := by
      simp
    _ = -(K.comp (A.comp K)) := by
      have hCore : K.comp (A.comp K) = A := by
        calc
          K.comp (A.comp K) = K.comp (-(K.comp A)) := by rw [hA]
          _ = -((K.comp K).comp A) := by simp [ContinuousLinearMap.comp_assoc]
          _ = -((-(ContinuousLinearMap.id ℝ H₂)).comp A) := by rw [hK2]
          _ = A := by simp
      simp [hCore]

lemma comp_complex_i_isPhaseAntilinear
    (A : EndH) (hA : IsPhaseAntilinear (E := E) A) :
    IsPhaseAntilinear (E := E) (A.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    comp_modularComplexI_isPhaseAntilinear (E := E) A hA

lemma phaseAxisForce_phase_odd
    (H : EndH) :
    IsPhaseAntilinear (E := E) (phaseAxisForce (E := E) H) := by
  rw [phaseAxisForce_eq_from_phaseAntilinearPart (E := E) H]
  have hA :
      IsPhaseAntilinear (E := E) (phaseAntilinearPart (E := E) H) :=
    phaseAntilinearPart_isPhaseAntilinear (E := E) H
  have hComp :
      IsPhaseAntilinear (E := E)
        ((phaseAntilinearPart (E := E) H).comp (InfoGeometry.Krein.clockAxis (E := E))) :=
    comp_modularComplexI_isPhaseAntilinear
      (E := E) (A := phaseAntilinearPart (E := E) H) hA
  unfold IsPhaseAntilinear at hComp ⊢
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simpa [smul_neg] using congrArg (fun T => (2 : ℝ) • T) hComp

noncomputable def weldedProjectorObstructionAxis
    (CCI : CertifiedConformalInference E) :
    BigradedOperator (E := E) where
  op := phaseAxisResponse (E := E) CCI.liftedProjectorObstructionOperator
  phaseParity := .odd
  superParity := .even
  hasPhaseParity := by
    simpa [phaseAxisResponse] using
      phaseAxisForce_phase_odd (E := E) CCI.liftedProjectorObstructionOperator

@[simp] theorem weldedProjectorObstructionAxis_bidegree
    (CCI : CertifiedConformalInference E) :
    (weldedProjectorObstructionAxis (E := E) CCI).bidegree
      =
    (PhaseParity.odd, SuperParity.even) := rfl

/-- Hestenes-twisted Berry readout attached to the welded obstruction axis. -/
noncomputable def weldedProjectorObstructionBerry
    (CCI : CertifiedConformalInference E) : LinearMap.BilinForm ℝ H₂ :=
  berryTwoFormJEpsOfOperator (E := E)
    (weldedProjectorObstructionAxis (E := E) CCI).op

/-! Incidence implies vanishing of the welded obstruction and its Berry readout. -/

theorem weldedProjectorObstructionAxis_eq_zero_of_operatorialIncidence
    (CCI : CertifiedConformalInference E)
    (hInc : CCI.operatorialIncidence) :
    (weldedProjectorObstructionAxis (E := E) CCI).op = 0 := by
  have hZero : CCI.liftedProjectorObstructionOperator = 0 := hInc
  simp [weldedProjectorObstructionAxis, phaseAxisResponse, phaseAxisForce,
    transportCommutator, hZero]

theorem weldedProjectorObstructionBerry_eq_zero_of_operatorialIncidence
    (CCI : CertifiedConformalInference E)
    (hInc : CCI.operatorialIncidence) :
    weldedProjectorObstructionBerry (E := E) CCI = 0 := by
  have hAxis :
      (weldedProjectorObstructionAxis (E := E) CCI).op = 0 :=
    weldedProjectorObstructionAxis_eq_zero_of_operatorialIncidence (E := E) CCI hInc
  ext u v
  simp [weldedProjectorObstructionBerry, berryTwoFormJEpsOfOperator, hAxis,
    GeometricQuantumTensor.metricOfOperator_zero]

/--
Operatorial dilation-charge response mode.

This packet is deliberately assembled from owner theorems rather than a new
scalar charge: Cartan puts the conformal generator `D` in the Weyl-dilation
sector, operatorial incidence kills the Hestenes-welded Berry obstruction, and
the CPT supercharge transport lane identifies the quasilattice analytical index
with the operatorial central charge.
-/
@[rep_depth transport]
theorem dilationChargeResponseMode_of_operatorialIncidence
    {A B : Type}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [FiniteDimensional ℝ E]
    [KreinSpace H₂] [KreinGradedModule H₂]
    (CBA : ConformalBeliefAlgebra E)
    (CCI : CertifiedConformalInference E)
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (hInc : CCI.operatorialIncidence)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    CBA.IsWeylDilationPart CBA.D
      ∧ weldedProjectorObstructionBerry (E := E) CCI = 0
      ∧ quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
        =
        operatorialCentralCharge (A := A) (B := B) (E := E) X hX := by
  refine ⟨?_, ?_, ?_⟩
  · exact CBA.D_in_weylDilation_of_cartan hCartan
  · exact weldedProjectorObstructionBerry_eq_zero_of_operatorialIncidence
      (E := E) CCI hInc
  · exact quasilatticeAnalyticalIndex_eq_operatorialCentralCharge_on_cpt_lane
      (A := A) (B := B) (E := E) V X hX hEven t

section StateDependent

open InfoGeometry.Canonical.StateDependentTransport

/-- State-dependent modular owner datum from the lifted projector obstruction seed. -/
noncomputable def liftedProjectorStateModularDatum
    (CCI : CertifiedConformalInference E) :
    StateModularDatum E :=
  constantStateModularDatum (E := E) CCI.liftedProjectorObstructionOperator

/--
State-dependent QGT readout attached to the welded obstruction axis.
This keeps the readout on the operator seed, not on the state itself.
-/
noncomputable def weldedProjectorObstructionStateQGTReadout
    (CCI : CertifiedConformalInference E) (ψ : H₂) :
    StateQGTReadout E :=
  stateQGTReadout (E := E)
    (liftedProjectorStateModularDatum (E := E) CCI)
    ψ
    (weldedProjectorObstructionAxis (E := E) CCI).op

theorem weldedProjectorObstruction_state_split
    (CCI : CertifiedConformalInference E) (ψ : H₂) :
    stateInducedDynamics (E := E)
        (liftedProjectorStateModularDatum (E := E) CCI)
        ψ
        (weldedProjectorObstructionAxis (E := E) CCI).op
      =
    stateGaugeDynamics (E := E)
        (liftedProjectorStateModularDatum (E := E) CCI)
        ψ
        (weldedProjectorObstructionAxis (E := E) CCI).op
      +
    stateSourceDynamics (E := E)
        (liftedProjectorStateModularDatum (E := E) CCI)
        ψ
        (weldedProjectorObstructionAxis (E := E) CCI).op := by
  simpa using
    (stateInducedDynamics_eq_gauge_add_source
      (E := E)
      (liftedProjectorStateModularDatum (E := E) CCI)
      ψ
      (weldedProjectorObstructionAxis (E := E) CCI).op)

theorem weldedProjectorObstruction_pairedSourceCancellation
    (P : JPairedStateGenerators E) (CCI : CertifiedConformalInference E)
    (ψ : H₂)
    (hCancel :
      pairedStateSourceDynamics (E := E) P ψ
        (weldedProjectorObstructionAxis (E := E) CCI).op = 0) :
    pairedStateInducedDynamics (E := E) P ψ
        (weldedProjectorObstructionAxis (E := E) CCI).op
      =
    pairedStateGaugeDynamics (E := E) P ψ
        (weldedProjectorObstructionAxis (E := E) CCI).op := by
  simpa using
    (pairedSourceCancellation (E := E) P ψ
      (weldedProjectorObstructionAxis (E := E) CCI).op hCancel)

end StateDependent

/--
The lifted Einstein anomaly itself is also an even-even operator on the doubled
carrier. The phase-sensitive channel comes from the canonical Hestenes `K`-twist
used by the QGT lift, not from labeling the bare anomaly operator phase-odd.
-/
noncomputable def starCertifiedEinsteinAnomalyAxis
    (SCI : StarCertifiedConformalInference E) :
    BigradedOperator (E := E) where
  op := SCI.liftedEinsteinAnomalyOperator
  phaseParity := .even
  superParity := .even
  hasPhaseParity := SCI.liftedEinsteinAnomalyOperator_isPhaseLinear

@[simp] theorem starCertifiedEinsteinAnomalyAxis_bidegree
    (SCI : StarCertifiedConformalInference E) :
    (starCertifiedEinsteinAnomalyAxis (E := E) SCI).bidegree
      =
    (PhaseParity.even, SuperParity.even) := rfl

/--
On the star-property conformal surface, the Hestenes-twisted QGT Berry sector
of the even-even lifted Einstein anomaly is exactly the metric readout of the
lifted projector obstruction under projector agreement.
-/
theorem starCertifiedEinsteinAnomalyAxis_phaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
    (SCI : StarCertifiedConformalInference E)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    (starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry
      =
    metricOfOperator (E := E)
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
  exact
    starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement
      (E := E) SCI hProj

end AnomalyPlacement

section StateDependentLayer

open InfoGeometry.Canonical.StateDependentTransport

/--
State-dependent modular datum obtained by freezing the lifted projector
obstruction as the operator seed on every doubled state.
-/
noncomputable def propertyProjectorObstructionStateDatum
    (CCI : CertifiedConformalInference E) :
    StateModularDatum E :=
  constantStateModularDatum (E := E) CCI.liftedProjectorObstructionOperator

/--
State-dependent modular datum obtained by freezing the lifted Einstein anomaly as
the operator seed on every doubled state.
-/
noncomputable def starCertifiedEinsteinAnomalyStateDatum
    (SCI : StarCertifiedConformalInference E) :
    StateModularDatum E :=
  constantStateModularDatum (E := E) SCI.liftedEinsteinAnomalyOperator

@[simp] theorem propertyProjectorObstructionStateInducedDynamics_eq_relativeModularDeriv
    (CCI : CertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateInducedDynamics (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    relativeModularDeriv (E := E) CCI.liftedProjectorObstructionOperator A := by
  rfl

@[simp] theorem starCertifiedEinsteinAnomalyStateInducedDynamics_eq_relativeModularDeriv
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateInducedDynamics (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    relativeModularDeriv (E := E) SCI.liftedEinsteinAnomalyOperator A := by
  rfl

@[simp] theorem propertyProjectorObstructionStateMetricReadout_eq_hestenesMetricTwoForm
    (CCI : CertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTMetricReadout (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    InfoGeometry.Canonical.BerryPhase.hestenesMetricTwoForm (E := E)
      CCI.liftedProjectorObstructionOperator A := rfl

@[simp] theorem propertyProjectorObstructionStatePhaseReadout_eq_hestenesBerryTwoForm
    (CCI : CertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    InfoGeometry.Canonical.BerryPhase.hestenesBerryTwoForm (E := E)
      CCI.liftedProjectorObstructionOperator A := rfl

@[simp] theorem propertyProjectorObstructionStatePhaseReadout_eq_metric_comp_complex_i
    (CCI : CertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    (stateQGTMetricReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A).compLeft
      (InfoGeometry.Krein.clockAxis (E := E)).toLinearMap := by
  calc
    stateQGTPhaseReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    (stateQGTMetricReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
        exact stateQGTPhaseReadout_eq_metric_comp_complex_i (E := E)
          (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
    _ =
    (stateQGTMetricReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A).compLeft
      (InfoGeometry.Krein.clockAxis (E := E)).toLinearMap := by
        rw [InfoGeometry.Krein.complex_i_eq_clockAxis (E := E)]

@[simp] theorem propertyProjectorObstructionStatePhaseReadout_eq_metric_comp_K
    (CCI : CertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    (stateQGTMetricReadout (E := E)
        (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A).compLeft
      (InfoGeometry.Krein.clockAxis (E := E)).toLinearMap := by
  exact propertyProjectorObstructionStatePhaseReadout_eq_metric_comp_complex_i
    (E := E) CCI ψ A

attribute
  [deprecated propertyProjectorObstructionStatePhaseReadout_eq_metric_comp_complex_i
    (since := "2026-04-11")]
  propertyProjectorObstructionStatePhaseReadout_eq_metric_comp_K

@[simp] theorem starCertifiedEinsteinAnomalyStateMetricReadout_eq_hestenesMetricTwoForm
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTMetricReadout (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    InfoGeometry.Canonical.BerryPhase.hestenesMetricTwoForm (E := E)
      SCI.liftedEinsteinAnomalyOperator A := rfl

@[simp] theorem starCertifiedEinsteinAnomalyStatePhaseReadout_eq_hestenesBerryTwoForm
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    InfoGeometry.Canonical.BerryPhase.hestenesBerryTwoForm (E := E)
      SCI.liftedEinsteinAnomalyOperator A := rfl

@[simp] theorem starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_complex_i
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    (stateQGTMetricReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A).compLeft
      (InfoGeometry.Krein.clockAxis (E := E)).toLinearMap := by
  calc
    stateQGTPhaseReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    (stateQGTMetricReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
        exact stateQGTPhaseReadout_eq_metric_comp_complex_i (E := E)
          (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
    _ =
    (stateQGTMetricReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A).compLeft
      (InfoGeometry.Krein.clockAxis (E := E)).toLinearMap := by
        rw [InfoGeometry.Krein.complex_i_eq_clockAxis (E := E)]

@[simp] theorem starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_K
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateQGTPhaseReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    (stateQGTMetricReadout (E := E)
        (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A).compLeft
      (InfoGeometry.Krein.clockAxis (E := E)).toLinearMap := by
  exact starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_complex_i
    (E := E) SCI ψ A

attribute
  [deprecated starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_complex_i
    (since := "2026-04-11")]
  starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_K

/--
State-indexed phase readout for the star-property anomaly QGT.
This is constant in the state parameter and keeps the readout operatorial.
-/
noncomputable def starCertifiedEinsteinAnomalyStatePhaseReadout
    (SCI : StarCertifiedConformalInference E) (_ψ : H₂) :
    LinearMap.BilinForm ℝ H₂ :=
  (starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry

/--
State-dependent phase readout attached to the welded obstruction axis.
This is inherited from the star-property anomaly readout on the same surface.
-/
noncomputable def weldedProjectorObstructionStatePhaseReadout
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) :
    LinearMap.BilinForm ℝ H₂ :=
  starCertifiedEinsteinAnomalyStatePhaseReadout (E := E) SCI ψ

noncomputable def weldedProjectorObstructionStateGeneratorField
    (SCI : StarCertifiedConformalInference E) :
    InfoGeometry.Canonical.PolarizedMadelungBridge.StateGeneratorField (E := E) :=
  fun _ => SCI.liftedEinsteinAnomalyOperator

/--
State-dependent phase readout of the welded obstruction axis, expressed through
the operatorial state-generator field.
-/
noncomputable def weldedProjectorObstructionStatePhaseReadout_fromGenerator
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) :
    LinearMap.BilinForm ℝ H₂ :=
  InfoGeometry.Canonical.PolarizedMadelungBridge.StateGeneratorField.statePhaseReadout
    (weldedProjectorObstructionStateGeneratorField SCI)
    ψ
    (weldedProjectorObstructionAxis (E := E) SCI.toCertifiedConformalInference).op

theorem starCertifiedEinsteinAnomalyStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
    (SCI : StarCertifiedConformalInference E) (ψ : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    starCertifiedEinsteinAnomalyStatePhaseReadout (E := E) SCI ψ
      =
    metricOfOperator (E := E)
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
  simpa [starCertifiedEinsteinAnomalyStatePhaseReadout] using
    (starCertifiedEinsteinAnomalyAxis_phaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
      (E := E) SCI hProj)

theorem weldedProjectorObstructionStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
    (SCI : StarCertifiedConformalInference E) (ψ : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ
      =
    metricOfOperator (E := E)
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
  simpa [weldedProjectorObstructionStatePhaseReadout] using
    (starCertifiedEinsteinAnomalyStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
      (E := E) SCI ψ hProj)

/--
Local split identity for the constant projector-obstruction state datum:
the induced dynamics separates canonically into gauge and source branches.
-/
theorem propertyProjectorObstructionStateInducedDynamics_eq_gauge_add_source
    (CCI : CertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateInducedDynamics (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      =
    stateGaugeDynamics (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A
      +
    stateSourceDynamics (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A := by
  exact
    stateInducedDynamics_eq_gauge_add_source (E := E)
      (propertyProjectorObstructionStateDatum (E := E) CCI) ψ A

/--
Local split identity for the constant Einstein-anomaly state datum:
the induced dynamics separates canonically into gauge and source branches.
-/
theorem starCertifiedEinsteinAnomalyStateInducedDynamics_eq_gauge_add_source
    (SCI : StarCertifiedConformalInference E) (ψ : H₂) (A : EndH) :
    stateInducedDynamics (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      =
    stateGaugeDynamics (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A
      +
    stateSourceDynamics (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A := by
  exact
    stateInducedDynamics_eq_gauge_add_source (E := E)
      (starCertifiedEinsteinAnomalyStateDatum (E := E) SCI) ψ A

end StateDependentLayer

end InfoGeometry.Quantum
