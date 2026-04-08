import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Convex.ProjectiveRays
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.EinsteinAnomalyOperator

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
open InfoGeometry.Quantum.RealMajorana
open InfoGeometry.Quantum.GeometricQuantumTensor

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
Operator together with a certified Hestenes phase parity.

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

The super label chooses the bracket sector; the phase witness certifies how the
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

/-- The stored Majorana phase axis coincides with the canonical doubled-space `K = Jε`. -/
theorem K_eq_modularComplexI
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) :
    D.K = modularComplexI (E := E) := by
  unfold ProjectivePolarizedBigradedBogoliubovDatum.K RealMajoranaDatum.K
  rw [D.J_eq_modularConjugationJ, D.eps_eq_modularSignEpsilon]
  rfl

/-- The QGT carried by the datum is compatible with the stored Hestenes axis. -/
theorem compat
    (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (u v : H₂) :
    D.qgt.berry u v = D.qgt.metric (D.K u) v := by
  simpa [D.K_eq_modularComplexI] using D.qgt.compat u v

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
    (modularSignEpsilon (E := E)).comp (modularComplexI (E := E))
      = -(modularConjugationJ (E := E)) := by
          simpa [TomitaTakesaki.modularSignEpsilon, TomitaTakesaki.modularComplexI,
            TomitaTakesaki.modularConjugationJ] using
            (InfoGeometry.Krein.spectral_epsilon_comp_complex_i (E := E))
    _ = -((modularComplexI (E := E)).comp (modularSignEpsilon (E := E))) := by
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
noncomputable def certifiedProjectorObstructionAxis
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

@[simp] theorem certifiedProjectorObstructionAxis_bidegree
    (CCI : CertifiedConformalInference E) :
    (certifiedProjectorObstructionAxis (E := E) CCI).bidegree
      =
    (PhaseParity.even, SuperParity.even) := rfl

/--
The welded projector obstruction is the phase-axis response of the lifted
projector obstruction. It sits in the (phase-odd, super-even) sector.
-/
lemma comp_modularComplexI_isPhaseAntilinear
    (A : EndH) (hA : IsPhaseAntilinear (E := E) A) :
    IsPhaseAntilinear (E := E) (A.comp (modularComplexI (E := E))) := by
  unfold IsPhaseAntilinear at hA ⊢
  have hKA : (modularComplexI (E := E)).comp A = -(A.comp (modularComplexI (E := E))) := by
    simpa using (congrArg Neg.neg hA).symm
  calc
    (A.comp (modularComplexI (E := E))).comp (modularComplexI (E := E))
        = A.comp ((modularComplexI (E := E)).comp (modularComplexI (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (-(ContinuousLinearMap.id ℝ H₂)) := by
          rw [modularComplexI_sq (E := E)]
    _ = -A := by
          simp
    _ = -(((modularComplexI (E := E)).comp A).comp (modularComplexI (E := E))) := by
          rw [hKA]
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((modularComplexI (E := E)).comp
            (A.comp (modularComplexI (E := E)))) := by
          simp [ContinuousLinearMap.comp_assoc]

lemma phaseAxisForce_phase_odd
    (H : EndH) :
    IsPhaseAntilinear (E := E) (phaseAxisForce (E := E) H) := by
  rw [phaseAxisForce_eq_from_phaseAntilinearPart (E := E) H]
  have hA :
      IsPhaseAntilinear (E := E) (phaseAntilinearPart (E := E) H) :=
    phaseAntilinearPart_isPhaseAntilinear (E := E) H
  have hComp :
      IsPhaseAntilinear (E := E)
        ((phaseAntilinearPart (E := E) H).comp (modularComplexI (E := E))) :=
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
On the star-certified conformal surface, the Hestenes-twisted QGT Berry sector
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

end InfoGeometry.Quantum
