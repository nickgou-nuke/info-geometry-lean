import InfoGeometry.Canonical.GrandUnificationMetric
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.KKTCore
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.KKTCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Conformal Inference Structure.
Formalizes the unification of Conformal Algebra, Generalized Inverses,
and Geometric Chirality.
-/
structure ConformalInference (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] extends InfoGeometry.Canonical.InverseKernel E where

/--
Certified conformal inference package.

This is the proof-carrying refinement of `ConformalInference`: the supplied
Drazin and Moore-Penrose regularizations are certified against the base
operator `A`.
-/
structure CertifiedConformalInference (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] extends ConformalInference E where
  drazinIndex : ℕ
  hDrazin : IsDrazinInverse A A_D drazinIndex
  hMoorePenrose : IsMoorePenroseInverse A A_MP

namespace CertifiedConformalInference

variable (CCI : CertifiedConformalInference E)

/-- Adapter from the conformal surface to the canonical certified inverse kernel. -/
abbrev toCertifiedInverseKernel : InfoGeometry.Canonical.CertifiedInverseKernel E :=
  { toInverseKernel := CCI.toConformalInference.toInverseKernel
    drazinIndex := CCI.drazinIndex
    hDrazin := CCI.hDrazin
    hMoorePenrose := CCI.hMoorePenrose }

/-- The certified Drazin spectral projector. -/
abbrev spectralProjector : E →L[ℝ] E := CCI.toCertifiedInverseKernel.spectralProjector

/-- The certified Moore-Penrose range projector. -/
abbrev mpRangeProjector : E →L[ℝ] E :=
  CCI.toCertifiedInverseKernel.mpRangeProjector

/-- The certified Moore-Penrose domain projector. -/
abbrev metricProjector : E →L[ℝ] E := CCI.toCertifiedInverseKernel.metricProjector

/-- The certified Drazin spectral projector is idempotent. -/
theorem spectralProjector_idempotent :
    CCI.spectralProjector * CCI.spectralProjector = CCI.spectralProjector := by
  simpa [CertifiedConformalInference.spectralProjector] using
    CCI.toCertifiedInverseKernel.spectralProjector_idempotent

/-- The certified Moore-Penrose range projector is idempotent. -/
theorem mpRangeProjector_idempotent :
    CCI.mpRangeProjector * CCI.mpRangeProjector = CCI.mpRangeProjector := by
  simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_idempotent

/-- The certified Moore-Penrose domain projector is idempotent. -/
theorem metricProjector_idempotent :
    CCI.metricProjector * CCI.metricProjector = CCI.metricProjector := by
  simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_idempotent

/-- The certified Moore-Penrose domain projector is self-adjoint. -/
theorem metricProjector_star :
    star CCI.metricProjector = CCI.metricProjector := by
  simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_star

/-- The certified Moore-Penrose range projector is self-adjoint. -/
theorem mpRangeProjector_star :
    star CCI.mpRangeProjector = CCI.mpRangeProjector := by
  simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_star

end CertifiedConformalInference

namespace ConformalInference

variable (CI : ConformalInference E)

/-! ### 1. Conformal Generators -/

/--
Information Translation Generator (P).
Identified with the primary information operator A.
-/
def P : E →L[ℝ] E := CI.A

/--
Special Conformal Information Generator (K).
Identified with the Moore-Penrose inverse A+, representing metric inversion.
-/
def K : E →L[ℝ] E := CI.A_MP

/--
Conformal inversion realization of the special conformal generator:
if `J` implements inversion on translation, then `K = J P J`.
-/
theorem specialConformal_eq_modularInversion_translation
    (J : E →L[ℝ] E)
    (hJPJ : J * CI.P * J = CI.K) :
    CI.K = J * CI.P * J := by
  simpa using hJPJ.symm

/--
Involutive inversion (`J² = 1`) recovers translation from special conformal
generator: `P = J K J`.
-/
theorem translation_eq_modularInversion_specialConformal
    (J : E →L[ℝ] E)
    (hJ2 : J * J = (1 : E →L[ℝ] E))
    (hJPJ : J * CI.P * J = CI.K) :
    J * CI.K * J = CI.P := by
  calc
    J * CI.K * J = J * (J * CI.P * J) * J := by rw [hJPJ]
    _ = (J * J) * CI.P * (J * J) := by
          simp [mul_assoc]
    _ = (1 : E →L[ℝ] E) * CI.P * (1 : E →L[ℝ] E) := by
          simp [hJ2]
    _ = CI.P := by simp

/--
Emergent Information Dilation Generator (D).
D = 1/2 [P, K].
This operator generates the 'Information Scale' flow.
-/
noncomputable def D : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.P * CI.K - CI.K * CI.P)

/--
The dilation operator is exactly half the difference between the Moore-Penrose
range and domain projectors.
-/
theorem dilation_eq_half_sub_mp_projectors :
    CI.D =
      ((2 : ℝ)⁻¹) •
        (IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
          - IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) := by
  simp [D, P, K, IsMoorePenroseInverse.rightProjector, IsMoorePenroseInverse.leftProjector]

/-! ### 2. Chiral Projectors and Anomaly -/

/--
Spectral Chiral Projector (P_D).
Filters the belief space based on algebraic/nilpotent structure.
-/
def P_D : E →L[ℝ] E := IsDrazinInverse.projection CI.A CI.A_D

/-- Canonical naming alias for the spectral chiral projector. -/
abbrev spectralChiralProjector : E →L[ℝ] E := CI.P_D

/--
Metric Chiral Projector (P_MP).
Filters the belief space based on metric orthogonality.
-/
def P_MP : E →L[ℝ] E := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP

/-- Canonical naming alias for the metric chiral projector. -/
abbrev metricChiralProjector : E →L[ℝ] E := CI.P_MP

/--
Moore-Penrose range projector.
This is the right-projector convention used by `Singular.EinsteinAnomaly`.
-/
def P_MP_right : E →L[ℝ] E := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP

/-- Canonical naming alias for the right Moore-Penrose projector. -/
abbrev metricRangeProjector : E →L[ℝ] E := CI.P_MP_right

/--
The Geometric Chiral Anomaly (χ).
χ = [P_D, P_MP].
This measures the topological 'twist' between information gain and metric distance.
-/
noncomputable def chiralAnomaly : E →L[ℝ] E :=
  CI.P_D * CI.P_MP - CI.P_MP * CI.P_D

/-- Canonical naming alias for the chiral-anomaly operator. -/
noncomputable abbrev chiralAnomalyOperator : E →L[ℝ] E := CI.chiralAnomaly

/--
Explicit left-projector convention alias for the canonical chiral anomaly.

In this repository, the unqualified `chiralAnomaly` is the left-projector
anomaly `χ_L = [P_D, P_MP_left]`.
-/
noncomputable abbrev leftChiralAnomaly : E →L[ℝ] E := CI.chiralAnomaly

/-- Explicit operator alias for the canonical left-projector anomaly `χ_L`. -/
noncomputable abbrev leftChiralAnomalyOperator : E →L[ℝ] E := CI.leftChiralAnomaly

/--
KKT operator bridge: if `A`, `A_MP`, and `A_D` occupy the expected `g₁/g₋₁`
wings for a split-`Cl(1,1)` action, then the projector-obstruction operator
lies in grade zero.
-/
@[rep_depth krein] theorem chiralAnomalyOperator_isGZero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    IsGZero X CI.chiralAnomalyOperator := by
  have hAanti :
      X.eps * CI.A = -(CI.A * X.eps) :=
    eps_mul_eq_neg_mul_eps_of_isGOne (X := X) (A := CI.A) hA
  have hAMPanti :
      X.eps * CI.A_MP = -(CI.A_MP * X.eps) :=
    eps_mul_eq_neg_mul_eps_of_isGNegOne (X := X) (A := CI.A_MP) hAMP
  have hADanti :
      X.eps * CI.A_D = -(CI.A_D * X.eps) :=
    eps_mul_eq_neg_mul_eps_of_isGNegOne (X := X) (A := CI.A_D) hAD
  have hPDcomm :
      X.eps * CI.P_D = CI.P_D * X.eps := by
    unfold P_D IsDrazinInverse.projection
    calc
      X.eps * (CI.A * CI.A_D)
          = (X.eps * CI.A) * CI.A_D := by simp [mul_assoc]
      _ = (-(CI.A * X.eps)) * CI.A_D := by rw [hAanti]
      _ = -(CI.A * (X.eps * CI.A_D)) := by simp [mul_assoc]
      _ = -(CI.A * (-(CI.A_D * X.eps))) := by rw [hADanti]
      _ = CI.A * (CI.A_D * X.eps) := by simp
      _ = (CI.A * CI.A_D) * X.eps := by simp [mul_assoc]
  have hPMPcomm :
      X.eps * CI.P_MP = CI.P_MP * X.eps := by
    unfold P_MP IsMoorePenroseInverse.leftProjector
    calc
      X.eps * (CI.A_MP * CI.A)
          = (X.eps * CI.A_MP) * CI.A := by simp [mul_assoc]
      _ = (-(CI.A_MP * X.eps)) * CI.A := by rw [hAMPanti]
      _ = -(CI.A_MP * (X.eps * CI.A)) := by simp [mul_assoc]
      _ = -(CI.A_MP * (-(CI.A * X.eps))) := by rw [hAanti]
      _ = CI.A_MP * (CI.A * X.eps) := by simp
      _ = (CI.A_MP * CI.A) * X.eps := by simp [mul_assoc]
  have hObsComm :
      X.eps * CI.chiralAnomalyOperator = CI.chiralAnomalyOperator * X.eps := by
    unfold chiralAnomalyOperator chiralAnomaly
    apply ContinuousLinearMap.ext
    intro u
    have hPDu : X.eps (CI.P_D u) = CI.P_D (X.eps u) := by
      simpa using congrArg (fun F : E →L[ℝ] E => F u) hPDcomm
    have hPMPu : X.eps (CI.P_MP u) = CI.P_MP (X.eps u) := by
      simpa using congrArg (fun F : E →L[ℝ] E => F u) hPMPcomm
    have hPDPMPu : X.eps (CI.P_D (CI.P_MP u)) = CI.P_D (CI.P_MP (X.eps u)) := by
      have h := congrArg (fun F : E →L[ℝ] E => F (CI.P_MP u)) hPDcomm
      simpa [hPMPu] using h
    have hPMPPDu : X.eps (CI.P_MP (CI.P_D u)) = CI.P_MP (CI.P_D (X.eps u)) := by
      have h := congrArg (fun F : E →L[ℝ] E => F (CI.P_D u)) hPMPcomm
      simpa [hPDu] using h
    calc
      X.eps (CI.P_D (CI.P_MP u) - CI.P_MP (CI.P_D u))
          = X.eps (CI.P_D (CI.P_MP u)) - X.eps (CI.P_MP (CI.P_D u)) := by
              simp
      _ = CI.P_D (CI.P_MP (X.eps u)) - CI.P_MP (CI.P_D (X.eps u)) := by
            rw [hPDPMPu, hPMPPDu]
      _ = (CI.P_D * CI.P_MP - CI.P_MP * CI.P_D) (X.eps u) := by
            simp [sub_eq_add_neg, mul_assoc]
      _ = ((CI.P_D * CI.P_MP - CI.P_MP * CI.P_D) * X.eps) u := by
            simp [mul_assoc]
  exact isGZero_of_eps_commute (X := X) hObsComm

@[rep_depth krein] theorem chiralAnomalyOperator_gOnePart_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    gOnePart X CI.chiralAnomalyOperator = 0 := by
  exact gOnePart_eq_zero_of_isGZero (X := X)
    (A := CI.chiralAnomalyOperator)
    (CI.chiralAnomalyOperator_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD)

@[rep_depth krein] theorem chiralAnomalyOperator_gNegOnePart_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    gNegOnePart X CI.chiralAnomalyOperator = 0 := by
  exact gNegOnePart_eq_zero_of_isGZero (X := X)
    (A := CI.chiralAnomalyOperator)
    (CI.chiralAnomalyOperator_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD)

@[rep_depth krein] theorem chiralAnomalyOperator_eq_diagonal_blocks_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    CI.chiralAnomalyOperator
      = plusProjector X * CI.chiralAnomalyOperator * plusProjector X
        + minusProjector X * CI.chiralAnomalyOperator * minusProjector X := by
  exact InfoGeometry.Canonical.KKTCore.eq_diagonal_blocks_of_isGZero (X := X)
    (A := CI.chiralAnomalyOperator)
    (CI.chiralAnomalyOperator_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD)

@[rep_depth krein] theorem chiralAnomalyOperator_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    plusProjector X * CI.chiralAnomalyOperator * minusProjector X = 0 := by
  exact plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero (X := X)
    (A := CI.chiralAnomalyOperator)
    (CI.chiralAnomalyOperator_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD)

@[rep_depth krein] theorem chiralAnomalyOperator_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    minusProjector X * CI.chiralAnomalyOperator * plusProjector X = 0 := by
  exact minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero (X := X)
    (A := CI.chiralAnomalyOperator)
    (CI.chiralAnomalyOperator_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD)

/--
Right-projector chiral anomaly.
This is the anomaly built from the Moore-Penrose range projector instead of the
left projector used in `CI.chiralAnomaly`.
-/
noncomputable def rightChiralAnomaly : E →L[ℝ] E :=
  CI.P_D * CI.P_MP_right - CI.P_MP_right * CI.P_D

/-- Explicit operator alias for the right-projector anomaly `χ_R`. -/
noncomputable abbrev rightChiralAnomalyOperator : E →L[ℝ] E := CI.rightChiralAnomaly

/--
The singular Einstein anomaly is exactly the negative of the right-projector
chiral anomaly.
-/
theorem einsteinAnomaly_eq_neg_rightChiralAnomaly :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = -CI.rightChiralAnomaly := by
  unfold InfoGeometry.Canonical.EinsteinAnomaly rightChiralAnomaly P_D P_MP_right
  unfold IsDrazinInverse.projection IsMoorePenroseInverse.rightProjector
  noncomm_ring

/--
Singular Einstein anomaly bridge, explicitly labeled through the right anomaly
convention `χ_R`.
-/
theorem singularEinsteinAnomaly_eq_neg_rightChiralAnomaly :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D
      = -CI.rightChiralAnomalyOperator := by
  simpa [rightChiralAnomalyOperator] using CI.einsteinAnomaly_eq_neg_rightChiralAnomaly

/--
If the Moore-Penrose left and right projectors coincide, then the singular
Einstein anomaly is the negative of the conformal left-projector anomaly.
-/
theorem einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CI.A CI.A_MP =
        IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = -CI.chiralAnomalyOperator := by
  rw [CI.einsteinAnomaly_eq_neg_rightChiralAnomaly]
  simp [rightChiralAnomaly, chiralAnomalyOperator, chiralAnomaly, P_D, P_MP_right, P_MP, hProj]

/--
Under left/right Moore-Penrose projector agreement, the singular Einstein
anomaly is the negative of the canonical left-projector anomaly `χ_L`.
-/
theorem singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CI.A CI.A_MP =
        IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D
      = -CI.leftChiralAnomalyOperator := by
  simpa [leftChiralAnomalyOperator] using
    CI.einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement hProj

/--
The commutator of the Drazin spectral projector with the dilation operator
decomposes into the difference of its commutators with the Moore-Penrose range
and domain projectors.
-/
theorem spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators :
    CI.P_D * CI.D - CI.D * CI.P_D =
      ((2 : ℝ)⁻¹) •
        ((CI.P_D * IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
            - IsMoorePenroseInverse.rightProjector CI.A CI.A_MP * CI.P_D)
          -
          (CI.P_D * IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
            - IsMoorePenroseInverse.leftProjector CI.A CI.A_MP * CI.P_D)) := by
  rw [CI.dilation_eq_half_sub_mp_projectors]
  simp [sub_eq_add_neg, smul_sub]
  noncomm_ring

/--
Equivalent bridge form: the spectral-projector/dilation commutator is half the
difference between the spectral-vs-range-projector commutator and the chiral
anomaly operator.
-/
theorem spectralProjector_commutator_dilation_eq_half_sub_anomaly :
    CI.P_D * CI.D - CI.D * CI.P_D =
      ((2 : ℝ)⁻¹) •
        ((CI.P_D * IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
            - IsMoorePenroseInverse.rightProjector CI.A CI.A_MP * CI.P_D)
          - CI.chiralAnomalyOperator) := by
  rw [CI.spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators]
  simp [chiralAnomalyOperator, chiralAnomaly, P_MP, metricChiralProjector,
    IsMoorePenroseInverse.leftProjector]

/--
Bridge identity between the singular/right-projector anomaly convention and the
conformal/left-projector anomaly convention.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral :
    CI.P_D * CI.D - CI.D * CI.P_D =
      -((2 : ℝ)⁻¹) •
        (InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D + CI.chiralAnomalyOperator) := by
  rw [CI.spectralProjector_commutator_dilation_eq_half_sub_anomaly]
  rw [CI.einsteinAnomaly_eq_neg_rightChiralAnomaly]
  simp [rightChiralAnomaly, chiralAnomalyOperator, chiralAnomaly, P_MP_right,
    IsMoorePenroseInverse.rightProjector, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm, smul_add, smul_neg]

/--
If the Drazin spectral projector commutes with the Moore-Penrose right
projector, then its commutator with the conformal dilation generator is exactly
minus one half of the left-projector chiral anomaly.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D =
      -((2 : ℝ)⁻¹) • CI.chiralAnomalyOperator := by
  rw [CI.spectralProjector_commutator_dilation_eq_half_sub_anomaly]
  have hRightComm :
      CI.P_D * IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
        - IsMoorePenroseInverse.rightProjector CI.A CI.A_MP * CI.P_D = 0 := by
    rw [sub_eq_zero]
    simpa [P_MP_right] using hRight
  rw [hRightComm]
  simp [sub_eq_add_neg, chiralAnomalyOperator, smul_sub, smul_neg]

/--
Right-projector commutation collapse, explicitly labeled by the canonical
left-projector anomaly `χ_L`.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_leftChiralAnomaly_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D =
      -((2 : ℝ)⁻¹) • CI.leftChiralAnomalyOperator := by
  simpa [leftChiralAnomalyOperator] using
    CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute hRight

/--
If the Drazin spectral projector commutes with the Moore-Penrose right
projector and the chiral anomaly vanishes, then it commutes with the conformal
dilation generator.
-/
theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D)
    (hχ : CI.chiralAnomalyOperator = 0) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  rw [CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute hRight]
  simp [hχ]

/--
Specialized zero corollary, explicitly labeled with left-projector anomaly
notation.
-/
theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_leftChiralAnomaly_eq_zero
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D)
    (hχL : CI.leftChiralAnomalyOperator = 0) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  simpa [leftChiralAnomalyOperator] using
    CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero
      hRight hχL

/-! ### 3. Unification Theorems -/

/--
Theorem: The chiral anomaly vanishes exactly when the spectral and metric
projectors commute.
-/
theorem chiral_commutation_link :
    CI.chiralAnomaly = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  simp [chiralAnomaly, spectralChiralProjector, metricChiralProjector, sub_eq_zero]

/-- Vanishing anomaly iff spectral and metric projectors commute. -/
theorem chiralAnomalyOperator_eq_zero_iff_projectors_commute :
    CI.chiralAnomalyOperator = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  simpa [chiralAnomalyOperator] using (CI.chiral_commutation_link)

/-- Left-projector anomaly vanishing iff spectral and metric projectors commute. -/
theorem leftChiralAnomalyOperator_eq_zero_iff_projectors_commute :
    CI.leftChiralAnomalyOperator = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  simpa [leftChiralAnomalyOperator] using CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute

/--
Constructive forward direction: vanishing anomaly implies projector commutation.
-/
theorem projectors_commute_of_chiralAnomaly_eq_zero
    (hχ : CI.chiralAnomalyOperator = 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector :=
  (CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute).1 hχ

/--
Constructive reverse direction: projector commutation implies vanishing anomaly.
-/
theorem chiralAnomaly_eq_zero_of_projectors_commute
    (hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector) :
    CI.chiralAnomalyOperator = 0 :=
  (CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute).2 hComm


end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
