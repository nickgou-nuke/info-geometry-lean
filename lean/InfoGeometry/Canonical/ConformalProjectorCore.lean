import InfoGeometry.Canonical.GrandUnificationMetric
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.AnomalyGauge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin
open SpectralInference
open InfoGeometry.Canonical.KKTCore
open AnomalyGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Conformal Inference Structure.
Formalizes the unification of Conformal Algebra, Generalized Inverses,
and Geometric Chirality.
-/
abbrev ConformalInference (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] := InfoGeometry.Canonical.InverseKernel E

namespace ConformalInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Native compatibility view for clients that previously traversed the redundant
conformal wrapper before reaching the canonical inverse-kernel carrier. -/
abbrev toInverseKernel (CI : ConformalInference E) :
    InfoGeometry.Canonical.InverseKernel E := CI

end ConformalInference

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

/--
Star-certified conformal inference package.

This strengthens `CertifiedConformalInference` with an explicit certification
that the Drazin spectral projector is self-adjoint.
-/
structure StarCertifiedConformalInference (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] extends CertifiedConformalInference E where
  spectralProjector_star :
    star (A * A_D) = A * A_D

/--
Projector-agreement-certified conformal inference package.

This strengthens `CertifiedConformalInference` with an explicit certification
that the Moore-Penrose right and left projectors coincide.
-/
structure ProjectorAgreementCertifiedConformalInference (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] extends CertifiedConformalInference E where
  projectorAgreement :
    IsMoorePenroseInverse.rightProjector A A_MP =
      IsMoorePenroseInverse.leftProjector A A_MP

namespace CertifiedInverseKernel

variable (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)

/-- Adapter from the canonical certified inverse-kernel owner to the conformal
surface. -/
abbrev toConformalInference : ConformalInference E :=
  CIK.toInverseKernel'

/-- Certified adapter from the inverse-kernel owner to the certified conformal
surface. -/
abbrev toCertifiedConformalInference : CertifiedConformalInference E :=
  { A := CIK.A
    A_D := CIK.A_D
    A_MP := CIK.A_MP
    drazinIndex := CIK.drazinIndex
    hDrazin := CIK.hDrazin
    hMoorePenrose := CIK.hMoorePenrose }

end CertifiedInverseKernel

namespace CertifiedConformalInference

variable (CCI : CertifiedConformalInference E)

/-- Native view of the certified carrier as its canonical inverse kernel. -/
abbrev toConformalInference : ConformalInference E :=
  { A := CCI.A, A_D := CCI.A_D, A_MP := CCI.A_MP }

/-- Adapter from the conformal surface to the canonical certified inverse kernel. -/
abbrev toCertifiedInverseKernel : InfoGeometry.Canonical.CertifiedInverseKernel E :=
  { A := CCI.A
    A_D := CCI.A_D
    A_MP := CCI.A_MP
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

/-- Certified left-projector anomaly commutator. -/
def chiralAnomaly : E →L[ℝ] E :=
  CCI.spectralProjector * CCI.metricProjector - CCI.metricProjector * CCI.spectralProjector

/-- Certified operator alias for the canonical left-projector anomaly. -/
abbrev chiralAnomalyOperator : E →L[ℝ] E := CCI.chiralAnomaly

/-- Explicit certified left-projector anomaly alias. -/
abbrev leftChiralAnomaly : E →L[ℝ] E := CCI.chiralAnomaly

/-- Explicit certified left-projector anomaly operator alias. -/
abbrev leftChiralAnomalyOperator : E →L[ℝ] E := CCI.leftChiralAnomaly

/-- Certified right-projector anomaly commutator. -/
def rightChiralAnomaly : E →L[ℝ] E :=
  CCI.spectralProjector * CCI.mpRangeProjector - CCI.mpRangeProjector * CCI.spectralProjector

/-- Certified operator alias for the right-projector anomaly. -/
abbrev rightChiralAnomalyOperator : E →L[ℝ] E := CCI.rightChiralAnomaly

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

/-- The certified Drazin spectral projector is self-adjoint if `A` and `A_D` are. -/
theorem spectralProjector_star_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    star CCI.spectralProjector = CCI.spectralProjector := by
  simpa [CertifiedConformalInference.spectralProjector] using
    CCI.toCertifiedInverseKernel.spectralProjector_star_of_isSelfAdjoint
      (by simpa [CertifiedConformalInference.toCertifiedInverseKernel] using hA)
      (by simpa [CertifiedConformalInference.toCertifiedInverseKernel] using hAD)

/-- The certified Drazin spectral projector is self-adjoint if `A` and `A_D` are. -/
theorem spectralProjector_isSelfAdjoint_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    IsSelfAdjoint CCI.spectralProjector := by
  simpa [CertifiedConformalInference.spectralProjector] using
    CCI.toCertifiedInverseKernel.spectralProjector_isSelfAdjoint_of_isSelfAdjoint
      (by simpa [CertifiedConformalInference.toCertifiedInverseKernel] using hA)
      (by simpa [CertifiedConformalInference.toCertifiedInverseKernel] using hAD)

/-- The certified left anomaly commutator is skew-adjoint if `A` and `A_D` are. -/
theorem leftAnomalyCommutator_star_eq_neg_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    star (CCI.spectralProjector * CCI.metricProjector
        - CCI.metricProjector * CCI.spectralProjector) =
      -(CCI.spectralProjector * CCI.metricProjector
        - CCI.metricProjector * CCI.spectralProjector) := by
  exact commutator_is_skew_adjoint CCI.spectralProjector CCI.metricProjector
    (CCI.spectralProjector_star_of_isSelfAdjoint hA hAD)
    CCI.metricProjector_star

/-- The certified right anomaly commutator is skew-adjoint if `A` and `A_D` are. -/
theorem rightAnomalyCommutator_star_eq_neg_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    star (CCI.spectralProjector * CCI.mpRangeProjector
        - CCI.mpRangeProjector * CCI.spectralProjector) =
      -(CCI.spectralProjector * CCI.mpRangeProjector
        - CCI.mpRangeProjector * CCI.spectralProjector) := by
  exact commutator_is_skew_adjoint CCI.spectralProjector CCI.mpRangeProjector
    (CCI.spectralProjector_star_of_isSelfAdjoint hA hAD)
    CCI.mpRangeProjector_star

/--
The canonical left-projector anomaly operator is skew-adjoint on the certified
conformal surface once `A` and `A_D` are self-adjoint.
-/
theorem chiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    star CCI.chiralAnomalyOperator = -CCI.chiralAnomalyOperator := by
  simpa [CertifiedConformalInference.chiralAnomalyOperator,
    CertifiedConformalInference.chiralAnomaly] using
      CCI.leftAnomalyCommutator_star_eq_neg_of_isSelfAdjoint hA hAD

/-- Explicit left-projector alias for certified skew-adjointness of `χ_L`. -/
theorem leftChiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    star CCI.leftChiralAnomalyOperator = -CCI.leftChiralAnomalyOperator := by
  exact CCI.chiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint hA hAD

/-- The certified right-projector anomaly operator is skew-adjoint if `A` and `A_D` are. -/
theorem rightChiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
    star CCI.rightChiralAnomalyOperator = -CCI.rightChiralAnomalyOperator := by
  simpa [CertifiedConformalInference.rightChiralAnomalyOperator,
    CertifiedConformalInference.rightChiralAnomaly] using
      CCI.rightAnomalyCommutator_star_eq_neg_of_isSelfAdjoint hA hAD

end CertifiedConformalInference

namespace ProjectorAgreementCertifiedConformalInference

variable (PCCI : ProjectorAgreementCertifiedConformalInference E)

/-- The explicit right/left Moore-Penrose projector agreement witness. -/
theorem rightProjector_eq_leftProjector :
    IsMoorePenroseInverse.rightProjector PCCI.A PCCI.A_MP =
      IsMoorePenroseInverse.leftProjector PCCI.A PCCI.A_MP :=
  PCCI.projectorAgreement

/-- Certified-kernel form of projector agreement. -/
theorem mpRangeProjector_eq_metricProjector :
    PCCI.toCertifiedConformalInference.mpRangeProjector
      = PCCI.toCertifiedConformalInference.metricProjector := by
  change IsMoorePenroseInverse.rightProjector PCCI.A PCCI.A_MP =
    IsMoorePenroseInverse.leftProjector PCCI.A PCCI.A_MP
  exact PCCI.rightProjector_eq_leftProjector

/-- Under projector-agreement certification, the right and left certified
anomaly conventions coincide. -/
theorem rightChiralAnomaly_eq_chiralAnomaly :
    PCCI.toCertifiedConformalInference.rightChiralAnomaly
      = PCCI.toCertifiedConformalInference.chiralAnomaly := by
  exact
    PCCI.toCertifiedConformalInference.rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement
      (PCCI.mpRangeProjector_eq_metricProjector)

end ProjectorAgreementCertifiedConformalInference

namespace CertifiedConformalInference

variable (CCI : CertifiedConformalInference E)

/--
Package constructor: if `A` and `A_D` are self-adjoint, the certified conformal
surface upgrades to the star-certified surface with explicit `star P_D = P_D`.
-/
def toStarCertifiedConformalInference
    (hA : IsSelfAdjoint CCI.A)
    (hAD : IsSelfAdjoint CCI.A_D) :
  StarCertifiedConformalInference E where
  A := CCI.A
  A_D := CCI.A_D
  A_MP := CCI.A_MP
  drazinIndex := CCI.drazinIndex
  hDrazin := CCI.hDrazin
  hMoorePenrose := CCI.hMoorePenrose
  spectralProjector_star := CCI.spectralProjector_star_of_isSelfAdjoint hA hAD

/--
Package constructor: if left/right Moore-Penrose projectors agree, the
certified conformal surface upgrades to projector-agreement-certified form.
-/
def toProjectorAgreementCertifiedConformalInference
    (hProj :
      IsMoorePenroseInverse.rightProjector CCI.A CCI.A_MP =
        IsMoorePenroseInverse.leftProjector CCI.A CCI.A_MP) :
  ProjectorAgreementCertifiedConformalInference E where
  A := CCI.A
  A_D := CCI.A_D
  A_MP := CCI.A_MP
  drazinIndex := CCI.drazinIndex
  hDrazin := CCI.hDrazin
  hMoorePenrose := CCI.hMoorePenrose
  projectorAgreement := hProj

end CertifiedConformalInference

namespace StarCertifiedConformalInference

variable (SCI : StarCertifiedConformalInference E)

/-- Adapter from star-certified conformal data to certified inverse-kernel data. -/
abbrev toCertifiedInverseKernel : InfoGeometry.Canonical.CertifiedInverseKernel E :=
  SCI.toCertifiedConformalInference.toCertifiedInverseKernel

/-- The star-certified Drazin spectral projector. -/
abbrev spectralProjector : E →L[ℝ] E := SCI.toCertifiedConformalInference.spectralProjector

/-- The star-certified Moore-Penrose range projector. -/
abbrev mpRangeProjector : E →L[ℝ] E := SCI.toCertifiedConformalInference.mpRangeProjector

/-- The star-certified Moore-Penrose domain projector. -/
abbrev metricProjector : E →L[ℝ] E := SCI.toCertifiedConformalInference.metricProjector

/-- Star-certified left-projector anomaly commutator. -/
abbrev chiralAnomaly : E →L[ℝ] E := SCI.toCertifiedConformalInference.chiralAnomaly

/-- Star-certified operator alias for the canonical left anomaly commutator. -/
abbrev chiralAnomalyOperator : E →L[ℝ] E := SCI.toCertifiedConformalInference.chiralAnomalyOperator

/-- Explicit star-certified left anomaly alias. -/
abbrev leftChiralAnomaly : E →L[ℝ] E := SCI.toCertifiedConformalInference.leftChiralAnomaly

/-- Explicit star-certified left anomaly operator alias. -/
abbrev leftChiralAnomalyOperator : E →L[ℝ] E := SCI.toCertifiedConformalInference.leftChiralAnomalyOperator

/-- Star-certified right-projector anomaly commutator. -/
abbrev rightChiralAnomaly : E →L[ℝ] E := SCI.toCertifiedConformalInference.rightChiralAnomaly

/-- Star-certified operator alias for the right anomaly commutator. -/
abbrev rightChiralAnomalyOperator : E →L[ℝ] E := SCI.toCertifiedConformalInference.rightChiralAnomalyOperator

/-- The star-certified Moore-Penrose domain projector is self-adjoint. -/
theorem metricProjector_star :
    star SCI.metricProjector = SCI.metricProjector := by
  simpa [StarCertifiedConformalInference.metricProjector] using
    SCI.toCertifiedConformalInference.metricProjector_star

/-- The star-certified Drazin spectral projector is self-adjoint. -/
theorem spectralProjector_star_eq :
    star SCI.spectralProjector = SCI.spectralProjector := by
  simpa [StarCertifiedConformalInference.spectralProjector,
    CertifiedConformalInference.spectralProjector,
    CertifiedConformalInference.toCertifiedInverseKernel,
    CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.spectralProjector, IsDrazinInverse.projection] using
      SCI.spectralProjector_star

/-- The star-certified Moore-Penrose range projector is self-adjoint. -/
theorem mpRangeProjector_star :
    star SCI.mpRangeProjector = SCI.mpRangeProjector := by
  simpa [StarCertifiedConformalInference.mpRangeProjector] using
    SCI.toCertifiedConformalInference.mpRangeProjector_star

/-- The star-certified left anomaly commutator is skew-adjoint. -/
theorem leftAnomalyCommutator_star_eq_neg :
    star (SCI.spectralProjector * SCI.metricProjector
        - SCI.metricProjector * SCI.spectralProjector) =
      -(SCI.spectralProjector * SCI.metricProjector
        - SCI.metricProjector * SCI.spectralProjector) := by
  exact commutator_is_skew_adjoint SCI.spectralProjector SCI.metricProjector
    (SCI.spectralProjector_star_eq)
    SCI.metricProjector_star

/-- The star-certified right anomaly commutator is skew-adjoint. -/
theorem rightAnomalyCommutator_star_eq_neg :
    star (SCI.spectralProjector * SCI.mpRangeProjector
        - SCI.mpRangeProjector * SCI.spectralProjector) =
      -(SCI.spectralProjector * SCI.mpRangeProjector
        - SCI.mpRangeProjector * SCI.spectralProjector) := by
  exact commutator_is_skew_adjoint SCI.spectralProjector SCI.mpRangeProjector
    (SCI.spectralProjector_star_eq)
    SCI.mpRangeProjector_star

/-- The canonical star-certified left anomaly operator is skew-adjoint. -/
theorem chiralAnomalyOperator_star_eq_neg :
    star SCI.chiralAnomalyOperator = -SCI.chiralAnomalyOperator := by
  simpa [StarCertifiedConformalInference.chiralAnomalyOperator,
    StarCertifiedConformalInference.chiralAnomaly,
    CertifiedConformalInference.chiralAnomalyOperator,
    CertifiedConformalInference.chiralAnomaly] using
      SCI.leftAnomalyCommutator_star_eq_neg

/-- Explicit left-projector alias for star-certified skew-adjointness of `χ_L`. -/
theorem leftChiralAnomalyOperator_star_eq_neg :
    star SCI.leftChiralAnomalyOperator = -SCI.leftChiralAnomalyOperator := by
  exact SCI.chiralAnomalyOperator_star_eq_neg

/-- The star-certified right anomaly operator is skew-adjoint. -/
theorem rightChiralAnomalyOperator_star_eq_neg :
    star SCI.rightChiralAnomalyOperator = -SCI.rightChiralAnomalyOperator := by
  simpa [StarCertifiedConformalInference.rightChiralAnomalyOperator,
    StarCertifiedConformalInference.rightChiralAnomaly,
    CertifiedConformalInference.rightChiralAnomalyOperator,
    CertifiedConformalInference.rightChiralAnomaly] using
      SCI.rightAnomalyCommutator_star_eq_neg

end StarCertifiedConformalInference

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
Vanishing singular Einstein anomaly is equivalent to vanishing right-projector
chiral anomaly.
-/
theorem einsteinAnomaly_eq_zero_iff_rightChiralAnomaly_eq_zero :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = 0
      ↔ CI.rightChiralAnomalyOperator = 0 := by
  constructor
  · intro hE
    rw [CI.singularEinsteinAnomaly_eq_neg_rightChiralAnomaly] at hE
    simpa [rightChiralAnomalyOperator] using hE
  · intro hχR
    rw [CI.singularEinsteinAnomaly_eq_neg_rightChiralAnomaly]
    simpa [rightChiralAnomalyOperator, hχR]

/--
Under projector agreement, vanishing singular Einstein anomaly is equivalent to
vanishing left-projector chiral anomaly.
-/
theorem einsteinAnomaly_eq_zero_iff_leftChiralAnomaly_eq_zero_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CI.A CI.A_MP =
        IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = 0
      ↔ CI.leftChiralAnomalyOperator = 0 := by
  constructor
  · intro hE
    rw [CI.singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement hProj] at hE
    simpa using hE
  · intro hχL
    rw [CI.singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement hProj]
    simpa [hχL]

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
Under Moore-Penrose projector agreement, commutation with the left metric
projector implies commutation with the right range projector.
-/
theorem rightProjector_commute_of_projectorAgreement_of_metricProjector_commute
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D := by
  simpa [hProj] using hLeft

/--
Structured dilation-source closure:
if left/right Moore-Penrose projectors agree and the Drazin projector commutes
with the left metric projector, then the dilation commutator is
`-1/2` times the left anomaly.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_projectorAgreement_of_metricProjector_commute
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D =
      -((2 : ℝ)⁻¹) • CI.chiralAnomalyOperator := by
  exact
    CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute
      (CI.rightProjector_commute_of_projectorAgreement_of_metricProjector_commute hProj hLeft)

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
Under right-projector commutation, the dilation commutator vanishes exactly
when the chiral anomaly vanishes.
-/
theorem spectralProjector_commutator_dilation_eq_zero_iff_chiralAnomaly_eq_zero_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 ↔ CI.chiralAnomalyOperator = 0 := by
  constructor
  · intro hComm
    have hEq :=
      spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute
        (CI := CI) hRight
    rw [hComm] at hEq
    have hzero : ((2 : ℝ)⁻¹) • CI.chiralAnomalyOperator = 0 := by
      have hEq' : 0 = -(((2 : ℝ)⁻¹) • CI.chiralAnomalyOperator) := by
        simpa [neg_smul] using hEq
      simpa using hEq'
    have hscalar : ((2 : ℝ)⁻¹) ≠ 0 := by
      norm_num
    exact Or.resolve_left (smul_eq_zero.mp hzero) hscalar
  · intro hχ
    exact CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero
      hRight hχ

/--
Left-projector notation variant of the same vanishing equivalence.
-/
theorem spectralProjector_commutator_dilation_eq_zero_iff_leftChiralAnomaly_eq_zero_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 ↔ CI.leftChiralAnomalyOperator = 0 := by
  simpa [leftChiralAnomalyOperator] using
    CI.spectralProjector_commutator_dilation_eq_zero_iff_chiralAnomaly_eq_zero_of_rightProjector_commute
      hRight

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
Under projector agreement, vanishing singular Einstein anomaly is equivalent to
spectral/metric projector commutation.
-/
theorem einsteinAnomaly_eq_zero_iff_projectors_commute_of_projectorAgreement
    (hProj :
      IsMoorePenroseInverse.rightProjector CI.A CI.A_MP =
        IsMoorePenroseInverse.leftProjector CI.A CI.A_MP) :
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  calc
    InfoGeometry.Canonical.EinsteinAnomaly CI.A CI.A_MP CI.A_D = 0
        ↔ CI.leftChiralAnomalyOperator = 0 :=
      CI.einsteinAnomaly_eq_zero_iff_leftChiralAnomaly_eq_zero_of_projectorAgreement hProj
    _ ↔ CI.spectralChiralProjector * CI.metricChiralProjector
          = CI.metricChiralProjector * CI.spectralChiralProjector :=
      CI.leftChiralAnomalyOperator_eq_zero_iff_projectors_commute

/--
Under right-projector commutation, vanishing dilation commutator is equivalent
to spectral/metric projector commutation.
-/
theorem spectralProjector_commutator_dilation_eq_zero_iff_projectors_commute_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 ↔
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector := by
  calc
    CI.P_D * CI.D - CI.D * CI.P_D = 0
        ↔ CI.chiralAnomalyOperator = 0 :=
      CI.spectralProjector_commutator_dilation_eq_zero_iff_chiralAnomaly_eq_zero_of_rightProjector_commute
        hRight
    _ ↔ CI.spectralChiralProjector * CI.metricChiralProjector
          = CI.metricChiralProjector * CI.spectralChiralProjector :=
      CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute

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

namespace CertifiedConformalInference

variable [FiniteDimensional ℝ E]

/--
Finite-dimensional constructor: any certified spectral triple induces a
`CertifiedConformalInference` package on the same base Dirac operator.
-/
theorem exists_of_spectralTriple
    (ST : SpectralInference.SpectralTriple E) :
    ∃ CCI : CertifiedConformalInference E, CCI.A = ST.D := by
  rcases SpectralInference.CertifiedChiralSpectralTriple.exists_of_spectralTriple
      (E := E) ST with ⟨CCST, hST⟩
  subst hST
  refine ⟨
    CertifiedInverseKernel.toCertifiedConformalInference (E := E) CCST.toCertifiedInverseKernel,
    rfl
  ⟩

/--
Finite-dimensional constructor specialized to `InfoSpectralTriple`.
-/
theorem exists_of_infoSpectralTriple
    (IST : SpectralInference.InfoSpectralTriple E) :
    ∃ CCI : CertifiedConformalInference E, CCI.A = IST.D :=
  exists_of_spectralTriple (E := E) IST.toSpectralTriple

end CertifiedConformalInference

end InfoGeometry.Canonical.ConformalUnification
