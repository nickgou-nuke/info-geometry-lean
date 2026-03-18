import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.MoorePenrose
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

/-!
# Certified Inverse Kernel

Canonical proof-carrying center for operator packages that carry both a Drazin
and a Moore-Penrose regularization. Downstream surfaces such as conformal,
spectral, and modular theories should adapt to this kernel rather than re-bundle
the same inverse data ad hoc.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Witness-level inverse kernel with chosen Drazin and Moore-Penrose data. -/
structure InverseKernel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  A : E →L[ℝ] E
  A_D : E →L[ℝ] E
  A_MP : E →L[ℝ] E

/--
Proof-carrying certified inverse kernel. This is the canonical center bundle for
inverse/projector/anomaly data.
-/
structure CertifiedInverseKernel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] extends InverseKernel E where
  drazinIndex : ℕ
  hDrazin : IsDrazinInverse A A_D drazinIndex
  hMoorePenrose : IsMoorePenroseInverse A A_MP

namespace InverseKernel

variable (IK : InverseKernel E)

/-- The Drazin spectral projector attached to the kernel. -/
abbrev spectralProjector : E →L[ℝ] E :=
  IsDrazinInverse.projection IK.A IK.A_D

/-- The Moore-Penrose range projector attached to the kernel. -/
abbrev mpRangeProjector : E →L[ℝ] E :=
  IsMoorePenroseInverse.rightProjector IK.A IK.A_MP

/-- The Moore-Penrose domain projector attached to the kernel. -/
abbrev metricProjector : E →L[ℝ] E :=
  IsMoorePenroseInverse.leftProjector IK.A IK.A_MP

/-- Spectral-metric projector mismatch. -/
def projectorMismatch : E →L[ℝ] E :=
  IK.spectralProjector - IK.metricProjector

/-- Left-projector anomaly commutator. -/
def chiralAnomaly : E →L[ℝ] E :=
  IK.spectralProjector * IK.metricProjector - IK.metricProjector * IK.spectralProjector

/-- Right-projector anomaly commutator. -/
def rightChiralAnomaly : E →L[ℝ] E :=
  IK.spectralProjector * IK.mpRangeProjector - IK.mpRangeProjector * IK.spectralProjector

/-- Half-difference between the Moore-Penrose range and domain projectors. -/
noncomputable def dilationGap : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (IK.mpRangeProjector - IK.metricProjector)

/-- Norm of the certified left-projector anomaly commutator. -/
noncomputable def chiralScale : ℝ :=
  nnnorm IK.chiralAnomaly

end InverseKernel

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Forgetful map from the certified kernel to the witness-level kernel. -/
abbrev toInverseKernel' : InverseKernel E :=
  CIK.toInverseKernel

/-- Certified Drazin spectral projector. -/
abbrev spectralProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.spectralProjector

/-- Certified Moore-Penrose range projector. -/
abbrev mpRangeProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.mpRangeProjector

/-- Certified Moore-Penrose domain projector. -/
abbrev metricProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.metricProjector

/-- Certified projector mismatch. -/
abbrev projectorMismatch : E →L[ℝ] E :=
  CIK.toInverseKernel'.projectorMismatch

/-- Certified left-projector anomaly commutator. -/
abbrev chiralAnomaly : E →L[ℝ] E :=
  CIK.toInverseKernel'.chiralAnomaly

/-- Certified right-projector anomaly commutator. -/
abbrev rightChiralAnomaly : E →L[ℝ] E :=
  CIK.toInverseKernel'.rightChiralAnomaly

/-- Certified half-difference between Moore-Penrose projectors. -/
noncomputable abbrev dilationGap : E →L[ℝ] E :=
  CIK.toInverseKernel'.dilationGap

/-- Certified anomaly scale. -/
noncomputable abbrev chiralScale : ℝ :=
  CIK.toInverseKernel'.chiralScale

/-- The certified Drazin projector is idempotent. -/
theorem spectralProjector_idempotent :
    CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector := by
  simpa [CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.spectralProjector] using
    IsDrazinInverse.projection_is_idempotent CIK.hDrazin

/-- The certified Moore-Penrose range projector is idempotent. -/
theorem mpRangeProjector_idempotent :
    CIK.mpRangeProjector * CIK.mpRangeProjector = CIK.mpRangeProjector := by
  simpa [CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.mpRangeProjector] using
    IsMoorePenroseInverse.rightProjector_idempotent CIK.hMoorePenrose

/-- The certified Moore-Penrose domain projector is idempotent. -/
theorem metricProjector_idempotent :
    CIK.metricProjector * CIK.metricProjector = CIK.metricProjector := by
  simpa [CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.metricProjector] using
    IsMoorePenroseInverse.leftProjector_idempotent CIK.hMoorePenrose

/-- The certified Moore-Penrose range projector is self-adjoint. -/
theorem mpRangeProjector_star :
    star CIK.mpRangeProjector = CIK.mpRangeProjector := by
  simpa [CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.mpRangeProjector] using
    IsMoorePenroseInverse.rightProjector_star CIK.hMoorePenrose

/-- The certified Moore-Penrose domain projector is self-adjoint. -/
theorem metricProjector_star :
    star CIK.metricProjector = CIK.metricProjector := by
  simpa [CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.metricProjector] using
    IsMoorePenroseInverse.leftProjector_star CIK.hMoorePenrose

end CertifiedInverseKernel

end InfoGeometry.Canonical
