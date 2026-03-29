import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.DiracMetricCompatibility
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Krein.Metric
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Singular
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Determinant

namespace InfoGeometry.Canonical.SpectralInference

open InfoGeometry.Convex
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-! ### 1. Chains of Bayesian Steps (Max Caliber & Eikonal Paths) -/

/--
The discrete action (Eikonal integral) of a Bayesian chain.
According to the Max Caliber principle, this is the path-entropy
accumulated over a sequence of belief updates.
-/
noncomputable def bayesianAction (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, H.divergence (γ i) (γ (i + 1))

omit [FiniteDimensional ℝ E] in
@[simp] lemma bayesianAction_zero (H : HessianGeometry E) (γ : ℕ → E) :
    bayesianAction H γ 0 = 0 := by
  simp [bayesianAction]

omit [FiniteDimensional ℝ E] in
@[simp] lemma bayesianAction_succ (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ) :
    bayesianAction H γ (N + 1) = bayesianAction H γ N + H.divergence (γ N) (γ (N + 1)) := by
  unfold bayesianAction
  simpa using Finset.sum_range_succ (f := fun i => H.divergence (γ i) (γ (i + 1))) N

omit [FiniteDimensional ℝ E] in
/-- The spectral-chain Bayesian action is nonnegative. -/
theorem bayesianAction_nonneg (H : HessianGeometry E) (γ : ℕ → E) (N : ℕ) :
    0 ≤ bayesianAction H γ N := by
  unfold bayesianAction
  exact Finset.sum_nonneg (fun i _ => H.divergence_nonneg (γ i) (γ (i + 1)))

/-! ### 2. The Information Spectral Triple -/

/--
A toy finite-dimensional self-adjoint Dirac package.
Here the Hilbert space is `E`, the algebra is bounded linear operators `E →L[ℝ] E`,
and the Dirac operator `D` is a self-adjoint operator on `E`.
-/
structure SpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  D : E →L[ℝ] E
  is_self_adjoint : IsSelfAdjoint D

namespace SpectralTriple

variable (ST : SpectralTriple E)

/-- The commutator [A, B] = A * B - B * A -/
noncomputable def commutator (A B : E →L[ℝ] E) : E →L[ℝ] E :=
  A * B - B * A

/--
Inner fluctuation (Gauge field) A = a [D, b].
In Bayesian terms, this represents a localized information update or external evidence.
-/
noncomputable def gaugeField (a b : E →L[ℝ] E) : E →L[ℝ] E :=
  a * commutator ST.D b

/-- The perturbed Dirac operator D_A = D + A -/
noncomputable def perturbedDirac (A : E →L[ℝ] E) : E →L[ℝ] E :=
  ST.D + A

end SpectralTriple

/-! ### 3. Drazin Regularization and Spectral Action -/

/--
A witness-level regularized spectral triple.
The Dirac package is equipped with a chosen Drazin-regularization candidate `DD`,
but no certification is stored in this compatibility layer.
-/
structure RegularizedSpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  DD : E →L[ℝ] E -- The Drazin Inverse of D
  index : ℕ

/--
A proof-carrying regularized spectral triple.
This refines `RegularizedSpectralTriple` by certifying that `DD` is a Drazin
inverse of `D` with the stored index.
-/
structure CertifiedRegularizedSpectralTriple (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  DD : E →L[ℝ] E
  index : ℕ
  hDrazin : IsDrazinInverse D DD index

namespace RegularizedSpectralTriple

variable (RST : RegularizedSpectralTriple E)

/--
Reduced log-det spectral-action model.
In this finite-dimensional model we use the log-absolute Jacobian determinant of
the regularized Dirac operator as the scalar spectral-action proxy.
-/
noncomputable def spectralAction (Λ : ℝ) : ℝ :=
  Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • RST.DD))|)

end RegularizedSpectralTriple

namespace CertifiedRegularizedSpectralTriple

variable (CRST : CertifiedRegularizedSpectralTriple E)

/-- Forgetful map from the certified layer to the witness-level regularized package. -/
abbrev toRegularizedSpectralTriple : RegularizedSpectralTriple E :=
  { toSpectralTriple := CRST.toSpectralTriple
    DD := CRST.DD
    index := CRST.index }

/-- Certified regularized spectral-action model. -/
noncomputable def spectralAction (Λ : ℝ) : ℝ :=
  RegularizedSpectralTriple.spectralAction CRST.toRegularizedSpectralTriple Λ

/-
The following projector lemmas are purely algebraic and do not use the ambient
finite-dimensional hypothesis needed by the global constructors.
-/
omit [FiniteDimensional ℝ E] in
/-- The certified Drazin projector is idempotent. -/
theorem spectralProjector_idempotent :
    IsDrazinInverse.projection CRST.D CRST.DD * IsDrazinInverse.projection CRST.D CRST.DD
      = IsDrazinInverse.projection CRST.D CRST.DD := by
  simpa using IsDrazinInverse.projection_is_idempotent CRST.hDrazin

/-- Global finite-dimensional constructor for the certified regularized layer. -/
theorem exists_of_spectralTriple (ST : SpectralTriple E) :
    ∃ CRST : CertifiedRegularizedSpectralTriple E, CRST.toSpectralTriple = ST := by
  rcases InfoGeometry.Canonical.exists_drazinInverse_global (A := ST.D) with ⟨k, DD, hD⟩
  refine ⟨{ toSpectralTriple := ST, DD := DD, index := k, hDrazin := hD }, rfl⟩

end CertifiedRegularizedSpectralTriple

/-! ### 4. Chiral Unification -/

/--
A witness-level chiral spectral triple.
The Dirac package is equipped with chosen Drazin- and Moore-Penrose-style
regularization candidates, but no certification is stored in this
compatibility layer.
-/
structure ChiralSpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  DD : E →L[ℝ] E -- Drazin Inverse
  DP : E →L[ℝ] E -- Penrose Inverse

/--
A proof-carrying chiral spectral triple.
This refines `ChiralSpectralTriple` by certifying the Drazin and Moore-Penrose
regularizations attached to the base Dirac operator.
-/
structure CertifiedChiralSpectralTriple (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  DD : E →L[ℝ] E
  DP : E →L[ℝ] E
  drazinIndex : ℕ
  hDrazin : IsDrazinInverse D DD drazinIndex
  hMoorePenrose : IsMoorePenroseInverse D DP

namespace ChiralSpectralTriple

variable (CST : ChiralSpectralTriple E)

/-- The emergent anomaly scale ε for the spectral triple. -/
noncomputable def epsilon (CST : ChiralSpectralTriple E) : ℝ :=
  chiralScale CST.D CST.DD CST.DP

/--
Reduced anomaly-shifted log-det spectral-action model.
This is the log-volume proxy of the shifted operator `((D^D + ε I) / Λ)`.
-/
noncomputable def chiralSpectralAction (Λ : ℝ) : ℝ :=
  Real.log
    (|LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • (CST.DD + CST.epsilon • 1)))|)

end ChiralSpectralTriple

namespace CertifiedChiralSpectralTriple

variable (CCST : CertifiedChiralSpectralTriple E)

/-- Adapter from the certified chiral spectral surface to the canonical inverse kernel. -/
abbrev toCertifiedInverseKernel : InfoGeometry.Canonical.CertifiedInverseKernel E :=
  { toInverseKernel := { A := CCST.D, A_D := CCST.DD, A_MP := CCST.DP }
    drazinIndex := CCST.drazinIndex
    hDrazin := CCST.hDrazin
    hMoorePenrose := CCST.hMoorePenrose }

/-- Forgetful map from the certified layer to the witness-level chiral package. -/
abbrev toChiralSpectralTriple : ChiralSpectralTriple E :=
  { toSpectralTriple := CCST.toSpectralTriple
    DD := CCST.DD
    DP := CCST.DP }

/-- Certified anomaly scale for the spectral triple. -/
noncomputable def epsilon : ℝ :=
  ChiralSpectralTriple.epsilon CCST.toChiralSpectralTriple

/-- Certified anomaly-shifted spectral-action model. -/
noncomputable def chiralSpectralAction (Λ : ℝ) : ℝ :=
  ChiralSpectralTriple.chiralSpectralAction CCST.toChiralSpectralTriple Λ

omit [FiniteDimensional ℝ E] in
/-- The certified Drazin spectral projector is idempotent. -/
theorem spectralProjector_idempotent :
    IsDrazinInverse.projection CCST.D CCST.DD * IsDrazinInverse.projection CCST.D CCST.DD
      = IsDrazinInverse.projection CCST.D CCST.DD := by
  simpa [CertifiedChiralSpectralTriple.toCertifiedInverseKernel,
    CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.spectralProjector] using
      CCST.toCertifiedInverseKernel.spectralProjector_idempotent

omit [FiniteDimensional ℝ E] in
/-- The certified Moore-Penrose left projector is idempotent. -/
theorem metricProjector_idempotent :
    IsMoorePenroseInverse.leftProjector CCST.D CCST.DP
      * IsMoorePenroseInverse.leftProjector CCST.D CCST.DP
      = IsMoorePenroseInverse.leftProjector CCST.D CCST.DP := by
  simpa [CertifiedChiralSpectralTriple.toCertifiedInverseKernel,
    CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.metricProjector] using
      CCST.toCertifiedInverseKernel.metricProjector_idempotent

omit [FiniteDimensional ℝ E] in
/-- The certified Moore-Penrose left projector is self-adjoint. -/
theorem metricProjector_star :
    star (IsMoorePenroseInverse.leftProjector CCST.D CCST.DP)
      = IsMoorePenroseInverse.leftProjector CCST.D CCST.DP := by
  simpa [CertifiedChiralSpectralTriple.toCertifiedInverseKernel,
    CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.metricProjector] using
      CCST.toCertifiedInverseKernel.metricProjector_star

/-- Global finite-dimensional constructor for the certified chiral layer. -/
theorem exists_of_spectralTriple (ST : SpectralTriple E) :
    ∃ CCST : CertifiedChiralSpectralTriple E, CCST.toSpectralTriple = ST := by
  rcases InfoGeometry.Canonical.exists_drazinInverse_global (A := ST.D) with ⟨k, DD, hD⟩
  rcases InfoGeometry.Canonical.exists_moorePenroseInverse_global (A := ST.D) with ⟨DP, hMP⟩
  refine ⟨{ toSpectralTriple := ST
            DD := DD
            DP := DP
            drazinIndex := k
            hDrazin := hD
            hMoorePenrose := hMP }, rfl⟩

end CertifiedChiralSpectralTriple

/-! ### 5. Bridging Hessian Geometry -/

/--
To link Information Geometry to Noncommutative Geometry, we identify the square
of the Dirac operator with the Hessian metric operator: D² = ∇²ψ.
-/
structure InfoSpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  H : HessianGeometry E
  x₀ : E
  compatibility : DiracMetricCompatibility D H x₀

namespace InfoSpectralTriple

variable (IST : InfoSpectralTriple E)

/-- Constructor from a lower spectral-root compatibility witness. -/
def ofCompatibility
    (ST : SpectralTriple E)
    (H : HessianGeometry E)
    (x₀ : E)
    (compatibility : DiracMetricCompatibility ST.D H x₀) :
    InfoSpectralTriple E :=
  { toSpectralTriple := ST
    H := H
    x₀ := x₀
    compatibility := compatibility }

/--
Constructor from the canonical symmetric nonnegative quadratic form carried by the Hessian metric
operator at the basepoint. The Dirac operator is chosen canonically as the positive square root of
that metric operator, so the square compatibility is derived rather than supplied.
-/
noncomputable def ofMetric
    (H : HessianGeometry E)
    (x₀ : E) :
    InfoSpectralTriple E :=
  ofCompatibility
    { D := DiracMetricCompatibility.canonicalDiracOfMetric (E := E) H x₀
      is_self_adjoint :=
          (DiracMetricCompatibility.canonicalDiracOfMetric_isPositive (E := E) H x₀
            (H.metricOp_isSymmetric x₀) (fun u => H.metric_quadratic_nonneg x₀ u)).isSelfAdjoint }
    H x₀
    (DiracMetricCompatibility.ofMetric (E := E) H x₀)

-- theorem-class: derived
/-- A positive Dirac operator compatible with the metric is forced to be the canonical positive root. -/
theorem dirac_eq_canonicalDiracOfMetric_of_isPositive
    (hPos : IST.D.IsPositive) :
    IST.D = DiracMetricCompatibility.canonicalDiracOfMetric (E := E) IST.H IST.x₀ := by
  exact DiracMetricCompatibility.eq_canonicalDiracOfMetric_of_isPositive
    (E := E) IST.compatibility hPos

omit [FiniteDimensional ℝ E] in
-- theorem-class: bridge
/-- The Dirac square is identified with the Hessian metric operator at the basepoint. -/
@[rep_depth krein]
theorem dirac_sq_eq_metric :
    IST.D * IST.D = IST.H.metricOp IST.x₀ :=
  IST.compatibility.dirac_sq_eq_metric

omit [FiniteDimensional ℝ E] in
/-- The metric at the basepoint is recovered by applying the Dirac operator twice. -/
lemma inner_dirac_sq (u v : E) :
    inner ℝ u (IST.D (IST.D v)) = IST.H.metric IST.x₀ u v := by
  exact IST.compatibility.inner_dirac_sq u v

end InfoSpectralTriple

end InfoGeometry.Canonical.SpectralInference
