import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Krein.Metric
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.MoorePenrose
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

/-! ### 2. The Information Spectral Triple -/

/--
A toy finite-dimensional Spectral Triple (A, H, D).
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
A regularized Spectral Triple where the Dirac operator comes with its Drazin inverse.
This allows defining the propagator even for degenerate geometries.
-/
structure RegularizedSpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  DD : E →L[ℝ] E -- The Drazin Inverse of D
  index : ℕ
  is_drazin : IsDrazinInverse D DD index

namespace RegularizedSpectralTriple

variable (RST : RegularizedSpectralTriple E)

/--
The Spectral Action Principle: S(D) = Tr(f(D^D / Λ)).
In our toy model, we compute the trace of the Drazin-regularized Dirac operator.
-/
noncomputable def spectralAction (Λ : ℝ) : ℝ :=
  LinearMap.trace ℝ E (ContinuousLinearMap.toLinearMap ((1 / Λ) • RST.DD))

end RegularizedSpectralTriple

/-! ### 4. Chiral Unification -/

/--
A regularized Spectral Triple where the Dirac operator comes with both its 
Drazin inverse (spectral) and Moore-Penrose inverse (metric).
This allows for the emergence of the chiral scale ε.
-/
structure ChiralSpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  DD : E →L[ℝ] E -- Drazin Inverse
  DP : E →L[ℝ] E -- Penrose Inverse
  is_drazin : IsDrazinInverse D DD 1
  is_penrose : IsMoorePenroseInverse D DP

namespace ChiralSpectralTriple

variable (CST : ChiralSpectralTriple E)

/-- The emergent anomaly scale ε for the spectral triple. -/
noncomputable def epsilon (CST : ChiralSpectralTriple E) : ℝ :=
  chiralScale CST.D CST.DD CST.DP

/--
The Anomaly-Shifted Spectral Action.
S(D) = Tr(f((D^D + ε I) / Λ)).
The chiral anomaly ε acts as a generated mass/scale term.
-/
noncomputable def chiralSpectralAction (Λ : ℝ) : ℝ :=
  LinearMap.trace ℝ E (ContinuousLinearMap.toLinearMap ((1 / Λ) • (CST.DD + CST.epsilon • 1)))

end ChiralSpectralTriple

/-! ### 5. Bridging Hessian Geometry -/

/--
To link Information Geometry to Noncommutative Geometry, we identify the square 
of the Dirac operator with the Hessian metric operator: D² = ∇²ψ.
-/
structure InfoSpectralTriple (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SpectralTriple E where
  H : HessianGeometry E
  x₀ : E
  dirac_sq_eq_metric : D * D = H.metricOp x₀

namespace InfoSpectralTriple

variable (IST : InfoSpectralTriple E)

omit [FiniteDimensional ℝ E] in
/-- The metric at the basepoint is recovered by applying the Dirac operator twice. -/
lemma inner_dirac_sq (u v : E) :
    inner ℝ u (IST.D (IST.D v)) = IST.H.metric IST.x₀ u v := by
  have h_sq : IST.D * IST.D = IST.H.metricOp IST.x₀ := IST.dirac_sq_eq_metric
  have h_eval : (IST.D * IST.D) v = IST.D (IST.D v) := rfl
  rw [← h_eval, h_sq]
  rfl

end InfoSpectralTriple

end InfoGeometry.Canonical.SpectralInference
