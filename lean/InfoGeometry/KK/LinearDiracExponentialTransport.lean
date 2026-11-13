/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.LinearDiracTransport
import InfoGeometry.Canonical.QuasilatticeDirac
import InfoGeometry.Krein.ExponentialIsometry

/-!
# Linear-domain transport along the existing exponential operator family

The frame is the repository's actual continuous linear exponential automorphism.
The bounded conjugation is identified with the existing quasilattice operator.
The domain-valued operator remains defined on the transported linear domain.
-/

noncomputable section

namespace InfoGeometry.KK.LinearDiracTransport

open InfoGeometry.Krein

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem expAutomorphism_symm_toContinuousLinearMap
    (G : H →L[ℝ] H) (t : ℝ) :
    ((expAutomorphism G t).symm : H →L[ℝ] H) =
      NormedSpace.exp (t • (-G)) := by
  letI := NormedSpace.invertibleExp (t • G)
  change ⅟(NormedSpace.exp (t • G)) = NormedSpace.exp (t • (-G))
  rw [NormedSpace.invOf_exp]
  simp only [smul_neg]

theorem conjugate_expAutomorphism
    (G A : H →L[ℝ] H) (t : ℝ) :
    (expAutomorphism G t).conjContinuousAlgEquiv A =
      InfoGeometry.Canonical.expTransport G A t := by
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
    expAutomorphism_toContinuousLinearMap, expAutomorphism_symm_toContinuousLinearMap]
  rfl

/-- The existing exponential covariance law is an actual derivative of the
bounded conjugation family, with no supplied family-continuity certificate. -/
theorem hasDerivAt_conjugate_expAutomorphism
    (G A : H →L[ℝ] H) (t : ℝ) :
    HasDerivAt (fun s => (expAutomorphism G s).conjContinuousAlgEquiv A)
      ((expAutomorphism G t).conjContinuousAlgEquiv ⁅G, A⁆) t := by
  simpa only [conjugate_expAutomorphism] using
    InfoGeometry.Canonical.hasDerivAt_expTransport G A t

theorem continuous_conjugate_expAutomorphism (G A : H →L[ℝ] H) :
    Continuous (fun t => (expAutomorphism G t).conjContinuousAlgEquiv A) :=
  continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_conjugate_expAutomorphism G A t).continuousAt)

/-- Compact linear resolvents transported along the exponential frame form
an operator-norm continuous family. -/
theorem continuous_exponential_resolvent (G : H →L[ℝ] H)
    {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventBridge.RealSplitKreinLinearResolventData S D) :
    Continuous (fun t => (resolvent (expAutomorphism G t) R).resolvent) :=
  continuous_conjugate_expAutomorphism G R.resolvent

/-- The same exponential frame carries dense domains and closed operator graphs. -/
theorem exponential_domain_regular
    (G : H →L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (hS : Dense (S : Set H)) (hD : IsClosed (graph D)) (t : ℝ) :
    Dense (domain (expAutomorphism G t) S : Set H) ∧
      IsClosed (graph (operator (expAutomorphism G t) D)) :=
  ⟨dense_domain _ _ hS, closed_graph _ _ hD⟩

/-- The bounded operator family agrees with the repository's quasilattice owner. -/
theorem conjugate_expAutomorphism_eq_quasilatticeDirac
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) (t : ℝ) :
    (expAutomorphism V.connectionGenerator t).conjContinuousAlgEquiv A =
      InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac V A t :=
  conjugate_expAutomorphism V.connectionGenerator A t

end InfoGeometry.KK.LinearDiracTransport
