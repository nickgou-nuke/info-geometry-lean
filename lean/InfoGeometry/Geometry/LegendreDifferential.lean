import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.TopDualPairing

/-!
# Native Legendre differential and Hessian

This file packages the smooth Legendre coordinate map using Mathlib's native
Fréchet derivative and continuous dual.  It deliberately does not introduce a
new notion of derivative, gradient, or dual carrier.

For a scalar potential `ψ : E → ℝ`, the nonlinear Legendre coordinate map is

`x ↦ fderiv ℝ ψ x : E →L[ℝ] ℝ`.

Its linearization is the Fréchet derivative of that dual-valued map, i.e. the
Hessian as a continuous linear map

`E →L[ℝ] (E →L[ℝ] ℝ)`.

The scalar primal-dual pairing is Mathlib's canonical `topDualPairing`.  No
separate "Legendre product" operation is introduced.
-/

noncomputable section

namespace InfoGeometry.Geometry.LegendreDifferential

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mathlib's continuous real dual, used as the codomain of the smooth
Legendre coordinate map. -/
abbrev ContinuousCovector (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] ℝ

/-- The canonical primal-dual scalar pairing, implemented by Mathlib's
`topDualPairing`. -/
def legendrePairing (η : ContinuousCovector E) (x : E) : ℝ :=
  topDualPairing ℝ E η x

@[simp] theorem legendrePairing_apply
    (η : ContinuousCovector E) (x : E) :
    legendrePairing η x = η x := by
  exact topDualPairing_apply η x

/-- The repository's Legendre pairing is literally Mathlib's canonical
continuous-dual pairing. -/
theorem legendrePairing_eq_topDualPairing
    (η : ContinuousCovector E) (x : E) :
    legendrePairing η x = topDualPairing ℝ E η x :=
  rfl

/-- The nonlinear smooth Legendre coordinate map associated with a scalar
potential: the point is sent to its Fréchet derivative. -/
noncomputable def legendreMap (ψ : E → ℝ) : E → ContinuousCovector E :=
  fun x => fderiv ℝ ψ x

@[simp] theorem legendreMap_apply (ψ : E → ℝ) (x : E) :
    legendreMap ψ x = fderiv ℝ ψ x :=
  rfl

/-- If a derivative has actually been proved at `x`, the nonlinear Legendre
map reads out exactly that derivative rather than Mathlib's default `fderiv`
value outside the differentiability locus. -/
theorem legendreMap_eq_of_hasFDerivAt
    {ψ : E → ℝ} {x : E} {dψ : E →L[ℝ] ℝ}
    (hψ : HasFDerivAt ψ dψ x) :
    legendreMap ψ x = dψ := by
  exact hψ.fderiv

/-- The Hessian/linearization of the nonlinear Legendre map, expressed
entirely through Mathlib's native `fderiv`. -/
noncomputable def hessianMap (ψ : E → ℝ) (x : E) :
    E →L[ℝ] ContinuousCovector E :=
  fderiv ℝ (legendreMap ψ) x

@[simp] theorem hessianMap_apply_def
    (ψ : E → ℝ) (x u : E) :
    hessianMap ψ x u = fderiv ℝ (legendreMap ψ) x u :=
  rfl

/-- A proved derivative of the nonlinear Legendre map is exactly its Hessian
linearization. -/
theorem hessianMap_eq_of_hasFDerivAt_legendreMap
    {ψ : E → ℝ} {x : E}
    {H : E →L[ℝ] ContinuousCovector E}
    (hH : HasFDerivAt (legendreMap ψ) H x) :
    hessianMap ψ x = H := by
  exact hH.fderiv

/-- Directional readout of the previous Hessian identification. -/
theorem hessianMap_apply_eq_of_hasFDerivAt_legendreMap
    {ψ : E → ℝ} {x : E}
    {H : E →L[ℝ] ContinuousCovector E}
    (hH : HasFDerivAt (legendreMap ψ) H x)
    (u : E) :
    hessianMap ψ x u = H u := by
  rw [hessianMap_eq_of_hasFDerivAt_legendreMap hH]

/-- The same Legendre coordinate map transported to Mathlib's algebraic dual.
This is the bridge to repository owners whose neutral primal/dual carrier is
built from `Module.Dual`. -/
noncomputable def algebraicLegendreMap (ψ : E → ℝ) : E → Module.Dual ℝ E :=
  fun x => (legendreMap ψ x).toLinearMap

@[simp] theorem algebraicLegendreMap_apply
    (ψ : E → ℝ) (x u : E) :
    algebraicLegendreMap ψ x u = fderiv ℝ ψ x u :=
  rfl

/-- Evaluation in the algebraic-dual presentation agrees with Mathlib's
continuous-dual pairing. -/
theorem algebraicLegendreMap_pairing
    (ψ : E → ℝ) (x u : E) :
    algebraicLegendreMap ψ x u = legendrePairing (legendreMap ψ x) u := by
  simp [legendrePairing]

end InfoGeometry.Geometry.LegendreDifferential
