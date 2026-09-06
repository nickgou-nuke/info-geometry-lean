import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CantorDiracZetaBrane
import InfoGeometry.Canonical.ZetaFunctionalEquationLayer

/-!
# Native zeta functional-equation duality

This module re-exports the concrete completed-xi, Cayley, and prime-holonomy
objects from `ZetaFunctionalEquationLayer`.  It contains no deferred interface, packet, or
evidence structure.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaFunctionalEquationDuality

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.ZetaFunctionalEquationLayer

/-- Zeros of completed xi reflect under `s ↦ 1-s`. -/
@[rep_depth operator]
theorem completedZeta_zero_reflects
    {s : ℂ}
    (hz : completedRiemannXi s = 0) :
    completedRiemannXi (1 - s) = 0 := by
  unfold completedRiemannXi at hz ⊢
  calc
    completedRiemannXi (1 - s) = completedRiemannXi s := by
      symm
      simpa [riemannReflection] using completedRiemannXi_reflection s
    _ = 0 := hz

/-- The compactified completed period is invariant under Cayley inversion. -/
@[rep_depth operator]
theorem cayleyXi_inversion
    {w : ℂ}
    (hw : w ≠ 0)
    (h1w : 1 - w ≠ 0) :
    cayleyCompletedXi w = cayleyCompletedXi w⁻¹ :=
  cayleyCompletedXi_inversion hw h1w

/-- Critical-line membership is equivalent to unit norm in the Cayley chart. -/
@[rep_depth operator]
theorem criticalLine_iff_cayleyCircle
    (s : ℂ) :
    OnCriticalLine s ↔ ‖cayleyToFugacity s‖ = 1 := by
  change OnCriticalLine s ↔ ‖cayleyToFugacity s‖ = 1
  rw [criticalLine_iff_cayley_unitCircle]
  unfold OnLeeYangCircle
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro hsq
    nlinarith [norm_nonneg (cayleyToFugacity s)]
  · intro hnorm
    rw [hnorm]
    norm_num

/-- Prime holonomy is inverted by the Riemann reflection. -/
@[rep_depth operator]
theorem prime_holonomy_inverts
    (p : ℕ)
    (s : ℂ) :
    primeHolonomy p (1 - s) =
      (primeHolonomy p s)⁻¹ := by
  simpa [riemannReflection] using
    primeHolonomy_reflection_eq_inv p s

/-- On the critical line, prime-holonomy inversion is conjugation. -/
@[rep_depth operator]
theorem prime_holonomy_inverse_eq_adjoint
    (p : ℕ)
    (hp : 1 < p)
    {s : ℂ}
    (hs : OnCriticalLine s) :
    (primeHolonomy p s)⁻¹ =
      star (primeHolonomy p s) := by
  simpa using
    primeHolonomy_inv_eq_conj_of_criticalLine p hp s hs

/-- Agreement with completed xi transports reflected zeros. -/
@[rep_depth operator]
theorem zetaPeriod_zero_reflects_of_agrees
    {zetaPeriod : ℂ → ℂ}
    (hagrees : zetaPeriod = completedRiemannXi)
    {s : ℂ}
    (hz : zetaPeriod s = 0) :
    zetaPeriod (1 - s) = 0 := by
  rw [hagrees] at hz ⊢
  exact completedZeta_zero_reflects hz

/-! ## Cantor--Dirac brane readback

The former interface stored the functional equation, Cayley duality, and prime
holonomy laws in additional evidence records.  Those laws now belong to
`ZetaFunctionalEquationLayer`.  The nontrivial surviving bridge is the
identification of a concrete brane period with the canonical completed xi
function.
-/

open InfoGeometry.Canonical.CantorDiracZetaBrane

/--
A Cantor--Dirac brane period identified with completed xi inherits reflection
of its zero set.  The identification is explicit theorem input, not a field in
an additional wrapper packet.
-/
@[rep_depth operator]
theorem braneZetaPeriod_zero_reflects
    (centralCharge : ℂ → ℂ)
    (hagrees :
      ∀ z : ℂ, centralCharge z = completedRiemannXi z)
    {s : ℂ}
    (hz : centralCharge s = 0) :
    centralCharge (1 - s) = 0 := by
  apply zetaPeriod_zero_reflects_of_agrees
    (zetaPeriod := centralCharge)
    (hagrees := funext hagrees)
    hz

/--
The existing Cantor--Dirac self-adjointness owner still puts a brane-period
zero on the critical line.  This theorem only reconciles the two canonical
critical-line predicates.
-/
@[rep_depth operator]
theorem braneZetaPeriod_zero_implies_criticalLine
    (centralCharge : ℂ → ℂ)
    (selfAdjoint : ℂ → Prop)
    (hSelfAdjoint :
      InfoGeometry.Canonical.CantorDiracZetaBrane.SelfAdjointOnCriticalLine
        selfAdjoint)
    (hVanish :
      ∀ z : ℂ,
        centralCharge z = 0 → selfAdjoint z)
    (s : ℂ)
    (hz : centralCharge s = 0) :
    OnCriticalLine s := by
  simpa [OnCriticalLine,
      InfoGeometry.Canonical.CantorDiracZetaBrane.CriticalLine,
    OnCriticalLine] using
    InfoGeometry.Canonical.CantorDiracZetaBrane.zetaPeriod_zero_implies_criticalLine
      centralCharge selfAdjoint hSelfAdjoint hVanish s hz

/--
Combining completed-xi reflection with the Cantor--Dirac owner places the
reflected brane-period zero on the critical line.
-/
@[rep_depth operator]
theorem reflected_braneZetaPeriod_zero_implies_criticalLine
    (centralCharge : ℂ → ℂ)
    (selfAdjoint : ℂ → Prop)
    (hSelfAdjoint :
      InfoGeometry.Canonical.CantorDiracZetaBrane.SelfAdjointOnCriticalLine
        selfAdjoint)
    (hagrees :
      ∀ z : ℂ, centralCharge z = completedRiemannXi z)
    (hVanish :
      ∀ z : ℂ,
        centralCharge z = 0 → selfAdjoint z)
    (s : ℂ)
    (hz : centralCharge s = 0) :
    OnCriticalLine (1 - s) :=
  braneZetaPeriod_zero_implies_criticalLine
    centralCharge selfAdjoint hSelfAdjoint hVanish (1 - s)
      (braneZetaPeriod_zero_reflects centralCharge hagrees hz)

end InfoGeometry.Canonical.ZetaFunctionalEquationDuality
