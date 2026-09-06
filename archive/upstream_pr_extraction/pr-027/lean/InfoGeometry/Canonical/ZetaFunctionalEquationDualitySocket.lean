import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CantorDiracZetaBraneSocket
import InfoGeometry.Canonical.ZetaFunctionalEquationLayer

/-!
# Native zeta functional-equation duality

This module re-exports the concrete completed-xi, Cayley, and prime-holonomy
objects from `ZetaFunctionalEquationLayer`.  It contains no socket, packet, or
evidence structure.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaFunctionalEquationDualitySocket

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.ZetaFunctionalEquationLayer

/-- Canonical critical-line predicate. -/
abbrev CriticalLine : ℂ → Prop :=
  OnCriticalLine

/-- Canonical Cayley fugacity coordinate. -/
abbrev cayleyZetaCoordinate : ℂ → ℂ :=
  cayleyToFugacity

/-- The completed zeta period is the native completed Riemann xi function. -/
abbrev completedZeta : ℂ → ℂ :=
  completedRiemannXi

/-- The compactified completed period in the Cayley coordinate. -/
abbrev cayleyXi : ℂ → ℂ :=
  cayleyCompletedXi

/-- The normalized prime holonomy. -/
abbrev normalizedPrimeHolonomy : ℕ → ℂ → ℂ :=
  primeHolonomy

/-- Zeros of completed xi reflect under `s ↦ 1-s`. -/
@[rep_depth operator]
theorem completedZeta_zero_reflects
    {s : ℂ}
    (hz : completedZeta s = 0) :
    completedZeta (1 - s) = 0 := by
  unfold completedZeta at hz ⊢
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
    cayleyXi w = cayleyXi w⁻¹ :=
  cayleyCompletedXi_inversion hw h1w

/-- Critical-line membership is equivalent to unit norm in the Cayley chart. -/
@[rep_depth operator]
theorem criticalLine_iff_cayleyCircle
    (s : ℂ) :
    CriticalLine s ↔ ‖cayleyZetaCoordinate s‖ = 1 := by
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
    normalizedPrimeHolonomy p (1 - s) =
      (normalizedPrimeHolonomy p s)⁻¹ := by
  simpa [riemannReflection] using
    primeHolonomy_reflection_eq_inv p s

/-- On the critical line, prime-holonomy inversion is conjugation. -/
@[rep_depth operator]
theorem prime_holonomy_inverse_eq_adjoint
    (p : ℕ)
    (hp : 1 < p)
    {s : ℂ}
    (hs : CriticalLine s) :
    (normalizedPrimeHolonomy p s)⁻¹ =
      star (normalizedPrimeHolonomy p s) := by
  simpa using
    primeHolonomy_inv_eq_conj_of_criticalLine p hp s hs

/--
Exact identification required of any proposed brane zeta-period readout.
This definition carries no proof or additional data.
-/
def ZetaPeriodAgreesWithCompletedXi
    (zetaPeriod : ℂ → ℂ) : Prop :=
  zetaPeriod = completedZeta

/-- Zero-location target for a concrete zeta-period function. -/
def ZetaPeriodZerosOnCriticalLine
    (zetaPeriod : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, zetaPeriod s = 0 → CriticalLine s

/-- Agreement with completed xi transports reflected zeros. -/
@[rep_depth operator]
theorem zetaPeriod_zero_reflects_of_agrees
    {zetaPeriod : ℂ → ℂ}
    (hagrees : ZetaPeriodAgreesWithCompletedXi zetaPeriod)
    {s : ℂ}
    (hz : zetaPeriod s = 0) :
    zetaPeriod (1 - s) = 0 := by
  unfold ZetaPeriodAgreesWithCompletedXi at hagrees
  rw [hagrees] at hz ⊢
  exact completedZeta_zero_reflects hz

/-! ## Cantor--Dirac brane readback

The former socket stored the functional equation, Cayley duality, and prime
holonomy laws in additional evidence records.  Those laws now belong to
`ZetaFunctionalEquationLayer`.  The nontrivial surviving bridge is the
identification of a concrete brane period with the canonical completed xi
function.
-/

open InfoGeometry.Canonical.CantorDiracZetaBraneSocket

/--
A Cantor--Dirac brane period identified with completed xi inherits reflection
of its zero set.  The identification is explicit theorem input, not a field in
an additional wrapper packet.
-/
@[rep_depth operator]
theorem braneZetaPeriod_zero_reflects
    (S : CantorDiracSYZZetaBraneConjectureSocket)
    (hagrees :
      ∀ z : ℂ, S.centralCharge z = completedZeta z)
    {s : ℂ}
    (hz : S.centralCharge s = 0) :
    S.centralCharge (1 - s) = 0 := by
  apply zetaPeriod_zero_reflects_of_agrees
    (zetaPeriod := S.centralCharge)
    (hagrees := funext hagrees)
    hz

/--
The existing Cantor--Dirac self-adjointness owner still puts a brane-period
zero on the critical line.  This theorem only reconciles the two canonical
critical-line predicates.
-/
@[rep_depth operator]
theorem braneZetaPeriod_zero_implies_criticalLine
    (S : CantorDiracSYZZetaBraneConjectureSocket)
    (hVanish :
      ∀ z : ℂ,
        S.centralCharge z = 0 →
          S.totalDirac.TotalSelfAdjoint z)
    (s : ℂ)
    (hz : S.centralCharge s = 0) :
    CriticalLine s := by
  simpa [CriticalLine,
    InfoGeometry.Canonical.CantorDiracZetaBraneSocket.CriticalLine,
    OnCriticalLine] using
    InfoGeometry.Canonical.CantorDiracZetaBraneSocket.zetaPeriod_zero_implies_criticalLine
      S hVanish s hz

/--
Combining completed-xi reflection with the Cantor--Dirac owner places the
reflected brane-period zero on the critical line.
-/
@[rep_depth operator]
theorem reflected_braneZetaPeriod_zero_implies_criticalLine
    (S : CantorDiracSYZZetaBraneConjectureSocket)
    (hagrees :
      ∀ z : ℂ, S.centralCharge z = completedZeta z)
    (hVanish :
      ∀ z : ℂ,
        S.centralCharge z = 0 →
          S.totalDirac.TotalSelfAdjoint z)
    (s : ℂ)
    (hz : S.centralCharge s = 0) :
    CriticalLine (1 - s) :=
  braneZetaPeriod_zero_implies_criticalLine
    S hVanish (1 - s)
      (braneZetaPeriod_zero_reflects S hagrees hz)

end InfoGeometry.Canonical.ZetaFunctionalEquationDualitySocket
