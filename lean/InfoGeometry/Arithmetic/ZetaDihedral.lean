import Mathlib
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

/-!
# InfoGeometry.Arithmetic.ZetaDihedral

Proof-only complex-plane symmetry layer for the zeta/thermodynamic reflection
maps.

The concrete maps `s ↦ 1 - s` and `s ↦ conj s` are involutions and commute.
Their concrete generated image on the `s`-plane is therefore Klein-four, not a
faithful `D_∞` action.  The critical line `Re(s) = 1/2` is the fixed locus of
the antiunitary reflection `s ↦ 1 - conj s`.

No sockets. No certificates. No axioms. No `sorry`.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ZetaDihedral

open Complex
open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

/-- The functional-equation reflection `s ↦ 1 - s`. -/
abbrev tau (s : ℂ) : ℂ :=
  functionalReflection s

/-- The arithmetic reflection `s ↦ conj s`. -/
abbrev sigma (s : ℂ) : ℂ :=
  conjugationReflection s

/-- The composite antiunitary reflection `s ↦ 1 - conj s`. -/
abbrev gamma (s : ℂ) : ℂ :=
  antiunitaryCriticalReflection s

/-- The critical line in the complex plane. -/
abbrev CriticalLine (s : ℂ) : Prop :=
  CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s

/-! ## Group structure proofs -/

/-- `tau` is an involution. -/
theorem tau_involution (s : ℂ) : tau (tau s) = s := by
  simpa [tau] using functionalReflection_involutive s

/-- `sigma` is an involution. -/
theorem sigma_involution (s : ℂ) : sigma (sigma s) = s := by
  simpa [sigma] using conjugationReflection_involutive s

/-- The composite symmetry `gamma` is an involution. -/
theorem gamma_involution (s : ℂ) : gamma (gamma s) = s := by
  simpa [gamma] using antiunitaryCriticalReflection_involutive s

/-- The concrete reflections `tau` and `sigma` commute. -/
theorem tau_sigma_commute (s : ℂ) :
    tau (sigma s) = sigma (tau s) := by
  simpa [tau, sigma] using functional_conjugation_commute s

/-! ## The critical line as the fixed locus -/

/--
The fixed locus of the antiunitary reflection `s ↦ 1 - conj s` is exactly the
critical line `Re(s) = 1/2`.
-/
theorem critical_line_is_invariant_orbit (s : ℂ) :
    gamma s = s ↔ CriticalLine s := by
  simpa [gamma, CriticalLine, eq_comm] using
    (fixed_antiunitaryCriticalReflection_iff_criticalLine s)

/-- `tau` preserves the real part exactly on the critical line. -/
theorem tau_preserves_re_iff_critical_line (s : ℂ) :
    (tau s).re = s.re ↔ s.re = (1 / 2 : ℝ) := by
  unfold tau
  constructor
  · intro h
    have h' : (1 - s.re : ℝ) = s.re := by simpa [Complex.sub_re] using h
    linarith
  · intro hs
    have h' : (1 - s.re : ℝ) = s.re := by linarith
    simpa [Complex.sub_re] using h'

/--
If a state is fixed by `gamma`, then the functional and arithmetic reflections
agree on that state.
-/
theorem stable_state_reflection (s : ℂ) (h_stable : gamma s = s) :
    tau s = sigma s := by
  have h_eq : s = antiunitaryCriticalReflection s := by
    simpa [gamma, tau, sigma, eq_comm] using h_stable
  have hs : CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s := by
    exact (fixed_antiunitaryCriticalReflection_iff_criticalLine s).mp h_eq.symm
  have hs' : s.re = (1 / 2 : ℝ) := by
    simpa [CompletedZetaSouriauDInfinityThermodynamics.CriticalLine] using hs
  apply Complex.ext
  · have h_re : (1 - s.re : ℝ) = s.re := by
      nlinarith [hs']
    simpa [tau, sigma, Complex.sub_re] using h_re
  · simp [tau, sigma, functionalReflection, conjugationReflection]

end InfoGeometry.Arithmetic.ZetaDihedral
