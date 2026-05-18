import Mathlib

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

/-! ## 1. Generators on the Riemann plane -/

/-- The functional equation reflection `s ↦ 1 - s`. -/
def tau (s : ℂ) : ℂ := 1 - s

/-- The arithmetic reflection `s ↦ conj s`. -/
def sigma (s : ℂ) : ℂ := conj s

/-- The composite antiunitary reflection `s ↦ 1 - conj s`. -/
def gamma (s : ℂ) : ℂ := tau (sigma s)

/-! ## 2. Group-structure proofs -/

/-- `tau` is an involution. -/
theorem tau_involution (s : ℂ) : tau (tau s) = s := by
  simp [tau]

/-- `sigma` is an involution. -/
theorem sigma_involution (s : ℂ) : sigma (sigma s) = s := by
  simp [sigma, Complex.conj_conj]

/-- The composite symmetry `gamma` is an involution. -/
theorem gamma_involution (s : ℂ) : gamma (gamma s) = s := by
  simp [gamma, tau, sigma, Complex.conj_conj]

/-- The concrete reflections `tau` and `sigma` commute. -/
theorem tau_sigma_commute (s : ℂ) :
    tau (sigma s) = sigma (tau s) := by
  simp [tau, sigma]

/-! ## 3. The critical line as the fixed locus -/

/--
The fixed locus of the antiunitary reflection `s ↦ 1 - conj s` is exactly the
critical line `Re(s) = 1/2`.
-/
theorem critical_line_is_invariant_orbit (s : ℂ) :
    gamma s = s ↔ s.re = (1 : ℝ) / 2 := by
  unfold gamma tau sigma
  constructor
  · intro h
    have hre : (1 - conj s : ℂ).re = s.re := by
      simpa using congrArg Complex.re h
    simp [Complex.sub_re, Complex.conj_re, Complex.one_re] at hre
    linarith
  · intro hs
    apply Complex.ext <;> simp [tau, sigma, hs, Complex.conj_re, Complex.conj_im]

/-- `tau` preserves the real part exactly on the critical line. -/
theorem tau_preserves_re_iff_critical_line (s : ℂ) :
    (tau s).re = s.re ↔ s.re = (1 : ℝ) / 2 := by
  unfold tau
  constructor
  · intro h
    simp [Complex.sub_re, Complex.one_re] at h
    linarith
  · intro h
    simp [Complex.sub_re, Complex.one_re]
    linarith

/--
If a state is fixed by `gamma`, then the functional and arithmetic reflections
agree on that state.
-/
theorem stable_state_reflection (s : ℂ) (h_stable : gamma s = s) :
    tau s = sigma s := by
  have h_apply : sigma s = tau s := by
    simpa [gamma, tau, sigma] using congrArg tau h_stable
  simpa [tau, sigma] using h_apply.symm

end InfoGeometry.Arithmetic.ZetaDihedral
