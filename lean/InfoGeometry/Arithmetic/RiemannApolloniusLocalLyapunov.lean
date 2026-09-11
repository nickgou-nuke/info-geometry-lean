import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A local Lyapunov packet for the Apollonius neutral leaf

This owner records only finite-dimensional algebraic facts.  The transverse
coordinate is `delta = sigma - 1 / 2`; the chosen dissipative field is the
explicit normal field `(-delta, 0)`.  No global ODE or attraction statement is
encoded here.
-/

namespace InfoGeometry.Arithmetic.RiemannApolloniusLocalLyapunov

noncomputable section

/-- The transverse information potential. -/
def informationPotential (sigma : ℝ) : ℝ := (1 / 2) * (sigma - 1 / 2) ^ 2

/-- An explicit normal dissipative field for the transverse coordinate. -/
def irrotationalField (sigma : ℝ) : ℝ × ℝ := (-(sigma - 1 / 2), 0)

theorem informationPotential_nonneg (sigma : ℝ) :
    0 ≤ informationPotential sigma := by
  unfold informationPotential
  positivity

theorem informationPotential_eq_zero_iff (sigma : ℝ) :
    informationPotential sigma = 0 ↔ sigma = 1 / 2 := by
  unfold informationPotential
  constructor
  · intro h
    have hs : (sigma - 1 / 2) ^ 2 = 0 := by
      nlinarith
    nlinarith
  · intro h
    rw [h]
    norm_num

theorem irrotationalField_is_normal (sigma : ℝ) :
    irrotationalField sigma = (-(sigma - 1 / 2), 0) := by
  rfl

/-- The directional derivative of the potential along the chosen field.

This is the finite-dimensional Lyapunov identity
`d Phi / d tau = -(sigma - 1/2)^2` for `sigma' = -(sigma - 1/2)`.
-/
theorem informationPotential_directional_derivative (sigma : ℝ) :
    (sigma - 1 / 2) * (irrotationalField sigma).1 =
      -(sigma - 1 / 2) ^ 2 := by
  simp [irrotationalField]
  ring

theorem informationPotential_directional_derivative_nonpos (sigma : ℝ) :
    (sigma - 1 / 2) * (irrotationalField sigma).1 ≤ 0 := by
  rw [informationPotential_directional_derivative]
  exact neg_nonpos.mpr (sq_nonneg _)

theorem neutralLeaf_invariant :
    (irrotationalField (1 / 2)).1 = 0 ∧
      (irrotationalField (1 / 2)).2 = 0 := by
  simp [irrotationalField]

theorem informationPotential_lyapunov_packet (sigma : ℝ) :
    0 ≤ informationPotential sigma ∧
      (informationPotential sigma = 0 ↔ sigma = 1 / 2) ∧
      (sigma - 1 / 2) * (irrotationalField sigma).1 ≤ 0 := by
  exact ⟨informationPotential_nonneg sigma,
    informationPotential_eq_zero_iff sigma,
    informationPotential_directional_derivative_nonpos sigma⟩

end

end InfoGeometry.Arithmetic.RiemannApolloniusLocalLyapunov
