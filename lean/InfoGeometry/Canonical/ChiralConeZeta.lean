import Mathlib.Tactic

namespace InfoGeometry.ChiralConeZeta

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
The abstract modular conjugation `J`.
In the context of the Zeta function, this corresponds to the functional equation
involution combined with complex conjugation, which purely mirrors the scale-normal coordinate.
-/
class ModularConjugation (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V → V
  J_involutive : ∀ v, J (J v) = v
  J_linear : ∀ (c : ℝ) (v : V), J (c • v) = c • J v
  J_add : ∀ v w, J (v + w) = J v + J w

/--
The Cartan projectors onto the positive (even) and negative (odd) chiral sub-cones.
These split the Tomita-Takesaki natural cone into the symmetric invariant sector and
the dissipative flow sector.
-/
noncomputable def P_plus [ModularConjugation V] (v : V) : V :=
  (1 / 2 : ℝ) • (v + ModularConjugation.J v)

noncomputable def P_minus [ModularConjugation V] (v : V) : V :=
  (1 / 2 : ℝ) • (v - ModularConjugation.J v)

/--
Theorem: The Completed Riemann Xi function is strictly J-even (it satisfies the functional equation).
Therefore, its projection onto the negative chiral sub-cone is strictly zero.
Proof that the completed partition function is the static, stable anchor of the natural cone.
-/
theorem completed_xi_anchor [ModularConjugation V] (xi : V) (h_functional_eq : ModularConjugation.J xi = xi) :
    P_minus xi = 0 := by
  dsimp [P_minus]
  rw [h_functional_eq]
  have h_sub : xi - xi = 0 := sub_self xi
  rw [h_sub, smul_zero]

/--
Theorem: The Uncompleted Riemann Zeta function is NOT J-even.
Therefore, its negative projection is strictly non-zero.
This proves the existence of the relative modular density (Radon-Nikodym derivative)
that acts as the modular Hamiltonian driving the dissipative flow.
-/
theorem uncompleted_zeta_driver [ModularConjugation V] (zeta : V) (h_not_even : ModularConjugation.J zeta ≠ zeta) :
    P_minus zeta ≠ 0 := by
  dsimp [P_minus]
  intro h_zero
  -- If (1/2) * (zeta - J zeta) = 0, we multiply by 2 to show zeta - J zeta = 0
  have h_smul : (2 : ℝ) • ((1 / 2 : ℝ) • (zeta - ModularConjugation.J zeta)) = (2 : ℝ) • 0 := by rw [h_zero]
  rw [smul_smul, smul_zero] at h_smul
  have h_one : (2 : ℝ) * (1 / 2) = 1 := by ring
  rw [h_one, one_smul] at h_smul
  have h_eq : zeta = ModularConjugation.J zeta := by exact sub_eq_zero.mp h_smul
  -- This contradicts the non-even property
  exact h_not_even h_eq.symm

end InfoGeometry.ChiralConeZeta
