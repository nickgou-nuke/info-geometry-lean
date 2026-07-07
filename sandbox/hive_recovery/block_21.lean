/-- The $J$-odd projection operator $P^-_J = \frac{1}{2}(I - J)$ acting on a function $f(z)$. -/
def P_minus_J (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (f z - f (-z))

/-- Under the symmetry-adapted parity (the Riemann functional equation), the completed zeta function has zero $J$-odd projection. -/
theorem P_minus_J_symmetryAdaptedXi_eq_zero
    (h_even : ∀ z : ℂ, RiemannZetaEquivalences.symmetryAdaptedXi z = RiemannZetaEquivalences.symmetryAdaptedXi (-z)) (z : ℂ) :
    P_minus_J RiemannZetaEquivalences.symmetryAdaptedXi z = 0 := by
  unfold P_minus_J
  rw [h_even z]
  ring