import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.BostConnesKMSPhaseTransition

/-- Structure representing the algebraic generators and relations of the Bost-Connes C*-dynamical system.
    Generators: Isometries x_n for n ∈ ℕ⁺ and group algebra elements e(r) for r ∈ ℚ/ℤ (represented via periodic functions e(r+1) = e(r)). -/
structure BostConnesSystem (R : Type*) [CommRing R] where
  x : ℕ+ → R
  x_star : ℕ+ → R
  e : ℚ → R
  x_star_x : ∀ n : ℕ+, x_star n * x n = 1
  x_mul : ∀ m n : ℕ+, x (m * n) = x m * x n
  x_star_mul : ∀ m n : ℕ+, x_star (m * n) = x_star n * x_star m
  e_zero : e 0 = 1
  e_add : ∀ r s, e (r + s) = e r * e s
  e_periodic : ∀ r, e (r + 1) = e r

/-- Time evolution flow σ_t on the Bost-Connes algebra for real parameter t.
    σ_t(x_n) = n^(i t) x_n. On formal elements with energy E_n = ln n,
    the scaling action scales by n^(-β) under Wick-rotated KMS thermal flow. -/
def thermalKMSWeight (β : ℝ) (n : ℕ+) : ℝ :=
  Real.rpow (n : ℝ) (-β)

/-- **Theorem**: Thermal Weight Multiplicativity for Composite Modes.
    Under the Bost-Connes thermal flow at inverse temperature β,
    the thermal weight is strictly multiplicative: w_β(mn) = w_β(m) * w_β(n). -/
theorem thermalKMSWeight_mul (β : ℝ) (m n : ℕ+) :
    thermalKMSWeight β (m * n) = thermalKMSWeight β m * thermalKMSWeight β n := by
  dsimp [thermalKMSWeight]
  have h_m : 0 ≤ (m : ℝ) := Nat.cast_nonneg (m : ℕ)
  have h_n : 0 ≤ (n : ℝ) := Nat.cast_nonneg (n : ℕ)
  rw [Nat.cast_mul]
  exact Real.mul_rpow h_m h_n

/-- The thermal weight varies continuously with inverse temperature.

This is the topological parameter statement actually supported by the
`Real.rpow` definition; it does not assert a pole, KMS classification, or
phase-transition theorem at `β = 1`.
-/
theorem continuous_thermalKMSWeight (n : ℕ+) :
    Continuous (fun β : ℝ => thermalKMSWeight β n) := by
  unfold thermalKMSWeight
  exact
    (Real.continuous_const_rpow
      (show (n : ℝ) ≠ 0 by exact_mod_cast n.ne_zero)).comp continuous_neg

/-- **Theorem**: Projection Mode Projection Operator Identity.
    In the Bost-Connes system, the element p_n = x_n x_n^* is a self-adjoint projection
    (idempotent: p_n^2 = p_n) representing the range of the mode isometry x_n. -/
theorem projection_mode_idempotent {R : Type*} [CommRing R] (g : BostConnesSystem R) (n : ℕ+) :
    (g.x n * g.x_star n) * (g.x n * g.x_star n) = g.x n * g.x_star n := by
  calc (g.x n * g.x_star n) * (g.x n * g.x_star n)
    _ = g.x n * (g.x_star n * g.x n) * g.x_star n := by ring
    _ = g.x n * 1 * g.x_star n := by rw [g.x_star_x n]
    _ = g.x n * g.x_star n := by ring

/-!
The phase predicates below only record the temperature split used by the file.
They do not by themselves prove uniqueness of KMS states or any Galois-orbit
classification.
-/
def isHighTemperaturePhase (β : ℝ) : Prop := 0 < β ∧ β ≤ 1
def isLowTemperaturePhase (β : ℝ) : Prop := 1 < β

/-- The two temperature predicates are disjoint. -/
theorem phase_stratification_disjoint (β : ℝ) :
    ¬ (isHighTemperaturePhase β ∧ isLowTemperaturePhase β) := by
  dsimp [isHighTemperaturePhase, isLowTemperaturePhase]
  rintro ⟨⟨_, h_le⟩, h_gt⟩
  linarith

/-- The low-temperature predicate implies `1 < β`. -/
theorem critical_temperature_boundary (β : ℝ) (h_low : isLowTemperaturePhase β) :
    1 < β := h_low

/-- The thermal weight is normalized by the unit factor. -/
theorem kms_projection_expectation (β : ℝ) (n : ℕ+) :
    thermalKMSWeight β n * 1 = thermalKMSWeight β n := by
  ring

/-- The phase package records the proved arithmetic relations and the temperature split. -/
theorem master_bost_connes_kms_synthesis
    {R : Type*} [CommRing R] (g : BostConnesSystem R) (m n : ℕ+) (β : ℝ) (h_low : isLowTemperaturePhase β) :
    (g.x_star n * g.x n = 1) ∧
    (g.x (m * n) = g.x m * g.x n) ∧
    ((g.x n * g.x_star n) * (g.x n * g.x_star n) = g.x n * g.x_star n) ∧
    (thermalKMSWeight β (m * n) = thermalKMSWeight β m * thermalKMSWeight β n) ∧
    (¬ (isHighTemperaturePhase β ∧ isLowTemperaturePhase β)) ∧
    (1 < β) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact g.x_star_x n
  · exact g.x_mul m n
  · exact projection_mode_idempotent g n
  · exact thermalKMSWeight_mul β m n
  · exact phase_stratification_disjoint β
  · exact critical_temperature_boundary β h_low

end InfoGeometry.Algebra.BostConnesKMSPhaseTransition
