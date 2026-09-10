import InfoGeometry.Canonical.PolarizedShearSpinEvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Explicit global solutions of the finite polarized shear and spin ODE

For a supplied positive frequency `k` with `k² = w²-s²`, the damped sine/cosine
formula gives a solution for every initial vector.  The previously established
energy and coordinate estimates therefore apply to an explicit trajectory.
This remains a finite constant-coefficient ODE construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarizedShearSpinFrame

/-- Every positive elliptic gap supplies a real positive rotation frequency. -/
theorem frequency_exists {s w : ℝ} (h : |s| < w) :
    ∃ k : ℝ, 0 < k ∧ k ^ 2 = w ^ 2 - s ^ 2 := by
  have hw : 0 < w := lt_of_le_of_lt (abs_nonneg s) h
  have hp := mul_pos (sub_pos.mpr h) (add_pos_of_pos_of_nonneg hw (abs_nonneg s))
  have hsq : 0 < w ^ 2 - s ^ 2 := by nlinarith [sq_abs s]
  exact ⟨Real.sqrt (w ^ 2 - s ^ 2), Real.sqrt_pos.mpr hsq,
    Real.sq_sqrt (le_of_lt hsq)⟩

/-- One coordinate of the matrix sine/cosine solution formula. -/
def oscillator (nu k a b t : ℝ) : ℝ :=
  Real.exp (-nu * t) * (Real.cos (k * t) * a + (Real.sin (k * t) / k) * b)

theorem hasDerivAt_oscillator (nu k a b t : ℝ) (hk : k ≠ 0) :
    HasDerivAt (oscillator nu k a b)
      (-nu * oscillator nu k a b t + Real.exp (-nu * t) *
        (-k * Real.sin (k * t) * a + Real.cos (k * t) * b)) t := by
  have hphase : HasDerivAt (fun r : ℝ => k * r) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hdamping : HasDerivAt (fun r : ℝ => -nu * r) (-nu) t := by
    simpa using (hasDerivAt_id t).const_mul (-nu)
  have hbase := hdamping.exp.mul
    ((hphase.cos.mul_const a).add ((hphase.sin.div_const k).mul_const b))
  convert hbase using 1
  dsimp [oscillator]
  field_simp [hk]

/-- The explicit solution `exp(-nu*t) (cos(k*t) I + sin(k*t)/k L) x0`. -/
def solution (s w nu k : ℝ) (x0 : Vec2) (t : ℝ) : Vec2 :=
  ![oscillator nu k (x0 0) ((s + w) * x0 1) t,
    oscillator nu k (x0 1) ((s - w) * x0 0) t]

@[simp] theorem solution_zero (s w nu k : ℝ) (x0 : Vec2) :
    solution s w nu k x0 0 = x0 := by
  ext i
  fin_cases i <;> simp [solution, oscillator]

/-- The explicit trajectory satisfies both coordinate equations at every time. -/
theorem hasDerivAt_solution {s w nu k : ℝ} (hk : 0 < k)
    (hfrequency : k ^ 2 = w ^ 2 - s ^ 2) (x0 : Vec2) (t : ℝ) (i : Fin 2) :
    HasDerivAt (fun r => solution s w nu k x0 r i)
      (velocity s w nu (solution s w nu k x0 t) i) t := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hcoupling : -k = ((s + w) * (s - w)) / k := by
    apply (eq_div_iff hk0).mpr
    nlinarith [hfrequency]
  fin_cases i
  · have hd := hasDerivAt_oscillator nu k (x0 0) ((s + w) * x0 1) t hk0
    change HasDerivAt (oscillator nu k (x0 0) ((s + w) * x0 1)) _ t
    convert hd using 1
    change velocity s w nu (solution s w nu k x0 t) 0 = _
    rw [velocity_zero_coordinate]
    dsimp [solution, oscillator]
    rw [hcoupling]
    ring
  · have hd := hasDerivAt_oscillator nu k (x0 1) ((s - w) * x0 0) t hk0
    change HasDerivAt (oscillator nu k (x0 1) ((s - w) * x0 0)) _ t
    convert hd using 1
    change velocity s w nu (solution s w nu k x0 t) 1 = _
    rw [velocity_one_coordinate]
    dsimp [solution, oscillator]
    rw [hcoupling]
    ring

/-- The explicit solution has the exact energy law from its initial vector. -/
theorem solution_energy {s w nu k : ℝ} (hk : 0 < k)
    (hfrequency : k ^ 2 = w ^ 2 - s ^ 2) (x0 : Vec2) (t : ℝ) :
    energy s w (solution s w nu k x0 t) =
      Real.exp (-2 * nu * t) * energy s w x0 := by
  simpa using energy_evolution (hasDerivAt_solution hk hfrequency x0) 0 t

/-- Nonzero initial vectors give nonzero trajectories throughout the elliptic regime. -/
theorem solution_ne_zero {s w nu k : ℝ} (hk : 0 < k)
    (hfrequency : k ^ 2 = w ^ 2 - s ^ 2) (helliptic : |s| < w)
    {x0 : Vec2} (hx0 : x0 ≠ 0) (t : ℝ) : solution s w nu k x0 t ≠ 0 := by
  intro hz
  have hpos : 0 < energy s w (solution s w nu k x0 t) := by
    rw [solution_energy hk hfrequency]
    exact mul_pos (Real.exp_pos _) (energy_pos helliptic hx0)
  simp [hz, energy] at hpos

/-- The coordinate stability estimate now applies to the constructed solution. -/
theorem solution_coordinate_bound {s w nu k t : ℝ} (hk : 0 < k)
    (hfrequency : k ^ 2 = w ^ 2 - s ^ 2) (helliptic : |s| < w)
    (hnu : 0 ≤ nu) (ht : 0 ≤ t) (x0 : Vec2) :
    solution s w nu k x0 t 0 ^ 2 + solution s w nu k x0 t 1 ^ 2 ≤
      ((w + |s|) / (w - |s|)) * (x0 0 ^ 2 + x0 1 ^ 2) := by
  simpa using coordinate_square_bound
    (hasDerivAt_solution hk hfrequency x0) helliptic hnu ht

/-- Global solutions bounded forward in time are constructed for every initial vector in the
finite elliptic regime; no global-solution premise is required. -/
theorem exists_bounded_solution {s w nu : ℝ} (h : |s| < w) (hnu : 0 ≤ nu)
    (x0 : Vec2) :
    ∃ x : ℝ → Vec2, x 0 = x0 ∧
      (∀ t : ℝ, ∀ i : Fin 2, HasDerivAt (fun r => x r i)
        (velocity s w nu (x t) i) t) ∧
      (∀ t : ℝ, 0 ≤ t → x t 0 ^ 2 + x t 1 ^ 2 ≤
        ((w + |s|) / (w - |s|)) * (x0 0 ^ 2 + x0 1 ^ 2)) := by
  obtain ⟨k, hk, hfrequency⟩ := frequency_exists h
  refine ⟨solution s w nu k x0, solution_zero s w nu k x0,
    hasDerivAt_solution hk hfrequency x0, ?_⟩
  intro t ht
  exact solution_coordinate_bound hk hfrequency h hnu ht x0

end InfoGeometry.Canonical.PolarizedShearSpinFrame
