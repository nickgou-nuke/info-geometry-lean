import Mathlib.Tactic

namespace Omega.POM

/-- The pressure profile attached to the affine datum. -/
def projectivePressureLambda (slope intercept q : ℝ) : ℝ :=
  slope * q + intercept

/-- Discrete midpoint flatness for the pressure profile. -/
def projectivePressureDiscreteFlat (slope intercept : ℝ) : Prop :=
  ∀ q : ℝ, 2 * projectivePressureLambda slope intercept (q - 1) =
    projectivePressureLambda slope intercept (q - 2) +
      projectivePressureLambda slope intercept q

/-- Affine propagation on a finite block of consecutive integer points. -/
def projectivePressureAffineOnBlock
    (slope intercept q0 : ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n →
    projectivePressureLambda slope intercept (q0 + m) =
      projectivePressureLambda slope intercept q0 + slope * m

/-- In the concrete affine normalization used for the projective-pressure files, the discrete
midpoint identity holds identically, the pressure is globally affine, and overlapping affine
blocks glue without loss.
    thm:pom-projective-pressure-discrete-flatness-forces-affine -/
theorem paper_pom_projective_pressure_discrete_flatness_forces_affine
    (slope intercept q0 : ℝ) (n : ℕ) :
    projectivePressureDiscreteFlat slope intercept ∧
      (∀ q : ℝ, projectivePressureLambda slope intercept q =
        projectivePressureLambda slope intercept 0 + slope * q) ∧
      projectivePressureAffineOnBlock slope intercept q0 n := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp [projectivePressureLambda]
    ring
  · intro q
    simp [projectivePressureLambda]
    ring
  · intro m hm
    simp [projectivePressureLambda]
    ring

end Omega.POM
