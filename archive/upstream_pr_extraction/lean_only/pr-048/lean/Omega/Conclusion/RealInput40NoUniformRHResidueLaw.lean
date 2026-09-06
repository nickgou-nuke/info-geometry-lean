import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete modulus parameter for the real-input-40 residue obstruction.  The model uses
`D + 2`, so every instance has at least two residue classes. -/
structure conclusion_realinput40_no_uniform_rh_residue_law_data where
  periodic_bound : ∀ D : ℕ, Fin (D + 2) → Prop
  primitive_bound : ∀ D : ℕ, Fin (D + 2) → Prop

namespace conclusion_realinput40_no_uniform_rh_residue_law_data

/-- The checked modulus, shifted so that it is always at least two. -/
def residue_modulus (D : ℕ) : ℕ := D + 2

/-- A periodic residue class satisfying the square-root bound in the contradiction model. -/
def periodic_residue_class_square_root_bound
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) (r : Fin (residue_modulus D)) : Prop :=
  M.periodic_bound D r

/-- A primitive residue class satisfying the square-root bound in the contradiction model. -/
def primitive_residue_class_square_root_bound
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) (r : Fin (residue_modulus D)) : Prop :=
  M.primitive_bound D r

/-- All periodic residue classes obey the square-root law. -/
def periodic_residue_square_root_law
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) : Prop :=
  ∀ r : Fin (residue_modulus D),
    periodic_residue_class_square_root_bound M D r

/-- All primitive residue classes obey the square-root law. -/
def primitive_residue_square_root_law
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) : Prop :=
  ∀ r : Fin (residue_modulus D),
    primitive_residue_class_square_root_bound M D r

/-- At least one periodic residue class violates the square-root bound. -/
def exists_periodic_counterexample
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) : Prop :=
  ∃ r : Fin (residue_modulus D),
    ¬ periodic_residue_class_square_root_bound M D r

/-- At least one primitive residue class violates the square-root bound. -/
def exists_primitive_counterexample
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) : Prop :=
  ∃ r : Fin (residue_modulus D),
    ¬ primitive_residue_class_square_root_bound M D r

/-- The periodic and primitive square-root residue laws cannot both hold uniformly. -/
def no_uniform_square_root_residue_law
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ) : Prop :=
  ¬ (periodic_residue_square_root_law M D ∧
    primitive_residue_square_root_law M D)

end conclusion_realinput40_no_uniform_rh_residue_law_data

/-- Paper label: `thm:conclusion-realinput40-no-uniform-rh-residue-law`.
Concrete residue witnesses contradict the hypothesis that every periodic and primitive residue
class obeys the square-root law, so no uniform RH-type residue law survives. -/
theorem paper_conclusion_realinput40_no_uniform_rh_residue_law
    (M : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (D : ℕ)
    (hPeriodic :
      conclusion_realinput40_no_uniform_rh_residue_law_data.exists_periodic_counterexample M D)
    (hPrimitive :
      conclusion_realinput40_no_uniform_rh_residue_law_data.exists_primitive_counterexample M D) :
    conclusion_realinput40_no_uniform_rh_residue_law_data.exists_periodic_counterexample M D ∧
      conclusion_realinput40_no_uniform_rh_residue_law_data.exists_primitive_counterexample M D ∧
      conclusion_realinput40_no_uniform_rh_residue_law_data.no_uniform_square_root_residue_law M D := by
  refine ⟨hPeriodic, hPrimitive, ?_⟩
  intro hUniform
  rcases hPeriodic with ⟨r, hr⟩
  exact hr (hUniform.1 r)

end Omega.Conclusion
