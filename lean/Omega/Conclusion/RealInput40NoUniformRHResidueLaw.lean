import Mathlib.Tactic

namespace Omega.Conclusion

/-- Parameter for a finite residue-predicate exercise.  The model uses `D + 2`,
so the finite type contains the two distinguished indices zero and one.  No
analytic number-theoretic modulus is represented by this parameter. -/
abbrev conclusion_realinput40_no_uniform_rh_residue_law_data := ℕ

namespace conclusion_realinput40_no_uniform_rh_residue_law_data

/-- The checked modulus, shifted so that it is always at least two. -/
def residue_modulus (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : ℕ :=
  D + 2

/-- Placeholder finite predicate: the residue index is not zero.  This
definition does not encode a square-root estimate. -/
def periodic_residue_class_square_root_bound
    (_D : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (r : Fin (_D.residue_modulus)) : Prop :=
  r.val ≠ 0

/-- Placeholder finite predicate: the residue index is not one.  This
definition does not encode a primitive-residue estimate. -/
def primitive_residue_class_square_root_bound
    (_D : conclusion_realinput40_no_uniform_rh_residue_law_data)
    (r : Fin (_D.residue_modulus)) : Prop :=
  r.val ≠ 1

/-- All periodic residue classes obey the square-root law. -/
def periodic_residue_square_root_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∀ r : Fin D.residue_modulus, D.periodic_residue_class_square_root_bound r

/-- All primitive residue classes obey the square-root law. -/
def primitive_residue_square_root_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∀ r : Fin D.residue_modulus, D.primitive_residue_class_square_root_bound r

/-- At least one periodic residue class violates the square-root bound. -/
def exists_periodic_counterexample
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∃ r : Fin D.residue_modulus, ¬ D.periodic_residue_class_square_root_bound r

/-- At least one primitive residue class violates the square-root bound. -/
def exists_primitive_counterexample
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ∃ r : Fin D.residue_modulus, ¬ D.primitive_residue_class_square_root_bound r

/-- The periodic and primitive square-root residue laws cannot both hold uniformly. -/
def no_uniform_square_root_residue_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) : Prop :=
  ¬ (D.periodic_residue_square_root_law ∧ D.primitive_residue_square_root_law)

end conclusion_realinput40_no_uniform_rh_residue_law_data

/-- The two finite predicates are not universally true: index zero refutes
the first and index one refutes the second.  This theorem is only about the
definitions above; it has no RH, prime-counting, or analytic content. -/
theorem finite_residue_exclusions_disprove_local_universal_predicates
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) :
    D.exists_periodic_counterexample ∧ D.exists_primitive_counterexample ∧
      D.no_uniform_square_root_residue_law := by
  have hPeriodic : D.exists_periodic_counterexample := by
    refine ⟨⟨0, ?_⟩, ?_⟩
    · unfold conclusion_realinput40_no_uniform_rh_residue_law_data.residue_modulus
      omega
    · intro hbound
      exact hbound rfl
  have hPrimitive : D.exists_primitive_counterexample := by
    refine ⟨⟨1, ?_⟩, ?_⟩
    · unfold conclusion_realinput40_no_uniform_rh_residue_law_data.residue_modulus
      omega
    · intro hbound
      exact hbound rfl
  refine ⟨hPeriodic, hPrimitive, ?_⟩
  intro hUniform
  rcases hPeriodic with ⟨r, hr⟩
  exact hr (hUniform.1 r)

/-- Compatibility alias for the former paper-facing name.  Its proposition
remains exactly the finite predicate statement above and does not formalize
an RH residue law. -/
theorem paper_conclusion_realinput40_no_uniform_rh_residue_law
    (D : conclusion_realinput40_no_uniform_rh_residue_law_data) :
    D.exists_periodic_counterexample ∧ D.exists_primitive_counterexample ∧
      D.no_uniform_square_root_residue_law :=
  finite_residue_exclusions_disprove_local_universal_predicates D

end Omega.Conclusion
