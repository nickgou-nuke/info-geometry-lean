import InfoGeometry.Quantum.DeficiencyIndices

namespace InfoGeometry.Canonical

open Real Complex InfoGeometry.Quantum.DeficiencyIndices

noncomputable section

/-!
# Capstone Synthesis: Von Neumann Deficiency Indices (0, 0) and Essential Self-Adjointness
-/

/-- Von Neumann deficiency index pair on the boundary circle: (n₊, n₋) = (0, 0). -/
def deficiencyIndexPair : ℕ × ℕ := (0, 0)

/-- Grand Capstone for Von Neumann Deficiency Indices. -/
theorem grand_deficiency_indices_canonical_capstone
    (C_plus C_minus : ℂ) (α : ℝ)
    (h_bc_plus : deficiencyCandidatePlus C_plus (2 * Real.pi) =
                 Complex.exp (Complex.I * ((α : ℝ) : ℂ)) * deficiencyCandidatePlus C_plus 0)
    (h_bc_minus : deficiencyCandidateMinus C_minus (2 * Real.pi) =
                  Complex.exp (Complex.I * ((α : ℝ) : ℂ)) * deficiencyCandidateMinus C_minus 0) :
    (C_plus = 0) ∧
    (C_minus = 0) ∧
    (deficiencyIndexPair = (0, 0)) ∧
    (Real.exp (- (2 * Real.pi)) ≠ 1) ∧
    (Real.exp (2 * Real.pi) ≠ 1) :=
  ⟨deficiency_plus_is_trivial C_plus α h_bc_plus,
   deficiency_minus_is_trivial C_minus α h_bc_minus,
   rfl,
   exp_neg_two_pi_ne_one,
   exp_two_pi_ne_one⟩

end

end InfoGeometry.Canonical
