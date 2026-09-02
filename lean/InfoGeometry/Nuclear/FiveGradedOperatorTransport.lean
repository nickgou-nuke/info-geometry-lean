import InfoGeometry.Nuclear.GradedBathCommutant

/-! Transport of the associative nuclear five-grading through an algebra
equivalence.  This is the common interface for operator realizations; it does
not identify the separate Freudenthal/TKK carrier with an associative algebra. -/

namespace InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading

variable {A B : Type*} [Ring A] [Ring B]
variable [Algebra ℝ A] [Algebra ℝ B]

def transport (e : A ≃ₐ[ℝ] B) (G : OperatorFiveGrading A) :
    OperatorFiveGrading B where
  gNegTwo := G.gNegTwo.map e.toLinearMap
  gNegOne := G.gNegOne.map e.toLinearMap
  gZero := G.gZero.map e.toLinearMap
  gPosOne := G.gPosOne.map e.toLinearMap
  gPosTwo := G.gPosTwo.map e.toLinearMap
  negOne_posOne_mem_zero := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.negOne_posOne_mem_zero hX' hY', ?_⟩
    simp [opCommutator]
  posOne_posOne_mem_posTwo := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.posOne_posOne_mem_posTwo hX' hY', ?_⟩
    simp [opCommutator]
  negOne_negOne_mem_negTwo := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.negOne_negOne_mem_negTwo hX' hY', ?_⟩
    simp [opCommutator]
  zero_posOne_mem_posOne := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.zero_posOne_mem_posOne hX' hY', ?_⟩
    simp [opCommutator]
  zero_negOne_mem_negOne := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.zero_negOne_mem_negOne hX' hY', ?_⟩
    simp [opCommutator]

@[simp] theorem transport_gNegTwo (e : A ≃ₐ[ℝ] B) (G : OperatorFiveGrading A) :
    (transport e G).gNegTwo = G.gNegTwo.map e.toLinearMap := rfl

end InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading
