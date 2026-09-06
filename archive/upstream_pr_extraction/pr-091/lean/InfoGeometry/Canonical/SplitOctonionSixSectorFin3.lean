import InfoGeometry.Canonical.SplitOctonionChiralFrame

namespace InfoGeometry.Canonical

noncomputable section

theorem sixSectorBasisFin3_square_zero
    (s : Fin 2) (c : Fin 3) :
    chiralZornMul (sixSectorBasisFin3 s c) (sixSectorBasisFin3 s c) = 0 := by
  simpa [sixSectorBasisFin3] using
    sixSectorBasis_square_zero s (colourFin3Equiv c)

theorem sixSectorBasisFin3_pos_mul_neg_same
    (c : Fin 3) :
    chiralZornMul (sixSectorBasisFin3 0 c) (sixSectorBasisFin3 1 c) =
      modularNPlus := by
  simpa [sixSectorBasisFin3] using
    sixSectorBasis_pos_mul_neg (colourFin3Equiv c)

theorem sixSectorBasisFin3_neg_mul_pos_same
    (c : Fin 3) :
    chiralZornMul (sixSectorBasisFin3 1 c) (sixSectorBasisFin3 0 c) =
      modularNMinus := by
  simpa [sixSectorBasisFin3] using
    sixSectorBasis_neg_mul_pos (colourFin3Equiv c)

theorem sixSectorBasisFin3_pos_mul_neg
    (c d : Fin 3) :
    chiralZornMul (sixSectorBasisFin3 0 c) (sixSectorBasisFin3 1 d) =
      if c = d then modularNPlus else 0 := by
  by_cases h : c = d
  · subst d
    simpa [sixSectorBasisFin3] using
      sixSectorBasis_pos_mul_neg (colourFin3Equiv c)
  · have hcolour : colourFin3Equiv c ≠ colourFin3Equiv d := by
      intro hcd
      exact h (colourFin3Equiv.injective hcd)
    simpa [sixSectorBasisFin3, h] using
      (sixSector_pos_mul_neg_of_ne hcolour)

theorem sixSectorBasisFin3_neg_mul_pos
    (c d : Fin 3) :
    chiralZornMul (sixSectorBasisFin3 1 c) (sixSectorBasisFin3 0 d) =
      if c = d then modularNMinus else 0 := by
  by_cases h : c = d
  · subst d
    simpa [sixSectorBasisFin3] using
      sixSectorBasis_neg_mul_pos (colourFin3Equiv c)
  · have hcolour : colourFin3Equiv c ≠ colourFin3Equiv d := by
      intro hcd
      exact h (colourFin3Equiv.injective hcd)
    simpa [sixSectorBasisFin3, h] using
      (sixSector_neg_mul_pos_of_ne hcolour)

theorem sixSectorBasisFin3_pos_mul_pos_skew
    {c d : Fin 3} (h : c ≠ d) :
    chiralZornMul (sixSectorBasisFin3 0 c) (sixSectorBasisFin3 0 d) =
      -chiralZornMul (sixSectorBasisFin3 0 d) (sixSectorBasisFin3 0 c) := by
  apply sixSector_pos_mul_pos_skew
  intro hcolour
  exact h (colourFin3Equiv.injective hcolour)

theorem sixSectorBasisFin3_neg_mul_neg_skew
    {c d : Fin 3} (h : c ≠ d) :
    chiralZornMul (sixSectorBasisFin3 1 c) (sixSectorBasisFin3 1 d) =
      -chiralZornMul (sixSectorBasisFin3 1 d) (sixSectorBasisFin3 1 c) := by
  apply sixSector_neg_mul_neg_skew
  intro hcolour
  exact h (colourFin3Equiv.injective hcolour)

theorem chiralFrame_two_poles_plus_six_channels_fin3 :
    Set.range chiralFrame =
      {modularNPlus, modularNMinus} ∪
        Set.range (fun p : Fin 2 × Fin 3 =>
          sixSectorBasisFin3 p.1 p.2) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · simp
    · exact Or.inr ⟨(0, 0), rfl⟩
    · exact Or.inr ⟨(0, 1), rfl⟩
    · exact Or.inr ⟨(0, 2), rfl⟩
    · simp
    · exact Or.inr ⟨(1, 0), rfl⟩
    · exact Or.inr ⟨(1, 1), rfl⟩
    · exact Or.inr ⟨(1, 2), rfl⟩
  · intro hz
    rcases hz with hz | hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨4, rfl⟩
    · rcases hz with ⟨⟨s, c⟩, rfl⟩
      fin_cases s <;> fin_cases c <;>
        first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ |
          exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩

end
end InfoGeometry.Canonical
