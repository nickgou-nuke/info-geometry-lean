import re

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'r') as f:
    text = f.read()

proof = """theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero (t : ℝ) (ht : t ≠ 0)
    (p : CircularNullBoundary) :
    circularNullBoundaryFlow t p = p ↔
      (p.1.rep ∈ positiveWeightSubmodule ∨
       p.1.rep ∈ negativeWeightSubmodule ∨
       (p.1.rep ∈ zeroWeightSubmodule ∧ (p.1.rep 0 = 0 ∨ p.1.rep 4 = 0))) := by
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with
  | h x hx =>
      obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℝ x hx
      have hu_ne : (u : ℝ) ≠ 0 := u.ne_zero
      have h_rep_pos : (Projectivization.mk ℝ x hx).rep ∈ positiveWeightSubmodule ↔ x ∈ positiveWeightSubmodule := by
        rw [← hu, Submodule.smul_mem_iff _ hu_ne]
      have h_rep_neg : (Projectivization.mk ℝ x hx).rep ∈ negativeWeightSubmodule ↔ x ∈ negativeWeightSubmodule := by
        rw [← hu, Submodule.smul_mem_iff _ hu_ne]
      have h_rep_zero : (Projectivization.mk ℝ x hx).rep ∈ zeroWeightSubmodule ↔ x ∈ zeroWeightSubmodule := by
        rw [← hu, Submodule.smul_mem_iff _ hu_ne]
      have h_rep_0 : (Projectivization.mk ℝ x hx).rep 0 = 0 ↔ x 0 = 0 := by
        rw [← hu]; simp [Units.smul_def, hu_ne]
      have h_rep_4 : (Projectivization.mk ℝ x hx).rep 4 = 0 ↔ x 4 = 0 := by
        rw [← hu]; simp [Units.smul_def, hu_ne]
      rw [h_rep_pos, h_rep_neg, h_rep_zero, h_rep_0, h_rep_4]
      have hQ : circularPeirceQuadratic x = 0 :=
        (isNull_mk_iff circularPeirceQuadratic x hx).mp hp
      have hproj_aux : hyperbolicFlowCoordinate t x ≠ 0 := (hyperbolicFlowCoordinateEquiv t).injective.ne hx
      have hproj : circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩ = ⟨Projectivization.mk ℝ x hx, hp⟩ ↔
          Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux = Projectivization.mk ℝ x hx := by
        constructor
        · intro h
          have h1 : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ x hx := congr_arg Subtype.val h
          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux :=
            circularNullBoundaryFlow_mk_axialFlow t x hx hp hproj_aux
          rw [aux] at h1
          exact h1
        · intro h
          apply Subtype.ext
          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).val = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux :=
            circularNullBoundaryFlow_mk_axialFlow t x hx hp hproj_aux
          rw [aux, h]
      have hsep : Real.exp t ≠ Real.exp (-t) := by
        intro h
        apply ht
        have := Real.exp_injective h
        linarith
      constructor
      · intro hfixed
        have hfixed2 := hproj.mp hfixed
        have he : ∃ a : ℝ, a • x = hyperbolicFlowCoordinate t x := (Projectivization.mk_eq_mk_iff' ℝ (hyperbolicFlowCoordinate t x) x hproj_aux hx).mp hfixed2
        obtain ⟨a, hax⟩ := he
        have hc (i : Fin 8) : a = Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) ∨ x i = 0 := by
          have hax'' := congrFun hax i
          simpa [hyperbolicFlowCoordinate_apply, smul_eq_mul] using hax''.symm
        have kill (i : Fin 8) (c : ℝ) (he : a ≠ c)
            (hi : Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) = c) :
            x i = 0 := by
          have := hc i
          rcases this with (ha | hxi)
          · exfalso; apply he; rw [ha, hi]
          · exact hxi
        have memPos : ∀ {y : Coord}, y 0 = 0 → y 4 = 0 → y 5 = 0 → y 6 = 0 → y 7 = 0 → y ∈ positiveWeightSubmodule := by
          intro y h0 h4 h5 h6 h7
          rw [show y = y 1 • Pi.single 1 (1:ℝ) + y 2 • Pi.single 2 (1:ℝ) + y 3 • Pi.single 3 (1:ℝ) by
            ext i; fin_cases i <;> simp [h0, h4, h5, h6, h7]]
          exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have memNeg : ∀ {y : Coord}, y 0 = 0 → y 1 = 0 → y 2 = 0 → y 3 = 0 → y 4 = 0 → y ∈ negativeWeightSubmodule := by
          intro y h0 h1 h2 h3 h4
          rw [show y = y 5 • Pi.single 5 (1:ℝ) + y 6 • Pi.single 6 (1:ℝ) + y 7 • Pi.single 7 (1:ℝ) by
            ext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]]
          exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have memZero : ∀ {y : Coord}, y 1 = 0 → y 2 = 0 → y 3 = 0 → y 5 = 0 → y 6 = 0 → y 7 = 0 → y ∈ zeroWeightSubmodule := by
          intro y h1 h2 h3 h5 h6 h7
          rw [show y = y 0 • Pi.single 0 (1:ℝ) + y 4 • Pi.single 4 (1:ℝ) by
            ext i; fin_cases i <;> simp [h1, h2, h3, h5, h6, h7]]
          exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        by_cases h1 : x 1 ≠ 0
        · have ha' : a = Real.exp t := by
            have := hc 1
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx1); exact ha; exfalso; exact h1 hx1
          exact Or.inl (memPos (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])) (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])))
        by_cases h2 : x 2 ≠ 0
        · have ha' : a = Real.exp t := by
            have := hc 2
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx2); exact ha; exfalso; exact h2 hx2
          exact Or.inl (memPos (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])) (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])))
        by_cases h3 : x 3 ≠ 0
        · have ha' : a = Real.exp t := by
            have := hc 3
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx3); exact ha; exfalso; exact h3 hx3
          exact Or.inl (memPos (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])) (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight])))
        by_cases h5 : x 5 ≠ 0
        · have ha' : a = Real.exp (-t) := by
            have := hc 5
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx5); exact ha; exfalso; exact h5 hx5
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))))
        by_cases h6 : x 6 ≠ 0
        · have ha' : a = Real.exp (-t) := by
            have := hc 6
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx6); exact ha; exfalso; exact h6 hx6
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))))
        by_cases h7 : x 7 ≠ 0
        · have ha' : a = Real.exp (-t) := by
            have := hc 7
            simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight] at this
            rcases this with (ha | hx7); exact ha; exfalso; exact h7 hx7
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))
            (kill 4 1 (by rintro rfl; apply ht; have := Real.exp_injective (by simpa using ha'.symm); linarith) (by simp [InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight]))))
        · right; right
          have hz := memZero (y := x) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          refine ⟨hz, ?_⟩
          rw [circularPeirceQuadratic_formula] at hQ
          simp_all
      · rintro (h | h | ⟨h, h04⟩)
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp t, ?_⟩
          rw [hyperbolicFlow_on_positiveWeight t x h]
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Real.exp (-t), ?_⟩
          rw [hyperbolicFlow_on_negativeWeight t x h]
        · apply hproj.mpr
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨1, ?_⟩
          rw [hyperbolicFlow_on_zeroWeight t x h]
          simp
"""

text = re.sub(r'theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero.*?(?=theorem circularNullBoundaryFlow_preserves_incidence)', proof + '\n', text, flags=re.DOTALL)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

