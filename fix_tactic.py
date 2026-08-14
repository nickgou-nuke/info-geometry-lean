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
      obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep x hx
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
          have h1 : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).1 = Projectivization.mk ℝ x hx := congr_arg Subtype.val h
          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).1 = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux := by
            rw [circularNullBoundaryFlow_mk_axialFlow]
          rw [aux] at h1
          exact h1
        · intro h
          apply Subtype.ext
          have aux : (circularNullBoundaryFlow t ⟨Projectivization.mk ℝ x hx, hp⟩).1 = Projectivization.mk ℝ (hyperbolicFlowCoordinate t x) hproj_aux := by
            rw [circularNullBoundaryFlow_mk_axialFlow]
          rw [aux, h]
      have hsep : Real.exp t ≠ Real.exp (-t) := by
        intro h
        apply ht
        have := Real.exp_injective h
        linarith
      constructor
      · intro hfixed
        have hfixed2 := hproj.mp hfixed
        have he : ∃ a : ℝˣ, a • x = hyperbolicFlowCoordinate t x := (Projectivization.mk_eq_mk_iff ℝ (hyperbolicFlowCoordinate t x) x hproj_aux hx).mp hfixed2
        rcases he with ⟨a, hax⟩
        have hc (i : Fin 8) : (a : ℝ) * x i =
            Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) * x i := by
          have hax' : a • x = hyperbolicFlowCoordinate t x := hax
          have hax'' := congrFun hax' i
          simpa [hyperbolicFlowCoordinate_apply, smul_eq_mul] using hax''.symm
        have kill (i : Fin 8) (c : ℝ) (he : (a : ℝ) ≠ c)
            (hi : Real.exp (t * InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i) = c) :
            x i = 0 := by
          by_contra hxi
          apply he
          apply (mul_right_cancel₀ hxi)
          simpa [hi] using hc i
        have memPos : ∀ {y : Coord}, y 0 = 0 → y 4 = 0 → y 5 = 0 → y 6 = 0 → y 7 = 0 → y ∈ positiveWeightSubmodule := by
          intro y h0 h4 h5 h6 h7
          rw [show y = y 1 • Pi.single 1 1 + y 2 • Pi.single 2 1 + y 3 • Pi.single 3 1 by
            ext i; fin_cases i <;> simp [h0, h4, h5, h6, h7]]
          exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have memNeg : ∀ {y : Coord}, y 0 = 0 → y 1 = 0 → y 2 = 0 → y 3 = 0 → y 4 = 0 → y ∈ negativeWeightSubmodule := by
          intro y h0 h1 h2 h3 h4
          rw [show y = y 5 • Pi.single 5 1 + y 6 • Pi.single 6 1 + y 7 • Pi.single 7 1 by
            ext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]]
          exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have memZero : ∀ {y : Coord}, y 1 = 0 → y 2 = 0 → y 3 = 0 → y 5 = 0 → y 6 = 0 → y 7 = 0 → y ∈ zeroWeightSubmodule := by
          intro y h1 h2 h3 h5 h6 h7
          rw [show y = y 0 • Pi.single 0 1 + y 4 • Pi.single 4 1 by
            ext i; fin_cases i <;> simp [h1, h2, h3, h5, h6, h7]]
          exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        by_cases h1 : x 1 ≠ 0
        · have ha' : (a : ℝ) = Real.exp t := by apply (mul_right_cancel₀ h1); simpa using hc 1
          exact Or.inl (memPos (kill 0 1 (by simpa [ha']) (by simp)) (kill 4 1 (by simpa [ha']) (by simp))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg])))
        by_cases h2 : x 2 ≠ 0
        · have ha' : (a : ℝ) = Real.exp t := by apply (mul_right_cancel₀ h2); simpa using hc 2
          exact Or.inl (memPos (kill 0 1 (by simpa [ha']) (by simp)) (kill 4 1 (by simpa [ha']) (by simp))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg])))
        by_cases h3 : x 3 ≠ 0
        · have ha' : (a : ℝ) = Real.exp t := by apply (mul_right_cancel₀ h3); simpa using hc 3
          exact Or.inl (memPos (kill 0 1 (by simpa [ha']) (by simp)) (kill 4 1 (by simpa [ha']) (by simp))
            (kill 5 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg]))
            (kill 6 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg]))
            (kill 7 (Real.exp (-t)) (by simpa [ha'] using hsep) (by simp [Real.exp_neg])))
        by_cases h5 : x 5 ≠ 0
        · have ha' : (a : ℝ) = Real.exp (-t) := by apply (mul_right_cancel₀ h5); simpa [Real.exp_neg] using hc 5
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by simpa [ha']) (by simp))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 4 1 (by simpa [ha']) (by simp))))
        by_cases h6 : x 6 ≠ 0
        · have ha' : (a : ℝ) = Real.exp (-t) := by apply (mul_right_cancel₀ h6); simpa [Real.exp_neg] using hc 6
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by simpa [ha']) (by simp))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 4 1 (by simpa [ha']) (by simp))))
        by_cases h7 : x 7 ≠ 0
        · have ha' : (a : ℝ) = Real.exp (-t) := by apply (mul_right_cancel₀ h7); simpa [Real.exp_neg] using hc 7
          exact Or.inr (Or.inl (memNeg (kill 0 1 (by simpa [ha']) (by simp))
            (kill 1 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 2 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 3 (Real.exp t) (by simpa [ha'] using hsep.symm) (by simp))
            (kill 4 1 (by simpa [ha']) (by simp))))
        · right; right
          have hz := memZero (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
          refine ⟨hz, ?_⟩
          rw [circularPeirceQuadratic_formula] at hQ
          simp_all
      · rintro (h | h | ⟨h, h04⟩)
        · apply hproj.mpr
          have H := projective_positiveWeight_fixed t x hx h
          exact congr_arg Subtype.val H
        · apply hproj.mpr
          have H := projective_negativeWeight_fixed t x hx h
          exact congr_arg Subtype.val H
        · apply hproj.mpr
          rw [circularNullBoundaryFlow_mk_axialFlow]
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
          refine ⟨Units.mk0 1 one_ne_zero, ?_⟩
          rw [hyperbolicFlow_on_zeroWeight t x h]
          simp [Units.smul_def]
"""

text = re.sub(r'theorem circularNullBoundaryFlow_fixed_iff_of_ne_zero.*?(?=theorem circularNullBoundaryFlow_preserves_incidence)', proof + '\n', text, flags=re.DOTALL)

with open('lean/InfoGeometry/Lie/SplitOctonionCircularProjectiveFixedLocus.lean', 'w') as f:
    f.write(text)

