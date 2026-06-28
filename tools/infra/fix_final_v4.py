with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Replace the sup_even_odd_proof logic
old_sup = """private lemma sup_even_odd_proof : evenPart ⊔ oddPart = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x B.H • (Pi.single B.H (1 : ℝ) : OSp12) + x B.Ep • (Pi.single B.Ep (1 : ℝ) : OSp12) + x B.Em • (Pi.single B.Em (1 : ℝ) : OSp12) +
                x B.G1 • (Pi.single B.G1 (1 : ℝ) : OSp12) + x B.G2 • (Pi.single B.G2 (1 : ℝ) : OSp12) := by
    ext k <;> fin_cases k <;> simp [Pi.single]
  rw [hx]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.add_mem
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))"""

new_sup = """private lemma sup_even_odd_proof : evenPart ⊔ oddPart = ⊤ := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  rw [eq_top_iff]
  intro x _
  have hsum : x = (x B.H • (Pi.single B.H (1 : ℝ) : OSp12) + x B.Ep • (Pi.single B.Ep (1 : ℝ) : OSp12) + x B.Em • (Pi.single B.Em (1 : ℝ) : OSp12)) +
                  (x B.G1 • (Pi.single B.G1 (1 : ℝ) : OSp12) + x B.G2 • (Pi.single B.G2 (1 : ℝ) : OSp12)) := by
    ext k <;> fin_cases k <;> simp [Pi.single]
  rw [hsum]
  apply Submodule.add_mem (evenPart ⊔ oddPart)
  · apply Submodule.mem_sup_left
    rw [evenPart, heven]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.mem_sup_right
    rw [oddPart, hodd]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))"""

if old_sup in text:
    text = text.replace(old_sup, new_sup)
else:
    print("Could not find old_sup")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
