with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Add the lemmas BEFORE even_odd_inter_proof
new_lemmas = """private lemma evenPart_zero_on_odd (x : OSp12) (hxeven : x ∈ Submodule.span ℝ ({(Pi.single B.H (1 : ℝ) : OSp12), (Pi.single B.Ep (1 : ℝ) : OSp12), (Pi.single B.Em (1 : ℝ) : OSp12)} : Set OSp12)) : x B.G1 = 0 ∧ x B.G2 = 0 := by
  induction hxeven using Submodule.span_induction with
  | mem v hv => rcases hv with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  | zero => exact ⟨rfl, rfl⟩
  | add u v hu hv ih_u ih_v => exact ⟨by simp [Pi.add_apply, ih_u.1, ih_v.1], by simp [Pi.add_apply, ih_u.2, ih_v.2]⟩
  | smul r u hu ih_u => exact ⟨by simp [Pi.smul_apply, ih_u.1], by simp [Pi.smul_apply, ih_u.2]⟩

private lemma oddPart_zero_on_even (x : OSp12) (hxodd : x ∈ Submodule.span ℝ ({(Pi.single B.G1 (1 : ℝ) : OSp12), (Pi.single B.G2 (1 : ℝ) : OSp12)} : Set OSp12)) : x B.H = 0 ∧ x B.Ep = 0 ∧ x B.Em = 0 := by
  induction hxodd using Submodule.span_induction with
  | mem v hv => rcases hv with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  | zero => exact ⟨rfl, rfl, rfl⟩
  | add u v hu hv ih_u ih_v => exact ⟨by simp [Pi.add_apply, ih_u.1, ih_v.1], by simp [Pi.add_apply, ih_u.2.1, ih_v.2.1], by simp [Pi.add_apply, ih_u.2.2, ih_v.2.2]⟩
  | smul r u hu ih_u => exact ⟨by simp [Pi.smul_apply, ih_u.1], by simp [Pi.smul_apply, ih_u.2.1], by simp [Pi.smul_apply, ih_u.2.2]⟩

private lemma even_odd_inter_proof : evenPart ⊓ oddPart = ⊥ := by"""

text = text.replace("private lemma even_odd_inter_proof : evenPart ⊓ oddPart = ⊥ := by", new_lemmas)

# Now fix the inside of even_odd_inter_proof
old_inside = """  have hxeven_zero : x B.G1 = 0 ∧ x B.G2 = 0 := by
    induction hxeven using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
    | zero => exact ⟨rfl, rfl⟩
    | add u v hu hv ih_u ih_v =>
      rcases ih_u with ⟨hu1, hu2⟩
      rcases ih_v with ⟨hv1, hv2⟩
      exact ⟨by simp [Pi.add_apply, hu1, hv1], by simp [Pi.add_apply, hu2, hv2]⟩
    | smul r u hu ih_u =>
      rcases ih_u with ⟨hu1, hu2⟩
      exact ⟨by simp [Pi.smul_apply, hu1], by simp [Pi.smul_apply, hu2]⟩
  have hxodd_zero : x B.H = 0 ∧ x B.Ep = 0 ∧ x B.Em = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
    | zero => exact ⟨rfl, rfl, rfl⟩
    | add u v hu hv ih_u ih_v =>
      rcases ih_u with ⟨hu1, hu2, hu3⟩
      rcases ih_v with ⟨hv1, hv2, hv3⟩
      exact ⟨by simp [Pi.add_apply, hu1, hv1], by simp [Pi.add_apply, hu2, hv2], by simp [Pi.add_apply, hu3, hv3]⟩
    | smul r u hu ih_u =>
      rcases ih_u with ⟨hu1, hu2, hu3⟩
      exact ⟨by simp [Pi.smul_apply, hu1], by simp [Pi.smul_apply, hu2], by simp [Pi.smul_apply, hu3]⟩"""

new_inside = """  have hxeven_zero := evenPart_zero_on_odd x hxeven
  have hxodd_zero := oddPart_zero_on_even x hxodd"""

text = text.replace(old_inside, new_inside)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
