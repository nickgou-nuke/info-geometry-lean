with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

old_induction = """  have hxG1 : x B.G1 = 0 := by
    induction hxeven using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v, Pi.add_apply]
    | smul r u hu ih_u => simp [ih_u, Pi.smul_apply]
  have hxG2 : x B.G2 = 0 := by
    induction hxeven using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v, Pi.add_apply]
    | smul r u hu ih_u => simp [ih_u, Pi.smul_apply]
  have hxH : x B.H = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v, Pi.add_apply]
    | smul r u hu ih_u => simp [ih_u, Pi.smul_apply]
  have hxEp : x B.Ep = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v, Pi.add_apply]
    | smul r u hu ih_u => simp [ih_u, Pi.smul_apply]
  have hxEm : x B.Em = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v, Pi.add_apply]
    | smul r u hu ih_u => simp [ih_u, Pi.smul_apply]
  ext k
  fin_cases k
  · exact hxH
  · exact hxEp
  · exact hxEm
  · exact hxG1
  · exact hxG2"""

new_induction = """  have hxeven_zero : x B.G1 = 0 ∧ x B.G2 = 0 := by
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
      exact ⟨by simp [Pi.smul_apply, hu1], by simp [Pi.smul_apply, hu2], by simp [Pi.smul_apply, hu3]⟩
  ext k
  fin_cases k
  · exact hxodd_zero.1
  · exact hxodd_zero.2.1
  · exact hxodd_zero.2.2
  · exact hxeven_zero.1
  · exact hxeven_zero.2"""

if old_induction in text:
    text = text.replace(old_induction, new_induction)
else:
    print("COULD NOT FIND OLD INDUCTION")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
