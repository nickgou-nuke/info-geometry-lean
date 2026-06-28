with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Fix even_odd_inter_proof
old_inter = """  rw [Submodule.mem_span_insert] at hxeven
  rcases hxeven with ⟨c1, v1, hv1, rfl⟩
  rw [Submodule.mem_span_insert] at hv1
  rcases hv1 with ⟨c2, v2, hv2, rfl⟩
  rw [Submodule.mem_span_singleton] at hv2
  rcases hv2 with ⟨c3, rfl⟩
  
  rw [Submodule.mem_span_insert] at hxodd
  rcases hxodd with ⟨d1, w1, hw1, rfl⟩
  rw [Submodule.mem_span_singleton] at hw1
  rcases hw1 with ⟨d2, rfl⟩
  have eq : c1 • (Pi.single B.H (1 : ℝ) : OSp12) + c2 • (Pi.single B.Ep (1 : ℝ) : OSp12) + c3 • (Pi.single B.Em (1 : ℝ) : OSp12) =
            d1 • (Pi.single B.G1 (1 : ℝ) : OSp12) + d2 • (Pi.single B.G2 (1 : ℝ) : OSp12) := by assumption
  ext k
  fin_cases k
  · have hH := congr_fun eq B.H; simpa [Pi.single] using hH
  · have hEp := congr_fun eq B.Ep; simpa [Pi.single] using hEp
  · have hEm := congr_fun eq B.Em; simpa [Pi.single] using hEm
  · have hG1 := congr_fun eq B.G1; simpa [Pi.single] using hG1
  · have hG2 := congr_fun eq B.G2; simpa [Pi.single] using hG2"""

new_inter = """  have hxG1 : x B.G1 = 0 := by
    induction hxeven using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v]
    | smul r u hu ih_u => simp [ih_u]
  have hxG2 : x B.G2 = 0 := by
    induction hxeven using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v]
    | smul r u hu ih_u => simp [ih_u]
  have hxH : x B.H = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v]
    | smul r u hu ih_u => simp [ih_u]
  have hxEp : x B.Ep = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v]
    | smul r u hu ih_u => simp [ih_u]
  have hxEm : x B.Em = 0 := by
    induction hxodd using Submodule.span_induction with
    | mem v hv => rcases hv with rfl | rfl <;> rfl
    | zero => rfl
    | add u v hu hv ih_u ih_v => simp [ih_u, ih_v]
    | smul r u hu ih_u => simp [ih_u]
  ext k
  fin_cases k
  · exact hxH
  · exact hxEp
  · exact hxEm
  · exact hxG1
  · exact hxG2"""

if old_inter in text:
    text = text.replace(old_inter, new_inter)
else:
    print("Could not find old_inter")

# Fix smul goals
text = text.replace("simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg, smul_add]; abel",
                    "simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg, smul_add, smul_sub]; abel")

text = text.replace("simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add]; abel",
                    "simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg, smul_add, smul_sub]; abel")

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")
