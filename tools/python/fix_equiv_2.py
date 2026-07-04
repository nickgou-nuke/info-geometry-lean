import re

with open("lean/InfoGeometry/Causal/EntropyFoliation.lean", "r") as f:
    content = f.read()

replacement = """/-- Equivalence relation proof. -/
lemma CausalRay.equiv_is_equiv {V : Type*} [AddCommGroup V] [Module ℝ V] (C : CausalStructure V) :
  Equivalence (@CausalRay.equiv V _ _ C) := by
  constructor
  · intro x
    use 1
    exact ⟨by norm_num, (one_smul ℝ x.v).symm⟩
  · rintro x y ⟨lam, hlam, heq⟩
    use lam⁻¹
    constructor
    · exact inv_pos.mpr hlam
    · rw [heq, smul_smul, inv_mul_cancel₀ (ne_of_gt hlam), one_smul]
  · rintro x y z ⟨lam1, hlam1, heq1⟩ ⟨lam2, hlam2, heq2⟩
    use lam1 * lam2
    constructor
    · exact mul_pos hlam1 hlam2
    · rw [heq1, heq2, smul_smul]"""

content = re.sub(r"/-- Equivalence relation proof\. -/\nlemma CausalRay\.equiv_is_equiv.*?smul_smul\]", replacement, content, flags=re.DOTALL)

with open("lean/InfoGeometry/Causal/EntropyFoliation.lean", "w") as f:
    f.write(content)
