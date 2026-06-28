import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean.bak", "r") as f:
    text = f.read()

# 1. Get head
start_idx = text.find("instance : SuperLieRing OSp12 where")
head = text[:start_idx]

# Fix head syntax errors
head = head.replace("set S : Set OSp12", "let S : Set OSp12")

# Fix head maxHeartbeats
if "set_option maxHeartbeats 8000000" not in head:
    head = head.replace("set_option maxHeartbeats 800000", "set_option maxHeartbeats 8000000")

# Fix head types in sets
head = re.sub(r"have h1' : \{fun x => match x with.*?\} = \{Pi.single.*?\} := by",
              r"have h1' : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) = ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by",
              head, flags=re.DOTALL)

head = re.sub(r"have h2' : \{fun x => match x with.*?\} = \{Pi.single.*?\} := by",
              r"have h2' : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) = ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by",
              head, flags=re.DOTALL)

# Make sure `(1 : ℝ)` is everywhere
head = head.replace("{Pi.single H 1, Pi.single Ep 1, Pi.single Em 1}", "{Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)}")
head = head.replace("{Pi.single G1 1, Pi.single G2 1}", "{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}")

# 2. Skew lemmas
lemmas_skew = """
private lemma add_lie_proof (x y z : OSp12) : bracket (x + y) z = bracket x z + bracket y z := by
  ext k; simp [bracket, add_mul, mul_add, Finset.sum_add_distrib]

private lemma lie_add_proof (x y z : OSp12) : bracket x (y + z) = bracket x y + bracket x z := by
  ext k; simp [bracket, add_mul, mul_add, Finset.sum_add_distrib]

private lemma smul_lie_proof (r : ℝ) (x y : OSp12) : bracket (r • x) y = r • bracket x y := by
  ext k; simp [bracket, mul_assoc, Finset.mul_sum]
  congr; ext i; congr; ext j; ring

private lemma lie_smul_proof (r : ℝ) (x y : OSp12) : bracket x (r • y) = r • bracket x y := by
  ext k; simp [bracket, mul_assoc, Finset.mul_sum]
  congr; ext i; congr; ext j; ring

private lemma sup_even_odd_proof : evenPart ⊔ oddPart = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x B.H • Pi.single B.H (1 : ℝ) + x B.Ep • Pi.single B.Ep (1 : ℝ) + x B.Em • Pi.single B.Em (1 : ℝ) +
                x B.G1 • Pi.single B.G1 (1 : ℝ) + x B.G2 • Pi.single B.G2 (1 : ℝ) := by
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
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private lemma even_odd_inter_proof : evenPart ⊓ oddPart = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases hx with ⟨hxeven, hxodd⟩
  have heven : ({{fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hodd : ({{fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  rw [evenPart, heven] at hxeven
  rw [oddPart, hodd] at hxodd
  rw [Submodule.mem_span_insert, Submodule.mem_span_insert, Submodule.mem_span_singleton] at hxeven
  rw [Submodule.mem_span_insert, Submodule.mem_span_singleton] at hxodd
  rcases hxeven with ⟨c1, v1, hv1, rfl⟩
  rcases hv1 with ⟨c2, v2, hv2, rfl⟩
  rcases hv2 with ⟨c3, rfl⟩
  rcases hxodd with ⟨d1, w1, hw1, rfl⟩
  rcases hw1 with ⟨d2, rfl⟩
  have eq : c1 • Pi.single B.H (1 : ℝ) + c2 • Pi.single B.Ep (1 : ℝ) + c3 • Pi.single B.Em (1 : ℝ) =
            d1 • Pi.single B.G1 (1 : ℝ) + d2 • Pi.single B.G2 (1 : ℝ) := by assumption
  ext k
  fin_cases k
  · have hH := congr_fun eq B.H; simpa [Pi.single] using hH
  · have hEp := congr_fun eq B.Ep; simpa [Pi.single] using hEp
  · have hEm := congr_fun eq B.Em; simpa [Pi.single] using hEm
  · have hG1 := congr_fun eq B.G1; simpa [Pi.single] using hG1
  · have hG2 := congr_fun eq B.G2; simpa [Pi.single] using hG2

private lemma even_even_skew_proof (x y : OSp12) : x ∈ evenPart → y ∈ evenPart → bracket x y = - bracket y x := by
  have heven : ({{fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  intro hx hy
  rw [evenPart, heven] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hxgen =>
      induction hy using Submodule.span_induction with
      | mem y hygen =>
          rcases hxgen with rfl | rfl | rfl <;>
          rcases hygen with rfl | rfl | rfl <;>
          ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel
      | smul r a ha haP =>
          simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg]; abel
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
  | add a b ha hb haP hbP =>
      simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel
  | smul r a ha haP =>
      simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg]; abel

private lemma even_odd_skew_proof (x y : OSp12) : x ∈ evenPart → y ∈ oddPart → bracket x y = - bracket y x := by
  have heven : ({{fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have hodd : ({{fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  intro hx hy
  rw [evenPart, heven] at hx
  rw [oddPart, hodd] at hy
  induction hx using Submodule.span_induction with
  | mem x hxgen =>
      induction hy using Submodule.span_induction with
      | mem y hygen =>
          rcases hxgen with rfl | rfl | rfl <;>
          rcases hygen with rfl | rfl <;>
          ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel
      | smul r a ha haP =>
          simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg]; abel
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
  | add a b ha hb haP hbP =>
      simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel
  | smul r a ha haP =>
      simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg]; abel

private lemma odd_odd_symm_proof (x y : OSp12) : x ∈ oddPart → y ∈ oddPart → bracket x y = bracket y x := by
  have hodd : ({{fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  intro hx hy
  rw [oddPart, hodd] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hxgen =>
      induction hy using Submodule.span_induction with
      | mem y hygen =>
          rcases hxgen with rfl | rfl <;>
          rcases hygen with rfl | rfl <;>
          ext k <;> fin_cases k <;>
          simp [bracket, Pi.single, Function.update, structConst]
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel
      | smul r a ha haP =>
          simp only [smul_lie_proof, lie_smul_proof, haP]
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
  | add a b ha hb haP hbP =>
      simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel
  | smul r a ha haP =>
      simp only [smul_lie_proof, lie_smul_proof, haP]

"""

import sys
sys.path.append("tools/infra")
from fix_jacobi_all import build_lemmas

# The build_lemmas function generated calc blocks that might fail, wait!
# Let's generate it and then replace calc blocks with simp only !
lemmas_jacobi = build_lemmas()

# Replace the types inside `lemmas_jacobi`
lemmas_jacobi = lemmas_jacobi.replace("B.H => 1", "B.H => (1 : ℝ)")
lemmas_jacobi = lemmas_jacobi.replace("B.Ep => 1", "B.Ep => (1 : ℝ)")
lemmas_jacobi = lemmas_jacobi.replace("B.Em => 1", "B.Em => (1 : ℝ)")
lemmas_jacobi = lemmas_jacobi.replace("B.G1 => 1", "B.G1 => (1 : ℝ)")
lemmas_jacobi = lemmas_jacobi.replace("B.G2 => 1", "B.G2 => (1 : ℝ)")
lemmas_jacobi = lemmas_jacobi.replace("x => 0", "x => (0 : ℝ)")

# Replace `simp [bracket, Pi.single, Function.update, structConst]`
lemmas_jacobi = lemmas_jacobi.replace("simp [bracket, Pi.single, Function.update, structConst]",
                                      "simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num")

# Now, `lemmas_jacobi` contains calc blocks like:
#      calc
#        bracket x (bracket (a + b) z) = bracket x (bracket a z) + bracket x (bracket b z) := by rw [lie_add_proof, lie_add_proof]
# we want: `simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel`
# Let's completely replace the induction branches in lemmas_jacobi
lemmas_jacobi = re.sub(r"\| add u v hu hv huP hvP =>\s+calc.*?\| smul",
                       r"| add u v hu hv huP hvP =>\n      simp only [add_lie_proof, lie_add_proof, huP, hvP]; abel\n  | smul",
                       lemmas_jacobi, flags=re.DOTALL)
lemmas_jacobi = re.sub(r"\| smul r u hu huP =>\s+calc.*?(?=\n\n)",
                       r"| smul r u hu huP =>\n      simp only [smul_lie_proof, lie_smul_proof, huP, smul_neg]; abel",
                       lemmas_jacobi, flags=re.DOTALL)


instance_block = """
instance : SuperLieRing OSp12 where
  bracket := bracket
  evenPart := evenPart
  oddPart := oddPart
  add_lie := add_lie_proof
  lie_add := lie_add_proof
  lie_smul := lie_smul_proof
  sup_even_odd := sup_even_odd_proof
  even_odd_inter := even_odd_inter_proof
  even_even_skew := even_even_skew_proof
  even_odd_skew := even_odd_skew_proof
  odd_odd_symm := odd_odd_symm_proof
  jacobi_even := jacobi_even_proof
  jacobi_odd_odd := by
    intro x y z hx hy
    exact jacobi_odd_odd_proof x y z hx hy

end OSp12

end InfoGeometry.Clifford.ConformalSpinorBridge
"""

# BUT WAIT! `head` already contains `sum_B_eval`? No, `.bak` DOES NOT HAVE `sum_B_eval`!
# I MUST ADD `sum_B_eval` to `head`!
sum_b_eval = """
private lemma sum_B_eval (f : B → ℝ) : ∑ i : B, f i = f B.H + f B.Ep + f B.Em + f B.G1 + f B.G2 := by
  have : (Finset.univ : Finset B) = {B.H, B.Ep, B.Em, B.G1, B.G2} := rfl
  simp [this, Finset.sum_insert, Finset.sum_singleton]
"""
# insert it before `noncomputable def evenPart`
even_idx = head.find("noncomputable def evenPart")
head = head[:even_idx] + sum_b_eval + "\n" + head[even_idx:]

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(head + lemmas_skew + lemmas_jacobi + instance_block)

print("Done")
