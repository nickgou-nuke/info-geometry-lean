import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean.bak", "r") as f:
    text = f.read()

# Extract the body of `instance : SuperLieRing OSp12 where`
instance_start = text.find("instance : SuperLieRing OSp12 where")
head = text[:instance_start]

lemmas = """
private lemma add_lie_proof (x y z : OSp12) : bracket (x + y) z = bracket x z + bracket y z := by
  ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]

private lemma lie_add_proof (x y z : OSp12) : bracket x (y + z) = bracket x y + bracket x z := by
  ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]

private lemma smul_lie_proof (r : ℝ) (x y : OSp12) : bracket (r • x) y = r • bracket x y := by
  ext k; simp only [bracket, Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ i j, (structConst i j k : ℝ) * (r * x i) * y j = r * ((structConst i j k : ℝ) * x i * y j) := by
    intro i j; ring
  simp_rw [h1, ← Finset.mul_sum]

private lemma lie_smul_proof (r : ℝ) (x y : OSp12) : bracket x (r • y) = r • bracket x y := by
  ext k; simp only [bracket, Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ i j, (structConst i j k : ℝ) * x i * (r * y j) = r * ((structConst i j k : ℝ) * x i * y j) := by
    intro i j; ring
  simp_rw [h1, ← Finset.mul_sum]

private lemma sup_even_odd_proof : evenPart ⊔ oddPart = ⊤ := by
  have hli : LinearIndependent ℝ (Pi.basisFun ℝ B) := (Pi.basisFun ℝ B).linearIndependent
  have hs : ({B.H, B.Ep, B.Em} : Set B) = ({B.G1, B.G2} : Set B)ᶜ := by
    ext x
    cases x <;> decide
  have hspan : Submodule.span ℝ (Set.range (Pi.basisFun ℝ B)) = ⊤ := (Pi.basisFun ℝ B).span_eq
  have hrange : Set.range (Pi.basisFun ℝ B) = (Pi.basisFun ℝ B) '' {B.H, B.Ep, B.Em} ∪ (Pi.basisFun ℝ B) '' {B.G1, B.G2} := by
    rw [hs, ← Set.image_union, Set.compl_union_self, Set.image_univ]
  have hsup : Submodule.span ℝ (Set.range (Pi.basisFun ℝ B)) = Submodule.span ℝ ((Pi.basisFun ℝ B) '' {B.H, B.Ep, B.Em}) ⊔ Submodule.span ℝ ((Pi.basisFun ℝ B) '' {B.G1, B.G2}) := by
    rw [hrange, Submodule.span_union]
  have h1 : (Pi.basisFun ℝ B) '' {B.H, B.Ep, B.Em} = {Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} := by
    ext f; constructor
    · rintro ⟨x, hx, rfl⟩; rcases hx with rfl | rfl | rfl
      · left; simp [Pi.basisFun_apply]
      · right; left; simp [Pi.basisFun_apply]
      · right; right; simp [Pi.basisFun_apply]
    · rintro (rfl | rfl | rfl)
      · exact ⟨B.H, Or.inl rfl, by simp [Pi.basisFun_apply]⟩
      · exact ⟨B.Ep, Or.inr (Or.inl rfl), by simp [Pi.basisFun_apply]⟩
      · exact ⟨B.Em, Or.inr (Or.inr rfl), by simp [Pi.basisFun_apply]⟩
  have h2 : (Pi.basisFun ℝ B) '' {B.G1, B.G2} = {Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} := by
    ext f; constructor
    · rintro ⟨x, hx, rfl⟩; rcases hx with rfl | rfl
      · left; simp [Pi.basisFun_apply]
      · right; simp [Pi.basisFun_apply]
    · rintro (rfl | rfl)
      · exact ⟨B.G1, Or.inl rfl, by simp [Pi.basisFun_apply]⟩
      · exact ⟨B.G2, Or.inr rfl, by simp [Pi.basisFun_apply]⟩
  rw [evenPart, oddPart]
  have h1' : {fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} = {Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have h2' : {fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} = {Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  rw [h1', h2']
  rw [← h1, ← h2]
  rw [← hsup, hspan]

private lemma even_odd_inter_proof : evenPart ⊓ oddPart = ⊥ := by
  have hli : LinearIndependent ℝ (Pi.basisFun ℝ B) := (Pi.basisFun ℝ B).linearIndependent
  have hs : Disjoint ({B.H, B.Ep, B.Em} : Set B) ({B.G1, B.G2} : Set B) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    cases x <;> simp
  have h1 : {fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} = {Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr (Or.inl ?_); ext x <;> cases x <;> simp
      · refine Or.inr (Or.inr ?_); ext x <;> cases x <;> simp
  have h2 : {fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} = {Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  rw [evenPart, oddPart, h1, h2]
  have eq1 : {Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} = (Pi.basisFun ℝ B) '' {B.H, B.Ep, B.Em} := by
    ext f; constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨B.H, Or.inl rfl, by simp [Pi.basisFun_apply]⟩
      · exact ⟨B.Ep, Or.inr (Or.inl rfl), by simp [Pi.basisFun_apply]⟩
      · exact ⟨B.Em, Or.inr (Or.inr rfl), by simp [Pi.basisFun_apply]⟩
    · rintro ⟨x, hx, rfl⟩; rcases hx with rfl | rfl | rfl
      · left; simp [Pi.basisFun_apply]
      · right; left; simp [Pi.basisFun_apply]
      · right; right; simp [Pi.basisFun_apply]
  have eq2 : {Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} = (Pi.basisFun ℝ B) '' {B.G1, B.G2} := by
    ext f; constructor
    · rintro (rfl | rfl)
      · exact ⟨B.G1, Or.inl rfl, by simp [Pi.basisFun_apply]⟩
      · exact ⟨B.G2, Or.inr rfl, by simp [Pi.basisFun_apply]⟩
    · rintro ⟨x, hx, rfl⟩; rcases hx with rfl | rfl
      · left; simp [Pi.basisFun_apply]
      · right; simp [Pi.basisFun_apply]
  rw [eq1, eq2]
  exact LinearIndependent.span_image_disjoint hli hs

private lemma even_even_skew_proof (x y : OSp12) : x ∈ evenPart → y ∈ evenPart → bracket x y = - bracket y x := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
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
          simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          calc
            bracket x (a + b) = bracket x a + bracket x b := by rw [lie_add_proof]
            _ = - bracket a x + - bracket b x := by rw [haP, hbP]
            _ = - bracket (a + b) x := by rw [add_lie_proof]; abel
      | smul r a ha haP =>
          calc
            bracket x (r • a) = r • bracket x a := by rw [lie_smul_proof]
            _ = r • - bracket a x := by rw [haP]
            _ = - r • bracket a x := by rw [smul_neg]
            _ = - bracket (r • a) x := by rw [smul_lie_proof]
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add a b ha hb haP hbP =>
      calc
        bracket (a + b) y = bracket a y + bracket b y := by rw [add_lie_proof]
        _ = - bracket y a + - bracket y b := by rw [haP, hbP]
        _ = - bracket y (a + b) := by rw [lie_add_proof]; abel
  | smul r a ha haP =>
      calc
        bracket (r • a) y = r • bracket a y := by rw [smul_lie_proof]
        _ = r • - bracket y a := by rw [haP]
        _ = - r • bracket y a := by rw [smul_neg]
        _ = - bracket y (r • a) := by rw [lie_smul_proof]

private lemma even_odd_skew_proof (x y : OSp12) : x ∈ evenPart → y ∈ oddPart → bracket x y = - bracket y x := by
  have heven : ({fun x => match x with | B.H => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Ep => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.Em => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
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
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
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
          simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          calc
            bracket x (a + b) = bracket x a + bracket x b := by rw [lie_add_proof]
            _ = - bracket a x + - bracket b x := by rw [haP, hbP]
            _ = - bracket (a + b) x := by rw [add_lie_proof]; abel
      | smul r a ha haP =>
          calc
            bracket x (r • a) = r • bracket x a := by rw [lie_smul_proof]
            _ = r • - bracket a x := by rw [haP]
            _ = - r • bracket a x := by rw [smul_neg]
            _ = - bracket (r • a) x := by rw [smul_lie_proof]
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add a b ha hb haP hbP =>
      calc
        bracket (a + b) y = bracket a y + bracket b y := by rw [add_lie_proof]
        _ = - bracket y a + - bracket y b := by rw [haP, hbP]
        _ = - bracket y (a + b) := by rw [lie_add_proof]; abel
  | smul r a ha haP =>
      calc
        bracket (r • a) y = r • bracket a y := by rw [smul_lie_proof]
        _ = r • - bracket y a := by rw [haP]
        _ = - r • bracket y a := by rw [smul_neg]
        _ = - bracket y (r • a) := by rw [lie_smul_proof]

private lemma odd_odd_symm_proof (x y : OSp12) : x ∈ oddPart → y ∈ oddPart → bracket x y = bracket y x := by
  have hodd : ({fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
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
          simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num
      | zero =>
          ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.zero_lie]
      | add a b ha hb haP hbP =>
          calc
            bracket x (a + b) = bracket x a + bracket x b := by rw [lie_add_proof]
            _ = bracket a x + bracket b x := by rw [haP, hbP]
            _ = bracket (a + b) x := by rw [add_lie_proof]
      | smul r a ha haP =>
          calc
            bracket x (r • a) = r • bracket x a := by rw [lie_smul_proof]
            _ = r • bracket a x := by rw [haP]
            _ = bracket (r • a) x := by rw [smul_lie_proof]
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add a b ha hb haP hbP =>
      calc
        bracket (a + b) y = bracket a y + bracket b y := by rw [add_lie_proof]
        _ = bracket y a + bracket y b := by rw [haP, hbP]
        _ = bracket y (a + b) := by rw [lie_add_proof]
  | smul r a ha haP =>
      calc
        bracket (r • a) y = r • bracket a y := by rw [smul_lie_proof]
        _ = r • bracket y a := by rw [haP]
        _ = bracket y (r • a) := by rw [lie_smul_proof]
"""

# Now write it out to reconstruct.py so it can be generated!
with open("tools/infra/inject_lemmas.py", "w") as f2:
    f2.write(f"""
with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean.bak", "r") as fb:
    tb = fb.read()

head = tb[:tb.find("instance : SuperLieRing OSp12 where")]

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as fw:
    fw.write(head + {repr(lemmas)})

""")

print("Done")
