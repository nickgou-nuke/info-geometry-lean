import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    lines = f.readlines()

for i, line in enumerate(lines):
    if line.startswith("private theorem jacobi_odd_odd_proof :"):
        start_idx = i
        break

pre_lines = lines[:start_idx]
post_lines = []
for i in range(start_idx, len(lines)):
    if lines[i].startswith("instance : SuperLieRing OSp12 where"):
        post_lines = lines[i:]
        break

new_lemmas = """
private lemma jacobi_odd_odd_z (x y z : OSp12)
    (hxgen : x ∈ ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12))
    (hygen : y ∈ ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12)) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
    ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
  have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
    rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
    exact (Pi.basisFun ℝ B).span_eq
  have hz : z ∈ Submodule.span ℝ S := by simpa [hspan] using (show z ∈ (⊤ : Submodule ℝ OSp12) from by simp)
  have hsmul_right : ∀ (r : ℝ) (a b : OSp12), bracket a (r • b) = r • bracket a b := by
    intro r a b; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  induction hz using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with rfl | rfl <;> rcases hygen with rfl | rfl <;>
        rcases hzgen with ⟨a, rfl⟩ <;> cases a <;>
        ext k <;> fin_cases k <;>
        simp [bracket, Pi.single, Function.update, structConst]
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add a b ha hb haP hbP =>
      calc
        bracket x (bracket y (a + b))
            = bracket x (bracket y a + bracket y b) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = bracket x (bracket y a) + bracket x (bracket y b) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket x y) a - bracket y (bracket x a)) +
              (bracket (bracket x y) b - bracket y (bracket x b)) := by simpa [add_comm, add_left_comm, add_assoc] using congrArg2 HAdd.hAdd haP hbP
        _ = bracket (bracket x y) (a + b) - bracket y (bracket x (a + b)) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add]
  | smul r a ha haP =>
      calc
        bracket x (bracket y (r • a))
            = bracket x (r • bracket y a) := by rw [hsmul_right]
        _ = r • bracket x (bracket y a) := by rw [hsmul_right]
        _ = r • (bracket (bracket x y) a - bracket y (bracket x a)) := by rw [haP]
        _ = bracket (bracket x y) (r • a) - bracket y (bracket x (r • a)) := by simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_sub, smul_add, add_comm, add_left_comm, add_assoc]

private lemma jacobi_odd_odd_y (x y z : OSp12)
    (hxgen : x ∈ ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12))
    (hy : y ∈ oddPart) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({fun x => match x with | B.G1 => 1 | x => 0, fun x => match x with | B.G2 => 1 | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
    ext f
    constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
    intro r a b; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  have hsmul_right : ∀ (r : ℝ) (a b : OSp12), bracket a (r • b) = r • bracket a b := by
    intro r a b; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  rw [oddPart, hodd] at hy
  induction hy using Submodule.span_induction with
  | mem y hygen => exact jacobi_odd_odd_z x y z hxgen hygen
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add a b ha hb haP hbP =>
      calc
        bracket x (bracket (a + b) z)
            = bracket x (bracket a z + bracket b z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = bracket x (bracket a z) + bracket x (bracket b z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket x a) z - bracket a (bracket x z)) +
              (bracket (bracket x b) z - bracket b (bracket x z)) := by simpa [add_comm, add_left_comm, add_assoc] using congrArg2 HAdd.hAdd haP hbP
        _ = bracket (bracket x (a + b)) z - bracket (a + b) (bracket x z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add]
  | smul r a ha haP =>
      calc
        bracket x (bracket (r • a) z)
            = bracket x (r • bracket a z) := by rw [hsmul_left]
        _ = r • bracket x (bracket a z) := by rw [hsmul_right]
        _ = r • (bracket (bracket x a) z - bracket a (bracket x z)) := by rw [haP]
        _ = bracket (bracket x (r • a)) z - bracket (r • a) (bracket x z) := by simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_sub, smul_add, add_comm, add_left_comm, add_assoc]

private theorem jacobi_odd_odd_proof :
    ∀ (x y z : OSp12), x ∈ oddPart → y ∈ oddPart → bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({fun x => match x with | B.G1 => 1 | x => 0, fun x => match x with | B.G2 => 1 | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
    ext f
    constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  have hsmul_left : ∀ (r : ℝ) (a b : OSp12), bracket (r • a) b = r • bracket a b := by
    intro r a b; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro x y z hx hy
  have hx2 := hx
  rw [oddPart, hodd] at hx2
  induction hx2 using Submodule.span_induction with
  | mem x hxgen => exact jacobi_odd_odd_y x y z hxgen hy
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add a b ha hb haP hbP =>
      calc
        bracket (a + b) (bracket y z)
            = bracket a (bracket y z) + bracket b (bracket y z) := by ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket a y) z - bracket y (bracket a z)) +
              (bracket (bracket b y) z - bracket y (bracket b z)) := by rw [haP, hbP]
        _ = bracket (bracket (a + b) y) z - bracket y (bracket (a + b) z) := by ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add]
  | smul r a ha haP =>
      calc
        bracket (r • a) (bracket y z)
            = r • bracket a (bracket y z) := by rw [hsmul_left]
        _ = r • (bracket (bracket a y) z - bracket y (bracket a z)) := by rw [haP]
        _ = bracket (bracket (r • a) y) z - bracket y (bracket (r • a) z) := by ext k; simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_sub]

"""

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.writelines(pre_lines)
    f.write(new_lemmas)
    f.writelines(post_lines)

print("Done")
