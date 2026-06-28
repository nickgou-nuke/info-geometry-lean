import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    lines = f.readlines()

for i, line in enumerate(lines):
    if line.startswith("private theorem jacobi_even_basis"):
        start_idx = i
        break

for i in range(start_idx, len(lines)):
    if lines[i].startswith("private theorem jacobi_even_proof :"):
        even_proof_idx = i
        break

for i in range(even_proof_idx, len(lines)):
    if lines[i].startswith("private theorem jacobi_odd_odd_proof :"):
        odd_proof_idx = i
        break

for i in range(odd_proof_idx, len(lines)):
    if lines[i].startswith("instance : SuperLieRing OSp12 where"):
        end_idx = i
        break

pre_lines = lines[:start_idx]
mid_lines = lines[even_proof_idx:odd_proof_idx] # wait no, I want to replace jacobi_even_proof as well!
post_lines = lines[end_idx:]

new_lemmas = """
private lemma jacobi_basis_even (a b c : B) (ha : a ∈ ({B.H, B.Ep, B.Em} : Set B)) :
    bracket (Pi.single a (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single a (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) +
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single a (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  rcases ha with rfl | rfl | rfl <;> cases b <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private lemma jacobi_even_z (x y z : OSp12)
    (hxgen : ∃ a ∈ ({B.H, B.Ep, B.Em} : Set B), x = Pi.single a (1 : ℝ))
    (hygen : ∃ b : B, y = Pi.single b (1 : ℝ)) :
    ∀ z : OSp12, z ∈ (⊤ : Submodule ℝ OSp12) → bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hsmul_right : ∀ (r : ℝ) (u v : OSp12), bracket u (r • v) = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro z hz
  have hz_span : z ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rwa [hspan]
  induction hz_span using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with ⟨a, ha, rfl⟩
      rcases hygen with ⟨b, rfl⟩
      rcases hzgen with ⟨c, rfl⟩
      exact jacobi_basis_even a b c ha
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add u v hu hv huP hvP =>
      calc
        bracket x (bracket y (u + v))
            = bracket x (bracket y u + bracket y v) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = bracket x (bracket y u) + bracket x (bracket y v) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket x y) u + bracket y (bracket x u)) +
              (bracket (bracket x y) v + bracket y (bracket x v)) := by simpa [add_comm, add_left_comm, add_assoc] using congrArg2 HAdd.hAdd huP hvP
        _ = bracket (bracket x y) (u + v) + bracket y (bracket x (u + v)) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
  | smul r u hu huP =>
      calc
        bracket x (bracket y (r • u))
            = bracket x (r • bracket y u) := by rw [hsmul_right]
        _ = r • bracket x (bracket y u) := by rw [hsmul_right]
        _ = r • (bracket (bracket x y) u + bracket y (bracket x u)) := by rw [huP]
        _ = bracket (bracket x y) (r • u) + bracket y (bracket x (r • u)) := by simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, smul_add, add_comm, add_left_comm, add_assoc]

private lemma jacobi_even_y (x y z : OSp12)
    (hxgen : ∃ a ∈ ({B.H, B.Ep, B.Em} : Set B), x = Pi.single a (1 : ℝ)) :
    ∀ y : OSp12, y ∈ (⊤ : Submodule ℝ OSp12) → bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hsmul_left : ∀ (r : ℝ) (u v : OSp12), bracket (r • u) v = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  have hsmul_right : ∀ (r : ℝ) (u v : OSp12), bracket u (r • v) = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro y hy
  have hy_span : y ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rwa [hspan]
  induction hy_span using Submodule.span_induction with
  | mem y hygen =>
      rcases hygen with ⟨b, rfl⟩
      exact jacobi_even_z x _ z hxgen ⟨b, rfl⟩ z (by simp)
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add u v hu hv huP hvP =>
      calc
        bracket x (bracket (u + v) z)
            = bracket x (bracket u z + bracket v z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = bracket x (bracket u z) + bracket x (bracket v z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket x u) z + bracket u (bracket x z)) +
              (bracket (bracket x v) z + bracket v (bracket x z)) := by simpa [add_comm, add_left_comm, add_assoc] using congrArg2 HAdd.hAdd huP hvP
        _ = bracket (bracket x (u + v)) z + bracket (u + v) (bracket x z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
  | smul r u hu huP =>
      calc
        bracket x (bracket (r • u) z)
            = bracket x (r • bracket u z) := by rw [hsmul_left]
        _ = r • bracket x (bracket u z) := by rw [hsmul_right]
        _ = r • (bracket (bracket x u) z + bracket u (bracket x z)) := by rw [huP]
        _ = bracket (bracket x (r • u)) z + bracket (r • u) (bracket x z) := by simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, smul_add, add_comm, add_left_comm, add_assoc]

private theorem jacobi_even_proof :
    ∀ (x y z : OSp12), x ∈ evenPart → bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  have heven : ({fun x => match x with | H => 1 | x => 0, fun x => match x with | Ep => 1 | x => 0, fun x => match x with | Em => 1 | x => 0} : Set OSp12) =
          ({Pi.single B.H (1 : ℝ), Pi.single B.Ep (1 : ℝ), Pi.single B.Em (1 : ℝ)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; left; ext x <;> cases x <;> simp
      · right; right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr <| Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr <| Or.inr ?_; ext x <;> cases x <;> simp
  have hsmul_left : ∀ (r : ℝ) (u v : OSp12), bracket (r • u) v = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro x y z hx
  have hx2 := hx
  rw [evenPart, heven] at hx2
  induction hx2 using Submodule.span_induction with
  | mem x hxgen =>
      have hxgen_a : ∃ a ∈ ({B.H, B.Ep, B.Em} : Set B), x = Pi.single a (1 : ℝ) := by
        rcases hxgen with rfl | rfl | rfl
        · exact ⟨B.H, Or.inl rfl, rfl⟩
        · exact ⟨B.Ep, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨B.Em, Or.inr (Or.inr rfl), rfl⟩
      exact jacobi_even_y x y z hxgen_a y (by simp)
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add u v hu hv huP hvP =>
      calc
        bracket (u + v) (bracket y z)
            = bracket u (bracket y z) + bracket v (bracket y z) := by ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket u y) z + bracket y (bracket u z)) +
              (bracket (bracket v y) z + bracket y (bracket v z)) := by rw [huP, hvP]
        _ = bracket (bracket (u + v) y) z + bracket y (bracket (u + v) z) := by ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, add_comm, add_left_comm, add_assoc]
  | smul r u hu huP =>
      calc
        bracket (r • u) (bracket y z)
            = r • bracket u (bracket y z) := by rw [hsmul_left]
        _ = r • (bracket (bracket u y) z + bracket y (bracket u z)) := by rw [huP]
        _ = bracket (bracket (r • u) y) z + bracket y (bracket (r • u) z) := by ext k; simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, smul_add, add_comm, add_left_comm, add_assoc]

private lemma jacobi_basis_odd (a b c : B) (ha : a ∈ ({B.G1, B.G2} : Set B)) (hb : b ∈ ({B.G1, B.G2} : Set B)) :
    bracket (Pi.single a (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single a (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) -
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single a (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;>
    simp [bracket, Pi.single, Function.update, structConst]

private lemma jacobi_odd_odd_z (x y z : OSp12)
    (hxgen : ∃ a ∈ ({B.G1, B.G2} : Set B), x = Pi.single a (1 : ℝ))
    (hygen : ∃ b ∈ ({B.G1, B.G2} : Set B), y = Pi.single b (1 : ℝ)) :
    ∀ z : OSp12, z ∈ (⊤ : Submodule ℝ OSp12) → bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hsmul_right : ∀ (r : ℝ) (u v : OSp12), bracket u (r • v) = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro z hz
  have hz_span : z ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rwa [hspan]
  induction hz_span using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with ⟨a, ha, rfl⟩
      rcases hygen with ⟨b, hb, rfl⟩
      rcases hzgen with ⟨c, rfl⟩
      exact jacobi_basis_odd a b c ha hb
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add u v hu hv huP hvP =>
      calc
        bracket x (bracket y (u + v))
            = bracket x (bracket y u + bracket y v) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = bracket x (bracket y u) + bracket x (bracket y v) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket x y) u - bracket y (bracket x u)) +
              (bracket (bracket x y) v - bracket y (bracket x v)) := by simpa [add_comm, add_left_comm, add_assoc] using congrArg2 HAdd.hAdd huP hvP
        _ = bracket (bracket x y) (u + v) - bracket y (bracket x (u + v)) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add]
  | smul r u hu huP =>
      calc
        bracket x (bracket y (r • u))
            = bracket x (r • bracket y u) := by rw [hsmul_right]
        _ = r • bracket x (bracket y u) := by rw [hsmul_right]
        _ = r • (bracket (bracket x y) u - bracket y (bracket x u)) := by rw [huP]
        _ = bracket (bracket x y) (r • u) - bracket y (bracket x (r • u)) := by simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_sub, smul_add, add_comm, add_left_comm, add_assoc]

private lemma jacobi_odd_odd_y (x y z : OSp12)
    (hxgen : ∃ a ∈ ({B.G1, B.G2} : Set B), x = Pi.single a (1 : ℝ)) :
    ∀ y : OSp12, y ∈ oddPart → bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({fun x => match x with | B.G1 => 1 | x => 0, fun x => match x with | B.G2 => 1 | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  have hsmul_left : ∀ (r : ℝ) (u v : OSp12), bracket (r • u) v = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  have hsmul_right : ∀ (r : ℝ) (u v : OSp12), bracket u (r • v) = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro y hy
  rw [oddPart, hodd] at hy
  induction hy using Submodule.span_induction with
  | mem y hygen =>
      have hygen_b : ∃ b ∈ ({B.G1, B.G2} : Set B), y = Pi.single b (1 : ℝ) := by
        rcases hygen with rfl | rfl
        · exact ⟨B.G1, Or.inl rfl, rfl⟩
        · exact ⟨B.G2, Or.inr rfl, rfl⟩
      exact jacobi_odd_odd_z x y z hxgen hygen_b z (by simp)
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add u v hu hv huP hvP =>
      calc
        bracket x (bracket (u + v) z)
            = bracket x (bracket u z + bracket v z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = bracket x (bracket u z) + bracket x (bracket v z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket x u) z - bracket u (bracket x z)) +
              (bracket (bracket x v) z - bracket v (bracket x z)) := by simpa [add_comm, add_left_comm, add_assoc] using congrArg2 HAdd.hAdd huP hvP
        _ = bracket (bracket x (u + v)) z - bracket (u + v) (bracket x z) := by simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add]
  | smul r u hu huP =>
      calc
        bracket x (bracket (r • u) z)
            = bracket x (r • bracket u z) := by rw [hsmul_left]
        _ = r • bracket x (bracket u z) := by rw [hsmul_right]
        _ = r • (bracket (bracket x u) z - bracket u (bracket x z)) := by rw [huP]
        _ = bracket (bracket x (r • u)) z - bracket (r • u) (bracket x z) := by simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_sub, smul_add, add_comm, add_left_comm, add_assoc]

private theorem jacobi_odd_odd_proof :
    ∀ (x y z : OSp12), x ∈ oddPart → y ∈ oddPart → bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({fun x => match x with | B.G1 => 1 | x => 0, fun x => match x with | B.G2 => 1 | x => 0} : Set OSp12) =
          ({Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  have hsmul_left : ∀ (r : ℝ) (u v : OSp12), bracket (r • u) v = r • bracket u v := by
    intro r u v; ext k; simp [bracket, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum]
  intro x y z hx hy
  have hx2 := hx
  rw [oddPart, hodd] at hx2
  induction hx2 using Submodule.span_induction with
  | mem x hxgen =>
      have hxgen_a : ∃ a ∈ ({B.G1, B.G2} : Set B), x = Pi.single a (1 : ℝ) := by
        rcases hxgen with rfl | rfl
        · exact ⟨B.G1, Or.inl rfl, rfl⟩
        · exact ⟨B.G2, Or.inr rfl, rfl⟩
      exact jacobi_odd_odd_y x y z hxgen_a y hy
  | zero =>
      ext k <;> simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  | add u v hu hv huP hvP =>
      calc
        bracket (u + v) (bracket y z)
            = bracket u (bracket y z) + bracket v (bracket y z) := by ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul]
        _ = (bracket (bracket u y) z - bracket y (bracket u z)) +
              (bracket (bracket v y) z - bracket y (bracket v z)) := by rw [huP, hvP]
        _ = bracket (bracket (u + v) y) z - bracket y (bracket (u + v) z) := by ext k; simp [bracket, Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add]
  | smul r u hu huP =>
      calc
        bracket (r • u) (bracket y z)
            = r • bracket u (bracket y z) := by rw [hsmul_left]
        _ = r • (bracket (bracket u y) z - bracket y (bracket u z)) := by rw [huP]
        _ = bracket (bracket (r • u) y) z - bracket y (bracket (r • u) z) := by ext k; simp [bracket, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, mul_sub]

"""

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.writelines(pre_lines)
    f.writelines(mid_lines) # but I don't want mid_lines actually, since mid_lines has odd proofs.
    # Ah wait. I am replacing the entirety of the end of the file.
    f.write(new_lemmas)
    f.writelines(post_lines)

print("Done")
