import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Define the calc blocks for EVEN and ODD
calc_add_z_even = """      calc
        bracket x (bracket y (u + v)) = bracket x (bracket y u + bracket y v) := by rw [lie_add_proof y u v]
        _ = bracket x (bracket y u) + bracket x (bracket y v) := by rw [lie_add_proof x (bracket y u) (bracket y v)]
        _ = (bracket (bracket x y) u + bracket y (bracket x u)) + (bracket (bracket x y) v + bracket y (bracket x v)) := by rw [huP, hvP]
        _ = (bracket (bracket x y) u + bracket (bracket x y) v) + (bracket y (bracket x u) + bracket y (bracket x v)) := by abel
        _ = bracket (bracket x y) (u + v) + bracket y (bracket x (u + v)) := by rw [← lie_add_proof (bracket x y) u v, ← lie_add_proof x u v, ← lie_add_proof y (bracket x u) (bracket x v)]"""

calc_smul_z_even = """      calc
        bracket x (bracket y (r • u)) = bracket x (r • bracket y u) := by rw [lie_smul_proof r y u]
        _ = r • bracket x (bracket y u) := by rw [lie_smul_proof r x (bracket y u)]
        _ = r • (bracket (bracket x y) u + bracket y (bracket x u)) := by rw [huP]
        _ = r • bracket (bracket x y) u + r • bracket y (bracket x u) := by simp [smul_add]
        _ = bracket (bracket x y) (r • u) + bracket y (bracket x (r • u)) := by rw [← lie_smul_proof r (bracket x y) u, ← lie_smul_proof r x u, ← lie_smul_proof r y (bracket x u)]"""

calc_add_y_even = """      calc
        bracket x (bracket (u + v) z) = bracket x (bracket u z + bracket v z) := by rw [add_lie_proof u v z]
        _ = bracket x (bracket u z) + bracket x (bracket v z) := by rw [lie_add_proof x (bracket u z) (bracket v z)]
        _ = (bracket (bracket x u) z + bracket u (bracket x z)) + (bracket (bracket x v) z + bracket v (bracket x z)) := by rw [huP, hvP]
        _ = (bracket (bracket x u) z + bracket (bracket x v) z) + (bracket u (bracket x z) + bracket v (bracket x z)) := by abel
        _ = bracket (bracket x (u + v)) z + bracket (u + v) (bracket x z) := by rw [← lie_add_proof x u v, ← add_lie_proof (bracket x u) (bracket x v) z, ← add_lie_proof u v (bracket x z)]"""

calc_smul_y_even = """      calc
        bracket x (bracket (r • u) z) = bracket x (r • bracket u z) := by rw [smul_lie_proof r u z]
        _ = r • bracket x (bracket u z) := by rw [lie_smul_proof r x (bracket u z)]
        _ = r • (bracket (bracket x u) z + bracket u (bracket x z)) := by rw [huP]
        _ = r • bracket (bracket x u) z + r • bracket u (bracket x z) := by simp [smul_add]
        _ = bracket (bracket x (r • u)) z + bracket (r • u) (bracket x z) := by rw [← lie_smul_proof r x u, ← smul_lie_proof r (bracket x u) z, ← smul_lie_proof r u (bracket x z)]"""

calc_add_x_even = """      calc
        bracket (u + v) (bracket y z) = bracket u (bracket y z) + bracket v (bracket y z) := by rw [add_lie_proof u v (bracket y z)]
        _ = (bracket (bracket u y) z + bracket y (bracket u z)) + (bracket (bracket v y) z + bracket y (bracket v z)) := by rw [huP, hvP]
        _ = (bracket (bracket u y) z + bracket (bracket v y) z) + (bracket y (bracket u z) + bracket y (bracket v z)) := by abel
        _ = bracket (bracket (u + v) y) z + bracket y (bracket (u + v) z) := by rw [← add_lie_proof u v y, ← add_lie_proof (bracket u y) (bracket v y) z, ← add_lie_proof u v z, ← lie_add_proof y (bracket u z) (bracket v z)]"""

calc_smul_x_even = """      calc
        bracket (r • u) (bracket y z) = r • bracket u (bracket y z) := by rw [smul_lie_proof r u (bracket y z)]
        _ = r • (bracket (bracket u y) z + bracket y (bracket u z)) := by rw [huP]
        _ = r • bracket (bracket u y) z + r • bracket y (bracket u z) := by simp [smul_add]
        _ = bracket (bracket (r • u) y) z + bracket y (bracket (r • u) z) := by rw [← smul_lie_proof r u y, ← smul_lie_proof r (bracket u y) z, ← smul_lie_proof r u z, ← lie_smul_proof r y (bracket u z)]"""

calc_add_z_odd = calc_add_z_even.replace(" + bracket y", " - bracket y").replace(" + bracket u", " - bracket u").replace(" + bracket v", " - bracket v")
calc_smul_z_odd = calc_smul_z_even.replace(" + bracket y", " - bracket y").replace(" + bracket u", " - bracket u").replace("[smul_add]", "[smul_sub]").replace(" + r •", " - r •")
calc_add_y_odd = calc_add_y_even.replace(" + bracket u", " - bracket u").replace(" + bracket v", " - bracket v").replace(" + bracket (u", " - bracket (u")
calc_smul_y_odd = calc_smul_y_even.replace(" + bracket u", " - bracket u").replace(" + bracket (r", " - bracket (r").replace("[smul_add]", "[smul_sub]").replace(" + r •", " - r •")
calc_add_x_odd = calc_add_x_even.replace(" + bracket y", " - bracket y")
calc_smul_x_odd = calc_smul_x_even.replace(" + bracket y", " - bracket y").replace("[smul_add]", "[smul_sub]").replace(" + r •", " - r •")

# Basis proof replacement
basis_simp = "simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton, bracket, Pi.single, Function.update, structConst]; abel"

# Replace the giant instance definitions
def build_lemmas():
    code = ""
    # Even basis
    for b in ["H", "Ep", "Em"]:
        code += f"""private lemma jacobi_basis_even_{b} (b c : B) :
    bracket (Pi.single B.{b} (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.{b} (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) +
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.{b} (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  cases b <;> cases c <;> ext k <;> fin_cases k <;>
    {basis_simp}

"""
    # Even induction lemmas
    code += f"""private lemma jacobi_even_z (x y z : OSp12)
    (hxgen : ∃ a ∈ ({{B.H, B.Ep, B.Em}} : Set B), x = Pi.single a (1 : ℝ))
    (hygen : ∃ b : B, y = Pi.single b (1 : ℝ)) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hz_span : z ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rw [hspan]
    exact Submodule.mem_top
  induction hz_span using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with ⟨a, ha, rfl⟩
      rcases hygen with ⟨b, rfl⟩
      rcases hzgen with ⟨c, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact jacobi_basis_even_H b c
      · exact jacobi_basis_even_Ep b c
      · exact jacobi_basis_even_Em b c
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
{calc_add_z_even}
  | smul r u hu huP =>
{calc_smul_z_even}

"""
    code += f"""private lemma jacobi_even_y (x y z : OSp12)
    (hxgen : ∃ a ∈ ({{B.H, B.Ep, B.Em}} : Set B), x = Pi.single a (1 : ℝ)) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hy_span : y ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rw [hspan]
    exact Submodule.mem_top
  induction hy_span using Submodule.span_induction with
  | mem y hygen =>
      rcases hygen with ⟨b, rfl⟩
      exact jacobi_even_z x (Pi.single b 1) z hxgen ⟨b, rfl⟩
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
{calc_add_y_even}
  | smul r u hu huP =>
{calc_smul_y_even}

"""
    code += f"""private lemma jacobi_even_proof (x y z : OSp12) (hx : x ∈ evenPart) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
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
  have hx2 := hx
  rw [evenPart, heven] at hx2
  clear hx
  induction hx2 using Submodule.span_induction with
  | mem x hxgen =>
      have hxgen_a : ∃ a ∈ ({{B.H, B.Ep, B.Em}} : Set B), x = Pi.single a (1 : ℝ) := by
        rcases hxgen with rfl | rfl | rfl
        · exact ⟨B.H, Or.inl rfl, rfl⟩
        · exact ⟨B.Ep, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨B.Em, Or.inr (Or.inr rfl), rfl⟩
      exact jacobi_even_y x y z hxgen_a
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
{calc_add_x_even}
  | smul r u hu huP =>
{calc_smul_x_even}

"""

    # Odd basis
    for b in ["G1", "G2"]:
        code += f"""private lemma jacobi_basis_odd_{b} (b c : B) (hb : b ∈ ({{B.G1, B.G2}} : Set B)) :
    bracket (Pi.single B.{b} (1 : ℝ)) (bracket (Pi.single b (1 : ℝ)) (Pi.single c (1 : ℝ))) =
      bracket (bracket (Pi.single B.{b} (1 : ℝ)) (Pi.single b (1 : ℝ))) (Pi.single c (1 : ℝ)) -
      bracket (Pi.single b (1 : ℝ)) (bracket (Pi.single B.{b} (1 : ℝ)) (Pi.single c (1 : ℝ))) := by
  rcases hb with rfl | rfl <;> cases c <;> ext k <;> fin_cases k <;>
    {basis_simp}

"""
    # Odd induction lemmas
    code += f"""private lemma jacobi_odd_odd_z (x y z : OSp12)
    (hxgen : ∃ a ∈ ({{B.G1, B.G2}} : Set B), x = Pi.single a (1 : ℝ))
    (hygen : ∃ b ∈ ({{B.G1, B.G2}} : Set B), y = Pi.single b (1 : ℝ)) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  let S : Set OSp12 := Set.range (fun a : B => Pi.single a (1 : ℝ))
  have hz_span : z ∈ Submodule.span ℝ S := by
    have hrange : Set.range (fun a : B => Pi.single a (1 : ℝ)) = Set.range (Pi.basisFun ℝ B) := by
      ext v; constructor <;> rintro ⟨a, rfl⟩ <;> exact ⟨a, by simp [Pi.basisFun_apply]⟩
    have hspan : Submodule.span ℝ S = (⊤ : Submodule ℝ OSp12) := by
      rw [show S = Set.range (fun a : B => Pi.single a (1 : ℝ)) by rfl, hrange]
      exact (Pi.basisFun ℝ B).span_eq
    rw [hspan]
    exact Submodule.mem_top
  induction hz_span using Submodule.span_induction with
  | mem z hzgen =>
      rcases hxgen with ⟨a, ha, rfl⟩
      rcases hygen with ⟨b, hb, rfl⟩
      rcases hzgen with ⟨c, rfl⟩
      rcases ha with rfl | rfl
      · exact jacobi_basis_odd_G1 b c hb
      · exact jacobi_basis_odd_G2 b c hb
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
{calc_add_z_odd}
  | smul r u hu huP =>
{calc_smul_z_odd}

"""
    code += f"""private lemma jacobi_odd_odd_y (x y z : OSp12)
    (hxgen : ∃ a ∈ ({{B.G1, B.G2}} : Set B), x = Pi.single a (1 : ℝ)) :
    y ∈ oddPart → bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({{fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  intro hy
  have hy2 := hy
  rw [oddPart, hodd] at hy2
  clear hy
  induction hy2 using Submodule.span_induction with
  | mem y hygen =>
      have hygen_b : ∃ b ∈ ({{B.G1, B.G2}} : Set B), y = Pi.single b (1 : ℝ) := by
        rcases hygen with rfl | rfl
        · exact ⟨B.G1, Or.inl rfl, rfl⟩
        · exact ⟨B.G2, Or.inr rfl, rfl⟩
      exact jacobi_odd_odd_z x y z hxgen hygen_b
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
{calc_add_y_odd}
  | smul r u hu huP =>
{calc_smul_y_odd}

"""
    code += f"""private lemma jacobi_odd_odd_proof (x y z : OSp12) (hx : x ∈ oddPart) (hy : y ∈ oddPart) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  have hodd : ({{fun x => match x with | B.G1 => (1 : ℝ) | x => (0 : ℝ), fun x => match x with | B.G2 => (1 : ℝ) | x => (0 : ℝ)}} : Set OSp12) =
          ({{Pi.single B.G1 (1 : ℝ), Pi.single B.G2 (1 : ℝ)}} : Set OSp12) := by
    ext f; constructor
    · intro hf; rcases hf with rfl | rfl
      · left; ext x <;> cases x <;> simp
      · right; ext x <;> cases x <;> simp
    · intro hf; rcases hf with rfl | rfl
      · refine Or.inl ?_; ext x <;> cases x <;> simp
      · refine Or.inr ?_; ext x <;> cases x <;> simp
  have hx2 := hx
  rw [oddPart, hodd] at hx2
  clear hx
  induction hx2 using Submodule.span_induction with
  | mem x hxgen =>
      have hxgen_a : ∃ a ∈ ({{B.G1, B.G2}} : Set B), x = Pi.single a (1 : ℝ) := by
        rcases hxgen with rfl | rfl
        · exact ⟨B.G1, Or.inl rfl, rfl⟩
        · exact ⟨B.G2, Or.inr rfl, rfl⟩
      exact jacobi_odd_odd_y x y z hxgen_a hy
  | zero =>
      ext k; simp [bracket, SuperBracket.zero_lie, SuperBracket.lie_zero_left]
  | add u v hu hv huP hvP =>
{calc_add_x_odd}
  | smul r u hu huP =>
{calc_smul_x_odd}

"""
    return code

match_str = r"  jacobi_even :=\s*by.*?  jacobi_odd_odd :=\s*by.*?(?=\s*sup_even_odd|end OSp12)"
# Wait, let's use a simpler pattern, finding the start of the `instance : SuperLieRing OSp12` block.
start_idx = text.find("instance : SuperLieRing OSp12 where")
if start_idx == -1:
    print("Instance not found")
    exit(1)

new_text = text[:start_idx] + build_lemmas() + """instance : SuperLieRing OSp12 where
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

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(new_text)

print("Done")
