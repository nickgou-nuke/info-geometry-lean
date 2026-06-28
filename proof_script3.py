import subprocess

LEAN_FILE = "lean/InfoGeometry/JordanDecomposition/Scratch.lean"

code = """import Mathlib

noncomputable section

open FiniteDimensional
open Submodule

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def NilpotentIndex (N : Module.End K V) (k : ℕ) : Prop :=
  (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

lemma linearIndependent_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndex N k) (x : V) (hx : (N ^ (k - 1)) x ≠ 0) :
    LinearIndependent K (fun (i : Fin k) => (N ^ (i : ℕ)) x) := by
  sorry

theorem nilpotent_split_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndex N k) (hk_pos : 1 ≤ k) :
    ∃ (x : V) (W : Submodule K V),
      (∀ y ∈ W, N y ∈ W) ∧
      (⊤ : Submodule K V) = span K { (N ^ i) x | i ≤ k-1 } ⊔ W ∧
      Disjoint (span K { (N ^ i) x | i ≤ k-1 }) W := by
  have hk_prev : N ^ (k - 1) ≠ 0 := hN.right
  have h_exists_x : ∃ x, (N ^ (k - 1)) x ≠ 0 := by
    contrapose! hk_prev; ext x; exact hk_prev x
  rcases h_exists_x with ⟨x, hx⟩
  
  have h_indep : LinearIndependent K (fun (i : Fin k) => (N ^ (i : ℕ)) x) :=
    linearIndependent_cyclic N k hN x hx
  
  -- Extend to a basis of V
  let B := Basis.extend h_indep
  
  -- The coordinate corresponding to N^{k-1} x is exactly at index ⟨k-1, ...⟩
  -- In Basis.extend, the index type is Sum (Fin k) _
  have hk1 : k - 1 < k := Nat.sub_lt_self hk_pos (by decide)
  let idx : Sum (Fin k) (B.State) := Sum.inl ⟨k - 1, hk1⟩
  let F : V →ₗ[K] K := B.coord idx
  
  -- define pi
  let pi : V →ₗ[K] V := ∑ i : Fin k, (LinearMap.smulRight (F.comp (N ^ (k - 1 - (i : ℕ)))) ((N ^ (i : ℕ)) x))
  
  -- Let W be ker pi
  let W := LinearMap.ker pi
  
  use x, W
  sorry
"""

with open("/home/goutev/repos/info-geometry-lean/" + LEAN_FILE, "w") as f:
    f.write(code)

result = subprocess.run(["lake", "env", "lean", "--run", LEAN_FILE], cwd="/home/goutev/repos/info-geometry-lean", capture_output=True, text=True)
print(result.stdout + result.stderr)
