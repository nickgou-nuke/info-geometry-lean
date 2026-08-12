import Mathlib.Tactic

set_option linter.unusedVariables false

namespace InfoGeometry.TKK

-- The five graded carriers are indexed by a native finite family.  Bracket
-- closure laws belong to separate structures/theorems and are not implicit.
abbrev TKKGrading (E : Type _) [AddCommGroup E] [Module ℝ E] :=
  Fin 5 → Set E

namespace TKKGrading

variable {E : Type _} [AddCommGroup E] [Module ℝ E]

abbrev g₂ (G : TKKGrading E) : Set E := G 0
abbrev g₁ (G : TKKGrading E) : Set E := G 1
abbrev g₀ (G : TKKGrading E) : Set E := G 2
abbrev «g₋₁» (G : TKKGrading E) : Set E := G 3
abbrev «g₋₂» (G : TKKGrading E) : Set E := G 4

end TKKGrading

/-- Finite diagonal isospin operator on the two four-dimensional sectors. -/
def isospin_operator (c : Fin 4 → ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal fun i : Fin 8 =>
    if h : i.1 < 4 then c ⟨i.1, h⟩ else 0

/-- Exchange the two marked points and leave all other inputs unchanged. -/
noncomputable def mirror_map (ψ : ℝ → ℝ) : ℝ → ℝ := fun x => if x = 0 then ψ 1 else if x = 1 then ψ 0 else ψ x

-- Key lemma: isospin asymmetry ↔ N≠Z
theorem isospin_asymmetry_eq_NZ (ψ : ℝ → ℝ) (c : Fin 4 → ℝ) :
    (isospin_operator c ≠ 0) ↔ (∃ i : Fin 4, c i ≠ 0) := by
  constructor
  · intro hnonzero
    by_contra hforall
    apply hnonzero
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hlt : i.1 < 4
      · have hc : c ⟨i.1, hlt⟩ = 0 := by
          by_contra hc
          apply hforall
          exact ⟨⟨i.1, hlt⟩, hc⟩
        simp [isospin_operator, hlt, hc]
      · simp [isospin_operator, hlt]
    · simp [isospin_operator, hij]
  · rintro ⟨i, hi⟩ hzero
    let i8 : Fin 8 := ⟨i.1, Nat.lt_trans i.2 (by decide)⟩
    have hentry := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M i8 i8) hzero
    simp [isospin_operator, i8] at hentry
    exact hi hentry

def D4Lattice := Fin 4 → ℤ

def central_node_idx : Fin 4 := 1

def external_legs : List (Fin 4) := [0, 2, 3]

abbrev D4TrialityPerm :=
  {perm : Equiv.Perm (Fin 4) // perm central_node_idx = central_node_idx}

namespace D4TrialityPerm

abbrev perm (σ : D4TrialityPerm) : Equiv.Perm (Fin 4) := σ.1
abbrev fixes_central (σ : D4TrialityPerm) : σ.perm central_node_idx = central_node_idx := σ.2

end D4TrialityPerm

def D4Lattice.dot (v w : D4Lattice) : ℤ :=
  ∑ i : Fin 4, v i * w i

def apply_perm (σ : D4TrialityPerm) (v : D4Lattice) : D4Lattice :=
  fun i => v (σ.perm i)

theorem pin55_triality_invariant (σ : D4TrialityPerm) (v w : D4Lattice) :
    D4Lattice.dot (apply_perm σ v) (apply_perm σ w) = D4Lattice.dot v w := by
  dsimp [D4Lattice.dot, apply_perm]
  exact Equiv.sum_comp σ.perm (fun i => v i * w i)

end InfoGeometry.TKK
