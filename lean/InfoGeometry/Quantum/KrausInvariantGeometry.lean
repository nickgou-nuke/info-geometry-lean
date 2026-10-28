/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KrausBoundaryDuality

/-!
# Geometry and order of invariant operator constraints

Invariant operators form intersections of native linear-map kernels in the
full matrix algebra. Adding Kraus constraints shrinks the solution submodule.
This is an order on actual operator constraints, not a physical causal order
or a convergence theorem for an iteration.
-/

noncomputable section
namespace InfoGeometry.Quantum.Choi

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Simultaneous backward-fixed operators, using the native submodule lattice. -/
def invariantOperators (S : Set (ι → Matrix n n ℂ)) : Submodule ℂ (Matrix n n ℂ) :=
  ⨅ V ∈ S, LinearMap.ker (krausMap (fun i => star (V i)) - LinearMap.id)

/-- Membership is conservation against every input and every specified map. -/
theorem mem_invariantOperators_iff (S : Set (ι → Matrix n n ℂ)) (E : Matrix n n ℂ) :
    E ∈ invariantOperators S ↔
      ∀ V ∈ S, ∀ X, trace (krausMap V X * E) = trace (X * E) := by
  simp only [invariantOperators, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, krausMap_conserved_iff]

/-- More operator constraints yield a smaller solution space. -/
theorem invariantOperators_antitone :
    Antitone (invariantOperators (n := n) (ι := ι)) := by
  intro S T hST E hE
  rw [mem_invariantOperators_iff] at hE ⊢
  exact fun V hV => hE V (hST hV)

/-- Combining constraints is intersection in the native submodule lattice. -/
theorem invariantOperators_union (S T : Set (ι → Matrix n n ℂ)) :
    invariantOperators (S ∪ T) = invariantOperators S ⊓ invariantOperators T := by
  ext E
  simp only [Submodule.mem_inf, mem_invariantOperators_iff, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun V hV => h V (Or.inl hV), fun V hV => h V (Or.inr hV)⟩
  · rintro ⟨hS, hT⟩ V (hV | hV)
    · exact hS V hV
    · exact hT V hV

/-- Simultaneous invariance extends to every word made from those maps. -/
theorem backwardWord_eq_of_mem_invariantOperators
    (S : Set (ι → Matrix n n ℂ)) {E : Matrix n n ℂ}
    (hE : E ∈ invariantOperators S) (word : List (ι → Matrix n n ℂ))
    (hword : ∀ V ∈ word, V ∈ S) : backwardWord word E = E := by
  induction word with
  | nil => rfl
  | cons V tail ih =>
      change krausMap (fun i => star (V i)) (backwardWord tail E) = E
      rw [ih (fun W hW => hword W (List.mem_cons_of_mem V hW))]
      exact (krausMap_conserved_iff V E).mp
        ((mem_invariantOperators_iff S E).mp hE V (hword V (List.mem_cons_self)))

end InfoGeometry.Quantum.Choi
