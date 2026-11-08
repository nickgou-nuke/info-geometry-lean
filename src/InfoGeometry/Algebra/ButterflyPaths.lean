/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixDisplacement
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Finite ordered paths through two-route stages

Each stage offers a stationary weighted route and a translated weighted route.
The native list enumeration retains both choices, including multiplicities
when their data coincide. Expanding the product gives a sum over these ordered
paths. The existing displacement-word theorem evaluates each path with the
rightmost matrix acting first and retains noncommutative coefficient order.

These are exact finite identities; no assertion of nonzero entries, universal
factorization, or an evaluation complexity bound is made.
-/

namespace InfoGeometry.Algebra.ButterflyPaths

open InfoGeometry.Algebra.MatrixDisplacement

variable {G R : Type*}

section Choices

variable [Zero G]

/-- `false` selects the stationary route; `true` selects the translated route. -/
def branch (stage : G × (G → R) × (G → R)) : Bool → G × (G → R)
  | false => (0, stage.2.1)
  | true => (stage.1, stage.2.2)

/-- All branch words, in the same order as the matrix factors. -/
def paths : List (G × (G → R) × (G → R)) → List (List (G × (G → R)))
  | [] => [[]]
  | stage :: stages =>
      (paths stages).map (fun w => branch stage false :: w) ++
        (paths stages).map (fun w => branch stage true :: w)

/-- Count branch choices with multiplicity, including the empty path. -/
theorem length_paths (stages : List (G × (G → R) × (G → R))) :
    (paths stages).length = 2 ^ stages.length := by
  induction stages with
  | nil => simp [paths]
  | cons stage stages ih => simp [paths, ih, pow_succ, Nat.mul_two]

theorem length_of_mem_paths {stages : List (G × (G → R) × (G → R))}
    {w : List (G × (G → R))} (hw : w ∈ paths stages) : w.length = stages.length := by
  induction stages generalizing w with
  | nil =>
      have he : w = [] := by simpa only [paths, List.mem_singleton] using hw
      simp only [he, List.length_nil]
  | cons stage stages ih =>
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_map.mp hw with ⟨v, hv, rfl⟩
        simp only [List.length_cons, ih hv]
      · rcases List.mem_map.mp hw with ⟨v, hv, rfl⟩
        simp only [List.length_cons, ih hv]

end Choices

variable [AddCommGroup G] [DecidableEq G] [Fintype G] [Ring R]

/-- Distributivity expands an ordered stage product into ordered route products. -/
theorem prod_bitStep_eq_sum_route_products
    (stages : List (G × (G → R) × (G → R))) :
    (stages.map (fun s => bitStep s.1 s.2.1 s.2.2)).prod =
      ((paths stages).map (fun w =>
        (w.map (fun s => weightedShift s.1 s.2)).prod)).sum := by
  induction stages with
  | nil => simp [paths]
  | cons stage stages ih =>
      simp only [List.map_cons, List.prod_cons, paths, List.map_append,
        List.sum_append, List.map_map, Function.comp_def]
      rw [ih]
      simp only [List.sum_map_mul_left, branch, bitStep, add_mul]

/-- Each expanded path is evaluated by the existing translated-weight recursion. -/
theorem prod_bitStep_eq_sum_weightedShift
    (stages : List (G × (G → R) × (G → R))) :
    (stages.map (fun s => bitStep s.1 s.2.1 s.2.2)).prod =
      ((paths stages).map (fun w =>
        weightedShift (wordDisplacement w) (wordWeight w))).sum := by
  simpa only [prod_weightedShift] using prod_bitStep_eq_sum_route_products stages

end InfoGeometry.Algebra.ButterflyPaths
