import proofs.BraidProject.Grids
import proofs.BraidProject.Reversing

inductive cell : FreeMonoid' ℕ → FreeMonoid' ℕ → FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | empty : (cell 1 1 1 1 : Prop)
  | top_bottom (i : ℕ) : cell 1 (FreeMonoid'.of i) 1 (FreeMonoid'.of i)
  | sides (i : ℕ) : cell (FreeMonoid'.of i) 1 (FreeMonoid'.of i) 1
  | top_left (i : ℕ) : cell (FreeMonoid'.of i) (FreeMonoid'.of i) 1 1
  | adjacent (i k : ℕ) (h : Nat.dist i k = 1) : cell (FreeMonoid'.of i) (FreeMonoid'.of k)
      (FreeMonoid'.of i * FreeMonoid'.of k) (FreeMonoid'.of k * FreeMonoid'.of i)
  | separated (i j : ℕ) (h : i +2 ≤ j ∨ j+2 <= i) : cell (FreeMonoid'.of i) (FreeMonoid'.of j)
      (FreeMonoid'.of i) (FreeMonoid'.of j)

theorem grid_from_cell (h : cell a b c d) : grid a b c d := by
  induction h with
  | empty => exact grid.empty
  | top_bottom i => exact grid.top_bottom _
  | sides i => exact grid.sides _
  | top_left i => exact grid.top_left _
  | adjacent i k h => exact grid.adjacent _ _ h
  | separated i j h => exact grid.separated _ _ h

def to_up (a : FreeMonoid' ℕ) : FreeMonoid' (Option ℕ × Bool) := FreeMonoid'.map
  (fun x => (some x, false)) a

def to_over (a : FreeMonoid' ℕ) : FreeMonoid' (Option ℕ × Bool) := FreeMonoid'.map
  (fun x => (some x, true)) a

def remover : (a : FreeMonoid' (Option ℕ × Bool)) → FreeMonoid' ℕ
  | 1 => 1
  | (some a, _) :: c => a :: remover c
  | (none, _) :: c => remover c

def grid_option (a b c d : FreeMonoid' (Option ℕ × Bool)) : Prop := grid (remover a) (remover b)
  (remover c) (remover d)

/-- A partial grid generalizes the notion of a grid to include "unfinished" grids. -/
inductive PartialGrid : FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) →
  FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ × Bool) → Prop
  | single_grid {a b c d : FreeMonoid' ℕ} (h : grid a b c d):
      PartialGrid (to_up a) (to_over b) (to_over d) 1 (to_up c)
  | empty (a b : FreeMonoid' ℕ) :
      PartialGrid (to_up a) (to_over b) 1 ((to_up a) * (to_over b)) 1
  | horizontal_append_one {a b bot up b2 bot2 mid2 up2} (g1 : grid_option a b up bot)
      (g2 : PartialGrid up b2 bot2 mid2 up2) : PartialGrid a (b*b2) (bot * bot2) mid2 up2
  | horizontal_append {a b bot mid up b2 bot2 mid2 up2 : FreeMonoid' (Option ℕ × Bool)}
      (g1 : PartialGrid a b bot mid up) (g2 : PartialGrid up b2 bot2 mid2 up2) :
      PartialGrid a (b*b2) bot (mid * bot2 * mid2) up2

def frontier2 (_pg : PartialGrid a b c d e) : FreeMonoid' (Option ℕ × Bool) := c * d * e

inductive pgrid : FreeMonoid' (Option ℕ) → FreeMonoid' (Option ℕ) → FreeMonoid' (Option ℕ) →
    FreeMonoid' (Option ℕ × Bool) → FreeMonoid' (Option ℕ) →  Prop
  | spine (a b : FreeMonoid' (Option ℕ)): pgrid a b 1 (((FreeMonoid'.map fun x => (x, false)) a) *
      ((FreeMonoid'.map fun x => (x, true)) b)) 1
  | cell {a b c d} (h : cell a b c d) : pgrid ((FreeMonoid'.map fun x => some x) a)
      ((FreeMonoid'.map fun x => some x) b) ((FreeMonoid'.map fun x => some x) c.reverse) 1
      ((FreeMonoid'.map fun x => some x) d)
  | horizontal_L (h1 : pgrid a b c 1 e) (h2 : pgrid e f g h i) : pgrid a (b * f) (c * g) h i
  | horizontal (h1 : pgrid a b c d e) (h2 : pgrid e f g h i) : pgrid a (b * f) c
      (d * (FreeMonoid'.map (fun x => (x, true)) g) * h) i
  | vertical_L (h1 : pgrid a b c 1 e) (h2 : pgrid f c g h i) : pgrid (a * f) b g h (i * e)
  | vertical (h1 : pgrid a b c d e) (h2 : pgrid f c g h i) : pgrid a (b * f) c
      (d * (FreeMonoid'.map (fun x => (x, true)) g) * h) i

open FreeMonoid'

theorem remover_to_up (a : FreeMonoid' ℕ) : remover (to_up a) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      simp [to_up, remover]
      change remover (to_up xs) = xs
      exact ih

theorem remover_to_over (a : FreeMonoid' ℕ) : remover (to_over a) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      simp [to_over, remover]
      change remover (to_over xs) = xs
      exact ih

theorem grid_option_of_grid (h : grid a b c d) :
    grid_option (to_up a) (to_over b) (to_up c) (to_over d) := by
  simpa [grid_option, remover_to_up, remover_to_over] using h

theorem PartialGrid.single_grid_frontier {a b c d : FreeMonoid' ℕ} (h : grid a b c d) :
    frontier2 (PartialGrid.single_grid h) = to_over d * to_up c := by
  simp [frontier2]

theorem PartialGrid.empty_frontier (a b : FreeMonoid' ℕ) :
    frontier2 (PartialGrid.empty a b) = to_up a * to_over b := by
  simp [frontier2]

def eraseOption : FreeMonoid' (Option ℕ) → FreeMonoid' ℕ
  | 1 => 1
  | some a :: xs => a :: eraseOption xs
  | none :: xs => eraseOption xs

theorem eraseOption_map_some (a : FreeMonoid' ℕ) :
    eraseOption (FreeMonoid'.map (fun x => some x) a) = a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      simp [eraseOption]
      change eraseOption (FreeMonoid'.map (fun x => some x) xs) = xs
      exact ih

theorem cell_erases_to_grid {a b c d : FreeMonoid' ℕ} (h : cell a b c d) :
    grid (eraseOption (FreeMonoid'.map (fun x => some x) a))
      (eraseOption (FreeMonoid'.map (fun x => some x) b))
      (eraseOption (FreeMonoid'.map (fun x => some x) c))
      (eraseOption (FreeMonoid'.map (fun x => some x) d)) := by
  repeat rw [eraseOption_map_some]
  exact grid_from_cell h
