import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.HilbertCuntz

/-! ## 1. Binary boundary and fiber function space -/

/- The binary boundary modeled as infinite binary sequences. -/
/-- Prepend a bit to a binary boundary word. -/
def prefix_word (b : Fin 2) (w : ℕ → Fin 2) : ℕ → Fin 2
  | 0 => b
  | n + 1 => w n

/-- Head extraction to decompose any arbitrary binary word. -/
def head_word (w : ℕ → Fin 2) : Fin 2 := w 0

/-- Tail extraction to recover the shifted sequence. -/
def tail_word (w : ℕ → Fin 2) : ℕ → Fin 2 := fun n => w (n + 1)

/-- Any binary word is definitionally equal to its head prepended to its tail. -/
theorem eta_word (w : ℕ → Fin 2) : w = prefix_word (head_word w) (tail_word w) := by
  apply funext; intro i
  cases i <;> rfl

/-- The internal Fiber space: ℝ² with its standard Euclidean norm. -/
abbrev Fiber := EuclideanSpace ℝ (Fin 2)

/-- The explicit function carrier on the binary boundary and real fiber.
    This definition is not an `lp` or Hilbert-space completion. -/
abbrev H := (ℕ → Fin 2) → Fiber

/-! ## 2. Algebraic branch actions -/

/-- A continuous fiber map acts pointwise on the boundary function carrier. -/
def K_op (J0 : Fiber →L[ℝ] Fiber) : H → H := fun f w => J0 (f w)

theorem K_op_apply (J0 : Fiber →L[ℝ] Fiber) (f : H) (w : ℕ → Fin 2) :
    K_op J0 f w = J0 (f w) := rfl

/-- The left binary branch pullback on the explicit function carrier. -/
def S_left : H → H := fun f w =>
  if head_word w = 0 then f (tail_word w) else 0

theorem S_left_apply_zero (f : H) (w : ℕ → Fin 2) : S_left f (prefix_word 0 w) = f w := rfl

theorem S_left_apply_one  (f : H) (w : ℕ → Fin 2) : S_left f (prefix_word 1 w) = 0 := rfl

/-! ## 3. Exact branch/fiber commutation -/

/--
THEOREM: the left branch pullback and the pointwise fiber map commute.

The branch pullback on the Cantor boundary does not interfere with an arbitrary
continuous fiber map acting pointwise. They act on separate degrees
of freedom:

  S_left acts on the base (binary boundary indexing)
  K acts on the fiber (ℝ² at each word)

Proof by case analysis on the binary head:
  Case 0: the active binary branch — the pullback shifts and K acts on fiber.
  Case 1: the other branch — the pullback is zero and K maps zero to zero.
-/
theorem branchPullback_K_commute_global (J0 : Fiber →L[ℝ] Fiber) (f : H)
    (w : ℕ → Fin 2) :
    S_left (K_op J0 f) w = K_op J0 (S_left f) w := by
  -- Decompose the arbitrary boundary point into its branch prefix
  rw [eta_word w]
  generalize h_tail : tail_word w = tw
  by_cases h : head_word w = 0
  · -- Case 0: the active binary branch
    rw [h] at *
    calc
      S_left (K_op J0 f) (prefix_word 0 tw) = (K_op J0 f) tw                     := by rw [S_left_apply_zero]
      _                                  = J0 (f tw)                       := by rw [K_op_apply]
      _                                  = J0 (S_left f (prefix_word 0 tw)) := by rw [S_left_apply_zero]
      _                                  = K_op J0 (S_left f) (prefix_word 0 tw) := by rw [K_op_apply]
  · -- Case 1: the other binary branch (head_word w = 1)
    have h1 : head_word w = 1 := by
      have h0_or_1 : head_word w = 0 ∨ head_word w = 1 := by
        have all : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
        have mem : head_word w ∈ (Finset.univ : Finset (Fin 2)) := Finset.mem_univ _
        simpa [all] using mem
      rcases h0_or_1 with (h0 | h1)
      · exact absurd h0 h
      · exact h1
    rw [h1] at *
    calc
      S_left (K_op J0 f) (prefix_word 1 tw) = 0                               := by rw [S_left_apply_one]
      _                                  = J0 0                            := by rw [map_zero]
      _                                  = J0 (S_left f (prefix_word 1 tw)) := by rw [S_left_apply_one]
      _                                  = K_op J0 (S_left f) (prefix_word 1 tw) := by rw [K_op_apply]

end InfoGeometry.Canonical.HilbertCuntz
