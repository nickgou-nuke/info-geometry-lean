import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite root-of-unity averaging operator keeps exactly the `k`-multiple frequencies. -/
def abel_hardy_projection_tower_reverse_martingale_projection
    (k : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if k ∣ n then f n else 0

/-- The explicit tower `f, E_k f, E_k^2 f, ...`. -/
def abel_hardy_projection_tower_reverse_martingale_towerModel
    (k : ℕ) (m : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  Nat.rec f
    (fun _ g => abel_hardy_projection_tower_reverse_martingale_projection k g) m

/-- The first tower step is the root-of-unity projection of the boundary data. -/
def boundaryProjectionFormula (k : ℕ) (boundary : ℕ → ℂ) (tower : ℕ → ℕ → ℂ) : Prop :=
  tower 1 = abel_hardy_projection_tower_reverse_martingale_projection k boundary

/-- Successive tower levels satisfy the reverse-martingale recursion. -/
def reverseMartingaleFormula (k : ℕ) (boundary : ℕ → ℂ) (tower : ℕ → ℕ → ℂ) : Prop :=
  ∀ m : ℕ,
    tower (m + 1) =
      abel_hardy_projection_tower_reverse_martingale_projection k (tower m)

/-- Paper label: `thm:abel-hardy-projection-tower-reverse-martingale`. Modeling the root-of-unity
average as the projection onto the `k`-multiple Fourier modes makes the boundary-value identity
the first iterate of the projection, and the full tower recursion is then obtained by iterating
that same operator. -/
theorem paper_abel_hardy_projection_tower_reverse_martingale
    (k : ℕ) (boundary : ℕ → ℂ) (tower : ℕ → ℕ → ℂ)
    (hk : 2 ≤ k)
    (tower_closed_form :
      ∀ m : ℕ,
        tower m = abel_hardy_projection_tower_reverse_martingale_towerModel k m boundary) :
    boundaryProjectionFormula k boundary tower ∧ reverseMartingaleFormula k boundary tower := by
  refine ⟨?_, ?_⟩
  · simpa [boundaryProjectionFormula] using tower_closed_form 1
  · intro m
    calc
      tower (m + 1)
          =
            abel_hardy_projection_tower_reverse_martingale_towerModel k (m + 1) boundary := by
                simpa using tower_closed_form (m + 1)
      _ = abel_hardy_projection_tower_reverse_martingale_projection k
            (abel_hardy_projection_tower_reverse_martingale_towerModel k m boundary) := by
                simp [abel_hardy_projection_tower_reverse_martingale_towerModel]
      _ = abel_hardy_projection_tower_reverse_martingale_projection k (tower m) := by
            rw [tower_closed_form m]

end Omega.Zeta
