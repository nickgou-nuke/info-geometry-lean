/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# TKK–Clifford Five-Graded $D_5 \subset B_5$ Dimension & Grade-Reflection Laws

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Formalizes the 5-graded Tits–Kantor–Koecher (TKK) dimension profile of
    $\mathfrak{g}_{B_5} \cong \mathfrak{so}(6,5)$ ($\dim = 55$) extending the
    3-graded bivector core $\mathfrak{g}_{D_5} \cong \mathfrak{so}(5,5)$ ($\dim = 45$)
    by the two 5-dimensional vector grades $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ ($\dim = 10$).
- BUCKET 2 (Explicit Finite-Grade Carrier):
  * `tkkGradeDim : Fin 5 → ℕ` assigns dimensions `(5, 10, 25, 10, 5)` to grades `(-2, -1, 0, +1, +2)`.
  * `gradeFlip (i : Fin 5) : Fin 5 := ⟨4 - i.val, ...⟩` reverses the 5-grading.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `gradeFlip_involutive`: `gradeFlip (gradeFlip i) = i`.
  * `tkkGradeDim_gradeFlip_symm`: `tkkGradeDim (gradeFlip i) = tkkGradeDim i`.
  * `tkk_d5_three_graded_dim_sum`: `tkkGradeDim 1 + tkkGradeDim 2 + tkkGradeDim 3 = 45`.
  * `tkk_b5_five_graded_dim_sum`: total 5-graded dimension equals `55 = 45 + 10`.
-/

namespace InfoGeometry.GrandUnification

/-- Dimension profile `(5, 10, 25, 10, 5)` of the 5-graded TKK decomposition
    $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$
    indexed by `Fin 5`. -/
def tkkGradeDim : Fin 5 → ℕ
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 10
  | ⟨2, _⟩ => 25
  | ⟨3, _⟩ => 10
  | ⟨4, _⟩ => 5

/-- Grade-reversal involution on `Fin 5` mapping index `i` to `4 - i`. -/
def gradeFlip (i : Fin 5) : Fin 5 :=
  ⟨4 - i.val, by omega⟩

/-- Grade-reversal `gradeFlip` is an involution on `Fin 5`. -/
theorem gradeFlip_involutive (i : Fin 5) :
    gradeFlip (gradeFlip i) = i := by
  ext
  dsimp [gradeFlip]
  omega

/-- The 5-graded TKK dimension profile is symmetric under `gradeFlip`. -/
theorem tkkGradeDim_gradeFlip_symm (i : Fin 5) :
    tkkGradeDim (gradeFlip i) = tkkGradeDim i := by
  fin_cases i <;> decide

/-- The inner 3-graded $D_5$ bivector core $\mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1}$
    has dimension $10 + 25 + 10 = 45$. -/
theorem tkk_d5_three_graded_dim_sum :
    tkkGradeDim 1 + tkkGradeDim 2 + tkkGradeDim 3 = 45 ∧
    tkkGradeDim 0 + tkkGradeDim 4 = 10 := by
  refine ⟨?_, ?_⟩
  · dsimp [tkkGradeDim]
  · dsimp [tkkGradeDim]

/-- Adding the extreme vector grades $\mathfrak{g}_{-2} \oplus \mathfrak{g}_{+2}$ ($5 + 5 = 10$)
    to the 45-dimensional $D_5$ core completes the 55-dimensional 5-graded $B_5$ carrier. -/
theorem tkk_b5_five_graded_dim_sum :
    tkkGradeDim 0 + tkkGradeDim 1 + tkkGradeDim 2 + tkkGradeDim 3 + tkkGradeDim 4 = 55 ∧
    (tkkGradeDim 1 + tkkGradeDim 2 + tkkGradeDim 3) + (tkkGradeDim 0 + tkkGradeDim 4) = 55 := by
  refine ⟨?_, ?_⟩
  · dsimp [tkkGradeDim]
  · dsimp [tkkGradeDim]

end InfoGeometry.GrandUnification
