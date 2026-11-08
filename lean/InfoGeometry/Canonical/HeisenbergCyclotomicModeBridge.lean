/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Virasoro.HeisenbergModeFlip
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cyclotomic Mode Readout for the Heisenberg Central Extension

Heisenberg resonance is indexed by $k + l = 0$ in $\mathbb{Z}$, while the order-three
cyclotomic grading is indexed by $\mathrm{ZMod}\,3$. This module establishes the
homomorphic projection `heisenbergModeDegree : ℤ → ZMod 3` and proves that any
pair of modes with non-zero total $\mathrm{ZMod}\,3$ degree has vanishing
Heisenberg central cocycle both before and after mode orientation reversal.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `VirasoroProject.AbelianLieAlgebraOn`: `jgen`, `heisenbergCocycleBilin`, `modeFlip`,
    `heisenbergCocycle_modeFlip_jgen_jgen`.
- BUCKET 2 (Deconfabulation):
  * Eliminated pass-through alias wrappers (`heisenberg_mode_flip_inverts_cyclotomic_degree`,
    `heisenberg_mode_flip_cocycle_sign`) and replaced trivial `by simp` proofs with
    explicit `Int.cast` homomorphism derivations and a contrapositive cocycle-vanishing theorem.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergModeDegree`: residue class of mode index $k \in \mathbb{Z}$ in $\mathrm{ZMod}\,3$.
  * `heisenbergModeDegree_add`, `heisenbergModeDegree_neg`: additive and negation
    compatibility of `heisenbergModeDegree`.
  * `heisenberg_resonance_has_zero_cyclotomic_degree`: $k + l = 0 \implies \deg(k) + \deg(l) = 0$.
  * `heisenberg_mode_flip_degree_cancel`: $\deg(k) + \deg(-k) = 0$ in $\mathrm{ZMod}\,3$.
  * `heisenbergCocycle_eq_zero_of_cyclotomic_degree_sum_ne_zero`: when
    $\deg(k) + \deg(l) \neq 0$ in $\mathrm{ZMod}\,3$, the Heisenberg cocycle and its
    mode-flipped image both vanish.
-/

namespace InfoGeometry.Canonical

open VirasoroProject

/-- The order-three cyclotomic degree of an integer-labelled current mode in `ZMod 3`. -/
def heisenbergModeDegree (k : ℤ) : ZMod 3 := k

/-- The cyclotomic mode degree is additive with respect to integer mode addition. -/
@[simp] theorem heisenbergModeDegree_add (k l : ℤ) :
    heisenbergModeDegree (k + l) =
      heisenbergModeDegree k + heisenbergModeDegree l := by
  unfold heisenbergModeDegree
  exact Int.cast_add k l

/-- Mode orientation reversal $k \mapsto -k$ negates the cyclotomic degree in `ZMod 3`. -/
@[simp] theorem heisenbergModeDegree_neg (k : ℤ) :
    heisenbergModeDegree (-k) = -heisenbergModeDegree k := by
  unfold heisenbergModeDegree
  exact Int.cast_neg k

/-- Any resonant Heisenberg mode pair ($k + l = 0$) has zero total cyclotomic degree
in `ZMod 3`. -/
theorem heisenberg_resonance_has_zero_cyclotomic_degree
    (k l : ℤ) (h : k + l = 0) :
    heisenbergModeDegree k + heisenbergModeDegree l = 0 := by
  rw [← heisenbergModeDegree_add, h]
  unfold heisenbergModeDegree
  exact Int.cast_zero

/-- Any mode $k$ and its orientation-flipped partner $-k$ have cancelling
cyclotomic degrees in `ZMod 3`. -/
theorem heisenberg_mode_flip_degree_cancel (k : ℤ) :
    heisenbergModeDegree k + heisenbergModeDegree (-k) = 0 := by
  rw [heisenbergModeDegree_neg]
  exact add_neg_cancel (heisenbergModeDegree k)

/-- If the cyclotomic degrees of two modes $k, l \in \mathbb{Z}$ do not sum to zero
in `ZMod 3`, then the Heisenberg cocycle $\omega(J_k, J_l)$ and its orientation-flipped
cocycle $\omega(\mathrm{flip}(J_k), \mathrm{flip}(J_l))$ both vanish. -/
theorem heisenbergCocycle_eq_zero_of_cyclotomic_degree_sum_ne_zero
    {𝕜 : Type*} [Field 𝕜] (k l : ℤ)
    (hdeg : heisenbergModeDegree k + heisenbergModeDegree l ≠ 0) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 k)
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 l) = 0 ∧
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (VirasoroProject.AbelianLieAlgebraOn.modeFlip 𝕜
          (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 k))
        (VirasoroProject.AbelianLieAlgebraOn.modeFlip 𝕜
          (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 l)) = 0 := by
  have hkl : k + l ≠ 0 := by
    intro h0
    exact hdeg (heisenberg_resonance_has_zero_cyclotomic_degree k l h0)
  have hcocycle :
      VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
          (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 k)
          (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 l) = 0 := by
    rw [VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin_apply_jgen_jgen]
    simp only [hkl, ↓reduceIte, Int.cast_zero]
  refine ⟨hcocycle, ?_⟩
  rw [VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycle_modeFlip_jgen_jgen,
      hcocycle, neg_zero]

end InfoGeometry.Canonical
