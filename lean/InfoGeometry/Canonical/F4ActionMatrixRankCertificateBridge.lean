import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge
import InfoGeometry.Algebra.SplitAlbertF4Classification
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornBasis

noncomputable section

namespace InfoGeometry.Canonical.F4ActionMatrix

/-! ### 1. Dimensions and Types -/

def dimAlbert : ℕ := 27
def dimEndAlbert : ℕ := 729
def dimF4 : ℕ := 52

theorem dimEndAlbert_eq : dimEndAlbert = 27 * 27 := by rfl

/-! ### 2. The 52-Derivation Action Matrix Interface -/

/-- Action matrix of the $i$-th $F_4$ derivation on the 27 Albert basis elements. -/
def f4BasisActionMatrix (i : Fin 52) : Matrix (Fin 27) (Fin 27) ℝ :=
  fun r c => f4BasisActionCoordinate i r c

/-! The same action matrix expressed through Mathlib's basis matrix API. -/
def f4BasisActionMatrixNative (i : Fin 52) : Matrix (Fin 27) (Fin 27) ℝ :=
  Matrix.transpose (h3ZornCoordinateBasis.toMatrix
    (fun r => (f4Basis i).1 (h3ZornCoordinateBasis r)))

theorem f4BasisActionMatrixNative_apply (i : Fin 52) (r c : Fin 27) :
    f4BasisActionMatrixNative i r c =
      (h3ZornCoordinateBasis.repr
        ((f4Basis i).1 (h3ZornCoordinateBasis r))) c := by
  simp [f4BasisActionMatrixNative, Module.Basis.toMatrix]

/-- **Theorem (Exact Readback Law via Certified Basis)**:
    $$A_i[r, c] = \operatorname{coord}_{B_V}(d_i(b_r))_c$$
-/
theorem f4BasisActionMatrix_readback (i : Fin 52) (r c : Fin 27) :
    f4BasisActionMatrix i r c = (h3ZornCoordinateBasis.repr ((f4Basis i).1 (h3ZornCoordinateBasis r))) c := by
  rw [h3ZornCoordinateBasis_apply]
  rw [h3ZornCoordinateBasis_repr_apply]
  rfl

theorem f4BasisActionMatrix_eq_native (i : Fin 52) :
    f4BasisActionMatrix i = f4BasisActionMatrixNative i := by
  ext r c
  rw [f4BasisActionMatrix_readback, f4BasisActionMatrixNative_apply]

/-- The canonical flattened $F_4$ action matrix $M \in \mathbb{R}^{52 \times 729}$. -/
def f4ActionMatrix : Matrix (Fin 52) (Fin 729) ℝ :=
  f4BasisActionCoordinateMatrix

/-- **Theorem (Flattened Row Readback)**:
    $$M[i, 27 r + c] = A_i[r, c]$$
-/
theorem f4BasisActionMatrix_flatten (i : Fin 52) (r c : Fin 27) :
    f4ActionMatrix i ⟨27 * r.val + c.val, by omega⟩ =
      f4BasisActionMatrix i r c := by
  dsimp [f4ActionMatrix, f4BasisActionMatrix]
  exact f4BasisActionCoordinateMatrix_apply i r c

/-! ### 3. Dimension and Span Bound -/

open Classical in
/-- **Theorem (Span Dimension Upper Bound 52)**:
    $$\dim_{\mathbb{R}} \operatorname{span} \{d_0, \dots, d_{51}\} \le 52$$
-/
theorem f4BasisSpan_finrank_le_52 :
    Module.finrank ℝ f4BasisSpan ≤ 52 := by
  have h_span : f4BasisSpan = Submodule.span ℝ (Set.range (fun i : Fin 52 => (f4Basis i).1)) := rfl
  rw [h_span]
  have h_eq : Set.range (fun i : Fin 52 => (f4Basis i).1) =
      (Finset.univ.image (fun i : Fin 52 => (f4Basis i).1) : Set (Module.End ℝ (H3Zorn ℝ))) := by
    ext x
    simp
  rw [h_eq]
  have h_le := finrank_span_finset_le_card (R := ℝ) (Finset.univ.image (fun i : Fin 52 => (f4Basis i).1))
  apply le_trans h_le
  have h_card : (Finset.univ.image (fun i : Fin 52 => (f4Basis i).1)).card ≤ 52 := by
    apply le_trans (Finset.card_image_le) (by simp)
  exact h_card

/-! ### 4. Explicit Closure Debt Statement -/

def f4_action_matrix_closure_debt : String :=
  "Open: evaluate the 37,908 rational action entries and prove rank(M) = 52 to certify exact linear independence of f4Basis."

/-! ### 5. Grand F₄ Action Matrix Synthesis -/

/-
🏆 **GRAND SYNTHESIS THEOREM: 52D $F_4$ Derivations on Certified 27D Albert Basis**
-/
/- theorem grand_f4_action_matrix_synthesis :
    -- 1. Dimensions: 27D Albert space, 729D endomorphism space, 52D F₄ algebra
    (dimAlbert = 27 ∧ dimEndAlbert = 729 ∧ dimF4 = 52) ∧
    -- 2. Certified Basis Readback Law
    (∀ (i : Fin 52) (r c : Fin 27),
      f4BasisActionMatrix i r c = (h3ZornCoordinateBasis.repr ((f4Basis i).1 (h3ZornCoordinateBasis r))) c) ∧
    -- 3. Row-Major Flattening to Action Matrix
    (∀ (i : Fin 52) (r c : Fin 27),
      f4ActionMatrix i ⟨27 * r.val + c.val, by omega⟩ = f4BasisActionMatrix i r c) ∧
    -- 4. Span Dimension Bound: dim span {d_i} ≤ 52
    (Module.finrank ℝ f4BasisSpan ≤ 52) := by
  refine ⟨⟨rfl, rfl, rfl⟩,
          f4BasisActionMatrix_readback,
          f4BasisActionMatrix_flatten,
          f4BasisSpan_finrank_le_52⟩ -/

end InfoGeometry.Canonical.F4ActionMatrix
