import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

namespace InfoGeometry.Canonical.F4ActionMatrixRankCertificateCapstone

open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
open InfoGeometry.Algebra

/--
🏆 **CAPSTONE: Canonical Verification of the 52D F₄ Derivation Action on Certified 27D Albert Space**
Includes exact rational action certificate, 52 separating column pivots, matrix rank 52,
and linear independence over ℝ and ℚ.
-/
theorem f4_action_matrix_rank_canonical_capstone :
    -- 1. Dimensions: 27D Albert space, 729D endomorphism space, 52D F₄ algebra
    (dimAlbert = 27 ∧ dimEndAlbert = 729 ∧ dimF4 = 52) ∧
    -- 2. Certified Basis Readback Law
    (∀ (i : Fin 52) (r c : Fin 27),
      f4BasisActionMatrix i r c = (h3ZornCoordinateBasis.repr ((f4Basis i).1 (h3ZornCoordinateBasis r))) c) ∧
    -- 3. Row-Major Flattening to Action Matrix
    (∀ (i : Fin 52) (r c : Fin 27),
      f4ActionMatrix i ⟨27 * r.val + c.val, by omega⟩ = f4BasisActionMatrix i r c) ∧
    -- 4. Span Dimension Bound: dim span {d_i} ≤ 52
    (Module.finrank ℝ f4BasisSpan ≤ 52) ∧
    -- 5. Exact Rational Action Matrix Rank = 52
    (Matrix.rank f4ActionMatrixQ = 52) ∧
    -- 6. Exact Rational Linear Independence
    (LinearIndependent ℚ (fun i : Fin 52 => f4ActionMatrixQ i)) ∧
    -- 7. Exact Real Action Matrix Rank = 52
    (Matrix.rank f4ActionMatrixReal = 52) ∧
    -- 8. Exact Real Linear Independence
    (LinearIndependent ℝ (fun i : Fin 52 => f4ActionMatrixReal i)) ∧
    -- 9. Exact Real Action Span Dimension = 52
    (Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin 52 => f4ActionMatrixReal i))) = 52) := by
  refine ⟨⟨rfl, rfl, rfl⟩,
          f4BasisActionMatrix_readback,
          f4BasisActionMatrix_flatten,
          f4BasisSpan_finrank_le_52,
          f4ActionMatrixQ_rank,
          f4ActionMatrixQ_linearIndependent,
          f4ActionMatrixReal_rank,
          f4ActionMatrixReal_linearIndependent,
          finrank_f4ActionMatrixReal_span_eq_52⟩

end InfoGeometry.Canonical.F4ActionMatrixRankCertificateCapstone
