import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
import InfoGeometry.Algebra.BaezF4H3Zorn

namespace InfoGeometry.Canonical.F4ActionMatrixRankCertificateCapstone

open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
open InfoGeometry.Algebra
open InfoGeometry.Algebra.F4Classification

theorem f4_action_matrix_rank_canonical_capstone :
    (dimAlbert = 27 ∧ dimEndAlbert = 729 ∧ dimF4 = 52) ∧
    (∀ (i : Fin 52) (r c : Fin 27),
      f4BasisActionMatrix i r c =
        (h3ZornCoordinateBasis.repr ((f4Basis i).1 (h3ZornCoordinateBasis r))) c) ∧
    (∀ (i : Fin 52) (r c : Fin 27),
      f4ActionMatrix i ⟨27 * r.val + c.val, by omega⟩ = f4BasisActionMatrix i r c) ∧
    (Module.finrank ℝ f4BasisSpan ≤ 52) ∧
    (Matrix.rank f4ActionMatrixQ = 52) ∧
    (LinearIndependent ℚ (fun i : Fin 52 => f4ActionMatrixQ i)) ∧
    (Matrix.rank f4ActionMatrixReal = 52) ∧
    (LinearIndependent ℝ (fun i : Fin 52 => f4ActionMatrixReal i)) ∧
    (Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin 52 => f4ActionMatrixReal i))) = 52) := by
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
