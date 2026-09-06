/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SchurDecomposition

/-- Canonical projection capstone for the Schur triangularization packet. -/
theorem schur_decomposition_canonical_capstone
    (K : Type*) [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K)
    (hB : UpperTriangular B) :
    let S := SchurDecompositionPacket.ofUpperTriangular K B hB
    -- 1. Exact similarity factorization: A = P * B * Q
    (S.A = S.P * S.B * S.Q) ∧
    -- 2. Left and right inverse relations
    (S.P * S.Q = 1 ∧ S.Q * S.P = 1) ∧
    -- 3. Upper triangularity
    UpperTriangular S.B ∧
    -- 4. Diagonal readout
    (diagList S.B = S.eigenvalues) ∧
    -- 5. Characteristic polynomial factorization
    (S.B.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (S.B i i))) := by
  intro S
  exact ⟨
    S.factorization,
    ⟨S.P_mul_Q, S.Q_mul_P⟩,
    S.upper_triangular,
    S.diag_eq,
    S.charpoly_schurUpperTriangular
  ⟩

end InfoGeometry.Canonical
