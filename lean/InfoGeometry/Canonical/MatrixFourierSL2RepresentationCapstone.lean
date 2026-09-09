import InfoGeometry.Quantum.MatrixFourierSL2Representation

namespace InfoGeometry.Canonical.MatrixFourierSL2RepresentationCapstone

open InfoGeometry.Quantum.MatrixFourierSL2Representation

theorem capstone_matrix_fourier_sl2_synthesis :
    (fourierMatrix5 ^ 5 = fourierMatrix5) ∧
    (P_vac5 + P_sym5 + P_anti5 = 1) ∧
    (P_sym5 * P_anti5 = 0) ∧
    (commutator sl2_h sl2_e = (2 : ℂ) • sl2_e) ∧
    (commutator sl2_h sl2_f = -((2 : ℂ) • sl2_f)) ∧
    (commutator sl2_e sl2_f = sl2_h) ∧
    (sl2_casimir = (3 / 2 : ℂ) • 1) ∧
    (commutator sl2_casimir sl2_e = 0) :=
    ⟨fourierMatrix5_quintic,
      fourier5_projector_completeness,
      fourier5_projector_orthogonality,
      sl2_comm_h_e,
      sl2_comm_h_f,
      sl2_comm_e_f,
      sl2_casimir_scalar,
      sl2_casimir_comm_e⟩

end InfoGeometry.Canonical.MatrixFourierSL2RepresentationCapstone
