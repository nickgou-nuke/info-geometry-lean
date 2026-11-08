import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.MD004GeometricStructures

/-!
# Repaired MD 000 / `n000`: finite foundational matrix framework

Source note: `github-nick:nickgou-nuke/MD` at the fetched `main` HEAD does not
contain `000.md`; the closest available source files are `n000.md` and
`n000_condensate.md`.  This owner repairs the theorem-safe finite algebraic core
of `n000.md` (foundational matrix framework).

The source chapter states a broad foundational program: Pauli matrices,
normalized Pauli coordinates, determinant/Minkowski readout, trace/Euclidean
readout, quaternionic complex structures, Clifford/gamma matrices, curved
spacetime, tetrads, Bures/QFI, and Kähler-Einstein claims.  Existing owners
already prove the finite matrix spine:

* `MD001MatrixQuantumGeometry`: Pauli determinant/Minkowski and trace core;
* `MD002FoundationalConventions`: normalized Pauli conventions, Jordan/Lie
  products, quaternion complex-structure packet;
* `MD003IsomorphicRepresentations`: trace coordinate recovery, quaternion norm
  shadow, finite Fierz identity;
* `MD004GeometricStructures`: coordinate `I,J,K` relations, metric preservation,
  and finite skew-form shadows.

This file is a small audited bridge over those owners.  It does not assert the
full smooth manifold, Lorentz-cover, Clifford-bundle, tetrad, spin-connection,
Bures/QFI, Kähler-Einstein, or physical spacetime-identification claims.
-/

noncomputable section

namespace InfoGeometry.Physics.MD000FoundationalMatrixFramework

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.MD002FoundationalConventions
open InfoGeometry.Physics.MD003IsomorphicRepresentations
open InfoGeometry.Physics.MD004GeometricStructures

/-- Finite repaired `n000` Pauli determinant readout. -/
theorem md000_pauli_determinant_readout (dt dx dy dz : ℂ) :
    Matrix.det (pauliSpacetimeMatrix dt dx dy dz) =
      dt * dt - (dx * dx + dy * dy + dz * dz) :=
  pauliSpacetimeMatrix_det dt dx dy dz

/-- Finite repaired `n000` normalized interval convention. -/
theorem md000_normalized_interval
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    (-2 : ℂ) * Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
      -(dt * dt) + (dx * dx + dy * dy + dz * dz) :=
  normalized_interval_eq_minkowski_minus_plus_plus_plus c dt dx dy dz hc

/-- Finite repaired `n000` trace-coordinate recovery packet. -/
theorem md000_trace_coordinate_recovery
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedAxis c 0) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dt ∧
    traceForm (normalizedAxis c 1) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dx ∧
    traceForm (normalizedAxis c 2) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dy ∧
    traceForm (normalizedAxis c 3) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dz := by
  exact ⟨md003_trace_recover_time c dt dx dy dz hc,
    md003_trace_recover_x c dt dx dy dz hc,
    md003_trace_recover_y c dt dx dy dz hc,
    md003_trace_recover_z c dt dx dy dz hc⟩

/-- Finite repaired `n000` trace/quaternion Euclidean norm shadow. -/
theorem md000_trace_self_eq_quaternion_norm
    (c t x y z : ℂ) (hc : IsPauliNormalization c) :
    traceForm (normalizedPauliSpacetimeMatrix c t x y z)
        (normalizedPauliSpacetimeMatrix c t x y z) =
      quaternionNormSq t x y z :=
  md003_quaternion_norm_eq_trace_self c t x y z hc

/-- Finite repaired `n000` Jordan/Lie algebra conventions. -/
theorem md000_jordan_lie_packet (A B : MatrixQuantumCarrier) :
    jordanProduct A B = jordanProduct B A ∧
    lieProduct B A = - lieProduct A B :=
  ⟨jordanProduct_comm A B, lieProduct_antisymm A B⟩

/-- Finite repaired `n000` quaternionic complex-structure packet on coordinates. -/
theorem md000_coord_quaternion_packet (a b : Coord4) :
    I4 (I4 a) = neg4 a ∧
    J4 (J4 a) = neg4 a ∧
    K4 (K4 a) = neg4 a ∧
    I4 (J4 a) = K4 a ∧
    dot4 (I4 a) (I4 b) = dot4 a b ∧
    dot4 (J4 a) (J4 b) = dot4 a b ∧
    dot4 (K4 a) (K4 b) = dot4 a b ∧
    omegaI b a = - omegaI a b ∧
    omegaJ b a = - omegaJ a b ∧
    omegaK b a = - omegaK a b := by
  exact ⟨I4_sq a, J4_sq a, K4_sq a, I4_mul_J4 a,
    I4_preserves_dot4 a b, J4_preserves_dot4 a b, K4_preserves_dot4 a b,
    omegaI_skew a b, omegaJ_skew a b, omegaK_skew a b⟩

/-- Finite repaired `n000` ambient complex structure on `ℂ⁴ ≃ ℝ⁸`. -/
theorem md000_ambient_complex_packet (u v : Coord8) :
    J0 (J0 u) = neg8 u ∧
    dot8 (J0 u) (J0 v) = dot8 u v ∧
    omega0 v u = - omega0 u v :=
  ⟨J0_sq u, J0_preserves_dot8 u v, omega0_skew u v⟩

/-- Repaired theorem-safe `n000` finite foundational packet. -/
theorem repaired_MD000_foundational_matrix_packet
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c)
    (A B : MatrixQuantumCarrier) (a b : Coord4) (u v : Coord8) :
    Matrix.det (pauliSpacetimeMatrix dt dx dy dz) =
        dt * dt - (dx * dx + dy * dy + dz * dz) ∧
    (-2 : ℂ) * Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
        -(dt * dt) + (dx * dx + dy * dy + dz * dz) ∧
    traceForm (normalizedAxis c 0) (normalizedPauliSpacetimeMatrix c dt dx dy dz) = dt ∧
    traceForm (normalizedPauliSpacetimeMatrix c dt dx dy dz)
        (normalizedPauliSpacetimeMatrix c dt dx dy dz) = quaternionNormSq dt dx dy dz ∧
    jordanProduct A B = jordanProduct B A ∧
    lieProduct B A = - lieProduct A B ∧
    I4 (J4 a) = K4 a ∧
    dot4 (I4 a) (I4 b) = dot4 a b ∧
    J0 (J0 u) = neg8 u ∧
    omega0 v u = - omega0 u v := by
  exact ⟨md000_pauli_determinant_readout dt dx dy dz,
    md000_normalized_interval c dt dx dy dz hc,
    (md000_trace_coordinate_recovery c dt dx dy dz hc).1,
    md000_trace_self_eq_quaternion_norm c dt dx dy dz hc,
    jordanProduct_comm A B,
    lieProduct_antisymm A B,
    I4_mul_J4 a,
    I4_preserves_dot4 a b,
    J0_sq u,
    omega0_skew u v⟩

end InfoGeometry.Physics.MD000FoundationalMatrixFramework

end noncomputable section
