import InfoGeometry.Core.PeirceDecomposition

namespace InfoGeometry.QuantumContext.MassAsCommutantCoupling

open InfoGeometry.Core.PeirceDecomposition

section Ring

variable {Carrier : Type*} [Ring Carrier]

def grading (projection : Carrier) : Carrier :=
  projection - complementIdempotent projection

theorem swap_complement (projection coupling : Carrier)
    (swap : projection * coupling = coupling * complementIdempotent projection) :
    complementIdempotent projection * coupling = coupling * projection := by
  unfold complementIdempotent at *
  calc
    (1 - projection) * coupling = coupling - projection * coupling := by noncomm_ring
    _ = coupling - coupling * (1 - projection) := by rw [swap]
    _ = coupling * projection := by noncomm_ring

theorem diagonal_corner_zero (projection coupling : Carrier)
    (idempotent : IsIdempotentElem projection)
    (swap : projection * coupling = coupling * complementIdempotent projection) :
    projection * coupling * projection = 0 := by
  rw [swap, mul_assoc, complement_mul_idempotent projection idempotent.eq, mul_zero]

theorem complement_corner_zero (projection coupling : Carrier)
    (idempotent : IsIdempotentElem projection)
    (swap : projection * coupling = coupling * complementIdempotent projection) :
    complementIdempotent projection * coupling * complementIdempotent projection = 0 := by
  rw [swap_complement projection coupling swap, mul_assoc,
    idempotent_mul_complement projection idempotent.eq, mul_zero]

theorem grading_anticommutes (projection coupling : Carrier)
    (swap : projection * coupling = coupling * complementIdempotent projection) :
    grading projection * coupling + coupling * grading projection = 0 := by
  unfold grading
  rw [sub_mul, mul_sub, swap, swap_complement projection coupling swap]
  abel

theorem grading_square (projection : Carrier) (idempotent : IsIdempotentElem projection) :
    grading projection * grading projection = 1 := by
  unfold grading
  calc
    (projection - complementIdempotent projection) *
        (projection - complementIdempotent projection) =
      projection * projection - projection * complementIdempotent projection -
        complementIdempotent projection * projection +
        complementIdempotent projection * complementIdempotent projection := by noncomm_ring
    _ = 1 := by
      rw [idempotent.eq, idempotent_mul_complement projection idempotent.eq,
        complement_mul_idempotent projection idempotent.eq,
        complementIdempotent_sq projection idempotent.eq]
      simpa using add_complementIdempotent projection

theorem square_sum_of_anticommute (kinetic coupling : Carrier)
    (anticommute : kinetic * coupling + coupling * kinetic = 0) :
    (kinetic + coupling) * (kinetic + coupling) = kinetic * kinetic + coupling * coupling := by
  calc
    (kinetic + coupling) * (kinetic + coupling) =
        kinetic * kinetic + (kinetic * coupling + coupling * kinetic) + coupling * coupling := by
      noncomm_ring
    _ = kinetic * kinetic + coupling * coupling := by rw [anticommute, add_zero]

end Ring

section RealAlgebra

variable {Carrier : Type*} [Ring Carrier] [Algebra ℝ Carrier]

theorem signed_momentum_anticommutes (projection coupling : Carrier) (momentum : ℝ)
    (swap : projection * coupling = coupling * complementIdempotent projection) :
    (momentum • grading projection) * coupling +
      coupling * (momentum • grading projection) = 0 := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add,
    grading_anticommutes projection coupling swap, smul_zero]

theorem signed_momentum_square (projection : Carrier) (momentum : ℝ)
    (idempotent : IsIdempotentElem projection) :
    (momentum • grading projection) * (momentum • grading projection) =
      algebraMap ℝ Carrier (momentum ^ 2) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, grading_square projection idempotent]
  simp only [Algebra.smul_def, mul_one, pow_two]

theorem hamiltonian_square (projection coupling : Carrier) (momentum mass : ℝ)
    (idempotent : IsIdempotentElem projection)
    (swap : projection * coupling = coupling * complementIdempotent projection)
    (coupling_square : coupling * coupling = algebraMap ℝ Carrier (mass ^ 2)) :
    (momentum • grading projection + coupling) * (momentum • grading projection + coupling) =
      algebraMap ℝ Carrier (momentum ^ 2 + mass ^ 2) := by
  rw [square_sum_of_anticommute _ _
    (signed_momentum_anticommutes projection coupling momentum swap),
    signed_momentum_square projection momentum idempotent, coupling_square, map_add]

end RealAlgebra

end InfoGeometry.QuantumContext.MassAsCommutantCoupling
