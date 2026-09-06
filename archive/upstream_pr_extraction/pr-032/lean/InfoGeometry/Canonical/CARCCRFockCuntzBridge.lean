import InfoGeometry.OperatorAlgebra.QCCRResidual
import InfoGeometry.Algebra.CuntzFockRepresentation
import InfoGeometry.Quantum.NoncommutativeFockBridge
import InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge
import InfoGeometry.Canonical.Cuntz2Isometries
import InfoGeometry.Canonical.CantorCuntzCliffordBridge

/-!
# CAR / CCR / Fock / Cuntz compatibility

The generic q-CCR residual is owned by `OperatorAlgebra.QCCRResidual`.
This owner records the finite CAR specialization, the finite-dimensional
obstruction to the bosonic CCR, and the Cuntz zero-parameter specialization.
The Fock and Cuntz colimit constructions remain owned by their respective
modules; no finite matrix is presented as an infinite-dimensional model.
-/

namespace InfoGeometry.Canonical.CARCCRFockCuntzBridge

open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge

/-! ### Finite CAR as the `q = -1` q-CCR specialization -/

theorem finite_car_qccr_residual :
    qCcrRelation annMatrix2 creMatrix2 (-1) = 0 := by
  exact (qccr_fermionic_limit annMatrix2 creMatrix2).2 annMatrix2_CAR

theorem finite_car_qccr_anticommutator :
    annMatrix2 * creMatrix2 + creMatrix2 * annMatrix2 = 1 :=
  annMatrix2_CAR

/-! ### Cuntz-derived CAR as the fermionic q-CCR boundary -/

theorem cuntz_derived_car_qccr_minus_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    qCcrRelation (carFromCuntz C) (star (carFromCuntz C)) (-1) = 0 := by
  exact (qccr_fermionic_limit (carFromCuntz C) (star (carFromCuntz C))).2
    (by simpa [cantorAnticommutator] using
      carFromCuntz_anticommutator_star_eq_one C)

/-! ### Cuntz isometries as the `q = 0` boundary relation -/

theorem cuntz_generator_qccr_zero {R : Type*} [Ring R] [StarRing R]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) :
    qCcrRelation (star (_root_.CuntzAlgebra.S1 C))
      (_root_.CuntzAlgebra.S1 C) 0 = 0 := by
  rw [qccr_to_cuntz_limit]
  exact _root_.CuntzAlgebra.h_isometry1 C

/-! A Cuntz isometry cannot also be a CAR annihilation operator.  The
fermionic endpoint would force its range projection to vanish, while the
Cuntz isometry then forces `1 = 0`. -/
theorem cuntz_generator_not_car
    {R : Type*} [Ring R] [StarRing R] [Nontrivial R]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) R) :
    ¬ qCcrRelation (star (_root_.CuntzAlgebra.S1 C))
        (_root_.CuntzAlgebra.S1 C) (-1) = 0 := by
  intro hcar
  have hisometry :
      star (_root_.CuntzAlgebra.S1 C) * _root_.CuntzAlgebra.S1 C = 1 :=
    _root_.CuntzAlgebra.h_isometry1 C
  have hcar' :
      star (_root_.CuntzAlgebra.S1 C) * _root_.CuntzAlgebra.S1 C +
          _root_.CuntzAlgebra.S1 C * star (_root_.CuntzAlgebra.S1 C) = 1 :=
    (qccr_fermionic_limit _ _).mp hcar
  have hrange :
      _root_.CuntzAlgebra.S1 C * star (_root_.CuntzAlgebra.S1 C) = 0 := by
    rw [hisometry] at hcar'
    have hcar'' :
        (1 : R) + _root_.CuntzAlgebra.S1 C * star (_root_.CuntzAlgebra.S1 C) =
          1 + 0 := by
      simpa using hcar'
    exact add_left_cancel hcar''
  have hone : (1 : R) = 0 := by
    calc
      (1 : R) =
          (star (_root_.CuntzAlgebra.S1 C) * _root_.CuntzAlgebra.S1 C) *
            (star (_root_.CuntzAlgebra.S1 C) * _root_.CuntzAlgebra.S1 C) := by
        rw [hisometry]
        simp
      _ = star (_root_.CuntzAlgebra.S1 C) *
          (_root_.CuntzAlgebra.S1 C * star (_root_.CuntzAlgebra.S1 C)) *
            _root_.CuntzAlgebra.S1 C := by
        noncomm_ring
      _ = 0 := by rw [hrange, mul_zero, zero_mul]
  exact one_ne_zero hone

/-! ### The same Cuntz boundary in the left-regular Fock action -/

theorem fock_left_regular_cuntz_qccr_zero
    (n : ℕ) (i : Fin n) (x : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg n) :
    qCcrRelation
        (InfoGeometry.Algebra.CuntzFockRepresentation.leftMultiplication n
          (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n i))
        (InfoGeometry.Algebra.CuntzFockRepresentation.leftMultiplication n
          (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n i)) 0 x = 0 := by
  have hqccr :
      qCcrRelation
          (InfoGeometry.Algebra.CuntzFockRepresentation.leftMultiplication n
            (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag n i))
          (InfoGeometry.Algebra.CuntzFockRepresentation.leftMultiplication n
            (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS n i)) 0 = 0 := by
    apply (qccr_to_cuntz_limit _ _).2
    ext y
    exact
      InfoGeometry.Algebra.CuntzFockRepresentation.leftMultiplication_cuntz_isometry n i y
  exact congrArg (fun f => f x) hqccr

/-!
### The finite-dimensional CCR obstruction

The trace of a commutator is zero, whereas the trace of the identity on a
nonempty finite matrix space is nonzero.  Thus a bosonic CCR pair cannot live
in a finite matrix algebra; it must be supplied by a genuine Fock/colimit
construction.
-/

theorem finite_matrix_ccr_impossible {n : ℕ} (hn : 0 < n)
    (a astar : Matrix (Fin n) (Fin n) ℂ)
    (h : qCcrRelation a astar 1 = 0) : False := by
  have hcomm : a * astar - astar * a = 1 :=
    (qccr_bosonic_limit a astar).mp h
  have htrace : Matrix.trace (a * astar - astar * a) =
      Matrix.trace (1 : Matrix (Fin n) (Fin n) ℂ) :=
    congrArg Matrix.trace hcomm
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self,
    Matrix.trace_one] at htrace
  have hn' : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  apply hn'
  simpa using htrace.symm

end InfoGeometry.Canonical.CARCCRFockCuntzBridge
