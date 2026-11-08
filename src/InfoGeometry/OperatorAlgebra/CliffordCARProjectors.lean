import InfoGeometry.OperatorAlgebra.CliffordCAR
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# CAR occupation projectors

For each CAR mode, `cre i * ann i` and `ann i * cre i` are the two
complementary finite algebraic projectors.  This file stays inside the native
`Clnn n` carrier and does not introduce a Fock-space or vacuum representation.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

noncomputable def occupationProjector (n : ℕ) (i : Fin n) : Clnn n :=
  cre n i * ann n i

noncomputable def vacancyProjector (n : ℕ) (i : Fin n) : Clnn n :=
  ann n i * cre n i

noncomputable def modeParity (n : ℕ) (i : Fin n) : Clnn n :=
  occupationProjector n i - vacancyProjector n i

theorem occupationProjector_add_vacancyProjector
    (n : ℕ) (i : Fin n) :
    occupationProjector n i + vacancyProjector n i = 1 := by
  simpa [occupationProjector, vacancyProjector, add_comm] using car_identity n i i

private theorem car_same (n : ℕ) (i : Fin n) :
    ann n i * cre n i + cre n i * ann n i = 1 := by
  simpa [if_pos rfl] using car_identity n i i

theorem occupationProjector_idempotent (n : ℕ) (i : Fin n) :
    occupationProjector n i * occupationProjector n i = occupationProjector n i := by
  unfold occupationProjector
  have hcar : ann n i * cre n i = 1 - cre n i * ann n i := by
    exact eq_sub_of_add_eq (car_same n i)
  calc
    (cre n i * ann n i) * (cre n i * ann n i) =
        cre n i * (ann n i * cre n i) * ann n i := by noncomm_ring
    _ = cre n i * (1 - cre n i * ann n i) * ann n i := by rw [hcar]
    _ = cre n i * ann n i := by
      calc
        cre n i * (1 - cre n i * ann n i) * ann n i =
            cre n i * ann n i - (cre n i * cre n i) *
              (ann n i * ann n i) := by noncomm_ring
        _ = cre n i * ann n i := by simp

theorem vacancyProjector_idempotent (n : ℕ) (i : Fin n) :
    vacancyProjector n i * vacancyProjector n i = vacancyProjector n i := by
  unfold vacancyProjector
  have hcar : cre n i * ann n i = 1 - ann n i * cre n i := by
    have h := car_same n i
    rw [add_comm] at h
    exact eq_sub_of_add_eq h
  calc
    (ann n i * cre n i) * (ann n i * cre n i) =
        ann n i * (cre n i * ann n i) * cre n i := by noncomm_ring
    _ = ann n i * (1 - ann n i * cre n i) * cre n i := by rw [hcar]
    _ = ann n i * cre n i := by
      calc
        ann n i * (1 - ann n i * cre n i) * cre n i =
            ann n i * cre n i - (ann n i * ann n i) *
              (cre n i * cre n i) := by noncomm_ring
        _ = ann n i * cre n i := by simp

theorem occupationProjector_mul_vacancyProjector (n : ℕ) (i : Fin n) :
    occupationProjector n i * vacancyProjector n i = 0 := by
  unfold occupationProjector vacancyProjector
  calc
    (cre n i * ann n i) * (ann n i * cre n i) =
        cre n i * (ann n i * ann n i) * cre n i := by noncomm_ring
    _ = 0 := by rw [ann_sq_zero]; simp

theorem vacancyProjector_mul_occupationProjector (n : ℕ) (i : Fin n) :
    vacancyProjector n i * occupationProjector n i = 0 := by
  unfold vacancyProjector occupationProjector
  calc
    (ann n i * cre n i) * (cre n i * ann n i) =
        ann n i * (cre n i * cre n i) * ann n i := by noncomm_ring
    _ = 0 := by rw [cre_sq_zero]; simp

theorem modeParity_sq (n : ℕ) (i : Fin n) :
    modeParity n i * modeParity n i = 1 := by
  unfold modeParity
  calc
    (occupationProjector n i - vacancyProjector n i) *
        (occupationProjector n i - vacancyProjector n i) =
        occupationProjector n i * occupationProjector n i -
          occupationProjector n i * vacancyProjector n i -
          vacancyProjector n i * occupationProjector n i +
          vacancyProjector n i * vacancyProjector n i := by noncomm_ring
    _ = occupationProjector n i + vacancyProjector n i := by
      rw [occupationProjector_idempotent, vacancyProjector_idempotent,
        occupationProjector_mul_vacancyProjector,
        vacancyProjector_mul_occupationProjector]
      noncomm_ring
    _ = 1 := occupationProjector_add_vacancyProjector n i

theorem modeParity_mul_ann (n : ℕ) (i : Fin n) :
    modeParity n i * ann n i = -(ann n i) := by
  unfold modeParity occupationProjector vacancyProjector
  have hcar : ann n i * cre n i = 1 - cre n i * ann n i := by
    exact eq_sub_of_add_eq (car_same n i)
  calc
    (cre n i * ann n i - ann n i * cre n i) * ann n i =
        cre n i * (ann n i * ann n i) -
          (ann n i * cre n i) * ann n i := by noncomm_ring
    _ = cre n i * 0 - (1 - cre n i * ann n i) * ann n i := by
      rw [ann_sq_zero, hcar]
    _ = -(ann n i) := by
      calc
        cre n i * 0 - (1 - cre n i * ann n i) * ann n i =
            -(ann n i) + (cre n i * ann n i) * ann n i := by
              noncomm_ring
        _ = -(ann n i) := by
          rw [show (cre n i * ann n i) * ann n i = 0 by
            calc
              (cre n i * ann n i) * ann n i =
                  cre n i * (ann n i * ann n i) := by noncomm_ring
              _ = 0 := by simp]
          simp

theorem ann_mul_modeParity (n : ℕ) (i : Fin n) :
    ann n i * modeParity n i = ann n i := by
  unfold modeParity occupationProjector vacancyProjector
  have hcar : ann n i * cre n i = 1 - cre n i * ann n i := by
    exact eq_sub_of_add_eq (car_same n i)
  calc
    ann n i * (cre n i * ann n i - ann n i * cre n i) =
        (ann n i * cre n i) * ann n i -
          (ann n i * ann n i) * cre n i := by noncomm_ring
    _ = (1 - cre n i * ann n i) * ann n i - 0 * cre n i := by
      rw [hcar, ann_sq_zero]
    _ = ann n i := by
      calc
        (1 - cre n i * ann n i) * ann n i - 0 * cre n i =
            ann n i - (cre n i * ann n i) * ann n i := by noncomm_ring
        _ = ann n i := by
          rw [show (cre n i * ann n i) * ann n i = 0 by
            calc
              (cre n i * ann n i) * ann n i =
                  cre n i * (ann n i * ann n i) := by noncomm_ring
              _ = 0 := by simp]
          simp

theorem modeParity_mul_cre (n : ℕ) (i : Fin n) :
    modeParity n i * cre n i = cre n i := by
  unfold modeParity occupationProjector vacancyProjector
  have hcar : ann n i * cre n i = 1 - cre n i * ann n i := by
    exact eq_sub_of_add_eq (car_same n i)
  calc
    (cre n i * ann n i - ann n i * cre n i) * cre n i =
        cre n i * (ann n i * cre n i) -
          ann n i * (cre n i * cre n i) := by noncomm_ring
    _ = cre n i * (1 - cre n i * ann n i) - ann n i * 0 := by
      rw [hcar, cre_sq_zero]
    _ = cre n i := by
      calc
        cre n i * (1 - cre n i * ann n i) - ann n i * 0 =
            cre n i - (cre n i * cre n i) * ann n i := by noncomm_ring
        _ = cre n i := by simp

theorem cre_mul_modeParity (n : ℕ) (i : Fin n) :
    cre n i * modeParity n i = -(cre n i) := by
  unfold modeParity occupationProjector vacancyProjector
  have hcar : cre n i * ann n i = 1 - ann n i * cre n i := by
    have h := car_same n i
    rw [add_comm] at h
    exact eq_sub_of_add_eq h
  calc
    cre n i * (cre n i * ann n i - ann n i * cre n i) =
        (cre n i * cre n i) * ann n i -
          (cre n i * ann n i) * cre n i := by noncomm_ring
    _ = 0 * ann n i - (1 - ann n i * cre n i) * cre n i := by
      rw [cre_sq_zero, hcar]
    _ = -(cre n i) := by
      calc
        0 * ann n i - (1 - ann n i * cre n i) * cre n i =
            -(cre n i) + (ann n i * cre n i) * cre n i := by noncomm_ring
        _ = -(cre n i) := by
          calc
            -(cre n i) + (ann n i * cre n i) * cre n i =
                -(cre n i) + ann n i * (cre n i * cre n i) := by noncomm_ring
            _ = -(cre n i) := by simp

theorem modeParity_ann_anticomm (n : ℕ) (i : Fin n) :
    modeParity n i * ann n i + ann n i * modeParity n i = 0 := by
  rw [modeParity_mul_ann, ann_mul_modeParity]
  abel

theorem modeParity_cre_anticomm (n : ℕ) (i : Fin n) :
    modeParity n i * cre n i + cre n i * modeParity n i = 0 := by
  rw [modeParity_mul_cre, cre_mul_modeParity]
  abel

/-
theorem centeredNumberOperator_commutator_occupationProjector
    (n : ℕ) (i : Fin n) :
    centeredNumberOperator n * occupationProjector n i -
        occupationProjector n i * centeredNumberOperator n = 0 := by
  simpa [occupationProjector] using
    centeredNumberOperator_commutator_cre_ann n i i

theorem centeredNumberOperator_commutator_vacancyProjector
    (n : ℕ) (i : Fin n) :
    centeredNumberOperator n * vacancyProjector n i -
        vacancyProjector n i * centeredNumberOperator n = 0 := by
  simpa [vacancyProjector] using
    centeredNumberOperator_commutator_ann_cre n i i
-/

end InfoGeometry.OperatorAlgebra.CliffordCAR
