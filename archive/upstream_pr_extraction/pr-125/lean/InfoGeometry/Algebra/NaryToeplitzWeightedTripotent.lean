import InfoGeometry.Algebra.CuntzN

namespace InfoGeometry.Algebra.Cuntz

/-!
Weighted supercharges for a finite Cuntz family.

This file separates the weighted creation operator from a Markov transfer
operator and from any Jordan/TKK construction.  The coefficients live in the
central scalar algebra `R`; the adjoint-side family is supplied by the
algebraic Cuntz presentation.
-/

variable {R A : Type*} [CommRing R] [Semiring A] [Algebra R A]
variable {N : ℕ}

def weightedSupercharge
    (P : AlgebraicCuntzNPresentation R N A) (c : Fin N → R) : A :=
  ∑ i : Fin N, P.S i * algebraMap R A (c i)

def weightedSuperchargeAdjoint
    (P : AlgebraicCuntzNPresentation R N A) (c : Fin N → R) : A :=
  ∑ i : Fin N, algebraMap R A (c i) * P.T i

theorem weightedSupercharge_adjoint_mul_self
    (P : AlgebraicCuntzNPresentation R N A) (c : Fin N → R)
    (h_norm : ∑ i : Fin N, c i * c i = 1) :
    weightedSuperchargeAdjoint P c * weightedSupercharge P c = 1 := by
  classical
  have hterm (i j : Fin N) :
      (algebraMap R A (c i) * P.T i) *
          (P.S j * algebraMap R A (c j)) =
        if i = j then algebraMap R A (c i * c j) else 0 := by
    calc
      (algebraMap R A (c i) * P.T i) *
          (P.S j * algebraMap R A (c j)) =
        algebraMap R A (c i) *
          ((P.T i * P.S j) * algebraMap R A (c j)) := by
            simp only [mul_assoc]
      _ = algebraMap R A (c i) *
          ((if i = j then 1 else 0) * algebraMap R A (c j)) := by
            rw [P.isometry]
      _ = if i = j then algebraMap R A (c i * c j) else 0 := by
            by_cases hij : i = j
            · subst hij
              simp [map_mul]
            · simp [hij]
  simp only [weightedSuperchargeAdjoint, weightedSupercharge,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← map_sum]
  simpa using congrArg (fun x : R => algebraMap R A x) h_norm

theorem weightedSupercharge_isometry
    (P : AlgebraicCuntzNPresentation R N A) (c : Fin N → R)
    (h_norm : ∑ i : Fin N, c i * c i = 1) :
    weightedSuperchargeAdjoint P c * weightedSupercharge P c = 1 :=
  weightedSupercharge_adjoint_mul_self P c h_norm

theorem weightedSupercharge_tripotent
    (P : AlgebraicCuntzNPresentation R N A) (c : Fin N → R)
    (h_norm : ∑ i : Fin N, c i * c i = 1) :
    weightedSupercharge P c * weightedSuperchargeAdjoint P c *
        weightedSupercharge P c = weightedSupercharge P c := by
  have h_iso := weightedSupercharge_isometry P c h_norm
  calc
    weightedSupercharge P c * weightedSuperchargeAdjoint P c *
        weightedSupercharge P c =
      weightedSupercharge P c *
        (weightedSuperchargeAdjoint P c * weightedSupercharge P c) := by
          rw [mul_assoc]
    _ = weightedSupercharge P c * 1 := by rw [h_iso]
    _ = weightedSupercharge P c := by simp

end InfoGeometry.Algebra.Cuntz
