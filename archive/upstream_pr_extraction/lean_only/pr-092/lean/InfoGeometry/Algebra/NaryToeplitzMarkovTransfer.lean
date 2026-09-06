import InfoGeometry.Algebra.NaryToeplitzWeightedTripotent

/-! The Markov/transfer operator associated to a finite algebraic Cuntz family.
It is kept separate from the weighted creation supercharge: the weights enter
as a convex transfer sum, while the Cuntz generators act on both sides. -/

namespace InfoGeometry.Algebra.Cuntz

variable {R A : Type*} [CommRing R] [Semiring A] [Algebra R A]
variable {N : ℕ}

def markovTransfer
    (P : AlgebraicCuntzNPresentation R N A) (p : Fin N → R) (X : A) : A :=
  ∑ i : Fin N,
    algebraMap R A (p i) * P.T i * X * P.S i

theorem markovTransfer_add
    (P : AlgebraicCuntzNPresentation R N A) (p : Fin N → R)
    (X Y : A) :
    markovTransfer P p (X + Y) =
      markovTransfer P p X + markovTransfer P p Y := by
  simp only [markovTransfer, mul_add, add_mul, Finset.sum_add_distrib]

theorem markovTransfer_zero
    (P : AlgebraicCuntzNPresentation R N A) (p : Fin N → R) :
    markovTransfer P p 0 = 0 := by
  simp [markovTransfer]

theorem markovTransfer_one
    (P : AlgebraicCuntzNPresentation R N A) (p : Fin N → R) :
    markovTransfer P p 1 =
      algebraMap R A (∑ i : Fin N, p i) := by
  classical
  simp only [markovTransfer, mul_assoc, mul_one]
  simp_rw [← mul_assoc (algebraMap R A (p _))]
  have hterm (i : Fin N) :
      algebraMap R A (p i) * P.T i * P.S i = algebraMap R A (p i) := by
    calc
      algebraMap R A (p i) * P.T i * P.S i =
          algebraMap R A (p i) * (P.T i * P.S i) := by rw [mul_assoc]
      _ = algebraMap R A (p i) * 1 := by simp [P.isometry i i]
      _ = algebraMap R A (p i) := by simp
  calc
    (∑ i : Fin N, algebraMap R A (p i) * P.T i * P.S i) =
        ∑ i : Fin N, algebraMap R A (p i) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = algebraMap R A (∑ i : Fin N, p i) := by
      rw [map_sum]

theorem markovTransfer_one_of_normalized
    (P : AlgebraicCuntzNPresentation R N A) (p : Fin N → R)
    (hprob : ∑ i : Fin N, p i = 1) :
    markovTransfer P p 1 = 1 := by
  rw [markovTransfer_one P p, hprob]
  simp

end InfoGeometry.Algebra.Cuntz
