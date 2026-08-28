import Mathlib

noncomputable section

namespace InfoGeometry.Physics.ChiralProjectorTransport

abbrev Operator (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def plusProjector {n : ℕ} (K : Operator n) : Operator n :=
  (1 / 2 : ℝ) • ((1 : Operator n) + K)

def minusProjector {n : ℕ} (K : Operator n) : Operator n :=
  (1 / 2 : ℝ) • ((1 : Operator n) - K)

theorem plusProjector_idempotent {n : ℕ} (K : Operator n)
    (hK : K * K = 1) : plusProjector K * plusProjector K = plusProjector K := by
  unfold plusProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul]
  rw [hK]
  module

theorem minusProjector_idempotent {n : ℕ} (K : Operator n)
    (hK : K * K = 1) : minusProjector K * minusProjector K = minusProjector K := by
  unfold minusProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul]
  rw [hK]
  module

theorem projectors_annihilate {n : ℕ} (K : Operator n)
    (hK : K * K = 1) :
    plusProjector K * minusProjector K = 0 ∧
      minusProjector K * plusProjector K = 0 := by
  constructor <;> unfold plusProjector minusProjector
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [hK]
    module
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [hK]
    module

theorem projectors_sum {n : ℕ} (K : Operator n) :
    plusProjector K + minusProjector K = (1 : Operator n) := by
  unfold plusProjector minusProjector
  module

theorem involution_from_projectors {n : ℕ} (K : Operator n) :
    plusProjector K - minusProjector K = K := by
  unfold plusProjector minusProjector
  module

theorem plusProjector_transport {n : ℕ} (K K' T : Operator n)
    (hIntertwine : T * K = K' * T) :
    T * plusProjector K = plusProjector K' * T := by
  unfold plusProjector
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul]
  rw [hIntertwine]

theorem minusProjector_transport {n : ℕ} (K K' T : Operator n)
    (hIntertwine : T * K = K' * T) :
    T * minusProjector K = minusProjector K' * T := by
  unfold minusProjector
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul]
  rw [hIntertwine]

theorem projector_transport_sum {n : ℕ} (K K' T : Operator n)
    (_hIntertwine : T * K = K' * T) :
    T * (plusProjector K + minusProjector K) = T := by
  unfold plusProjector minusProjector
  have hsum :
      (1 / 2 : ℝ) • ((1 : Operator n) + K) +
        (1 / 2 : ℝ) • ((1 : Operator n) - K) = (1 : Operator n) := by
    module
  rw [hsum, Matrix.mul_one]

end InfoGeometry.Physics.ChiralProjectorTransport
