import Mathlib.Tactic
import InfoGeometry.Section8

/-!
# Section 15: Quaternionic Hopf Fibration, finite algebraic core

This file repairs the Section 15 prose into theorem-safe finite algebra.

#### BUCKET 1: CLOSED FINITE THEOREMS
Hamilton quaternion associativity for the coordinate product from Section 8,
conjugation involution and additivity, the inverse-candidate equations for
nonzero norm, norm multiplicativity for `q1 * conj q2`, and the finite scalar
identity proving that the quaternionic Hopf readout has unit norm whenever
`normSq q1 + normSq q2 = 1`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The inverse-candidate theorems depend on the explicit premise
`Section8.Quat.normSq q ≠ 0`.  The Hopf target-norm theorem depends on the
explicit `S7`-shadow premise `normSq q1 + normSq q2 = 1`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove a topological fibration, fiber homeomorphism to `S^3`,
`S^3 ≃ SU(2)`, the double cover `SU(2) -> SO(3)`, smoothness, surjectivity, or
any projective-space classification.  Those require topology, Lie groups, and
smooth manifold data not present in this finite algebraic section.
-/

noncomputable section

namespace Section15

abbrev Quat := Section8.Quat

namespace Quat

open Section8.Quat

/-- Quaternion multiplication is associative for the coordinate Hamilton product. -/
theorem mul_assoc (a b c : Quat) : (a * b) * c = a * (b * c) := by
  ext <;> simp <;> ring

/-- Quaternion conjugation is involutive. -/
theorem conj_conj (q : Quat) : conj (conj q) = q := by
  ext <;> simp [conj]

/-- Quaternion conjugation distributes over addition. -/
theorem conj_add (p q : Quat) : conj (p + q) = conj p + conj q := by
  ext <;> simp [conj] <;> ring

/-- Quaternion conjugation reverses multiplication. -/
theorem conj_mul (p q : Quat) : conj (p * q) = conj q * conj p := by
  ext <;> simp [conj] <;> ring_nf

/-- Candidate inverse `conj q / normSq q`, written coordinatewise. -/
def inverseCandidate (q : Quat) : Quat :=
  ⟨q.r / normSq q, -q.x / normSq q, -q.y / normSq q, -q.z / normSq q⟩

theorem mul_inverseCandidate (q : Quat) (h : normSq q ≠ 0) :
    q * inverseCandidate q = 1 := by
  have hn : q.r ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≠ 0 := by
    simpa [normSq] using h
  ext <;> simp [inverseCandidate, normSq] <;> field_simp [hn] <;> ring

theorem inverseCandidate_mul (q : Quat) (h : normSq q ≠ 0) :
    inverseCandidate q * q = 1 := by
  have hn : q.r ^ 2 + q.x ^ 2 + q.y ^ 2 + q.z ^ 2 ≠ 0 := by
    simpa [normSq] using h
  ext <;> simp [inverseCandidate, normSq] <;> field_simp [hn] <;> ring

/-- Norm squared is multiplicative for the Hopf product `q1 * conj q2`. -/
theorem normSq_mul_conj (q1 q2 : Quat) :
    normSq (q1 * conj q2) = normSq q1 * normSq q2 := by
  simp [normSq, conj]
  ring

/-- Left multiplication by the scalar quaternion `2` multiplies norm squared by `4`. -/
theorem normSq_scalar_two_mul (q : Quat) :
    normSq (scalar 2 * q) = 4 * normSq q := by
  simp [normSq, scalar]
  ring

end Quat

/-- Finite `S7` shadow: a pair of quaternions whose squared norms sum to one. -/
def IsS7Pair (q1 q2 : Quat) : Prop :=
  Section8.Quat.normSq q1 + Section8.Quat.normSq q2 = 1

/--
Squared norm of the quaternionic Hopf readout
`(|q1|^2 - |q2|^2, 2 q1 conj(q2))` in `R ⊕ H`.
-/
def hopfImageNormSq (q1 q2 : Quat) : ℝ :=
  (Section8.Quat.normSq q1 - Section8.Quat.normSq q2) ^ 2 +
    Section8.Quat.normSq (Section8.Quat.scalar 2 * (q1 * Section8.Quat.conj q2))

/-- Algebraic norm calculation behind the quaternionic Hopf map. -/
theorem hopfImageNormSq_eq_sum_sq (q1 q2 : Quat) :
    hopfImageNormSq q1 q2 =
      (Section8.Quat.normSq q1 + Section8.Quat.normSq q2) ^ 2 := by
  simp [hopfImageNormSq, Quat.normSq_scalar_two_mul, Quat.normSq_mul_conj]
  ring

/-- The Hopf readout lands on the finite `S4` norm shadow for normalized pairs. -/
theorem hopfImageNormSq_eq_one_of_s7_pair
    (q1 q2 : Quat) (h : IsS7Pair q1 q2) :
    hopfImageNormSq q1 q2 = 1 := by
  rw [hopfImageNormSq_eq_sum_sq, h]
  ring

end Section15
