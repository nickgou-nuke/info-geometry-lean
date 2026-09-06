import InfoGeometry.Clifford.SplitQuaternion

set_option autoImplicit false
set_option linter.dupNamespace false

namespace InfoGeometry.Clifford
namespace SplitBiquaternion

/-- Complexified split quaternions, i.e. split-biquaternions. -/
structure Carrier where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ

abbrev SplitBiquaternion := Carrier

@[ext]
lemma ext {q1 q2 : SplitBiquaternion}
    (ha : q1.a = q2.a) (hb : q1.b = q2.b) (hc : q1.c = q2.c) (hd : q1.d = q2.d) :
    q1 = q2 := by
  cases q1
  cases q2
  congr

def add (q1 q2 : SplitBiquaternion) : SplitBiquaternion :=
  ⟨q1.a + q2.a, q1.b + q2.b, q1.c + q2.c, q1.d + q2.d⟩

def neg (q : SplitBiquaternion) : SplitBiquaternion :=
  ⟨-q.a, -q.b, -q.c, -q.d⟩

/--
Coordinate multiplication law for the basis `1, i, j, k` with
`i^2 = -1`, `j^2 = 1`, `k^2 = 1`, `ij = k`, `jk = -i`, `ki = j`.
-/
def mul (q1 q2 : SplitBiquaternion) : SplitBiquaternion :=
  ⟨q1.a * q2.a - q1.b * q2.b + q1.c * q2.c + q1.d * q2.d,
   q1.a * q2.b + q1.b * q2.a - q1.c * q2.d + q1.d * q2.c,
   q1.a * q2.c - q1.b * q2.d + q1.c * q2.a + q1.d * q2.b,
   q1.a * q2.d + q1.b * q2.c - q1.c * q2.b + q1.d * q2.a⟩

def one : SplitBiquaternion :=
  ⟨1, 0, 0, 0⟩

def zero : SplitBiquaternion :=
  ⟨0, 0, 0, 0⟩

instance : Add SplitBiquaternion where
  add := add

instance : Neg SplitBiquaternion where
  neg := neg

instance : Sub SplitBiquaternion where
  sub q1 q2 := q1 + (-q2)

instance : Mul SplitBiquaternion where
  mul := mul

instance : One SplitBiquaternion where
  one := one

instance : Zero SplitBiquaternion where
  zero := zero

def splitConj (q : SplitBiquaternion) : SplitBiquaternion :=
  ⟨q.a, -q.b, -q.c, -q.d⟩

def norm (q : SplitBiquaternion) : ℂ :=
  q.a * q.a + q.b * q.b - q.c * q.c - q.d * q.d

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Matrix packet `a + b i + c j + d k ↦ [[a+d, b+c],[-b+c,a-d]]`. -/
def toMatrix (q : SplitBiquaternion) : Mat2C :=
  !![q.a + q.d, q.b + q.c;
     -q.b + q.c, q.a - q.d]

def matMul2 (A B : Mat2C) : Mat2C :=
  !![A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1;
     A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1]

def det2 (M : Mat2C) : ℂ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

def scalar (z : ℂ) : SplitBiquaternion :=
  ⟨z, 0, 0, 0⟩

/-- Compact square-minus unit. -/
def I : SplitBiquaternion :=
  ⟨0, 1, 0, 0⟩

/-- First hyperbolic square-plus unit. -/
def J : SplitBiquaternion :=
  ⟨0, 0, 1, 0⟩

/-- Second hyperbolic square-plus unit. -/
def K : SplitBiquaternion :=
  ⟨0, 0, 0, 1⟩

def commutator (q1 q2 : SplitBiquaternion) : SplitBiquaternion :=
  q1 * q2 - q2 * q1

def anticommutator (q1 q2 : SplitBiquaternion) : SplitBiquaternion :=
  q1 * q2 + q2 * q1

theorem mul_assoc (q1 q2 q3 : SplitBiquaternion) :
    (q1 * q2) * q3 = q1 * (q2 * q3) := by
  change mul (mul q1 q2) q3 = mul q1 (mul q2 q3)
  ext <;> simp [mul] <;> ring

theorem one_mul (q : SplitBiquaternion) :
    1 * q = q := by
  change mul one q = q
  ext <;> simp [mul, one]

theorem mul_one (q : SplitBiquaternion) :
    q * 1 = q := by
  change mul q one = q
  ext <;> simp [mul, one]

theorem splitConj_mul (q : SplitBiquaternion) :
    splitConj q * q = ⟨norm q, 0, 0, 0⟩ := by
  change mul (splitConj q) q = ⟨norm q, 0, 0, 0⟩
  ext <;> simp [mul, splitConj, norm] <;> ring

theorem mul_splitConj (q : SplitBiquaternion) :
    q * splitConj q = ⟨norm q, 0, 0, 0⟩ := by
  change mul q (splitConj q) = ⟨norm q, 0, 0, 0⟩
  ext <;> simp [mul, splitConj, norm] <;> ring

theorem splitConj_splitConj (q : SplitBiquaternion) :
    splitConj (splitConj q) = q := by
  ext <;> simp [splitConj]

theorem norm_splitConj (q : SplitBiquaternion) :
    norm (splitConj q) = norm q := by
  simp [splitConj, norm]

theorem toMatrix_add (q1 q2 : SplitBiquaternion) :
    toMatrix (q1 + q2) = toMatrix q1 + toMatrix q2 := by
  change toMatrix (add q1 q2) = toMatrix q1 + toMatrix q2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, add] <;> ring_nf

theorem toMatrix_mul (q1 q2 : SplitBiquaternion) :
    toMatrix (q1 * q2) = matMul2 (toMatrix q1) (toMatrix q2) := by
  change toMatrix (mul q1 q2) = matMul2 (toMatrix q1) (toMatrix q2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, matMul2, mul] <;> ring

theorem norm_eq_det (q : SplitBiquaternion) :
    norm q = det2 (toMatrix q) := by
  simp [norm, det2, toMatrix]
  ring_nf

theorem I_sq : I * I = scalar (-1) := by
  change mul I I = scalar (-1)
  ext <;> norm_num [I, scalar, mul]

theorem J_sq : J * J = scalar 1 := by
  change mul J J = scalar 1
  ext <;> norm_num [J, scalar, mul]

theorem K_sq : K * K = scalar 1 := by
  change mul K K = scalar 1
  ext <;> norm_num [K, scalar, mul]

theorem IJ : I * J = K := by
  change mul I J = K
  ext <;> norm_num [I, J, K, mul]

theorem JI : J * I = -K := by
  change mul J I = neg K
  ext <;> norm_num [I, J, K, neg, mul]

theorem JK : J * K = -I := by
  change mul J K = neg I
  ext <;> norm_num [I, J, K, neg, mul]

theorem KJ : K * J = I := by
  change mul K J = I
  ext <;> norm_num [I, J, K, mul]

theorem KI : K * I = J := by
  change mul K I = J
  ext <;> norm_num [I, J, K, mul]

theorem IK : I * K = -J := by
  change mul I K = neg J
  ext <;> norm_num [I, J, K, neg, mul]

theorem commutator_I_J : commutator I J = scalar 2 * K := by
  change commutator I J = mul (scalar 2) K
  unfold commutator
  rw [IJ, JI]
  change add K (neg (neg K)) = mul (scalar 2) K
  ext <;> norm_num [K, scalar, add, neg, mul]

theorem commutator_J_K : commutator J K = scalar (-2) * I := by
  change commutator J K = mul (scalar (-2)) I
  unfold commutator
  rw [JK, KJ]
  change add (neg I) (neg I) = mul (scalar (-2)) I
  ext <;> norm_num [I, scalar, add, neg, mul]

theorem commutator_K_I : commutator K I = scalar 2 * J := by
  change commutator K I = mul (scalar 2) J
  unfold commutator
  rw [KI, IK]
  change add J (neg (neg J)) = mul (scalar 2) J
  ext <;> norm_num [J, scalar, add, neg, mul]

theorem anticommutator_I_J : anticommutator I J = 0 := by
  change anticommutator I J = zero
  unfold anticommutator
  rw [IJ, JI]
  change add K (neg K) = zero
  ext <;> norm_num [K, add, neg, zero]

theorem anticommutator_J_K : anticommutator J K = 0 := by
  change anticommutator J K = zero
  unfold anticommutator
  rw [JK, KJ]
  change add (neg I) I = zero
  ext <;> norm_num [I, add, neg, zero]

theorem anticommutator_K_I : anticommutator K I = 0 := by
  change anticommutator K I = zero
  unfold anticommutator
  rw [KI, IK]
  change add J (neg J) = zero
  ext <;> norm_num [J, add, neg, zero]

theorem matrix_of_I : toMatrix I = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I, toMatrix]

theorem matrix_of_J : toMatrix J = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, toMatrix]

theorem matrix_of_K : toMatrix K = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K, toMatrix]

/-- Real split quaternions embed into the complexified owner by scalar extension. -/
def ofSplitQuaternion (q : InfoGeometry.Clifford.SplitQuaternion) : SplitBiquaternion :=
  ⟨q.w, q.x, q.y, q.z⟩

theorem ofSplitQuaternion_toMatrix (q : InfoGeometry.Clifford.SplitQuaternion) :
    toMatrix (ofSplitQuaternion q) =
      !![(q.w : ℂ) + q.z, (q.x : ℂ) + q.y;
         -(q.x : ℂ) + q.y, (q.w : ℂ) - q.z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofSplitQuaternion, toMatrix]

/-! ## Inverses and unit-norm split-biquaternions -/

/-- The norm is multiplicative for the coordinate split-biquaternion product. -/
theorem norm_mul (q r : SplitBiquaternion) :
    norm (q * r) = norm q * norm r := by
  change norm (mul q r) = norm q * norm r
  simp [norm, mul]
  ring

/-- Scalar split-biquaternions act by coordinatewise scalar multiplication on the left. -/
theorem scalar_mul_apply (z : ℂ) (q : SplitBiquaternion) :
    scalar z * q = ⟨z * q.a, z * q.b, z * q.c, z * q.d⟩ := by
  change mul (scalar z) q = _
  ext <;> simp [scalar, mul]

/-- Scalar split-biquaternions act by coordinatewise scalar multiplication on the right. -/
theorem mul_scalar_apply (q : SplitBiquaternion) (z : ℂ) :
    q * scalar z = ⟨q.a * z, q.b * z, q.c * z, q.d * z⟩ := by
  change mul q (scalar z) = _
  ext <;> simp [scalar, mul]

/-- Scalar split-biquaternions commute with every split-biquaternion. -/
theorem scalar_comm (z : ℂ) (q : SplitBiquaternion) :
    q * scalar z = scalar z * q := by
  rw [mul_scalar_apply, scalar_mul_apply]
  ext <;> ring

/-- Candidate inverse `N(q)⁻¹ q̄` for a non-null split-biquaternion. -/
noncomputable def inverseCandidate (q : SplitBiquaternion) : SplitBiquaternion :=
  scalar (norm q)⁻¹ * splitConj q

/-- The inverse candidate is a left inverse whenever the norm is nonzero. -/
theorem inverseCandidate_mul (q : SplitBiquaternion) (hq : norm q ≠ 0) :
    inverseCandidate q * q = 1 := by
  unfold inverseCandidate
  rw [mul_assoc, splitConj_mul]
  change mul (scalar (norm q)⁻¹) ⟨norm q, 0, 0, 0⟩ = one
  apply ext
  · change (norm q)⁻¹ * norm q - 0 * 0 + 0 * 0 + 0 * 0 = 1
    simpa using inv_mul_cancel₀ hq
  · change (norm q)⁻¹ * 0 + 0 * norm q - 0 * 0 + 0 * 0 = 0
    ring
  · change (norm q)⁻¹ * 0 - 0 * 0 + 0 * norm q + 0 * 0 = 0
    ring
  · change (norm q)⁻¹ * 0 + 0 * 0 - 0 * 0 + 0 * norm q = 0
    ring

/-- The inverse candidate is a right inverse whenever the norm is nonzero. -/
theorem mul_inverseCandidate (q : SplitBiquaternion) (hq : norm q ≠ 0) :
    q * inverseCandidate q = 1 := by
  unfold inverseCandidate
  rw [← mul_assoc]
  rw [scalar_comm (norm q)⁻¹ q]
  rw [mul_assoc, mul_splitConj]
  change mul (scalar (norm q)⁻¹) ⟨norm q, 0, 0, 0⟩ = one
  apply ext
  · change (norm q)⁻¹ * norm q - 0 * 0 + 0 * 0 + 0 * 0 = 1
    simpa using inv_mul_cancel₀ hq
  · change (norm q)⁻¹ * 0 + 0 * norm q - 0 * 0 + 0 * 0 = 0
    ring
  · change (norm q)⁻¹ * 0 - 0 * 0 + 0 * norm q + 0 * 0 = 0
    ring
  · change (norm q)⁻¹ * 0 + 0 * 0 - 0 * 0 + 0 * norm q = 0
    ring

/-- Unit-norm split-biquaternions. -/
structure NormOneSplitBiquaternion where
  val : SplitBiquaternion
  property : norm val = 1

@[ext]
lemma NormOneSplitBiquaternion.ext {q r : NormOneSplitBiquaternion}
    (h : q.val = r.val) : q = r := by
  cases q
  cases r
  congr

instance : Mul NormOneSplitBiquaternion where
  mul q r := ⟨q.val * r.val, by
    rw [norm_mul, q.property, r.property]
    norm_num⟩

instance : One NormOneSplitBiquaternion where
  one := ⟨1, by
    change norm one = 1
    simp [norm, one]⟩

instance : Inv NormOneSplitBiquaternion where
  inv q := ⟨splitConj q.val, by
    have h : norm (splitConj q.val) = norm q.val := by
      simp [splitConj, norm]
    rw [h, q.property]⟩

instance : Group NormOneSplitBiquaternion where
  mul_assoc q r s := by
    apply NormOneSplitBiquaternion.ext
    exact mul_assoc q.val r.val s.val
  one_mul q := by
    apply NormOneSplitBiquaternion.ext
    exact one_mul q.val
  mul_one q := by
    apply NormOneSplitBiquaternion.ext
    exact mul_one q.val
  inv_mul_cancel q := by
    apply NormOneSplitBiquaternion.ext
    change splitConj q.val * q.val = (1 : SplitBiquaternion)
    rw [splitConj_mul, q.property]
    rfl

/-- Consolidated inverse/unit packet for the split-biquaternion owner. -/
theorem inverse_unit_packet (q : SplitBiquaternion) (hq : norm q ≠ 0) :
    inverseCandidate q * q = 1 ∧
    q * inverseCandidate q = 1 ∧
    ∀ u : NormOneSplitBiquaternion, (u⁻¹ * u).val = 1 := by
  exact ⟨inverseCandidate_mul q hq, mul_inverseCandidate q hq,
    fun u => by
      change splitConj u.val * u.val = (1 : SplitBiquaternion)
      rw [splitConj_mul, u.property]
      rfl⟩

end SplitBiquaternion
end InfoGeometry.Clifford
