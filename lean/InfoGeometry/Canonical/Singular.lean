import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Canonical.Clifford

/-!
# Einstein Universe: Singular Regularization
Integrating Drazin and Moore-Penrose inverses for degenerate metrics.
-/

namespace InfoGeometry.Canonical

variable {R : Type*} [Ring R] [StarRing R]

/--
Axioms for the Moore-Penrose inverse (Geometric Mirror).
Source: EINSTEIN/EinsteinLean/Singular.lean
-/
structure IsMoorePenroseInverse (a b : R) : Prop where
  aba : a * b * a = a
  bab : b * a * b = b
  ab_star : star (a * b) = a * b
  ba_star : star (b * a) = b * a

/--
Axioms for the Drazin inverse (Spectral Mirror).
Source: EINSTEIN/EinsteinLean/Singular.lean
-/
structure IsDrazinInverse (a b : R) (k : ℕ) : Prop where
  comm : a * b = b * a
  bab : b * a * b = b
  pow : a^(k + 1) * b = a^k

/--
The "Einstein Anomaly"
Defined as the commutator of the Geometric (MP) and Spectral (Drazin) projectors.
-/
def EinsteinAnomaly (a b_mp b_dr : R) (_k : ℕ)
  (_h_mp : IsMoorePenroseInverse a b_mp)
  (_h_dr : IsDrazinInverse a b_dr _k) : R :=
  let P_MP := a * b_mp
  let P_D  := a * b_dr
  P_MP * P_D - P_D * P_MP

/--
Theorem: Singularity Regularization
Degenerate manifolds in the Einstein Universe are stabilized by the generalized inverse.
-/
theorem RegularizationStability (a b_mp : R) (h_mp : IsMoorePenroseInverse a b_mp) :
  a * b_mp * a = a :=
  h_mp.aba

/--
Theorem: Chiral/Einstein Anomaly Skew-Adjointness
The anomaly, defined as the commutator between the Geometric and Spectral projectors,
is strictly skew-adjoint when both projectors are self-adjoint.
-/
theorem einsteinAnomaly_skew_adjoint (a b_mp b_dr : R) (k : ℕ)
    (h_mp : IsMoorePenroseInverse a b_mp)
    (h_dr : IsDrazinInverse a b_dr k)
    (h_dr_star : star (a * b_dr) = a * b_dr) :
    star (EinsteinAnomaly a b_mp b_dr k h_mp h_dr) =
      - (EinsteinAnomaly a b_mp b_dr k h_mp h_dr) := by
  unfold EinsteinAnomaly
  simp only [star_sub, star_mul, h_mp.ab_star, h_dr_star]
  rw [neg_sub]

/-!
## Constructive Nondegenerate Existence

For invertible (`IsUnit`) elements, generalized inverses are constructively
realized by the ordinary inverse.
-/

/--
Constructive Moore-Penrose inverse existence in the nondegenerate case.
If `a` is invertible, `a⁻¹` satisfies the Moore-Penrose axioms.
-/
theorem exists_moorePenroseInverse_of_isUnit
    (a : R) (ha : IsUnit a) :
    ∃ b : R, IsMoorePenroseInverse a b := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨↑u⁻¹, ?_⟩
  constructor <;> simp

/--
Constructive Drazin inverse existence in the nondegenerate case.
If `a` is invertible, `a⁻¹` is a Drazin inverse with index `k = 0`.
-/
theorem exists_drazinInverse_of_isUnit
    {S : Type*} [Ring S]
    (a : S) (ha : IsUnit a) :
    ∃ b : S, IsDrazinInverse a b 0 := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨↑u⁻¹, ?_⟩
  constructor <;> simp

/--
Constructive Moore-Penrose inverse existence in the degenerate projector case.
If `a` is a self-adjoint idempotent, then `a` is its own Moore-Penrose inverse.
-/
theorem exists_moorePenroseInverse_of_selfAdjoint_idempotent
    (a : R)
    (ha_idem : a * a = a)
    (ha_star : star a = a) :
    ∃ b : R, IsMoorePenroseInverse a b := by
  refine ⟨a, ?_⟩
  constructor
  · calc
      a * a * a = (a * a) * a := by simp [mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
  · calc
      a * a * a = (a * a) * a := by simp [mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
  · calc
      star (a * a) = star a * star a := by simpa using star_mul a a
      _ = a * a := by simpa [ha_star]
  · calc
      star (a * a) = star a * star a := by simpa using star_mul a a
      _ = a * a := by simpa [ha_star]

/--
Constructive Drazin inverse existence in the degenerate projector case.
If `a` is idempotent, then `a` is its own Drazin inverse with index `k = 1`.
-/
theorem exists_drazinInverse_of_idempotent
    {S : Type*} [Ring S]
    (a : S)
    (ha_idem : a * a = a) :
    ∃ b : S, IsDrazinInverse a b 1 := by
  refine ⟨a, ?_⟩
  constructor
  · simp
  · calc
      a * a * a = (a * a) * a := by simp [mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
  · calc
      a ^ (1 + 1) * a = (a * a) * a := by simp [pow_succ, mul_assoc]
      _ = a * a := by simpa [ha_idem]
      _ = a := ha_idem
      _ = a ^ 1 := by simp

/--
Joint constructive generalized-inverse package in the projector case.
For self-adjoint idempotent `a`, the same witness `a` satisfies both
Moore-Penrose and Drazin (`k = 1`) axioms.
-/
theorem exists_regularization_pair_of_selfAdjoint_idempotent
    (a : R)
    (ha_idem : a * a = a)
    (ha_star : star a = a) :
    ∃ b : R, IsMoorePenroseInverse a b ∧ IsDrazinInverse a b 1 := by
  refine ⟨a, ?_⟩
  constructor
  · constructor
    · calc
        a * a * a = (a * a) * a := by simp [mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
    · calc
        a * a * a = (a * a) * a := by simp [mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
    · calc
        star (a * a) = star a * star a := by simpa using star_mul a a
        _ = a * a := by simpa [ha_star]
    · calc
        star (a * a) = star a * star a := by simpa using star_mul a a
        _ = a * a := by simpa [ha_star]
  · constructor
    · simp
    · calc
        a * a * a = (a * a) * a := by simp [mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
    · calc
        a ^ (1 + 1) * a = (a * a) * a := by simp [pow_succ, mul_assoc]
        _ = a * a := by simpa [ha_idem]
        _ = a := ha_idem
        _ = a ^ 1 := by simp

/--
Joint constructive generalized-inverse package in the nondegenerate case.
The same inverse witness simultaneously satisfies Moore-Penrose and Drazin (`k=0`).
-/
theorem exists_regularization_pair_of_isUnit
    (a : R) (ha : IsUnit a) :
    ∃ b : R, IsMoorePenroseInverse a b ∧ IsDrazinInverse a b 0 := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨↑u⁻¹, ?_⟩
  constructor <;> constructor <;> simp

@[simp] theorem EinsteinAnomaly_eq_zero_of_regularization_pair
    (a b : R)
    (h_mp : IsMoorePenroseInverse a b)
    (h_dr : IsDrazinInverse a b 0) :
    EinsteinAnomaly a b b 0 h_mp h_dr = 0 := by
  unfold EinsteinAnomaly
  simp

@[simp] theorem EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent
    (a : R)
    (ha_idem : a * a = a)
    (ha_star : star a = a) :
    EinsteinAnomaly a a a 1
      (by
        constructor
        · calc
            a * a * a = (a * a) * a := by simp [mul_assoc]
            _ = a * a := by simpa [ha_idem]
            _ = a := ha_idem
        · calc
            a * a * a = (a * a) * a := by simp [mul_assoc]
            _ = a * a := by simpa [ha_idem]
            _ = a := ha_idem
        · calc
            star (a * a) = star a * star a := by simpa using star_mul a a
            _ = a * a := by simpa [ha_star]
        · calc
            star (a * a) = star a * star a := by simpa using star_mul a a
            _ = a * a := by simpa [ha_star])
      (by
        constructor
        · simp
        · calc
            a * a * a = (a * a) * a := by simp [mul_assoc]
            _ = a * a := by simpa [ha_idem]
            _ = a := ha_idem
        · calc
            a ^ (1 + 1) * a = (a * a) * a := by simp [pow_succ, mul_assoc]
            _ = a * a := by simpa [ha_idem]
            _ = a := ha_idem
            _ = a ^ 1 := by simp)
      = 0 := by
  unfold EinsteinAnomaly
  simp [ha_idem]

end InfoGeometry.Canonical
