import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

namespace InfoGeometry.Parahyperkahler.KreinCuntzBridge

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-! ## Projectors associated to an involution

For an element `J` with `J² = 1`, the two half-sums `(1 + J)/2` and
`(1 - J)/2` are complementary orthogonal idempotents. -/

noncomputable def half : A := algebraMap ℝ A (1 / 2)

noncomputable def PL (J : A) : A := half * (1 + J)
noncomputable def PR (J : A) : A := half * (1 - J)

lemma half_comm (x : A) : half * x = x * half :=
  Algebra.commutes (1 / 2 : ℝ) x

/-- The two half-sums form a partition of unity, for every `J`. -/
theorem PL_add_PR_eq_one (J : A) : PL J + PR J = 1 := by
  dsimp [PL, PR]
  rw [← mul_add]
  have hsum : (1 + J) + (1 - J) = (1 : A) + 1 := by noncomm_ring
  rw [hsum]
  dsimp [half]
  have hone : (1 : A) = algebraMap ℝ A (1 : ℝ) := by simp
  simp only [hone]
  rw [← map_add, ← map_mul]
  norm_num

/-- The two half-sums are orthogonal when `J` is an involution. -/
theorem PL_mul_PR_eq_zero (J : A) (hJ : J * J = 1) : PL J * PR J = 0 := by
  dsimp [PL, PR]
  calc (half * (1 + J)) * (half * (1 - J))
      = half * ((1 + J) * half) * (1 - J) := by noncomm_ring
    _ = half * (half * (1 + J)) * (1 - J) := by rw [half_comm (1 + J)]
    _ = (half * half) * ((1 + J) * (1 - J)) := by noncomm_ring
    _ = (half * half) * (1 - J * J) := by noncomm_ring
    _ = (half * half) * (1 - 1) := by rw [hJ]
    _ = 0 := by simp

/-! ## The algebraic Cuntz relations

These results are stated directly for elements of a star ring, with the
isometry and sum relations as hypotheses. No auxiliary structure is used to
encode the laws. -/

variable [StarRing A]

def CuntzPL (S1 : A) : A := S1 * star S1
def CuntzPR (S2 : A) : A := S2 * star S2

omit [Algebra ℝ A] in
/-- The sum relation says exactly that the two range elements sum to one. -/
theorem CuntzPL_add_CuntzPR_eq_one (S1 S2 : A)
    (hC : S1 * star S1 + S2 * star S2 = 1) :
    CuntzPL S1 + CuntzPR S2 = 1 := hC

omit [Algebra ℝ A] in
/-- Isometries satisfying the range-sum relation have orthogonal initial
spaces: `S1* S2 = 0`. -/
theorem S1_star_mul_S2_eq_zero (S1 S2 : A)
    (hS1 : star S1 * S1 = 1) (hS2 : star S2 * S2 = 1)
    (hC : S1 * star S1 + S2 * star S2 = 1) :
    star S1 * S2 = 0 := by
  let x : A := star S1 * S2
  have h := congrArg (fun z : A => star S1 * z * S2) hC
  change star S1 * (S1 * star S1 + S2 * star S2) * S2 = star S1 * 1 * S2 at h
  have hleft :
      star S1 * (S1 * star S1 + S2 * star S2) * S2 = x + x := by
    calc
      _ = (star S1 * S1) * (star S1 * S2) +
          (star S1 * S2) * (star S2 * S2) := by noncomm_ring
      _ = x + x := by rw [hS1, hS2]; dsimp [x]; noncomm_ring
  have hright : star S1 * 1 * S2 = x := by dsimp [x]; noncomm_ring
  rw [hleft, hright] at h
  calc
    star S1 * S2 = x := rfl
    _ = (x + x) - x := by noncomm_ring
    _ = x - x := by rw [h]
    _ = 0 := sub_self x

omit [Algebra ℝ A] in
/-- Taking stars gives the reverse mixed orthogonality relation. -/
theorem S2_star_mul_S1_eq_zero (S1 S2 : A)
    (hS1 : star S1 * S1 = 1) (hS2 : star S2 * S2 = 1)
    (hC : S1 * star S1 + S2 * star S2 = 1) :
    star S2 * S1 = 0 := by
  have h := congrArg star (S1_star_mul_S2_eq_zero S1 S2 hS1 hS2 hC)
  simpa [star_mul] using h

omit [Algebra ℝ A] in
/-- The first Cuntz range element is idempotent. -/
theorem CuntzPL_idempotent (S1 : A) (hS1 : star S1 * S1 = 1) :
    CuntzPL S1 * CuntzPL S1 = CuntzPL S1 := by
  dsimp [CuntzPL]
  calc
    (S1 * star S1) * (S1 * star S1) = S1 * (star S1 * S1) * star S1 := by noncomm_ring
    _ = S1 * 1 * star S1 := by rw [hS1]
    _ = S1 * star S1 := by noncomm_ring

omit [Algebra ℝ A] in
/-- The second Cuntz range element is idempotent. -/
theorem CuntzPR_idempotent (S2 : A) (hS2 : star S2 * S2 = 1) :
    CuntzPR S2 * CuntzPR S2 = CuntzPR S2 := by
  dsimp [CuntzPR]
  calc
    (S2 * star S2) * (S2 * star S2) = S2 * (star S2 * S2) * star S2 := by noncomm_ring
    _ = S2 * 1 * star S2 := by rw [hS2]
    _ = S2 * star S2 := by noncomm_ring

omit [Algebra ℝ A] in
/-- The Cuntz range elements are orthogonal under the stated isometry and
sum relations. -/
theorem CuntzPL_mul_CuntzPR_eq_zero (S1 S2 : A)
    (hS1 : star S1 * S1 = 1) (hS2 : star S2 * S2 = 1)
    (hC : S1 * star S1 + S2 * star S2 = 1) :
    CuntzPL S1 * CuntzPR S2 = 0 := by
  dsimp [CuntzPL, CuntzPR]
  calc (S1 * star S1) * (S2 * star S2)
      = S1 * (star S1 * S2) * star S2 := by noncomm_ring
    _ = 0 := by rw [S1_star_mul_S2_eq_zero S1 S2 hS1 hS2 hC]; noncomm_ring

end InfoGeometry.Parahyperkahler.KreinCuntzBridge
