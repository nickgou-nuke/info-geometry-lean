import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

set_option autoImplicit false

noncomputable section

namespace Cl11TensorTowerLimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

abbrev Stage (n : ℕ) : Type := Cl11TensorTower.MatStage n

/-- One-step bonding maps for the matrix `Cl(1,1)` tower, viewed as ring homomorphisms. -/
abbrev stageBond : ∀ n : ℕ, Stage n →+* Stage (n + 1) :=
  fun n => (Cl11TensorTower.stageEmbed n).toRingHom

abbrev Limit : Type :=
  DirectLimitSuperClosure (Stage := Stage) stageBond

def ofStage (n : ℕ) : Stage n →+* Limit :=
  directLimitOf (Stage := Stage) stageBond n

/-- The base-ring action on the direct limit induced by the stage-0 embedding. -/
noncomputable def realAlgebraMap : ℝ →+* Limit :=
  (ofStage 0).comp (algebraMap ℝ (Stage 0))

/-- The stagewise `★`-readout transported to the direct limit. -/
noncomputable def stageStarMap (n : ℕ) : Stage n →+ Limit where
  toFun := fun x => ofStage n (star x)
  map_zero' := by simp
  map_add' := by
    intro x y
    simp [map_add]

/-- The stagewise `★`-readout is compatible with the iterated bonding maps. -/
theorem stageStarMap_compat
    (i j : ℕ) (h : i ≤ j) (x : Stage i) :
    stageStarMap j (bondMap stageBond i j h x) = stageStarMap i x := by
  refine Nat.le_induction
    (m := i)
    (P := fun t ht =>
      stageStarMap t (bondMap stageBond i t ht x) = stageStarMap i x)
    ?base ?succ j h
  · simp [stageStarMap]
  · intro t hmt ih
    rw [bondMap_succ stageBond i t hmt]
    change stageStarMap (t + 1) (stageBond t (bondMap stageBond i t hmt x)) =
      stageStarMap i x
    have hstar :
        star (stageBond t (bondMap stageBond i t hmt x)) =
          stageBond t (star (bondMap stageBond i t hmt x)) := by
      simpa [stageBond] using
        (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed_star t
          (bondMap stageBond i t hmt x)).symm
    change ofStage (t + 1) (star (stageBond t (bondMap stageBond i t hmt x))) =
      stageStarMap i x
    rw [hstar]
    have hb :
        ofStage (t + 1) (stageBond t (star (bondMap stageBond i t hmt x))) =
          ofStage t (star (bondMap stageBond i t hmt x)) := by
      simpa [stageBond] using
        (directLimitOf_bond (Stage := Stage) stageBond t
          (star (bondMap stageBond i t hmt x)))
    rw [hb]
    exact ih

/- #### BUCKET 1: CLOSED FINITE THEOREMS -/
-- [Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

@[simp]
theorem ofStage_apply_bond (n : ℕ) (A : Stage n) :
    ofStage (n + 1) (stageEmbed n A) = ofStage n A := by
  exact directLimitOf_bond (Stage := Stage) stageBond n A

/-- The scalar embedding is independent of the finite representative stage. -/
@[simp] theorem realAlgebraMap_stage (n : ℕ) (r : ℝ) :
    realAlgebraMap r = ofStage n (algebraMap ℝ (Stage n) r) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        realAlgebraMap r = ofStage n (algebraMap ℝ (Stage n) r) := ih
        _ = ofStage (n + 1) (stageEmbed n (algebraMap ℝ (Stage n) r)) := by
              symm
              exact ofStage_apply_bond (n := n) (A := algebraMap ℝ (Stage n) r)
        _ = ofStage (n + 1) (algebraMap ℝ (Stage (n + 1)) r) := by
              rw [← (stageEmbed n).commutes r]

noncomputable instance : Algebra ℝ Limit :=
  RingHom.toAlgebra' realAlgebraMap (by
    intro r x
    induction x using DirectLimit.induction with
    | _ n x =>
        rw [realAlgebraMap_stage]
        simpa using congrArg (ofStage n) (Algebra.commutes r x))

@[simp]
theorem ofStage_zero (n : ℕ) :
    ofStage n (0 : Stage n) = 0 := by
  exact map_zero (ofStage n)

@[simp]
theorem ofStage_one (n : ℕ) :
    ofStage n (1 : Stage n) = 1 := by
  exact map_one (ofStage n)

@[simp]
theorem ofStage_add (n : ℕ) (A B : Stage n) :
    ofStage n (A + B) = ofStage n A + ofStage n B := by
  exact map_add (ofStage n) A B

@[simp]
theorem ofStage_mul (n : ℕ) (A B : Stage n) :
    ofStage n (A * B) = ofStage n A * ofStage n B := by
  exact map_mul (ofStage n) A B

@[simp]
theorem ofStage_pow (n k : ℕ) (A : Stage n) :
    ofStage n (A ^ k) = ofStage n A ^ k := by
  exact map_pow (ofStage n) A k

@[simp]
theorem ofStage_neg (n : ℕ) (A : Stage n) :
    ofStage n (-A) = -ofStage n A := by
  exact map_neg (ofStage n) A

@[simp]
theorem ofStage_sub (n : ℕ) (A B : Stage n) :
    ofStage n (A - B) = ofStage n A - ofStage n B := by
  exact map_sub (ofStage n) A B

theorem limit_square_zero {n : ℕ} {A : Stage n} (hA : A * A = 0) :
    ofStage n A * ofStage n A = 0 := by
  rw [← ofStage_mul, hA, ofStage_zero]

theorem limit_idempotent {n : ℕ} {P : Stage n} (hP : P * P = P) :
    ofStage n P * ofStage n P = ofStage n P := by
  rw [← ofStage_mul, hP]

theorem limit_involution {n : ℕ} {J : Stage n} (hJ : J * J = 1) :
    ofStage n J * ofStage n J = 1 := by
  rw [← ofStage_mul, hJ, ofStage_one]

theorem limit_commute {n : ℕ} {A B : Stage n} (h : A * B = B * A) :
    ofStage n A * ofStage n B = ofStage n B * ofStage n A := by
  rw [← ofStage_mul, ← ofStage_mul, h]

theorem limit_anticomm_zero {n : ℕ} {A B : Stage n} (h : A * B + B * A = 0) :
    ofStage n A * ofStage n B + ofStage n B * ofStage n A = 0 := by
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add, h, ofStage_zero]

theorem limit_commutator {n : ℕ} (A B : Stage n) :
    ofStage n (A * B - B * A) = ofStage n A * ofStage n B - ofStage n B * ofStage n A := by
  rw [ofStage_sub, ofStage_mul, ofStage_mul]

theorem finite_sequence_constant_in_limit
    (F : ∀ n : ℕ, Stage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1)) :
    ∀ n : ℕ, ofStage n (F n) = ofStage 0 (F 0) := by
  exact directLimitOf_eq_zero_stage (Stage := Stage) stageBond F hF

theorem finite_sequence_square_zero_in_limit
    (F : ∀ n : ℕ, Stage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1))
    (h0 : F 0 * F 0 = 0) :
    ∀ n : ℕ, ofStage n (F n) * ofStage n (F n) = 0 := by
  intro n
  rw [finite_sequence_constant_in_limit F hF n]
  exact limit_square_zero (n := 0) h0

theorem finite_sequence_idempotent_in_limit
    (F : ∀ n : ℕ, Stage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1))
    (h0 : F 0 * F 0 = F 0) :
    ∀ n : ℕ, ofStage n (F n) * ofStage n (F n) = ofStage n (F n) := by
  intro n
  rw [finite_sequence_constant_in_limit F hF n]
  exact limit_idempotent (n := 0) h0

theorem finite_sequence_involution_in_limit
    (F : ∀ n : ℕ, Stage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1))
    (h0 : F 0 * F 0 = 1) :
    ∀ n : ℕ, ofStage n (F n) * ofStage n (F n) = 1 := by
  intro n
  rw [finite_sequence_constant_in_limit F hF n]
  exact limit_involution (n := 0) h0

/- #### BUCKET 2: CONDITIONAL THEOREMS -/
-- [Empty.]

/- #### BUCKET 3: OPEN CLOSURE DEBT -/
-- [No open closure debt in this module.]

end Cl11TensorTowerLimit
