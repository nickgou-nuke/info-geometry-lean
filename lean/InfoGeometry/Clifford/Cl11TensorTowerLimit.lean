import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorTowerLimit

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

/-! The stagewise star compatibility descends to the iterated transition maps. -/

theorem bondMap_star
    (i j : ℕ) (h : i ≤ j) (x : Stage i) :
    star (bondMap stageBond i j h x) =
      bondMap stageBond i j h (star x) := by
  refine Nat.le_induction
    (m := i)
    (P := fun t ht =>
      star (bondMap stageBond i t ht x) =
        bondMap stageBond i t ht (star x))
    ?base ?succ j h
  · simp [bondMap_refl]
  · intro t hit ih
    rw [bondMap_succ stageBond i t hit]
    change star (stageBond t (bondMap stageBond i t hit x)) =
      stageBond t (bondMap stageBond i t hit (star x))
    change star (stageEmbed t (bondMap stageBond i t hit x)) =
      stageEmbed t (bondMap stageBond i t hit (star x))
    rw [← stageEmbed_star]
    exact congrArg (fun y => stageEmbed t y) ih

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

noncomputable instance limitStar : Star Limit where
  star :=
    DirectLimit.map
      (fun _ _ hij => bondMap stageBond _ _ hij)
      (fun _ _ hij => bondMap stageBond _ _ hij)
      (fun _ x => star x)
      (by
        intro i j hij x
        exact (bondMap_star i j hij x).symm)

@[simp] theorem limit_star_mk (n : ℕ) (x : Stage n) :
    star (⟦⟨n, x⟩⟧ : Limit) =
      (⟦⟨n, star x⟩⟧ : Limit) := rfl

noncomputable instance limitStarRing : StarRing Limit where
  star_involutive := by
    intro x
    induction x using DirectLimit.induction with
    | _ n x => simp [limit_star_mk]
  star_add := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n x y =>
        rw [DirectLimit.add_def, limit_star_mk, limit_star_mk,
          limit_star_mk, DirectLimit.add_def, star_add]
  star_mul := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n x y =>
        rw [DirectLimit.mul_def, limit_star_mk, limit_star_mk,
          limit_star_mk, DirectLimit.mul_def, star_mul]

noncomputable instance limitModuleReal : Module ℝ Limit :=
  Module.compHom Limit (realAlgebraMap : ℝ →+* Limit)

/-! ## The descended normalized trace -/

theorem normalizedTrace_add (n : ℕ) (A B : Stage n) :
    Cl11TensorTower.normalizedTrace n (A + B) =
      Cl11TensorTower.normalizedTrace n A +
        Cl11TensorTower.normalizedTrace n B := by
  unfold Cl11TensorTower.normalizedTrace
  rw [Matrix.trace_add]
  ring

theorem normalizedTrace_smul (n : ℕ) (c : ℝ) (A : Stage n) :
    Cl11TensorTower.normalizedTrace n (c • A) =
      c * Cl11TensorTower.normalizedTrace n A := by
  unfold Cl11TensorTower.normalizedTrace
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

theorem normalizedTrace_bondMap
    (m n : ℕ) (h : m ≤ n) (A : Stage m) :
    Cl11TensorTower.normalizedTrace n
        (bondMap stageBond m n h A) =
      Cl11TensorTower.normalizedTrace m A := by
  refine Nat.le_induction
    (m := m)
    (P := fun k hk =>
      Cl11TensorTower.normalizedTrace k
          (bondMap stageBond m k hk A) =
        Cl11TensorTower.normalizedTrace m A)
    ?base ?succ n h
  · simp [bondMap_refl]
  · intro k hmk ih
    rw [bondMap_succ stageBond m k hmk]
    change Cl11TensorTower.normalizedTrace (k + 1)
      (stageBond k (bondMap stageBond m k hmk A)) =
      Cl11TensorTower.normalizedTrace m A
    simpa [stageBond] using ih

def limitTrace : Limit →ₗ[ℝ] ℝ where
  toFun := DirectLimit.lift
    (fun _ _ hij => bondMap stageBond _ _ hij)
    (fun n A => Cl11TensorTower.normalizedTrace n A)
    (by
      intro m n h A
      exact (normalizedTrace_bondMap m n h A).symm)
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n A B =>
        simp only [DirectLimit.add_def, DirectLimit.lift_def]
        exact normalizedTrace_add n A B
  map_smul' := by
    intro c x
    induction x using DirectLimit.induction with
    | _ n A =>
        rw [show c • (⟦⟨n, A⟩⟧ : Limit) =
          realAlgebraMap c * (⟦⟨n, A⟩⟧ : Limit) by rfl,
          realAlgebraMap_stage n c]
        change DirectLimit.lift
            (fun _ _ hij => bondMap stageBond _ _ hij)
            (fun n A => Cl11TensorTower.normalizedTrace n A) _
            ((⟦⟨n, algebraMap ℝ (Stage n) c⟩⟧ : Limit) *
              (⟦⟨n, A⟩⟧ : Limit)) = _
        rw [DirectLimit.mul_def]
        simp only [DirectLimit.lift_def, RingHom.id_apply, smul_eq_mul]
        simpa [Algebra.algebraMap_eq_smul_one] using
          (normalizedTrace_smul n c A)

@[simp] theorem limitTrace_stage (n : ℕ) (A : Stage n) :
    limitTrace (ofStage n A) = Cl11TensorTower.normalizedTrace n A := by
  rfl

@[simp] theorem limitTrace_one : limitTrace (1 : Limit) = 1 := by
  calc
    limitTrace (1 : Limit) = limitTrace (ofStage 0 (1 : Stage 0)) := by
      exact congrArg limitTrace (map_one (ofStage 0)).symm
    _ = Cl11TensorTower.normalizedTrace 0 (1 : Stage 0) :=
      limitTrace_stage 0 (1 : Stage 0)
    _ = 1 := by
      unfold Cl11TensorTower.normalizedTrace
      rw [Matrix.trace_one]
      rw [InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two]
      norm_num

theorem limitTrace_commutator_zero (X Y : Limit) :
    limitTrace (X * Y - Y * X) = 0 := by
  induction X, Y using DirectLimit.induction₂ with
  | _ n A B =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def, DirectLimit.sub_def]
      change Cl11TensorTower.normalizedTrace n (A * B - B * A) = 0
      unfold Cl11TensorTower.normalizedTrace
      rw [Matrix.trace_sub, Matrix.trace_mul_comm B A]
      ring

@[simp] theorem limit_star_realAlgebraMap (r : ℝ) :
    star (realAlgebraMap r) = realAlgebraMap r := by
  change star (⟦⟨0, (algebraMap ℝ (Stage 0)) r⟩⟧ : Limit) =
    (⟦⟨0, (algebraMap ℝ (Stage 0)) r⟩⟧ : Limit)
  rw [limit_star_mk]
  apply congrArg (ofStage 0)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.star_apply]

noncomputable instance limitStarModuleReal : StarModule ℝ Limit where
  star_smul := by
    intro r x
    induction x using DirectLimit.induction with
    | _ n A =>
        change star (realAlgebraMap r * (⟦⟨n, A⟩⟧ : Limit)) =
          realAlgebraMap (star r) * star (⟦⟨n, A⟩⟧ : Limit)
        rw [star_mul, limit_star_realAlgebraMap, limit_star_mk]
        simpa using
          (Algebra.commutes r (star (⟦⟨n, A⟩⟧ : Limit))).symm

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

end InfoGeometry.Clifford.Cl11TensorTowerLimit
