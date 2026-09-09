import InfoGeometry.Canonical.CliffordCARGeneratorTopological
import InfoGeometry.Canonical.GNSCARColimit

/-!
# The common algebraic operator carrier for the `Cl(1,1)` tower

The finite Clifford stages act on one common carrier: the algebraic direct
limit itself.  The action is the canonical left-regular representation
provided by `Algebra.lsmul`.  This file deliberately does not call that
carrier a completed Fock space, and it does not identify it with the analytic
`FockEndomorphism` type.  Those are separate representation problems.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CommonFockCarrier

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CliffordCARGeneratorTopological
open InfoGeometry.Canonical.GNSCARColimit

abbrev Carrier : Type := AlgebraicLimit

abbrev Operator : Type := Module.End ℝ Carrier

abbrev Stage (n : ℕ) : Type := MatStage n

/-- The canonical left-regular representation of the algebraic colimit itself.

This is the common associative target for all finite stages.  It is an
algebraic operator carrier, not an analytic completion. -/
def limitRepresentation : Carrier →+* Operator where
  toFun a := LinearMap.mulLeft ℝ a
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp
  map_zero' := by
    ext x
    simp
  map_add' a b := by
    ext x
    simp [add_mul]

@[simp] theorem limitRepresentation_apply (a x : Carrier) :
    limitRepresentation a x = a * x := by
  simp [limitRepresentation]

/-- The common left-regular representation is faithful.  The proof is the
evaluation-at-one argument, so it does not use any dimension or completion
assumption. -/
theorem limitRepresentation_injective :
    Function.Injective limitRepresentation := by
  intro a b h
  have h_one := congrArg (fun T : Operator => T (1 : Carrier)) h
  simpa [limitRepresentation_apply] using h_one

/-! ## Stage representations -/

/-- The canonical left-regular representation of a finite stage on the
common algebraic colimit carrier. -/
def stageRepresentation (n : ℕ) : Stage n →+* Operator where
  toFun a := LinearMap.mulLeft ℝ (ofStage n a)
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp
  map_zero' := by
    ext x
    simp
  map_add' a b := by
    ext x
    simp [add_mul]

@[simp] theorem stageRepresentation_apply (n : ℕ) (a : Stage n)
    (x : Carrier) :
    stageRepresentation n a x = ofStage n a * x := by
  simp [stageRepresentation]

/-- The stage representations agree with the canonical representation of the
colimit element represented by that stage. -/
theorem stageRepresentation_eq_colimit_lsmul (n : ℕ) (a : Stage n) :
    stageRepresentation n a = LinearMap.mulLeft ℝ (ofStage n a) := rfl

@[simp] theorem limitRepresentation_ofStage (n : ℕ) (a : Stage n) :
    limitRepresentation (ofStage n a) = stageRepresentation n a := rfl

/-- The common representation is uniquely determined by its finite-stage
readouts. -/
theorem limitRepresentation_unique (f : Carrier →+* Operator)
    (hstage : ∀ n (a : Stage n),
      f (ofStage n a) = stageRepresentation n a) :
    f = limitRepresentation := by
  apply RingHom.ext
  intro x
  induction x using DirectLimit.induction with
  | _ n a =>
      change f (ofStage n a) = limitRepresentation (ofStage n a)
      rw [hstage, limitRepresentation_ofStage]

/-- Bond compatibility of the common left-regular representation. -/
theorem stageRepresentation_bond (n : ℕ) (a : Stage n) :
    stageRepresentation (n + 1) (stageEmbed n a) =
      stageRepresentation n a := by
  apply LinearMap.ext
  intro x
  change ofStage (n + 1) (stageEmbed n a) * x = ofStage n a * x
  rw [ofStage_apply_bond]

/-- Every finite stage therefore has a genuine representation into one and
the same associative operator algebra. -/
theorem stageRepresentation_bond_apply (n : ℕ) (a : Stage n) (x : Carrier) :
    stageRepresentation (n + 1) (stageEmbed n a) x =
      stageRepresentation n a x := by
  rw [stageRepresentation_bond]

/-! ## Generator readouts -/

def creationOperator (n : ℕ) (k : Fin n) : Operator :=
  stageRepresentation n (jwCreation n k)

def annihilationOperator (n : ℕ) (k : Fin n) : Operator :=
  stageRepresentation n (jwAnnihilation n k)

@[simp] theorem creationOperator_castSucc (n : ℕ) (k : Fin n) :
    creationOperator (n + 1) k.castSucc = creationOperator n k := by
  unfold creationOperator
  rw [show jwCreation (n + 1) k.castSucc = stageEmbed n (jwCreation n k) by
    exact (matStageEmbed_jwCreation k).symm]
  rw [stageRepresentation_bond]

@[simp] theorem annihilationOperator_castSucc (n : ℕ) (k : Fin n) :
    annihilationOperator (n + 1) k.castSucc = annihilationOperator n k := by
  unfold annihilationOperator
  rw [show jwAnnihilation (n + 1) k.castSucc = stageEmbed n (jwAnnihilation n k) by
    exact (matStageEmbed_jwAnnihilation k).symm]
  rw [stageRepresentation_bond]

theorem creationOperator_apply (n : ℕ) (k : Fin n) (x : Carrier) :
    creationOperator n k x = ofStage n (jwCreation n k) * x := by
  simp [creationOperator, stageRepresentation]

theorem annihilationOperator_apply (n : ℕ) (k : Fin n) (x : Carrier) :
    annihilationOperator n k x = ofStage n (jwAnnihilation n k) * x := by
  simp [annihilationOperator, stageRepresentation]

/-! ## Canonical mode readout and CAR -/

def modeCreationOperator (k : ℕ) : Operator :=
  creationOperator (k + 1) ⟨k, Nat.lt_succ_self k⟩

def modeAnnihilationOperator (k : ℕ) : Operator :=
  annihilationOperator (k + 1) ⟨k, Nat.lt_succ_self k⟩

theorem modeCreationOperator_eq_leftRegular (k : ℕ) :
    modeCreationOperator k = LinearMap.mulLeft ℝ (limit_u k) := by
  ext x
  change ofStage (k + 1) (jwCreation (k + 1)
      ⟨k, Nat.lt_succ_self k⟩) * x = limit_u k * x
  rw [limit_u_eq_uImage_last]
  rfl

theorem modeAnnihilationOperator_eq_leftRegular (k : ℕ) :
    modeAnnihilationOperator k = LinearMap.mulLeft ℝ (limit_v k) := by
  ext x
  change ofStage (k + 1) (jwAnnihilation (k + 1)
      ⟨k, Nat.lt_succ_self k⟩) * x = limit_v k * x
  rw [limit_v_eq_vImage_last]
  rfl

theorem modeCreationOperator_sq_zero (k : ℕ) :
    modeCreationOperator k * modeCreationOperator k = 0 := by
  rw [modeCreationOperator_eq_leftRegular]
  ext x
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
  rw [← mul_assoc, limit_u_sq_zero, zero_mul]
  simp

theorem modeAnnihilationOperator_sq_zero (k : ℕ) :
    modeAnnihilationOperator k * modeAnnihilationOperator k = 0 := by
  rw [modeAnnihilationOperator_eq_leftRegular]
  ext x
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
  rw [← mul_assoc, limit_v_sq_zero, zero_mul]
  rfl

theorem modeAnnihilationOperator_creationOperator_anticomm (k : ℕ) :
    modeAnnihilationOperator k * modeCreationOperator k +
        modeCreationOperator k * modeAnnihilationOperator k =
      (1 : Operator) := by
  rw [modeAnnihilationOperator_eq_leftRegular,
    modeCreationOperator_eq_leftRegular]
  ext x
  change limit_v k * (limit_u k * x) +
      limit_u k * (limit_v k * x) = x
  rw [← mul_assoc, ← mul_assoc, ← add_mul]
  rw [add_comm (limit_v k * limit_u k) (limit_u k * limit_v k)]
  rw [limit_uv_anticomm, one_mul]

theorem modeCreationOperator_cross_site_anticomm (i j : ℕ) (hij : i ≠ j) :
    modeCreationOperator i * modeCreationOperator j +
        modeCreationOperator j * modeCreationOperator i = 0 := by
  rw [modeCreationOperator_eq_leftRegular,
    modeCreationOperator_eq_leftRegular]
  ext x
  change limit_u i * (limit_u j * x) +
      limit_u j * (limit_u i * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    limit_u_cross_site_anticommute hij, zero_mul]

theorem modeAnnihilationOperator_cross_site_anticomm (i j : ℕ) (hij : i ≠ j) :
    modeAnnihilationOperator i * modeAnnihilationOperator j +
        modeAnnihilationOperator j * modeAnnihilationOperator i = 0 := by
  rw [modeAnnihilationOperator_eq_leftRegular,
    modeAnnihilationOperator_eq_leftRegular]
  ext x
  change limit_v i * (limit_v j * x) +
      limit_v j * (limit_v i * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    limit_v_cross_site_anticommute hij, zero_mul]

theorem modeCreationOperator_annihilationOperator_cross_site_anticomm
    (i j : ℕ) (hij : i ≠ j) :
    modeCreationOperator i * modeAnnihilationOperator j +
        modeAnnihilationOperator j * modeCreationOperator i = 0 := by
  rw [modeCreationOperator_eq_leftRegular,
    modeAnnihilationOperator_eq_leftRegular]
  ext x
  change limit_u i * (limit_v j * x) +
      limit_v j * (limit_u i * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    limit_u_v_cross_site_anticommute hij, zero_mul]

theorem modeAnnihilationOperator_creationOperator_cross_site_anticomm
    (i j : ℕ) (hij : i ≠ j) :
    modeAnnihilationOperator i * modeCreationOperator j +
        modeCreationOperator j * modeAnnihilationOperator i = 0 := by
  rw [modeAnnihilationOperator_eq_leftRegular,
    modeCreationOperator_eq_leftRegular]
  ext x
  change limit_v i * (limit_u j * x) +
      limit_u j * (limit_v i * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    limit_v_u_cross_site_anticommute hij, zero_mul]

theorem modeCreationOperator_annihilationOperator_anticomm_if
    (i j : ℕ) :
    modeCreationOperator i * modeAnnihilationOperator j +
        modeAnnihilationOperator j * modeCreationOperator i =
      if i = j then (1 : Operator) else 0 := by
  by_cases h : i = j
  · subst h
    simpa [add_comm] using
      (modeAnnihilationOperator_creationOperator_anticomm i)
  · simpa [h] using
      (modeCreationOperator_annihilationOperator_cross_site_anticomm i j h)

theorem modeAnnihilationOperator_creationOperator_anticomm_if
    (i j : ℕ) :
    modeAnnihilationOperator i * modeCreationOperator j +
        modeCreationOperator j * modeAnnihilationOperator i =
      if i = j then (1 : Operator) else 0 := by
  by_cases h : i = j
  · subst h
    simpa using modeAnnihilationOperator_creationOperator_anticomm i
  · simpa [h] using
      (modeAnnihilationOperator_creationOperator_cross_site_anticomm i j h)

theorem modeCreationOperator_creationOperator_anticomm
    (i j : ℕ) :
    modeCreationOperator i * modeCreationOperator j +
        modeCreationOperator j * modeCreationOperator i = 0 := by
  by_cases h : i = j
  · subst h
    simp [modeCreationOperator_sq_zero]
  · exact modeCreationOperator_cross_site_anticomm i j h

theorem modeAnnihilationOperator_annihilationOperator_anticomm
    (i j : ℕ) :
    modeAnnihilationOperator i * modeAnnihilationOperator j +
        modeAnnihilationOperator j * modeAnnihilationOperator i = 0 := by
  by_cases h : i = j
  · subst h
    simp [modeAnnihilationOperator_sq_zero]
  · exact modeAnnihilationOperator_cross_site_anticomm i j h

@[simp] theorem limitRepresentation_limit_u (k : ℕ) :
    limitRepresentation (limit_u k) = modeCreationOperator k := by
  rw [modeCreationOperator_eq_leftRegular]
  rfl

@[simp] theorem limitRepresentation_limit_v (k : ℕ) :
    limitRepresentation (limit_v k) = modeAnnihilationOperator k := by
  rw [modeAnnihilationOperator_eq_leftRegular]
  rfl

theorem limitRepresentation_limit_u_sq_zero (k : ℕ) :
    limitRepresentation (limit_u k) * limitRepresentation (limit_u k) = 0 := by
  rw [limitRepresentation_limit_u]
  exact modeCreationOperator_sq_zero k

theorem limitRepresentation_limit_v_sq_zero (k : ℕ) :
    limitRepresentation (limit_v k) * limitRepresentation (limit_v k) = 0 := by
  rw [limitRepresentation_limit_v]
  exact modeAnnihilationOperator_sq_zero k

theorem limitRepresentation_limit_v_u_anticomm (k : ℕ) :
    limitRepresentation (limit_v k) * limitRepresentation (limit_u k) +
        limitRepresentation (limit_u k) * limitRepresentation (limit_v k) =
      (1 : Operator) := by
  rw [limitRepresentation_limit_v, limitRepresentation_limit_u]
  exact modeAnnihilationOperator_creationOperator_anticomm k

/-! ## Finite Algebraic Number Operator & Projections -/

/-- The mode number operator $N_k = u_k v_k$ on the algebraic carrier. -/
def modeNumberOperator (k : ℕ) : Operator :=
  modeCreationOperator k * modeAnnihilationOperator k

/-- The mode hole / complement operator $H_k = v_k u_k$ on the algebraic carrier. -/
def modeHoleOperator (k : ℕ) : Operator :=
  modeAnnihilationOperator k * modeCreationOperator k

/-- Orthogonal decomposition of identity: $N_k + H_k = 1$. -/
theorem modeNumber_add_hole (k : ℕ) :
    modeNumberOperator k + modeHoleOperator k = 1 := by
  unfold modeNumberOperator modeHoleOperator
  rw [add_comm]
  exact modeAnnihilationOperator_creationOperator_anticomm k

/-- Idempotency of the mode number projection: $N_k^2 = N_k$. -/
theorem modeNumber_idempotent (k : ℕ) :
    modeNumberOperator k * modeNumberOperator k = modeNumberOperator k := by
  unfold modeNumberOperator
  have h_anticomm : modeAnnihilationOperator k * modeCreationOperator k =
      1 - modeCreationOperator k * modeAnnihilationOperator k := by
    have h := modeAnnihilationOperator_creationOperator_anticomm k
    have h_add : modeCreationOperator k * modeAnnihilationOperator k +
        modeAnnihilationOperator k * modeCreationOperator k = 1 := by
      rw [add_comm, h]
    exact eq_sub_of_add_eq' h_add
  have h1 : (modeCreationOperator k * modeAnnihilationOperator k) *
      (modeCreationOperator k * modeAnnihilationOperator k) =
    modeCreationOperator k *
      (modeAnnihilationOperator k * modeCreationOperator k) *
      modeAnnihilationOperator k := by simp only [mul_assoc]
  have h2 : modeCreationOperator k *
      (1 - modeCreationOperator k * modeAnnihilationOperator k) *
      modeAnnihilationOperator k =
    (modeCreationOperator k * 1 -
      modeCreationOperator k * (modeCreationOperator k * modeAnnihilationOperator k)) *
      modeAnnihilationOperator k := by rw [mul_sub]
  have h3 : (modeCreationOperator k * 1 -
      modeCreationOperator k * (modeCreationOperator k * modeAnnihilationOperator k)) =
    modeCreationOperator k := by
    rw [mul_one, ← mul_assoc (modeCreationOperator k), modeCreationOperator_sq_zero, zero_mul, sub_zero]
  rw [h1, h_anticomm, h2, h3]

/-- Action on creation operator: $N_k u_k = u_k$. -/
theorem modeNumber_creation (k : ℕ) :
    modeNumberOperator k * modeCreationOperator k = modeCreationOperator k := by
  unfold modeNumberOperator
  have h_anticomm : modeAnnihilationOperator k * modeCreationOperator k =
      1 - modeCreationOperator k * modeAnnihilationOperator k := by
    have h := modeAnnihilationOperator_creationOperator_anticomm k
    have h_add : modeCreationOperator k * modeAnnihilationOperator k +
        modeAnnihilationOperator k * modeCreationOperator k = 1 := by
      rw [add_comm, h]
    exact eq_sub_of_add_eq' h_add
  calc
    modeCreationOperator k * modeAnnihilationOperator k * modeCreationOperator k =
      modeCreationOperator k * (modeAnnihilationOperator k * modeCreationOperator k) := by rw [mul_assoc]
    _ = modeCreationOperator k * (1 - modeCreationOperator k * modeAnnihilationOperator k) := by rw [h_anticomm]
    _ = modeCreationOperator k * 1 - modeCreationOperator k * (modeCreationOperator k * modeAnnihilationOperator k) := by rw [mul_sub]
    _ = modeCreationOperator k - (modeCreationOperator k * modeCreationOperator k) * modeAnnihilationOperator k := by simp only [mul_one, mul_assoc]
    _ = modeCreationOperator k - 0 * modeAnnihilationOperator k := by rw [modeCreationOperator_sq_zero]
    _ = modeCreationOperator k := by rw [zero_mul, sub_zero]

/-- Exclusion principle: $u_k N_k = 0$. -/
theorem creation_modeNumber (k : ℕ) :
    modeCreationOperator k * modeNumberOperator k = 0 := by
  unfold modeNumberOperator
  calc
    modeCreationOperator k * (modeCreationOperator k * modeAnnihilationOperator k) =
      (modeCreationOperator k * modeCreationOperator k) * modeAnnihilationOperator k := by rw [mul_assoc]
    _ = 0 * modeAnnihilationOperator k := by rw [modeCreationOperator_sq_zero]
    _ = 0 := by rw [zero_mul]

/-- Action on annihilation operator: $N_k v_k = 0$. -/
theorem modeNumber_annihilation (k : ℕ) :
    modeNumberOperator k * modeAnnihilationOperator k = 0 := by
  unfold modeNumberOperator
  calc
    modeCreationOperator k * modeAnnihilationOperator k * modeAnnihilationOperator k =
      modeCreationOperator k * (modeAnnihilationOperator k * modeAnnihilationOperator k) := by rw [mul_assoc]
    _ = modeCreationOperator k * 0 := by rw [modeAnnihilationOperator_sq_zero]
    _ = 0 := by rw [mul_zero]

/-- Annihilation action: $v_k N_k = v_k$. -/
theorem annihilation_modeNumber (k : ℕ) :
    modeAnnihilationOperator k * modeNumberOperator k = modeAnnihilationOperator k := by
  unfold modeNumberOperator
  have h_anticomm : modeAnnihilationOperator k * modeCreationOperator k =
      1 - modeCreationOperator k * modeAnnihilationOperator k := by
    have h := modeAnnihilationOperator_creationOperator_anticomm k
    have h_add : modeCreationOperator k * modeAnnihilationOperator k +
        modeAnnihilationOperator k * modeCreationOperator k = 1 := by
      rw [add_comm, h]
    exact eq_sub_of_add_eq' h_add
  calc
    modeAnnihilationOperator k * (modeCreationOperator k * modeAnnihilationOperator k) =
      (modeAnnihilationOperator k * modeCreationOperator k) * modeAnnihilationOperator k := by rw [mul_assoc]
    _ = (1 - modeCreationOperator k * modeAnnihilationOperator k) * modeAnnihilationOperator k := by rw [h_anticomm]
    _ = 1 * modeAnnihilationOperator k - (modeCreationOperator k * modeAnnihilationOperator k) * modeAnnihilationOperator k := by rw [sub_mul]
    _ = modeAnnihilationOperator k - modeCreationOperator k * (modeAnnihilationOperator k * modeAnnihilationOperator k) := by simp only [one_mul, mul_assoc]
    _ = modeAnnihilationOperator k - modeCreationOperator k * 0 := by rw [modeAnnihilationOperator_sq_zero]
    _ = modeAnnihilationOperator k := by rw [mul_zero, sub_zero]

/-- Commutator $[N_k, u_k] = u_k$. -/
theorem modeNumber_commutator_creation (k : ℕ) :
    modeNumberOperator k * modeCreationOperator k -
        modeCreationOperator k * modeNumberOperator k =
      modeCreationOperator k := by
  rw [modeNumber_creation, creation_modeNumber, sub_zero]

/-- Commutator $[N_k, v_k] = -v_k$. -/
theorem modeNumber_commutator_annihilation (k : ℕ) :
    modeNumberOperator k * modeAnnihilationOperator k -
        modeAnnihilationOperator k * modeNumberOperator k =
      - modeAnnihilationOperator k := by
  rw [modeNumber_annihilation, annihilation_modeNumber, zero_sub]

end InfoGeometry.Canonical.Cl11CommonFockCarrier
