import Mathlib
import InfoGeometry.Canonical.Cl55V4SpinorFragmentation
import InfoGeometry.Canonical.TrialitySpin8Permutations

/-!
# V4 Semidirect S₃ Bridge

Lean bridge for the finite model of the `V₄ ⋊ S₃` signature acting on the
three triality sectors (vector, spinor⁺, spinor⁻).
-/

namespace InfoGeometry.Canonical.V4SemidirectS3Bridge

open InfoGeometry.Canonical.TrialitySpin8Permutations

/-- Four-element Klein four model used in the Cl(5,5) boundary layers. -/
inductive V4Element
  | I | J | S | JS
  deriving DecidableEq, Repr, Fintype

open V4Element

instance : One V4Element := ⟨I⟩

instance : Mul V4Element where
  mul
    | I, e => e
    | e, I => e
    | J, J => I
    | J, S => JS
    | J, JS => S
    | S, J => JS
    | S, S => I
    | S, JS => J
    | JS, J => S
    | JS, S => J
    | JS, JS => I

instance : Inv V4Element where
  inv x := x

instance : Group V4Element where
  mul := (· * ·)
  one := I
  inv := Inv.inv
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide
  one_mul := by
    intro a
    cases a <;> decide
  mul_one := by
    intro a
    cases a <;> decide
  inv_mul_cancel := by
    intro a
    cases a <;> decide

instance : CommGroup V4Element where
  mul_comm := by
    intro a b
    cases a <;> cases b <;> decide

@[simp] theorem v4_mul_I_left (x : V4Element) : I * x = x := by
  cases x <;> decide

@[simp] theorem v4_mul_I_right (x : V4Element) : x * I = x := by
  cases x <;> decide

@[simp] theorem v4_inv (x : V4Element) : x⁻¹ = x := by
  cases x <;> decide

/-- Re-embed a sector index into the abstract V₄ label. -/
def ofV4Label (i : Fin 3) : V4Element :=
  match i with
  | ⟨0, _⟩ => J
  | ⟨1, _⟩ => S
  | ⟨2, _⟩ => JS

@[simp] theorem ofV4Label_zero : ofV4Label 0 = J := by
  rfl

@[simp] theorem ofV4Label_one : ofV4Label 1 = S := by
  rfl

@[simp] theorem ofV4Label_two : ofV4Label 2 = JS := by
  rfl

/-- Canonical `S₃` sector action on the V₄ labels.

This action is the 3-cycle `J ↦ S ↦ JS ↦ J`.
-/
def trialityAction (σ : Equiv.Perm (Fin 3)) : V4Element → V4Element
  | I => I
  | J => ofV4Label (σ 0)
  | S => ofV4Label (σ 1)
  | JS => ofV4Label (σ 2)

/-- `ofV4Label` is equivariant for the action by definition. -/
theorem trialityAction_ofV4Label (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    trialityAction σ (ofV4Label i) = ofV4Label (σ i) := by
  fin_cases i <;> simp [ofV4Label, trialityAction]

instance : SMul (Equiv.Perm (Fin 3)) V4Element where
  smul := trialityAction

instance : MulAction (Equiv.Perm (Fin 3)) V4Element where
  one_smul := by
    intro x
    cases x <;> rfl
  mul_smul := by
    intro σ τ x
    cases x with
    | I => rfl
    | J =>
        calc
          (σ * τ) • (J : V4Element) = ofV4Label ((σ * τ) 0) := by rfl
          _ = ofV4Label (σ (τ 0)) := by rfl
          _ = σ • ofV4Label (τ 0) := by
            simpa using (trialityAction_ofV4Label (σ := σ) (i := τ 0)).symm
          _ = σ • (τ • (J : V4Element)) := by rfl
    | S =>
        calc
          (σ * τ) • (S : V4Element) = ofV4Label ((σ * τ) 1) := by rfl
          _ = ofV4Label (σ (τ 1)) := by rfl
          _ = σ • ofV4Label (τ 1) := by
            simpa using (trialityAction_ofV4Label (σ := σ) (i := τ 1)).symm
          _ = σ • (τ • (S : V4Element)) := by rfl
    | JS =>
        calc
          (σ * τ) • (JS : V4Element) = ofV4Label ((σ * τ) 2) := by rfl
          _ = ofV4Label (σ (τ 2)) := by rfl
          _ = σ • ofV4Label (τ 2) := by
            simpa using (trialityAction_ofV4Label (σ := σ) (i := τ 2)).symm
          _ = σ • (τ • (JS : V4Element)) := by rfl

@[simp] theorem trialityAction_I (σ : Equiv.Perm (Fin 3)) :
    σ • (I : V4Element) = I := by
  rfl

@[simp] theorem trialityAction_cycle_J :
    trialityCycle • (J : V4Element) = S := by
  decide

@[simp] theorem trialityAction_cycle_S :
    trialityCycle • (S : V4Element) = JS := by
  decide

@[simp] theorem trialityAction_cycle_JS :
    trialityCycle • (JS : V4Element) = J := by
  decide

@[simp] theorem trialityAction_cube :
    (trialityCycle ^ 3 : Equiv.Perm (Fin 3)) • (J : V4Element) = J := by
  simp [trialityCycle_pow_three]

@[simp] theorem trialityAction_cube_id (x : V4Element) :
    (trialityCycle ^ 3 : Equiv.Perm (Fin 3)) • x = x := by
  cases x <;> simp [trialityCycle_pow_three]

@[simp] theorem trialityCycle_pow_three_eq :
    (trialityCycle ^ 3 : Equiv.Perm (Fin 3)) = 1 := by
  simpa using trialityCycle_pow_three

/-- Multiplicative compatibility of the V₄ action by triality. -/
theorem trialityAction_mul (σ : Equiv.Perm (Fin 3)) (x y : V4Element) :
    σ • (x * y) = (σ • x) * (σ • y) := by
  cases x <;> cases y <;> fin_cases σ <;> decide

/-- Helper inverse-move lemmas for smul. -/
theorem trialityAction_inv_smul (σ : Equiv.Perm (Fin 3)) (x : V4Element) :
    σ • (σ⁻¹ • x) = x := by
  simpa using (smul_inv_smul σ x)

theorem trialityAction_smul_inv (σ : Equiv.Perm (Fin 3)) (x : V4Element) :
    σ⁻¹ • (σ • x) = x := by
  simpa using (inv_smul_smul σ x)

@[simp] theorem v4_sq (x : V4Element) : x * x = 1 := by
  cases x <;> decide

@[simp] theorem trialityAction_one (σ : Equiv.Perm (Fin 3)) : σ • (1 : V4Element) = 1 := by
  rfl

/-- Semidirect-product-style carrier set of the finite spine `V₄ ⋊ S₃`. -/
def V4SemidirectS3 := V4Element × Equiv.Perm (Fin 3)

/-- Multiplication `⟨v₁,σ₁⟩ * ⟨v₂,σ₂⟩ = ⟨v₁ * (σ₁ • v₂), σ₁σ₂⟩`. -/
def v4SemidirectMul (x y : V4SemidirectS3) : V4SemidirectS3 :=
  (x.1 * (x.2 • y.1), x.2 * y.2)

instance : One V4SemidirectS3 := ⟨(I, 1)⟩

instance : Inv V4SemidirectS3 :=
  ⟨fun x => (x.2⁻¹ • x.1⁻¹, x.2⁻¹)⟩

instance : Mul V4SemidirectS3 where
  mul := v4SemidirectMul

@[simp] theorem v4SemidirectMul_def (x y : V4SemidirectS3) :
    x * y = (x.1 * (x.2 • y.1), x.2 * y.2) := rfl

@[simp] theorem v4Semidirect_inv_def (x : V4SemidirectS3) :
    x⁻¹ = (x.2⁻¹ • x.1⁻¹, x.2⁻¹) := rfl

instance : Group V4SemidirectS3 where
  mul_assoc := by
    intro a b c
    apply Prod.ext <;> simp [v4SemidirectMul, trialityAction_mul, mul_assoc, smul_smul]
  one_mul := by
    intro a
    apply Prod.ext <;> simp [v4SemidirectMul]
  mul_one := by
    intro a
    apply Prod.ext <;> simp [v4SemidirectMul]
  inv_mul_cancel := by
    intro a
    apply Prod.ext
    · have hmul :
        (a.2⁻¹ • a.1⁻¹) * (a.2⁻¹ • a.1) = a.2⁻¹ • (a.1⁻¹ * a.1) := by
        simpa using (trialityAction_mul a.2⁻¹ a.1⁻¹ a.1).symm
      calc
        ((a.2⁻¹ • a.1⁻¹) * (a.2⁻¹ • a.1)) = a.2⁻¹ • (a.1⁻¹ * a.1) := hmul
        _ = a.2⁻¹ • (1 : V4Element) := by simp [v4_inv, v4_sq]
        _ = 1 := by simp
    · simp [v4Semidirect_inv_def, v4SemidirectMul]

instance : Inhabited V4SemidirectS3 := ⟨1⟩

/-- Left embedding `V₄ ↪ V₄ ⋊ S₃`. -/
def inl (x : V4Element) : V4SemidirectS3 := (x, 1)

/-- Right embedding `S₃ ↪ V₄ ⋊ S₃`. -/
def inr (σ : Equiv.Perm (Fin 3)) : V4SemidirectS3 := (I, σ)

@[simp] theorem inl_mul (x y : V4Element) :
    inl x * inl y = inl (x * y) := by
  simp [inl, v4SemidirectMul]

@[simp] theorem inr_mul (σ τ : Equiv.Perm (Fin 3)) :
    inr σ * inr τ = inr (σ * τ) := by
  rfl

/-- Conjugation formula in the semidirect model. -/
theorem inr_conjugates_inl (σ : Equiv.Perm (Fin 3)) (x : V4Element) :
    inr σ * inl x * (inr σ⁻¹) = inl (σ • x) := by
  apply Prod.ext <;> simp [inl, inr, v4SemidirectMul, mul_assoc, trialityAction_smul_inv]

/-- Embedding-powers identity into the `S₃`-only subgroup. -/
theorem inr_pow_eq (σ : Equiv.Perm (Fin 3)) : ∀ n : ℕ, (inr σ : V4SemidirectS3) ^ n = inr (σ ^ n)
  | 0 => by rfl
  | n + 1 => by
      calc
        (inr σ : V4SemidirectS3) ^ (n + 1) = (inr σ : V4SemidirectS3) ^ n * inr σ := by
          simp [pow_succ]
        _ = inr (σ ^ n) * inr σ := by
          rw [inr_pow_eq σ n]
        _ = inr ((σ ^ n) * σ) := by rfl
        _ = inr (σ ^ (n + 1)) := by simp [pow_succ]

/-- The 3-cycle sector automorphism has order three. -/
theorem cycle_order_three : (inr trialityCycle : V4SemidirectS3) ^ 3 = 1 := by
  calc
    (inr trialityCycle : V4SemidirectS3) ^ 3 = inr (trialityCycle ^ 3) := by
      simpa using inr_pow_eq (σ := trialityCycle) 3
    _ = inr (1 : Equiv.Perm (Fin 3)) := by
      simp [trialityCycle_pow_three_eq]
    _ = 1 := by rfl

/-- Non-triviality: order is not two on the `S₃` component. -/
theorem cycle_not_two : (inr trialityCycle : V4SemidirectS3) ^ 2 ≠ 1 := by
  intro h
  have h' : (trialityCycle ^ 2 : Equiv.Perm (Fin 3)) = 1 := by
    simpa using congrArg Prod.snd h
  have hcycle : (trialityCycle ^ 2 : Equiv.Perm (Fin 3)) ≠ (1 : Equiv.Perm (Fin 3)) := by
    decide
  exact hcycle h'

/-- Explicit conjugation on labels for the 3-cycle. -/
theorem cycle_conjugation_J :
    inr trialityCycle * inl J * (inr trialityCycle⁻¹) = inl S := by
  simpa [inr, inl] using (inr_conjugates_inl trialityCycle J)

theorem cycle_conjugation_S :
    inr trialityCycle * inl S * (inr trialityCycle⁻¹) = inl JS := by
  simpa [inr, inl] using (inr_conjugates_inl trialityCycle S)

theorem cycle_conjugation_JS :
    inr trialityCycle * inl JS * (inr trialityCycle⁻¹) = inl J := by
  simpa [inr, inl] using (inr_conjugates_inl trialityCycle JS)

/-- Triality triplet under one application of the 3-cycle. -/
theorem semidirect_nontrivial_triplet :
    (trialityCycle • (J : V4Element), trialityCycle • (S : V4Element),
      trialityCycle • (JS : V4Element)) = (S, JS, J) := by
  simp [trialityAction_cycle_J, trialityAction_cycle_S, trialityAction_cycle_JS]

end InfoGeometry.Canonical.V4SemidirectS3Bridge
