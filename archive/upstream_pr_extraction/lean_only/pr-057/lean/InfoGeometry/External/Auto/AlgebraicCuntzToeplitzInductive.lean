import Mathlib.Tactic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Algebraic Cuntz--Toeplitz inductive step

The unital Cuntz relation `∑ SᵢTᵢ = 1` is not canonically compatible with
`n ↦ n+1` by simply adding one generator: the old range projections sum to
`1 - S_new T_new`, not `1`.  The canonical finite-stage induction therefore
lives first at the Cuntz--Toeplitz level, where only `TᵢSⱼ = δᵢⱼ` is imposed.

This file constructs the tensor-algebra/RingQuot Cuntz--Toeplitz quotient and
proves the canonical one-step map `n → n+1` induced by `Fin.castSucc`.
-/

noncomputable section

namespace AlgebraicCuntzToeplitzInductive

open TensorAlgebra

/-- Formal Cuntz--Toeplitz letters. -/
inductive CTLetter (ι : Type*) where
  | s : ι → CTLetter ι
  | t : ι → CTLetter ι
  deriving DecidableEq, Repr

section Algebraic

variable {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]

abbrev Gen (R : Type*) [CommSemiring R] (ι : Type*) := CTLetter ι →₀ R
abbrev TAlg (R : Type*) [CommSemiring R] (ι : Type*) := TensorAlgebra R (Gen R ι)

def letter (a : CTLetter ι) : Gen R ι := Finsupp.single a 1

def S₀ (i : ι) : TAlg R ι := TensorAlgebra.ι R (letter (R := R) (CTLetter.s i))
def T₀ (i : ι) : TAlg R ι := TensorAlgebra.ι R (letter (R := R) (CTLetter.t i))

/-- Cuntz--Toeplitz relation: orthogonality/isometry only, no partition relation. -/
inductive Rel : TAlg R ι → TAlg R ι → Prop
  | ortho (i j : ι) : Rel (T₀ (R := R) i * S₀ (R := R) j) (if i = j then 1 else 0)

/-- Algebraic Cuntz--Toeplitz quotient. -/
def CTAlg (R : Type*) [CommSemiring R] (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  RingQuot (@Rel R ι _ _)
deriving Inhabited, Semiring, Algebra R

def mk : TAlg R ι →ₐ[R] CTAlg R ι := RingQuot.mkAlgHom R (@Rel R ι _ _)

def S (i : ι) : CTAlg R ι := mk (R := R) (S₀ (R := R) i)
def T (i : ι) : CTAlg R ι := mk (R := R) (T₀ (R := R) i)

theorem T_mul_S (i j : ι) : T (R := R) i * S (R := R) j = if i = j then 1 else 0 := by
  change mk (R := R) (T₀ (R := R) i) * mk (R := R) (S₀ (R := R) j) = _
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel R (Rel.ortho (R := R) i j)

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

def evalGen (s t : ι → A) : Gen R ι →ₗ[R] A :=
  Finsupp.linearCombination R (fun a : CTLetter ι =>
    match a with
    | .s i => s i
    | .t i => t i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem evalGen_s (s t : ι → A) (i : ι) :
    evalGen (R := R) s t (letter (R := R) (CTLetter.s i)) = s i := by
  simp [evalGen, letter]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem evalGen_t (s t : ι → A) (i : ι) :
    evalGen (R := R) s t (letter (R := R) (CTLetter.t i)) = t i := by
  simp [evalGen, letter]

def liftCondition (s t : ι → A)
    (h_ortho : ∀ i j, t i * s j = if i = j then 1 else 0) :
    ∀ ⦃x y : TAlg R ι⦄, Rel x y →
      (TensorAlgebra.lift R (evalGen (R := R) s t)) x =
        (TensorAlgebra.lift R (evalGen (R := R) s t)) y := by
  intro x y h
  cases h with
  | ortho i j =>
      simp [S₀, T₀, h_ortho]

/-- Universal map out of the algebraic Cuntz--Toeplitz quotient. -/
def lift (s t : ι → A)
    (h_ortho : ∀ i j, t i * s j = if i = j then 1 else 0) : CTAlg R ι →ₐ[R] A :=
  RingQuot.liftAlgHom R
    ⟨TensorAlgebra.lift R (evalGen (R := R) s t), liftCondition (R := R) s t h_ortho⟩

/-- Generator evaluation for `S`. -/
theorem lift_S (s t : ι → A)
    (h_ortho : ∀ i j, t i * s j = if i = j then 1 else 0) (i : ι) :
    lift (R := R) s t h_ortho (S (R := R) i) = s i := by
  calc
    lift (R := R) s t h_ortho (S (R := R) i)
        = (TensorAlgebra.lift R (evalGen (R := R) s t)) (S₀ (R := R) i) := by
      change ((RingQuot.liftAlgHom R)
          ⟨TensorAlgebra.lift R (evalGen (R := R) s t), liftCondition (R := R) s t h_ortho⟩)
          ((RingQuot.mkAlgHom R (@Rel R ι _ _)) (S₀ (R := R) i)) =
        (TensorAlgebra.lift R (evalGen (R := R) s t)) (S₀ (R := R) i)
      exact RingQuot.liftAlgHom_mkAlgHom_apply R
        (TensorAlgebra.lift R (evalGen (R := R) s t))
        (liftCondition (R := R) s t h_ortho)
        (S₀ (R := R) i)
    _ = s i := by simp [S₀]

/-- Generator evaluation for `T`. -/
theorem lift_T (s t : ι → A)
    (h_ortho : ∀ i j, t i * s j = if i = j then 1 else 0) (i : ι) :
    lift (R := R) s t h_ortho (T (R := R) i) = t i := by
  calc
    lift (R := R) s t h_ortho (T (R := R) i)
        = (TensorAlgebra.lift R (evalGen (R := R) s t)) (T₀ (R := R) i) := by
      change ((RingQuot.liftAlgHom R)
          ⟨TensorAlgebra.lift R (evalGen (R := R) s t), liftCondition (R := R) s t h_ortho⟩)
          ((RingQuot.mkAlgHom R (@Rel R ι _ _)) (T₀ (R := R) i)) =
        (TensorAlgebra.lift R (evalGen (R := R) s t)) (T₀ (R := R) i)
      exact RingQuot.liftAlgHom_mkAlgHom_apply R
        (TensorAlgebra.lift R (evalGen (R := R) s t))
        (liftCondition (R := R) s t h_ortho)
        (T₀ (R := R) i)
    _ = t i := by simp [T₀]

end Lift

end Algebraic

section InductiveStep

variable {R : Type*} [CommSemiring R]

/-- Canonical Cuntz--Toeplitz one-step inclusion, induced by `Fin.castSucc`. -/
def step (n : ℕ) : CTAlg R (Fin n) →ₐ[R] CTAlg R (Fin (n + 1)) :=
  lift (R := R) (A := CTAlg R (Fin (n + 1)))
    (fun i : Fin n => S (R := R) (Fin.castSucc i))
    (fun i : Fin n => T (R := R) (Fin.castSucc i))
    (by
      intro i j
      rw [T_mul_S]
      by_cases h : i = j
      · subst j
        simp
      · have hcast : Fin.castSucc i ≠ Fin.castSucc j := fun hc => h (Fin.castSucc_injective n hc)
        simp [h, hcast])

@[simp] theorem step_S (n : ℕ) (i : Fin n) :
    step (R := R) n (S (R := R) i) = S (R := R) (Fin.castSucc i) := by
  exact lift_S (R := R) (A := CTAlg R (Fin (n + 1)))
    (fun i : Fin n => S (R := R) (Fin.castSucc i))
    (fun i : Fin n => T (R := R) (Fin.castSucc i))
    (by
      intro i j
      rw [T_mul_S]
      by_cases h : i = j
      · subst j
        simp
      · have hcast : Fin.castSucc i ≠ Fin.castSucc j := fun hc => h (Fin.castSucc_injective n hc)
        simp [h, hcast]) i

@[simp] theorem step_T (n : ℕ) (i : Fin n) :
    step (R := R) n (T (R := R) i) = T (R := R) (Fin.castSucc i) := by
  exact lift_T (R := R) (A := CTAlg R (Fin (n + 1)))
    (fun i : Fin n => S (R := R) (Fin.castSucc i))
    (fun i : Fin n => T (R := R) (Fin.castSucc i))
    (by
      intro i j
      rw [T_mul_S]
      by_cases h : i = j
      · subst j
        simp
      · have hcast : Fin.castSucc i ≠ Fin.castSucc j := fun hc => h (Fin.castSucc_injective n hc)
        simp [h, hcast]) i

end InductiveStep

#check CTAlg
#check T_mul_S
#check step
#check step_S
#check step_T

end AlgebraicCuntzToeplitzInductive
