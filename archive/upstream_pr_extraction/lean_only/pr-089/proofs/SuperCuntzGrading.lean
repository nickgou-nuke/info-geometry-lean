import proofs.ChiralCuntzInductive

/-!
# Supergraded Cuntz--Toeplitz layer

This is the theorem-honest algebraic super layer on top of the finite
Cuntz--Toeplitz tower.  It does **not** claim a complex `StarAlgHom` or C*-level
universal completion.  The grading is algebraic: a parity-preserving involution
acts by `+1` on even modes and `-1` on odd modes.

The construction is intentionally at the `CTAlg` level, where the induction
`Fin (2*n) → Fin (2*(n+1))` is canonical.
-/

noncomputable section

namespace SuperCuntzGrading

open AlgebraicCuntzToeplitzInductive
open ChiralCuntzInductive
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Algebraic parity sign for a finite chiral mode. -/
def paritySign {m : ℕ} (i : Fin m) : R :=
  if chiralParity i = 0 then 1 else -1

@[simp] theorem paritySign_sq {m : ℕ} (i : Fin m) :
    paritySign (R := R) i * paritySign (R := R) i = 1 := by
  unfold paritySign
  by_cases h : chiralParity i = 0 <;> simp [h]

/-- The parity sign is preserved by the chiral induction. -/
theorem paritySign_chiralStep (n : ℕ) (i : Fin (2 * n)) :
    paritySign (R := R) (chiralStep n i) = paritySign (R := R) i := by
  unfold paritySign
  rw [chiralStep_parity_preserving]

/-- The algebraic grading involution: even generators are fixed, odd generators
pick up a minus sign. -/
def gradeInvolution (n : ℕ) : CTAlg R (Fin (2 * n)) →ₐ[R] CTAlg R (Fin (2 * n)) :=
  lift (R := R) (A := CTAlg R (Fin (2 * n)))
    (fun i : Fin (2 * n) => paritySign (R := R) i • S (R := R) i)
    (fun i : Fin (2 * n) => paritySign (R := R) i • T (R := R) i)
    (by
      intro i j
      rw [smul_mul_smul, T_mul_S]
      by_cases h : i = j
      · subst j
        simp [paritySign_sq]
      · simp [h])

@[simp] theorem gradeInvolution_S (n : ℕ) (i : Fin (2 * n)) :
    gradeInvolution (R := R) n (S (R := R) i) = paritySign (R := R) i • S (R := R) i := by
  exact lift_S (R := R) (A := CTAlg R (Fin (2 * n)))
    (fun i : Fin (2 * n) => paritySign (R := R) i • S (R := R) i)
    (fun i : Fin (2 * n) => paritySign (R := R) i • T (R := R) i)
    (by
      intro i j
      rw [smul_mul_smul, T_mul_S]
      by_cases h : i = j
      · subst j
        simp [paritySign_sq]
      · simp [h]) i

@[simp] theorem gradeInvolution_T (n : ℕ) (i : Fin (2 * n)) :
    gradeInvolution (R := R) n (T (R := R) i) = paritySign (R := R) i • T (R := R) i := by
  exact lift_T (R := R) (A := CTAlg R (Fin (2 * n)))
    (fun i : Fin (2 * n) => paritySign (R := R) i • S (R := R) i)
    (fun i : Fin (2 * n) => paritySign (R := R) i • T (R := R) i)
    (by
      intro i j
      rw [smul_mul_smul, T_mul_S]
      by_cases h : i = j
      · subst j
        simp [paritySign_sq]
      · simp [h]) i

/-- Compatibility of the grading involution with the parity-preserving induction
on generators. -/
theorem gradeInvolution_step_S (n : ℕ) (i : Fin (2 * n)) :
    gradeInvolution (R := R) (n + 1)
        (chiralStepHom (R := R) n (S (R := R) i)) =
      chiralStepHom (R := R) n (gradeInvolution (R := R) n (S (R := R) i)) := by
  simp [paritySign_chiralStep]

/-- Compatibility of the grading involution with the parity-preserving induction
on adjoint/formal dual generators. -/
theorem gradeInvolution_step_T (n : ℕ) (i : Fin (2 * n)) :
    gradeInvolution (R := R) (n + 1)
        (chiralStepHom (R := R) n (T (R := R) i)) =
      chiralStepHom (R := R) n (gradeInvolution (R := R) n (T (R := R) i)) := by
  simp [paritySign_chiralStep]

/-- Boolean test for the odd/odd case in the supercommutator. -/
def bothOdd (p q : ℕ) : Prop := p % 2 = 1 ∧ q % 2 = 1

/-- Algebraic superbracket for declared homogeneous degrees.  For two odd
operators this is the anticommutator; otherwise it is the commutator. -/
def superBracket {A : Type*} [Ring A] (p q : ℕ) (x y : A) : A := by
  classical
  exact if bothOdd p q then x * y + y * x else x * y - y * x

@[simp] theorem superBracket_even_left {A : Type*} [Ring A] (q : ℕ) (x y : A) :
    superBracket (A := A) 0 q x y = x * y - y * x := by
  simp [superBracket, bothOdd]

@[simp] theorem superBracket_even_right {A : Type*} [Ring A] (p : ℕ) (x y : A) :
    superBracket (A := A) p 0 x y = x * y - y * x := by
  simp [superBracket, bothOdd]

@[simp] theorem superBracket_odd_odd {A : Type*} [Ring A] (x y : A) :
    superBracket (A := A) 1 1 x y = x * y + y * x := by
  simp [superBracket, bothOdd]

/-- Nambu--Gorkov/BdG-style doubled formal pair in a chiral Cuntz--Toeplitz stage. -/
structure NambuGorkovPair (R : Type*) [CommRing R] (n : ℕ) where
  particle : CTAlg R (Fin (2 * n))
  hole : CTAlg R (Fin (2 * n))

/-- Algebraic supercharge package.  The centrality/square-root laws are fields,
not manufactured by the bare Cuntz--Toeplitz relations. -/
structure SuperchargePackage (R : Type*) [CommRing R] (n : ℕ) where
  Qplus : CTAlg R (Fin (2 * n))
  Qminus : CTAlg R (Fin (2 * n))
  H : CTAlg R (Fin (2 * n))
  Z : CTAlg R (Fin (2 * n))
  Qplus_sq : Qplus * Qplus = H
  Qminus_sq : Qminus * Qminus = H
  odd_anticommutator_central_charge : Qplus * Qminus + Qminus * Qplus = Z
  Z_central : ∀ x : CTAlg R (Fin (2 * n)), Z * x = x * Z

#check paritySign
#check paritySign_chiralStep
#check gradeInvolution
#check gradeInvolution_S
#check gradeInvolution_T
#check gradeInvolution_step_S
#check gradeInvolution_step_T
#check superBracket
#check superBracket_odd_odd
#check NambuGorkovPair
#check SuperchargePackage

end SuperCuntzGrading
