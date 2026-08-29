import Mathlib
import InfoGeometry.Exceptional.SplitOctonionZornReal

/-!
# Finite `J₃` carrier over the existing real Zorn model

This file introduces only the finite carrier and its hermitian predicate.
The entry multiplication is deliberately not promoted to an associative
matrix algebra: the Zorn multiplication is non-associative.  Consequently,
the Jordan product and its identity must be proved on a separately specified
hermitian subcarrier.
-/

namespace InfoGeometry.Exceptional.FiniteJ3Zorn

open InfoGeometry.Exceptional.RealZorn

theorem zorn_add_assoc (A B C : ZornMatrixReal) :
    (A + B) + C = A + (B + C) := by
  change ZornMatrixReal.add_mat (ZornMatrixReal.add_mat A B) C =
         ZornMatrixReal.add_mat A (ZornMatrixReal.add_mat B C)
  apply ZornMatrixReal.ext
  · dsimp [ZornMatrixReal.add_mat, add]; ring
  · dsimp [ZornMatrixReal.add_mat, add]; ring
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, add]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, add]; ring)

theorem zorn_add_comm (A B : ZornMatrixReal) :
    A + B = B + A := by
  change ZornMatrixReal.add_mat A B = ZornMatrixReal.add_mat B A
  apply ZornMatrixReal.ext
  · dsimp [ZornMatrixReal.add_mat, add]; ring
  · dsimp [ZornMatrixReal.add_mat, add]; ring
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, add]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, add]; ring)

theorem zorn_add_zero (A : ZornMatrixReal) :
    A + 0 = A := by
  change ZornMatrixReal.add_mat A ZornMatrixReal.zero = A
  apply ZornMatrixReal.ext
  · dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.zero, add]; ring
  · dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.zero, add]; ring
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.zero, add]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.zero, add]; ring)

theorem zorn_zero_add (A : ZornMatrixReal) :
    0 + A = A := by
  rw [zorn_add_comm, zorn_add_zero]

theorem zorn_add_neg (A : ZornMatrixReal) :
    A + (-A) = 0 := by
  change ZornMatrixReal.add_mat A (ZornMatrixReal.neg_mat A) = ZornMatrixReal.zero
  apply ZornMatrixReal.ext
  · dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.neg_mat, ZornMatrixReal.zero, add, smul]; ring
  · dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.neg_mat, ZornMatrixReal.zero, add, smul]; ring
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.neg_mat, ZornMatrixReal.zero, add, smul]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.neg_mat, ZornMatrixReal.zero, add, smul]; ring)

inductive CausalType
  | timelike
  | lightlike
  | spacelike
  deriving DecidableEq, Repr

noncomputable def causalType (q : ℝ) : CausalType :=
  if q < 0 then CausalType.timelike
  else if q = 0 then CausalType.lightlike
  else CausalType.spacelike

theorem causalType_eq_timelike {q : ℝ} (hq : q < 0) :
    causalType q = CausalType.timelike := by
  simp [causalType, hq]

theorem causalType_eq_lightlike {q : ℝ} (hq : q = 0) :
    causalType q = CausalType.lightlike := by
  simp [causalType, hq]

theorem causalType_eq_spacelike {q : ℝ} (hq : 0 < q) :
    causalType q = CausalType.spacelike := by
  simp [causalType, not_lt_of_ge (le_of_lt hq), ne_of_gt hq]

abbrev J3 := Fin 3 → Fin 3 → ZornMatrixReal

/-- Halving a Zorn matrix by scalar multiplication 1/2. -/
noncomputable def zornHalf (A : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a / 2
    b := A.b / 2
    u := smul (1 / 2) A.u
    v := smul (1 / 2) A.v }

/-! The standard Zorn conjugation swaps the diagonal entries and negates both
off-diagonal vectors. -/
def zornConj (A : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.b
    b := A.a
    u := smul (-1) A.u
    v := smul (-1) A.v }

theorem zornConj_zero : zornConj 0 = 0 := by
  change zornConj ZornMatrixReal.zero = ZornMatrixReal.zero
  apply ZornMatrixReal.ext
  · rfl
  · rfl
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, smul, ZornMatrixReal.zero]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, smul, ZornMatrixReal.zero]; ring)

theorem zornConj_involutive (A : ZornMatrixReal) :
    zornConj (zornConj A) = A := by
  apply ZornMatrixReal.ext
  · rfl
  · rfl
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, smul]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, smul]; ring)

theorem zornConj_norm (A : ZornMatrixReal) :
    (zornConj A).norm = A.norm := by
  dsimp [zornConj, ZornMatrixReal.norm, dot, smul]
  ring

theorem zornConj_causalType (A : ZornMatrixReal) :
    causalType (zornConj A).norm = causalType A.norm := by
  rw [zornConj_norm]

theorem zornConj_add (A B : ZornMatrixReal) :
    zornConj (A + B) = zornConj A + zornConj B := by
  change zornConj (ZornMatrixReal.add_mat A B) = ZornMatrixReal.add_mat (zornConj A) (zornConj B)
  apply ZornMatrixReal.ext
  · rfl
  · rfl
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, ZornMatrixReal.add_mat, add, smul]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, ZornMatrixReal.add_mat, add, smul]; ring)

theorem zornConj_half (A : ZornMatrixReal) :
    zornConj (zornHalf A) = zornHalf (zornConj A) := by
  apply ZornMatrixReal.ext
  · rfl
  · rfl
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, zornHalf, smul]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, zornHalf, smul]; ring)

theorem zornConj_mul_reverse (A B : ZornMatrixReal) :
    zornConj (A * B) = zornConj B * zornConj A := by
  change zornConj (ZornMatrixReal.mul A B) = ZornMatrixReal.mul (zornConj B) (zornConj A)
  apply ZornMatrixReal.ext
  · dsimp [zornConj, ZornMatrixReal.mul, dot, smul]; ring
  · dsimp [zornConj, ZornMatrixReal.mul, dot, smul]; ring
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, ZornMatrixReal.mul, dot, cross, add, sub, smul]; ring)
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (dsimp [zornConj, ZornMatrixReal.mul, dot, cross, add, sub, smul]; ring)

def hermitian (X : J3) : Prop :=
  ∀ i j, X i j = X j i

def zero : J3 := fun _ _ => 0

@[simp] theorem zero_apply (i j : Fin 3) : zero i j = 0 := rfl

theorem zero_hermitian : hermitian zero := by
  intro i j
  rfl

/-! Correct hermitian symmetry for the Zorn involution. -/
def hermitianStar (X : J3) : Prop :=
  ∀ i j, X i j = zornConj (X j i)

def HermitianJ3 := {X : J3 // hermitianStar X}

@[ext] theorem HermitianJ3_ext {X Y : HermitianJ3}
    (h : X.1 = Y.1) : X = Y := by
  exact Subtype.ext h

def j3RawMul (X Y : J3) (i k : Fin 3) : ZornMatrixReal :=
  X i 0 * Y 0 k + X i 1 * Y 1 k + X i 2 * Y 2 k

noncomputable def jordanProduct (X Y : J3) : J3 := fun i k =>
  zornHalf (j3RawMul X Y i k + j3RawMul Y X i k)

@[simp] theorem jordanProduct_apply (X Y : J3) (i k : Fin 3) :
    jordanProduct X Y i k =
      zornHalf (j3RawMul X Y i k + j3RawMul Y X i k) := rfl

theorem jordanProduct_comm (X Y : J3) :
    jordanProduct X Y = jordanProduct Y X := by
  funext i k
  dsimp [jordanProduct]
  rw [zorn_add_comm (j3RawMul X Y i k) (j3RawMul Y X i k)]

theorem zornConj_j3RawMul_transpose
    (X Y : HermitianJ3) (i k : Fin 3) :
    zornConj (j3RawMul X.1 Y.1 i k) =
      j3RawMul Y.1 X.1 k i := by
  fin_cases i <;> fin_cases k
  all_goals
    simp [j3RawMul, zornConj_add, zornConj_mul_reverse,
      ← X.property, ← Y.property]

theorem hermitianStar_reflect (X : J3) (hX : hermitianStar X) :
    ∀ i j, X j i = zornConj (X i j) := by
  intro i j
  have h := hX i j
  have h_conj := congr_arg zornConj h
  rw [zornConj_involutive] at h_conj
  exact h_conj.symm

@[ext] theorem J3_ext {X Y : J3} (h : ∀ i j, X i j = Y i j) : X = Y := by
  funext i j
  exact h i j

theorem zero_hermitianStar : hermitianStar zero := by
  intro i j
  dsimp [zero]
  rw [zornConj_zero]

def hermitianZero : HermitianJ3 := ⟨zero, zero_hermitianStar⟩

@[simp] theorem hermitianZero_val :
    (hermitianZero : HermitianJ3).1 = zero := rfl

def identity : J3 := fun i j => if i = j then 1 else 0

theorem identity_hermitian : hermitian identity := by
  intro i j
  dsimp [identity]
  by_cases h : i = j
  · subst h; rfl
  · have hne : j ≠ i := Ne.symm h
    simp [h, hne]

theorem hermitian_transpose (X : J3) (hX : hermitian X) :
    ∀ i j, X j i = X i j := by
  intro i j
  exact hX j i

end InfoGeometry.Exceptional.FiniteJ3Zorn
