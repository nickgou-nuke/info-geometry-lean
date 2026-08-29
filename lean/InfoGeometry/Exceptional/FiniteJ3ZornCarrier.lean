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
  apply ZornMatrixReal.ext <;>
    dsimp [ZornMatrixReal.add_mat, add]
    <;> ring

theorem zorn_add_comm (A B : ZornMatrixReal) :
    A + B = B + A := by
  apply ZornMatrixReal.ext <;>
    dsimp [ZornMatrixReal.add_mat, add]
    <;> ring

theorem zorn_add_zero (A : ZornMatrixReal) :
    A + 0 = A := by
  apply ZornMatrixReal.ext <;>
    dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.zero, add, zero]
    <;> ring

theorem zorn_zero_add (A : ZornMatrixReal) :
    0 + A = A := by
  rw [zorn_add_comm, zorn_add_zero]

theorem zorn_add_neg (A : ZornMatrixReal) :
    A + (-A) = 0 := by
  apply ZornMatrixReal.ext <;>
    dsimp [ZornMatrixReal.add_mat, ZornMatrixReal.neg_mat,
      ZornMatrixReal.zero, add, smul]
    <;> ring

inductive CausalType
  | timelike
  | lightlike
  | spacelike
  deriving DecidableEq, Repr

def causalType (q : ℝ) : CausalType :=
  if q < 0 then CausalType.timelike
  else if q = 0 then CausalType.lightlike
  else CausalType.spacelike

theorem causalType_eq_timelike {q : ℝ} (hq : q < 0) :
    causalType q = CausalType.timelike := by
  simp [causalType, hq]

theorem causalType_eq_lightlike {q : ℝ} (hq : q = 0) :
    causalType q = CausalType.lightlike := by
  simp [causalType, not_lt_of_ge (le_of_eq hq), hq]

theorem causalType_eq_spacelike {q : ℝ} (hq : 0 < q) :
    causalType q = CausalType.spacelike := by
  simp [causalType, not_lt_of_ge (le_of_lt hq), ne_of_gt hq]

abbrev J3 := Fin 3 → Fin 3 → ZornMatrixReal

/-! The standard Zorn conjugation swaps the diagonal entries and negates both
off-diagonal vectors. -/
def zornConj (A : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.b
    b := A.a
    u := smul (-1) A.u
    v := smul (-1) A.v }

theorem zornConj_involutive (A : ZornMatrixReal) :
    zornConj (zornConj A) = A := by
  apply ZornMatrixReal.ext
  · rfl
  · rfl
  · dsimp [zornConj, smul]
    congr 1 <;> ring
  · dsimp [zornConj, smul]
    congr 1 <;> ring

theorem zornConj_norm (A : ZornMatrixReal) :
    (zornConj A).norm = A.norm := by
  dsimp [zornConj, ZornMatrixReal.norm, dot, smul]
  ring

theorem zornConj_causalType (A : ZornMatrixReal) :
    causalType (zornConj A).norm = causalType A.norm := by
  rw [zornConj_norm]

theorem zornConj_add (A B : ZornMatrixReal) :
    zornConj (A + B) = zornConj A + zornConj B := by
  apply ZornMatrixReal.ext <;>
    dsimp [zornConj, ZornMatrixReal.add_mat, add, smul]
    <;> ring

theorem zornConj_half (A : ZornMatrixReal) :
    zornConj (zornHalf A) = zornHalf (zornConj A) := by
  apply ZornMatrixReal.ext <;>
    dsimp [zornConj, zornHalf, smul]
    <;> ring

theorem zornConj_mul_reverse (A B : ZornMatrixReal) :
    zornConj (A * B) = zornConj B * zornConj A := by
  apply ZornMatrixReal.ext <;>
    dsimp [zornConj, ZornMatrixReal.mul, dot, cross, add, sub, smul]
    <;> ring


def hermitian (X : J3) : Prop :=
  ∀ i j, X i j = X j i

def zero : J3 := fun _ _ => 0

@[simp] theorem zero_apply (i j : Fin 3) : zero i j = 0 := rfl

theorem zero_hermitian : hermitian zero := by
  intro i j
  rfl

/-! Correct hermitian symmetry for the Zorn involution.  The earlier
`hermitian` predicate is retained as the raw transpose readout; this predicate
is the one appropriate for a conjugated finite Jordan carrier. -/
def hermitianStar (X : J3) : Prop :=
  ∀ i j, X i j = zornConj (X j i)

def HermitianJ3 := {X : J3 // hermitianStar X}

@[ext] theorem HermitianJ3_ext {X Y : HermitianJ3}
    (h : (X : J3) = (Y : J3)) : X = Y := by
  exact Subtype.ext h

/-! Explicit finite 3×3 multiplication.  The three summands are written out
because the current Zorn carrier does not yet provide an additive-group
instance required by the generic matrix API. -/
def zornHalf (A : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a / 2
    b := A.b / 2
    u := smul (1 / 2) A.u
    v := smul (1 / 2) A.v }

def j3RawMul (X Y : J3) (i k : Fin 3) : ZornMatrixReal :=
  X i 0 * Y 0 k + X i 1 * Y 1 k + X i 2 * Y 2 k

def jordanProduct (X Y : J3) : J3 := fun i k =>
  zornHalf (j3RawMul X Y i k + j3RawMul Y X i k)

@[simp] theorem jordanProduct_apply (X Y : J3) (i k : Fin 3) :
    jordanProduct X Y i k =
      zornHalf (j3RawMul X Y i k + j3RawMul Y X i k) := rfl

theorem jordanProduct_comm (X Y : J3) :
    jordanProduct X Y = jordanProduct Y X := by
  funext i k
  apply ZornMatrixReal.ext
  all_goals
    dsimp [jordanProduct, j3RawMul, zornHalf, ZornMatrixReal.add_mat,
      ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring


theorem hermitianStar_reflect (X : J3) (hX : hermitianStar X) :
    ∀ i j, X j i = zornConj (X i j) := by
  intro i j
  rw [hX j i, zornConj_involutive]

@[ext] theorem J3_ext {X Y : J3} (h : ∀ i j, X i j = Y i j) : X = Y := by
  funext i j
  exact h i j

theorem zero_hermitianStar : hermitianStar zero := by
  intro i j
  apply ZornMatrixReal.ext
  · rfl
  · rfl
  · dsimp [zero, zornConj, smul]
    congr 1 <;> ring
  · dsimp [zero, zornConj, smul]
    congr 1 <;> ring

def hermitianZero : HermitianJ3 := ⟨zero, zero_hermitianStar⟩

@[simp] theorem hermitianZero_val :
    (hermitianZero : HermitianJ3).1 = zero := rfl

def identity : J3 := fun i j => if i = j then 1 else 0

theorem identity_hermitian : hermitian identity := by
  intro i j
  by_cases h : i = j <;> simp [identity, h, Ne.symm h]

theorem hermitian_transpose (X : J3) (hX : hermitian X) :
    ∀ i j, X j i = X i j := by
  intro i j
  exact (hX j i).symm

end InfoGeometry.Exceptional.FiniteJ3Zorn
