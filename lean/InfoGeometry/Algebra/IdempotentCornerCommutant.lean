import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Idempotent corner commutant

Let `A` be a unital associative algebra and let `e : A` satisfy `e * e = e`.
The principal left ideal

`Ae = {x : A | x * e = x}`

carries the restricted left action of `A`.  This file proves the exact
regular-ideal analogue of the usual evaluation-at-the-unit commutant theorem:
every `R`-linear endomorphism of `Ae` commuting with all restricted left
multiplications is right multiplication by its value at `e`.

That value lies in the corner

`eAe = {c : A | e * c = c ∧ c * e = c}`.

Thus the commutant carrier is canonically equivalent to the corner carrier.
No primitivity, simplicity, finite-dimensionality, norm, or topology is used.
Primitivity is needed only in later specializations that identify `eAe` with a
division algebra or with the scalar field.
-/

namespace InfoGeometry.Algebra.IdempotentCornerCommutant

section CornerCarrier

variable {A : Type*} [Semiring A]

/-- The algebraic corner carrier `eAe`, recorded by its two support equations. -/
def Corner (e : A) :=
  {c : A // e * c = c ∧ c * e = c}

/-- The principal left ideal `Ae = {x : A | x * e = x}`. -/
def principalLeftIdeal (e : A) : Set A :=
  {x : A | x * e = x}

/-- The principal right ideal `eA = {y : A | e * y = y}`. -/
def principalRightIdeal (e : A) : Set A :=
  {y : A | e * y = y}

/-- Multiplication inherited by the corner carrier. -/
def cornerMul (e : A) (c d : Corner e) : Corner e :=
  ⟨c.1 * d.1, by
    constructor
    · calc
        e * (c.1 * d.1) = (e * c.1) * d.1 := by rw [← mul_assoc]
        _ = c.1 * d.1 := by rw [c.2.1]
    · calc
        (c.1 * d.1) * e = c.1 * (d.1 * e) := by rw [mul_assoc]
        _ = c.1 * d.1 := by rw [d.2.2]⟩

/-- The idempotent itself is the internal unit of its corner. -/
def cornerUnit (e : A) (he : e * e = e) : Corner e :=
  ⟨e, he, he⟩

@[simp]
theorem cornerMul_val (e : A) (c d : Corner e) :
    (cornerMul e c d).1 = c.1 * d.1 :=
  rfl

@[simp]
theorem cornerUnit_val (e : A) (he : e * e = e) :
    (cornerUnit e he).1 = e :=
  rfl

end CornerCarrier

section LinearCommutant

variable {R A : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- The principal left ideal `Ae`, viewed as an `R`-submodule of `A`. -/
def principalLeftIdealSubmodule (e : A) : Submodule R A where
  carrier := {x | x * e = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  smul_mem' := by
    intro r x hx
    change (r • x) * e = r • x
    rw [Algebra.smul_mul_assoc, hx]

/-- The native carrier of the principal left ideal `Ae`. -/
abbrev PrincipalLeftIdeal (e : A) : Type _ :=
  ↥(principalLeftIdealSubmodule (R := R) e)

/-- The idempotent, regarded as the distinguished vector of `Ae`. -/
def idempotentVector (e : A) (he : e * e = e) :
    PrincipalLeftIdeal (R := R) e :=
  ⟨e, he⟩

/-- A corner element is automatically an element of the principal left ideal. -/
def cornerToLeftIdeal (e : A) (c : Corner e) :
    PrincipalLeftIdeal (R := R) e :=
  ⟨c.1, c.2.2⟩

/-- Restricted left multiplication by `a : A` on the principal left ideal `Ae`. -/
def leftAction (e a : A) :
    Module.End R (PrincipalLeftIdeal (R := R) e) where
  toFun x :=
    ⟨a * x.1, by
      calc
        (a * x.1) * e = a * (x.1 * e) := by rw [mul_assoc]
        _ = a * x.1 := by rw [x.2]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' r x := by
    apply Subtype.ext
    simp [Algebra.mul_smul_comm]

/-- Right multiplication by a corner element on `Ae`. -/
def rightCornerAction (e : A) (c : Corner e) :
    Module.End R (PrincipalLeftIdeal (R := R) e) where
  toFun x :=
    ⟨x.1 * c.1, by
      calc
        (x.1 * c.1) * e = x.1 * (c.1 * e) := by rw [mul_assoc]
        _ = x.1 * c.1 := by rw [c.2.2]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [add_mul]
  map_smul' r x := by
    apply Subtype.ext
    simp [Algebra.smul_mul_assoc]

@[simp]
theorem leftAction_apply (e a : A)
    (x : PrincipalLeftIdeal (R := R) e) :
    ((leftAction (R := R) e a x : PrincipalLeftIdeal (R := R) e) : A) =
      a * (x : A) :=
  rfl

@[simp]
theorem rightCornerAction_apply (e : A) (c : Corner e)
    (x : PrincipalLeftIdeal (R := R) e) :
    ((rightCornerAction (R := R) e c x : PrincipalLeftIdeal (R := R) e) : A) =
      (x : A) * c.1 :=
  rfl

@[simp]
theorem leftAction_idempotentVector (e : A) (he : e * e = e) :
    leftAction (R := R) e e (idempotentVector (R := R) e he) =
      idempotentVector (R := R) e he := by
  apply Subtype.ext
  exact he

@[simp]
theorem rightCornerAction_idempotentVector
    (e : A) (he : e * e = e) (c : Corner e) :
    rightCornerAction (R := R) e c (idempotentVector (R := R) e he) =
      cornerToLeftIdeal (R := R) e c := by
  apply Subtype.ext
  exact c.2.1

/-- Pointwise commutant of the restricted left regular action on `Ae`. -/
def leftIdealCommutant (e : A) :
    Set (Module.End R (PrincipalLeftIdeal (R := R) e)) :=
  {T | ∀ (a : A) (x : PrincipalLeftIdeal (R := R) e),
    T (leftAction (R := R) e a x) =
      leftAction (R := R) e a (T x)}

/-- Every corner right action commutes with every restricted left action. -/
theorem rightCornerAction_mem_leftIdealCommutant
    (e : A) (c : Corner e) :
    rightCornerAction (R := R) e c ∈ leftIdealCommutant (R := R) e := by
  intro a x
  apply Subtype.ext
  exact mul_assoc a (x : A) c.1

/-- Corner multiplication is represented in the opposite order by composition. -/
theorem rightCornerAction_cornerMul
    (e : A) (c d : Corner e) :
    rightCornerAction (R := R) e (cornerMul e c d) =
      (rightCornerAction (R := R) e d).comp
        (rightCornerAction (R := R) e c) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (mul_assoc (x : A) c.1 d.1).symm

/-- The internal corner unit acts identically on `Ae`. -/
@[simp]
theorem rightCornerAction_cornerUnit
    (e : A) (he : e * e = e) :
    rightCornerAction (R := R) e (cornerUnit e he) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact x.2

/--
Evaluate a commuting endomorphism at `e`.  The result is automatically supported
by `e` on both sides and hence belongs to the corner `eAe`.
-/
def cornerOfCommutant
    (e : A) (he : e * e = e)
    (T : Module.End R (PrincipalLeftIdeal (R := R) e))
    (hT : T ∈ leftIdealCommutant (R := R) e) : Corner e := by
  refine ⟨(T (idempotentVector (R := R) e he)).1, ?_, ?_⟩
  · have h := hT e (idempotentVector (R := R) e he)
    rw [leftAction_idempotentVector (R := R) e he] at h
    simpa [leftAction] using (congrArg Subtype.val h).symm
  · exact (T (idempotentVector (R := R) e he)).2

@[simp]
theorem cornerOfCommutant_val
    (e : A) (he : e * e = e)
    (T : Module.End R (PrincipalLeftIdeal (R := R) e))
    (hT : T ∈ leftIdealCommutant (R := R) e) :
    (cornerOfCommutant (R := R) e he T hT).1 =
      (T (idempotentVector (R := R) e he)).1 :=
  rfl

/--
Every endomorphism commuting with the restricted left action is right
multiplication by its value at the idempotent.
-/
theorem eq_rightCornerAction_of_mem_leftIdealCommutant
    (e : A) (he : e * e = e)
    (T : Module.End R (PrincipalLeftIdeal (R := R) e))
    (hT : T ∈ leftIdealCommutant (R := R) e) :
    T = rightCornerAction (R := R) e
      (cornerOfCommutant (R := R) e he T hT) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := hT (x : A) (idempotentVector (R := R) e he)
  have hx :
      leftAction (R := R) e (x : A) (idempotentVector (R := R) e he) = x := by
    apply Subtype.ext
    exact x.2
  rw [hx] at h
  simpa [leftAction, rightCornerAction] using congrArg Subtype.val h

/-- The corner action is faithful; evaluation at `e` recovers the corner element. -/
theorem rightCornerAction_injective
    (e : A) (he : e * e = e) :
    Function.Injective (rightCornerAction (R := R) e) := by
  intro c d h
  apply Subtype.ext
  have hApply := congrArg
    (fun T : Module.End R (PrincipalLeftIdeal (R := R) e) =>
      T (idempotentVector (R := R) e he)) h
  have hVal := congrArg Subtype.val hApply
  change e * c.1 = e * d.1 at hVal
  rw [c.2.1, d.2.1] at hVal
  exact hVal

/-- Exact range characterization of the commutant on the principal left ideal. -/
theorem leftIdealCommutant_eq_rightCornerRange
    (e : A) (he : e * e = e) :
    leftIdealCommutant (R := R) e =
      {T | ∃ c : Corner e, T = rightCornerAction (R := R) e c} := by
  ext T
  constructor
  · intro hT
    exact ⟨cornerOfCommutant (R := R) e he T hT,
      eq_rightCornerAction_of_mem_leftIdealCommutant (R := R) e he T hT⟩
  · rintro ⟨c, rfl⟩
    exact rightCornerAction_mem_leftIdealCommutant (R := R) e c

/--
Canonical carrier equivalence between the corner `eAe` and the full commutant
of the restricted left action on `Ae`.

The separate theorem `rightCornerAction_cornerMul` records that multiplication
is transported with the opposite order.
-/
def cornerEquivLeftIdealCommutant
    (e : A) (he : e * e = e) :
    Corner e ≃
      {T : Module.End R (PrincipalLeftIdeal (R := R) e) //
        T ∈ leftIdealCommutant (R := R) e} where
  toFun c :=
    ⟨rightCornerAction (R := R) e c,
      rightCornerAction_mem_leftIdealCommutant (R := R) e c⟩
  invFun T :=
    cornerOfCommutant (R := R) e he T.1 T.2
  left_inv c := by
    apply rightCornerAction_injective (R := R) e he
    exact
      (eq_rightCornerAction_of_mem_leftIdealCommutant
        (R := R) e he
        (rightCornerAction (R := R) e c)
        (rightCornerAction_mem_leftIdealCommutant (R := R) e c)).symm
  right_inv T := by
    apply Subtype.ext
    exact
      (eq_rightCornerAction_of_mem_leftIdealCommutant
        (R := R) e he T.1 T.2).symm

end LinearCommutant

end InfoGeometry.Algebra.IdempotentCornerCommutant

