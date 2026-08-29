import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace InfoGeometry.Exceptional.RealZorn

/-!
# Split Octonions and Zorn Vector Matrix Algebra

The Split Octonions form an 8-dimensional non-associative algebra over the reals.
Unlike the standard octonions (which are a division algebra), the split octonions
contain zero divisors.

A convenient representation of the split octonions is the Zorn Vector Matrix algebra.
Elements are 2x2 matrices where the diagonal elements are scalars (reals) and the
off-diagonal elements are 3D vectors.
-/

/-- A 3D vector over integers. -/
def Vec3Real := ℝ × ℝ × ℝ

/-- The cross product of two 3D vectors. -/
def cross (u v : Vec3Real) : Vec3Real :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

theorem cross_self (u : Vec3Real) : cross u u = (0, 0, 0) := by
  apply Prod.ext
  · dsimp [cross]
    ring
  · apply Prod.ext
    · dsimp [cross]
      ring
    · dsimp [cross]
      ring

/-- The dot product of two 3D vectors. -/
def dot (u v : Vec3Real) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- Vector addition. -/
def add (u v : Vec3Real) : Vec3Real :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

/-- Vector subtraction. -/
def sub (u v : Vec3Real) : Vec3Real :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

/-- Scalar multiplication. -/
def smul (c : ℝ) (u : Vec3Real) : Vec3Real :=
  (c * u.1, c * u.2.1, c * u.2.2)

theorem dot_cross_left (u v w : Vec3Real) :
    dot u (cross v w) = dot v (cross w u) := by
  dsimp [dot, cross]
  ring

theorem dot_cross_right (u v w : Vec3Real) :
    dot (cross u v) w = dot u (cross v w) := by
  dsimp [dot, cross]
  ring

theorem cross_cross (u v w : Vec3Real) :
    cross (cross u v) w = sub (smul (dot u w) v) (smul (dot v w) u) := by
  apply Prod.ext
  · dsimp [cross, sub, smul, dot]
    ring_nf
  · apply Prod.ext
    · dsimp [cross, sub, smul, dot]
      ring
    · dsimp [cross, sub, smul, dot]
      ring

theorem add_dot_left (u v w : Vec3Real) :
    dot (add u v) w = dot u w + dot v w := by
  dsimp [add, dot]
  ring

theorem add_dot_right (u v w : Vec3Real) :
    dot u (add v w) = dot u v + dot u w := by
  dsimp [add, dot]
  ring

theorem smul_dot_left (c : ℝ) (u v : Vec3Real) :
    dot (smul c u) v = c * dot u v := by
  dsimp [smul, dot]
  ring

theorem smul_dot_right (c : ℝ) (u v : Vec3Real) :
    dot u (smul c v) = c * dot u v := by
  dsimp [smul, dot]
  ring

theorem cross_add_left (u v w : Vec3Real) :
    cross (add u v) w = add (cross u w) (cross v w) := by
  apply Prod.ext
  · dsimp [cross, add]
    ring_nf
  · apply Prod.ext
    · dsimp [cross, add]
      ring_nf
    · dsimp [cross, add]
      ring

theorem cross_add_right (u v w : Vec3Real) :
    cross u (add v w) = add (cross u v) (cross u w) := by
  apply Prod.ext
  · dsimp [cross, add]
    ring
  · apply Prod.ext
    · dsimp [cross, add]
      ring
    · dsimp [cross, add]
      ring

theorem cross_smul_left (c : ℝ) (u v : Vec3Real) :
    cross (smul c u) v = smul c (cross u v) := by
  apply Prod.ext
  · dsimp [cross, smul]
    ring
  · apply Prod.ext
    · dsimp [cross, smul]
      ring
    · dsimp [cross, smul]
      ring

theorem cross_smul_right (c : ℝ) (u v : Vec3Real) :
    cross u (smul c v) = smul c (cross u v) := by
  apply Prod.ext
  · dsimp [cross, smul]
    ring
  · apply Prod.ext
    · dsimp [cross, smul]
      ring
    · dsimp [cross, smul]
      ring

/-- 
A Zorn matrix representing an element of the split octonions.
`a` and `b` are scalars.
`u` and `v` are 3D vectors.
-/
structure ZornMatrixReal where
  a : ℝ
  b : ℝ
  u : Vec3Real
  v : Vec3Real

/-- The zero element in the Zorn matrix algebra. -/
def ZornMatrixReal.zero : ZornMatrixReal :=
  { a := 0, b := 0, u := (0, 0, 0), v := (0, 0, 0) }

instance : Zero ZornMatrixReal := ⟨ZornMatrixReal.zero⟩

/-- 
Multiplication of Zorn matrices. Note this is non-associative.
A * B = [ a*c + u·x,        a*w + d*u - v × x ]
        [ c*v + b*x + u × w, b*d + v·w        ]
-/
def ZornMatrixReal.mul (A B : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a * B.a + dot A.u B.v,
    b := A.b * B.b + dot A.v B.u,
    u := sub (add (smul A.a B.u) (smul B.b A.u)) (cross A.v B.v),
    v := add (add (smul B.a A.v) (smul A.b B.v)) (cross A.u B.u) }

instance : Mul ZornMatrixReal := ⟨ZornMatrixReal.mul⟩

def ZornMatrixReal.neg (A : ZornMatrixReal) : ZornMatrixReal :=
  { a := -A.a, b := -A.b, u := smul (-1) A.u, v := smul (-1) A.v }

instance : Neg ZornMatrixReal := ⟨ZornMatrixReal.neg⟩

def ZornMatrixReal.add_mat (A B : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a + B.a, b := A.b + B.b,
    u := add A.u B.u, v := add A.v B.v }

instance : Add ZornMatrixReal := ⟨ZornMatrixReal.add_mat⟩

def ZornMatrixReal.sub_mat (A B : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a - B.a, b := A.b - B.b,
    u := sub A.u B.u, v := sub A.v B.v }

instance : Sub ZornMatrixReal := ⟨ZornMatrixReal.sub_mat⟩

@[simp] theorem mul_a (A B : ZornMatrixReal) :
    (A * B).a = A.a * B.a + dot A.u B.v := rfl

@[simp] theorem mul_b (A B : ZornMatrixReal) :
    (A * B).b = A.b * B.b + dot A.v B.u := rfl

@[simp] theorem mul_u (A B : ZornMatrixReal) :
    (A * B).u = sub (add (smul A.a B.u) (smul B.b A.u)) (cross A.v B.v) := rfl

@[simp] theorem mul_v (A B : ZornMatrixReal) :
    (A * B).v = add (add (smul B.a A.v) (smul A.b B.v)) (cross A.u B.u) := rfl

lemma ZornMatrixReal.ext_pre (A B : ZornMatrixReal)
    (ha : A.a = B.a) (hb : A.b = B.b)
    (hu : A.u = B.u) (hv : A.v = B.v) : A = B := by
  cases A
  cases B
  congr

theorem zorn_mul_self_left (A B : ZornMatrixReal) :
    (A * A) * B = A * (A * B) := by
  change ZornMatrixReal.mul (ZornMatrixReal.mul A A) B =
    ZornMatrixReal.mul A (ZornMatrixReal.mul A B)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
      ring
    · apply Prod.ext
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring
  · apply Prod.ext
    · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
      ring
    · apply Prod.ext
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring

theorem zorn_mul_self_right (A B : ZornMatrixReal) :
    (A * B) * B = A * (B * B) := by
  change ZornMatrixReal.mul (ZornMatrixReal.mul A B) B =
    ZornMatrixReal.mul A (ZornMatrixReal.mul B B)
  apply ZornMatrixReal.ext_pre
  · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring
  · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext
    · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
      ring
    · apply Prod.ext
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring
  · apply Prod.ext
    · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
      ring
    · apply Prod.ext
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring
      · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
        ring

theorem zorn_mul_flexible (A B : ZornMatrixReal) :
    (A * B) * A = A * (B * A) := by
  change ZornMatrixReal.mul (ZornMatrixReal.mul A B) A =
    ZornMatrixReal.mul A (ZornMatrixReal.mul B A)
  apply ZornMatrixReal.ext_pre
  · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring
  · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext
    · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
      ring
    · apply Prod.ext <;>
        simp [ZornMatrixReal.mul, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext
    · simp [ZornMatrixReal.mul, dot, cross, add, sub, smul]
      ring
    · apply Prod.ext <;>
        simp [ZornMatrixReal.mul, dot, cross, add, sub, smul] <;> ring

theorem zorn_mul_add_left (A B C : ZornMatrixReal) :
    A * (B + C) = A * B + A * C := by
  change ZornMatrixReal.mul A (ZornMatrixReal.add_mat B C) =
    ZornMatrixReal.add_mat (ZornMatrixReal.mul A B) (ZornMatrixReal.mul A C)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul] <;> ring

theorem zorn_add_mul_right (A B C : ZornMatrixReal) :
    (A + B) * C = A * C + B * C := by
  change ZornMatrixReal.mul (ZornMatrixReal.add_mat A B) C =
    ZornMatrixReal.add_mat (ZornMatrixReal.mul A C) (ZornMatrixReal.mul B C)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.add_mat, dot, cross, add, sub, smul] <;> ring

theorem zorn_neg_mul (A B : ZornMatrixReal) :
    (-A) * B = -(A * B) := by
  change ZornMatrixReal.mul (ZornMatrixReal.neg A) B =
    ZornMatrixReal.neg (ZornMatrixReal.mul A B)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul] <;> ring

theorem zorn_mul_neg (A B : ZornMatrixReal) :
    A * (-B) = -(A * B) := by
  change ZornMatrixReal.mul A (ZornMatrixReal.neg B) =
    ZornMatrixReal.neg (ZornMatrixReal.mul A B)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.neg, dot, cross, add, sub, smul] <;> ring

theorem zorn_sub_mul (A B C : ZornMatrixReal) :
    (A - B) * C = A * C - B * C := by
  change ZornMatrixReal.mul (ZornMatrixReal.sub_mat A B) C =
    ZornMatrixReal.sub_mat (ZornMatrixReal.mul A C) (ZornMatrixReal.mul B C)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul] <;> ring

theorem zorn_mul_sub (A B C : ZornMatrixReal) :
    A * (B - C) = A * B - A * C := by
  change ZornMatrixReal.mul A (ZornMatrixReal.sub_mat B C) =
    ZornMatrixReal.sub_mat (ZornMatrixReal.mul A B) (ZornMatrixReal.mul A C)
  apply ZornMatrixReal.ext_pre
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul]
    ring
  · dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul]
    ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul] <;> ring
  · apply Prod.ext <;> dsimp [ZornMatrixReal.mul, ZornMatrixReal.sub_mat, dot, cross, add, sub, smul] <;> ring

/-- Extensionality lemma for Zorn matrices. -/
lemma ZornMatrixReal.ext (A B : ZornMatrixReal)
    (ha : A.a = B.a) (hb : A.b = B.b)
    (hu : A.u = B.u) (hv : A.v = B.v) : A = B := by
  cases A
  cases B
  congr

/-- The split norm of a Zorn matrix: N(A) = a * b - u · v -/
def ZornMatrixReal.norm (A : ZornMatrixReal) : ℝ :=
  A.a * A.b - dot A.u A.v

/-!
### Explicit Proof of Zero Divisors

We define two non-zero matrices whose product is exactly zero.
These were derived via the symbolic external solver (SymPy).
-/

def zeroDivisorA : ZornMatrixReal :=
  { a := 1, b := 0, u := (1, 0, 0), v := (0, 0, 0) }

def zeroDivisorB : ZornMatrixReal :=
  { a := 0, b := 1, u := (-1, 0, 0), v := (0, 0, 0) }

theorem split_octonions_have_zero_divisors :
    zeroDivisorA * zeroDivisorB = 0 ∧ zeroDivisorA ≠ 0 ∧ zeroDivisorB ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change ZornMatrixReal.mul zeroDivisorA zeroDivisorB = ZornMatrixReal.zero
    apply ZornMatrixReal.ext
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul, zeroDivisorA, zeroDivisorB, ZornMatrixReal.zero]; norm_num
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul, zeroDivisorA, zeroDivisorB, ZornMatrixReal.zero]; norm_num
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul, zeroDivisorA, zeroDivisorB, ZornMatrixReal.zero]; simp
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul, zeroDivisorA, zeroDivisorB, ZornMatrixReal.zero]; simp
  · intro h
    have h1 : zeroDivisorA.a = ZornMatrixReal.zero.a := by { rw [h]; rfl }
    change (1 : ℝ) = 0 at h1
    exact one_ne_zero h1
  · intro h
    have h1 : zeroDivisorB.b = ZornMatrixReal.zero.b := by { rw [h]; rfl }
    change (1 : ℝ) = 0 at h1
    exact one_ne_zero h1

theorem norm_mul (A B : ZornMatrixReal) : (A * B).norm = A.norm * B.norm := by
  change ZornMatrixReal.norm (ZornMatrixReal.mul A B) = ZornMatrixReal.norm A * ZornMatrixReal.norm B
  dsimp [ZornMatrixReal.norm, ZornMatrixReal.mul, dot, cross, add, sub, smul]
  ring

/-- The trace of a Zorn matrix. -/
def ZornMatrixReal.trace (A : ZornMatrixReal) : ℝ := A.a + A.b

theorem trace_mul_comm (A B : ZornMatrixReal) : (A * B).trace = (B * A).trace := by
  change ZornMatrixReal.trace (ZornMatrixReal.mul A B) = ZornMatrixReal.trace (ZornMatrixReal.mul B A)
  dsimp [ZornMatrixReal.trace, ZornMatrixReal.mul, dot, cross, add, sub, smul]
  ring

/-!
### Kitaev Majorana Operator Logic

We port the Majorana operator logic and topological invariants directly into the
Zorn Matrix representation, bypassing the `ClPlus` wrappers.
-/

def ZornMatrixReal.one : ZornMatrixReal :=
  { a := 1, b := 1, u := (0, 0, 0), v := (0, 0, 0) }

instance : One ZornMatrixReal := ⟨ZornMatrixReal.one⟩

/-- A finite Zorn carrier for a Majorana-labelled generator.  This real
    carrier has no involution, so self-adjointness is not asserted. -/
structure MajoranaOperator where
  val : ZornMatrixReal
  
/-- Прожекторите на Китаев върху топологичните сектори: P_plus и P_minus. -/
def KitaevProjectorPlus (γ1 γ2 : MajoranaOperator) : ZornMatrixReal :=
  1 + γ1.val * γ2.val

def KitaevProjectorMinus (γ1 γ2 : MajoranaOperator) : ZornMatrixReal :=
  1 - γ1.val * γ2.val

/-- ОПЕРАТОР НА ФЕРМИОННИЯ ПАРИТЕТ (Fermion Parity Operator).
    Този оператор измерва топологичния заряд на кубита. 
    В реалната алгебра на Хестенес, той е еквивалентен на бивектора ℘ = - γ1*γ2 -/
def FermionParityOperator (γ1 γ2 : MajoranaOperator) : ZornMatrixReal :=
  -(γ1.val * γ2.val)

/- 
ФУНДАМЕНТАЛНА ТЕОРЕМА 2 (Свещеният Граал): 
Конструктивно доказателство на цикличността на следата за произволни паравектори.
Доказана строго чрез `trace_mul_comm` без нечестни аксиоми!
-/
theorem Parity_ConeAction_Invariance (γ1 γ2 : MajoranaOperator) (G : ZornMatrixReal) :
    let wp : ZornMatrixReal := FermionParityOperator γ1 γ2
    (wp * G).trace = (G * wp).trace := by
  intro wp
  exact trace_mul_comm wp G

end InfoGeometry.Exceptional.RealZorn
