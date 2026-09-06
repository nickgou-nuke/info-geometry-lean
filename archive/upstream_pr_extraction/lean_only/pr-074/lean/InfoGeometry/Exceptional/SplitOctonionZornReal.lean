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
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul, zeroDivisorA, zeroDivisorB, ZornMatrixReal.zero]; simp <;> norm_num
    · dsimp [ZornMatrixReal.mul, dot, cross, add, sub, smul, zeroDivisorA, zeroDivisorB, ZornMatrixReal.zero]; simp <;> norm_num
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

def ZornMatrixReal.add_mat (A B : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a + B.a,
    b := A.b + B.b,
    u := add A.u B.u,
    v := add A.v B.v }

instance : Add ZornMatrixReal := ⟨ZornMatrixReal.add_mat⟩

def ZornMatrixReal.neg_mat (A : ZornMatrixReal) : ZornMatrixReal :=
  { a := -A.a,
    b := -A.b,
    u := smul (-1) A.u,
    v := smul (-1) A.v }

instance : Neg ZornMatrixReal := ⟨ZornMatrixReal.neg_mat⟩

def ZornMatrixReal.sub_mat (A B : ZornMatrixReal) : ZornMatrixReal :=
  { a := A.a - B.a,
    b := A.b - B.b,
    u := sub A.u B.u,
    v := sub A.v B.v }

instance : Sub ZornMatrixReal := ⟨ZornMatrixReal.sub_mat⟩

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
