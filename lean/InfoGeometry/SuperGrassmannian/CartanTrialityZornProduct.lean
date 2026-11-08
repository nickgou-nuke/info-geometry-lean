import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
## Scope

This file proves finite permutation identities on three sector labels and
polynomial identities for a manually defined Zorn vector-matrix product over
an arbitrary commutative ring. It does not construct the root system `D₄`,
representations of `Spin(4,4)`, an outer automorphism group of a Lie algebra,
or a classification of split-octonion automorphisms.

The dependency order for the algebraic part is vector dot/cross identities,
then Zorn multiplication and conjugation, then norm composition and
alternativity. The label permutations form a separate finite branch.

1. **Three-coordinate dot and cross-product algebra**:
   - Commutative dot product $\mathbf{u} \cdot \mathbf{v}$.
   - Antisymmetric vector cross product $\mathbf{u} \times \mathbf{v}$.
   - Exact Lagrange / Binet-Cauchy identity:
     $(\mathbf{u} \times \mathbf{v}) \cdot (\mathbf{w} \times \mathbf{z}) = (\mathbf{u} \cdot \mathbf{w})(\mathbf{v} \cdot \mathbf{z}) - (\mathbf{u} \cdot \mathbf{z})(\mathbf{v} \cdot \mathbf{w})$.

2. **Zorn vector-matrix carrier and quadratic form**:
   - $X = \begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & b \end{pmatrix}$ over a commutative ring $R$.
   - $N(X) = ab - \mathbf{u} \cdot \mathbf{v}$ and conjugation identities.
   - A four-times quadratic-coordinate identity; this alone is not a real-signature classification.

3. **Zorn sector products**:
   - Diagonal idempotents $e_1, e_2$ and off-diagonal generators $U(\mathbf{u}), V(\mathbf{v})$.
   - Step 1: Diagonal contractions $U(\mathbf{u}_1) \cdot V(\mathbf{v}_2) = (\mathbf{u}_1 \cdot \mathbf{v}_2) e_1$.
   - Step 2: Off-diagonal products expressed using the vector cross product:
     $U(\mathbf{u}_1) \cdot U(\mathbf{u}_2) = V(\mathbf{u}_1 \times \mathbf{u}_2)$,
     $V(\mathbf{v}_1) \cdot V(\mathbf{v}_2) = - U(\mathbf{v}_1 \times \mathbf{v}_2)$.
   - These are algebraic product identities, not a fluid-vorticity theorem or a derivation of a Clifford representation.

4. **Quadratic norm composition and alternativity identities**:
   - $\det(X \cdot Y) = \det(X) \det(Y)$.
   - $X \cdot (X \cdot Y) = (X \cdot X) \cdot Y$ and
     $(Y \cdot X) \cdot X = Y \cdot (X \cdot X)$.

The typed Clifford actions and cyclic triality form live in
`CanonicalZornCompositionTriality.lean`. The real `(4,4)` Clifford/Spin
representation lives in `CanonicalZornRealSpin44.lean`. Neither result is a
proof here of `Aut(𝕆ₛ) ≅ G₂(2)` or of a fixed-subgroup classification.
-/

namespace InfoGeometry.SuperGrassmannian.CartanTrialityZorn

/-! ### Section 1: Permutations of three sector labels -/

/- These are labels only; no representation or root-system structure is
attached to this finite type. -/
inductive TrialityLabel where
  | vector : TrialityLabel
  | spinorPlus : TrialityLabel
  | spinorMinus : TrialityLabel
  deriving DecidableEq, Repr

/- The following functions are a 3-cycle and a transposition on labels. -/
def tau : TrialityLabel → TrialityLabel
  | .vector => .spinorPlus
  | .spinorPlus => .spinorMinus
  | .spinorMinus => .vector

def sigma : TrialityLabel → TrialityLabel
  | .vector => .spinorPlus
  | .spinorPlus => .vector
  | .spinorMinus => .spinorMinus

theorem tau_cubed (s : TrialityLabel) : tau (tau (tau s)) = s := by
  cases s <;> rfl

theorem sigma_sq (s : TrialityLabel) : sigma (sigma s) = s := by
  cases s <;> rfl

theorem sigma_tau_sigma (s : TrialityLabel) : sigma (tau (sigma s)) = tau (tau s) := by
  cases s <;> rfl

/-! ### Section 2: 3-Vector Euclidean and Cross-Product Algebra -/

/-- 3-dimensional vector carrier over an arbitrary commutative ring R. -/
@[ext]
structure Vec3 (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr

namespace Vec3

variable {R : Type*} [CommRing R]

def zero : Vec3 R := ⟨0, 0, 0⟩
def add (u v : Vec3 R) : Vec3 R := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def sub (u v : Vec3 R) : Vec3 R := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def neg (u : Vec3 R) : Vec3 R := ⟨-u.x, -u.y, -u.z⟩
def smul (c : R) (u : Vec3 R) : Vec3 R := ⟨c * u.x, c * u.y, c * u.z⟩

def dot (u v : Vec3 R) : R :=
  u.x * v.x + u.y * v.y + u.z * v.z

def cross (u v : Vec3 R) : Vec3 R :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

@[simp] theorem neg_x (u : Vec3 R) : (neg u).x = -u.x := rfl
@[simp] theorem neg_y (u : Vec3 R) : (neg u).y = -u.y := rfl
@[simp] theorem neg_z (u : Vec3 R) : (neg u).z = -u.z := rfl

@[simp] theorem zero_x : (zero : Vec3 R).x = 0 := rfl
@[simp] theorem zero_y : (zero : Vec3 R).y = 0 := rfl
@[simp] theorem zero_z : (zero : Vec3 R).z = 0 := rfl

@[simp] theorem add_x (u v : Vec3 R) : (add u v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vec3 R) : (add u v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Vec3 R) : (add u v).z = u.z + v.z := rfl

@[simp] theorem sub_x (u v : Vec3 R) : (sub u v).x = u.x - v.x := rfl
@[simp] theorem sub_y (u v : Vec3 R) : (sub u v).y = u.y - v.y := rfl
@[simp] theorem sub_z (u v : Vec3 R) : (sub u v).z = u.z - v.z := rfl

@[simp] theorem smul_x (c : R) (u : Vec3 R) : (smul c u).x = c * u.x := rfl
@[simp] theorem smul_y (c : R) (u : Vec3 R) : (smul c u).y = c * u.y := rfl
@[simp] theorem smul_z (c : R) (u : Vec3 R) : (smul c u).z = c * u.z := rfl

@[simp] theorem cross_x (u v : Vec3 R) : (cross u v).x = u.y * v.z - u.z * v.y := rfl
@[simp] theorem cross_y (u v : Vec3 R) : (cross u v).y = u.z * v.x - u.x * v.z := rfl
@[simp] theorem cross_z (u v : Vec3 R) : (cross u v).z = u.x * v.y - u.y * v.x := rfl

@[simp] theorem dot_comm (u v : Vec3 R) : dot u v = dot v u := by
  simp [dot]; ring

@[simp] theorem dot_zero_left (u : Vec3 R) : dot zero u = 0 := by
  simp [dot, zero]

@[simp] theorem dot_zero_right (u : Vec3 R) : dot u zero = 0 := by
  simp [dot, zero]

theorem dot_add_left (u v w : Vec3 R) : dot (add u v) w = dot u w + dot v w := by
  simp [dot, add]; ring

theorem dot_add_right (u v w : Vec3 R) : dot u (add v w) = dot u v + dot u w := by
  simp [dot, add]; ring

theorem dot_neg_left (u v : Vec3 R) : dot (neg u) v = -dot u v := by
  simp [dot, neg]; ring

theorem dot_neg_right (u v : Vec3 R) : dot u (neg v) = -dot u v := by
  simp [dot, neg]; ring

@[simp] theorem cross_self (u : Vec3 R) : cross u u = zero := by
  ext <;> simp <;> ring

theorem cross_antisymm (u v : Vec3 R) : cross u v = neg (cross v u) := by
  ext <;> simp <;> ring

theorem dot_cross_self_left (u v : Vec3 R) : dot u (cross u v) = 0 := by
  simp [dot, cross]; ring

theorem dot_cross_self_right (u v : Vec3 R) : dot v (cross u v) = 0 := by
  simp [dot, cross]; ring

theorem dot_cross_cyclic (u v w : Vec3 R) : dot (cross u v) w = dot u (cross v w) := by
  simp [dot, cross]; ring

/-- The exact Binet-Cauchy / Lagrange identity for two cross products:
    (u × v) · (w × z) = (u · w)(v · z) - (u · z)(v · w). -/
theorem dot_cross_cross (u v w z : Vec3 R) :
    dot (cross u v) (cross w z) = dot u w * dot v z - dot u z * dot v w := by
  simp [dot, cross]; ring

end Vec3

/-! ### Section 3: Split-Octonionic Zorn Vector Matrix Carrier -/

/-- Zorn vector matrix representation of the split-octonions M(R³):
    X = !![a, u; v, b] where a, b ∈ R and u, v ∈ Vec3 R. -/
@[ext]
structure ZornMatrix (R : Type*) where
  a : R
  u : Vec3 R
  v : Vec3 R
  b : R
  deriving DecidableEq, Repr

namespace ZornMatrix

variable {R : Type*} [CommRing R]

theorem zorn_ext {X Y : ZornMatrix R}
    (ha : X.a = Y.a)
    (hux : X.u.x = Y.u.x) (huy : X.u.y = Y.u.y) (huz : X.u.z = Y.u.z)
    (hvx : X.v.x = Y.v.x) (hvy : X.v.y = Y.v.y) (hvz : X.v.z = Y.v.z)
    (hb : X.b = Y.b) : X = Y := by
  cases X; cases Y
  congr
  · ext <;> assumption
  · ext <;> assumption

def zero : ZornMatrix R := ⟨0, Vec3.zero, Vec3.zero, 0⟩
def one : ZornMatrix R := ⟨1, Vec3.zero, Vec3.zero, 1⟩

def add (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a + Y.a, Vec3.add X.u Y.u, Vec3.add X.v Y.v, X.b + Y.b⟩

def sub (X Y : ZornMatrix R) : ZornMatrix R :=
  ⟨X.a - Y.a, Vec3.sub X.u Y.u, Vec3.sub X.v Y.v, X.b - Y.b⟩

def smul (c : R) (X : ZornMatrix R) : ZornMatrix R :=
  ⟨c * X.a, Vec3.smul c X.u, Vec3.smul c X.v, c * X.b⟩

/-- The quadratic norm N(X) = det(X) = ab - u · v. -/
def det (X : ZornMatrix R) : R :=
  X.a * X.b - Vec3.dot X.u X.v

/-- Octonionic conjugation: X̄ = !![b, -u; -v, a]. -/
def conj (X : ZornMatrix R) : ZornMatrix R :=
  ⟨X.b, Vec3.neg X.u, Vec3.neg X.v, X.a⟩

/-- Real trace: Tr(X) = a + b. -/
def trace (X : ZornMatrix R) : R :=
  X.a + X.b

/-- Invariant symmetric bilinear inner product (polar form of N):
    ⟨X, Y⟩ = a₁ b₂ + a₂ b₁ - u₁ · v₂ - u₂ · v₁. -/
def inner (X Y : ZornMatrix R) : R :=
  X.a * Y.b + Y.a * X.b - Vec3.dot X.u Y.v - Vec3.dot Y.u X.v

@[simp] theorem conj_a (X : ZornMatrix R) : (conj X).a = X.b := rfl
@[simp] theorem conj_u_x (X : ZornMatrix R) : (conj X).u.x = -X.u.x := rfl
@[simp] theorem conj_u_y (X : ZornMatrix R) : (conj X).u.y = -X.u.y := rfl
@[simp] theorem conj_u_z (X : ZornMatrix R) : (conj X).u.z = -X.u.z := rfl
@[simp] theorem conj_v_x (X : ZornMatrix R) : (conj X).v.x = -X.v.x := rfl
@[simp] theorem conj_v_y (X : ZornMatrix R) : (conj X).v.y = -X.v.y := rfl
@[simp] theorem conj_v_z (X : ZornMatrix R) : (conj X).v.z = -X.v.z := rfl
@[simp] theorem conj_b (X : ZornMatrix R) : (conj X).b = X.a := rfl

@[simp] theorem smul_a (c : R) (X : ZornMatrix R) : (smul c X).a = c * X.a := rfl
@[simp] theorem smul_u_x (c : R) (X : ZornMatrix R) : (smul c X).u.x = c * X.u.x := rfl
@[simp] theorem smul_u_y (c : R) (X : ZornMatrix R) : (smul c X).u.y = c * X.u.y := rfl
@[simp] theorem smul_u_z (c : R) (X : ZornMatrix R) : (smul c X).u.z = c * X.u.z := rfl
@[simp] theorem smul_v_x (c : R) (X : ZornMatrix R) : (smul c X).v.x = c * X.v.x := rfl
@[simp] theorem smul_v_y (c : R) (X : ZornMatrix R) : (smul c X).v.y = c * X.v.y := rfl
@[simp] theorem smul_v_z (c : R) (X : ZornMatrix R) : (smul c X).v.z = c * X.v.z := rfl
@[simp] theorem smul_b (c : R) (X : ZornMatrix R) : (smul c X).b = c * X.b := rfl

@[simp] theorem one_a : (one : ZornMatrix R).a = 1 := rfl
@[simp] theorem one_u_x : (one : ZornMatrix R).u.x = 0 := rfl
@[simp] theorem one_u_y : (one : ZornMatrix R).u.y = 0 := rfl
@[simp] theorem one_u_z : (one : ZornMatrix R).u.z = 0 := rfl
@[simp] theorem one_v_x : (one : ZornMatrix R).v.x = 0 := rfl
@[simp] theorem one_v_y : (one : ZornMatrix R).v.y = 0 := rfl
@[simp] theorem one_v_z : (one : ZornMatrix R).v.z = 0 := rfl
@[simp] theorem one_b : (one : ZornMatrix R).b = 1 := rfl

/-- Conjugation is an involution: X̄̄ = X. -/
@[simp] theorem conj_conj (X : ZornMatrix R) : conj (conj X) = X := by
  apply zorn_ext <;> simp

/-- Conjugation preserves determinant / quadratic norm: det(X̄) = det(X). -/
theorem det_conj (X : ZornMatrix R) : det (conj X) = det X := by
  simp [det, Vec3.dot]
  ring

/-- Conjugation preserves trace: Tr(X̄) = Tr(X). -/
theorem trace_conj (X : ZornMatrix R) : trace (conj X) = trace X := by
  simp [trace]; ring

/-- Self-inner product equals twice the determinant / norm: ⟨X, X⟩ = 2 det(X). -/
theorem inner_self (X : ZornMatrix R) : inner X X = 2 * det X := by
  simp [inner, det, Vec3.dot]; ring

/-- Inner product is symmetric: ⟨X, Y⟩ = ⟨Y, X⟩. -/
theorem inner_comm (X Y : ZornMatrix R) : inner X Y = inner Y X := by
  simp [inner, Vec3.dot]; ring

/- The coordinate identity below holds over every commutative ring. It is an
algebraic difference-of-squares identity, not by itself a signature theorem. -/
theorem four_mul_det_eq_difference_of_squares (x0 x7 u_x u_y u_z v_x v_y v_z : R) :
    let a := x0 + x7
    let b := x0 - x7
    let u : Vec3 R := ⟨u_x, u_y, u_z⟩
    let v : Vec3 R := ⟨v_x, v_y, v_z⟩
    let X : ZornMatrix R := ⟨a, u, v, b⟩
    4 * det X = (4 * x0^2 + (u_x - v_x)^2 + (u_y - v_y)^2 + (u_z - v_z)^2) -
                (4 * x7^2 + (u_x + v_x)^2 + (u_y + v_y)^2 + (u_z + v_z)^2) := by
  simp [det, Vec3.dot]
  ring

/-! ### Section 4: Zorn product and sector multiplication identities -/

/-- The Zorn vector matrix multiplication law:
    !![a₁, u₁; v₁, b₁] · !![a₂, u₂; v₂, b₂] =
    !![a₁ a₂ + u₁ · v₂,                 a₁ u₂ + b₂ u₁ - v₁ × v₂;
       a₂ v₁ + b₁ v₂ + u₁ × u₂,         b₁ b₂ + v₁ · u₂        ] -/
def mul (X Y : ZornMatrix R) : ZornMatrix R where
  a := X.a * Y.a + Vec3.dot X.u Y.v
  u := ⟨X.a * Y.u.x + Y.b * X.u.x - (Vec3.cross X.v Y.v).x,
        X.a * Y.u.y + Y.b * X.u.y - (Vec3.cross X.v Y.v).y,
        X.a * Y.u.z + Y.b * X.u.z - (Vec3.cross X.v Y.v).z⟩
  v := ⟨Y.a * X.v.x + X.b * Y.v.x + (Vec3.cross X.u Y.u).x,
        Y.a * X.v.y + X.b * Y.v.y + (Vec3.cross X.u Y.u).y,
        Y.a * X.v.z + X.b * Y.v.z + (Vec3.cross X.u Y.u).z⟩
  b := X.b * Y.b + Vec3.dot X.v Y.u

@[simp] theorem mul_a (X Y : ZornMatrix R) : (mul X Y).a = X.a * Y.a + Vec3.dot X.u Y.v := rfl
@[simp] theorem mul_u_x (X Y : ZornMatrix R) : (mul X Y).u.x = X.a * Y.u.x + Y.b * X.u.x - (Vec3.cross X.v Y.v).x := rfl
@[simp] theorem mul_u_y (X Y : ZornMatrix R) : (mul X Y).u.y = X.a * Y.u.y + Y.b * X.u.y - (Vec3.cross X.v Y.v).y := rfl
@[simp] theorem mul_u_z (X Y : ZornMatrix R) : (mul X Y).u.z = X.a * Y.u.z + Y.b * X.u.z - (Vec3.cross X.v Y.v).z := rfl
@[simp] theorem mul_v_x (X Y : ZornMatrix R) : (mul X Y).v.x = Y.a * X.v.x + X.b * Y.v.x + (Vec3.cross X.u Y.u).x := rfl
@[simp] theorem mul_v_y (X Y : ZornMatrix R) : (mul X Y).v.y = Y.a * X.v.y + X.b * Y.v.y + (Vec3.cross X.u Y.u).y := rfl
@[simp] theorem mul_v_z (X Y : ZornMatrix R) : (mul X Y).v.z = Y.a * X.v.z + X.b * Y.v.z + (Vec3.cross X.u Y.u).z := rfl
@[simp] theorem mul_b (X Y : ZornMatrix R) : (mul X Y).b = X.b * Y.b + Vec3.dot X.v Y.u := rfl

/-- The multiplicative unit element is one. -/
@[simp] theorem one_mul (X : ZornMatrix R) : mul one X = X := by
  apply zorn_ext <;> { simp [Vec3.dot, Vec3.cross]; try ring }

@[simp] theorem mul_one (X : ZornMatrix R) : mul X one = X := by
  apply zorn_ext <;> { simp [Vec3.dot, Vec3.cross]; try ring }

/-! #### Coordinate idempotents and off-diagonal sectors -/

/-- Diagonal idempotent e₁ = !![1, 0; 0, 0]. -/
def e1 : ZornMatrix R := ⟨1, Vec3.zero, Vec3.zero, 0⟩

/-- Diagonal idempotent e₂ = !![0, 0; 0, 1]. -/
def e2 : ZornMatrix R := ⟨0, Vec3.zero, Vec3.zero, 1⟩

/-- Off-diagonal upper-triangular generator U(u) = !![0, u; 0, 0]. -/
def U (u : Vec3 R) : ZornMatrix R := ⟨0, u, Vec3.zero, 0⟩

/-- Off-diagonal lower-triangular generator V(v) = !![0, 0; v, 0]. -/
def V (v : Vec3 R) : ZornMatrix R := ⟨0, Vec3.zero, v, 0⟩

/-- Idempotency of e₁: e₁ · e₁ = e₁. -/
theorem e1_mul_e1 : mul (e1 : ZornMatrix R) e1 = e1 := by
  apply zorn_ext <;> simp [e1, Vec3.dot, Vec3.cross]

/-- Idempotency of e₂: e₂ · e₂ = e₂. -/
theorem e2_mul_e2 : mul (e2 : ZornMatrix R) e2 = e2 := by
  apply zorn_ext <;> simp [e2, Vec3.dot, Vec3.cross]

/-- Orthogonality: e₁ · e₂ = 0 and e₂ · e₁ = 0. -/
theorem e1_mul_e2 : mul (e1 : ZornMatrix R) e2 = zero := by
  apply zorn_ext <;> simp [e1, e2, zero, Vec3.dot, Vec3.cross]

theorem e2_mul_e1 : mul (e2 : ZornMatrix R) e1 = zero := by
  apply zorn_ext <;> simp [e1, e2, zero, Vec3.dot, Vec3.cross]

/-- Completeness of diagonal projectors: e₁ + e₂ = 1. -/
theorem e1_add_e2 : add (e1 : ZornMatrix R) e2 = one := by
  apply zorn_ext <;> simp [add, e1, e2, one]

/-- Step 1 (Diagonal Contractions):
    U(u₁) · V(v₂) = (u₁ · v₂) e₁. -/
theorem U_mul_V (u v : Vec3 R) :
    mul (U u : ZornMatrix R) (V v) = smul (Vec3.dot u v) e1 := by
  apply zorn_ext <;> { simp [U, V, e1, smul, Vec3.dot, Vec3.cross]; try ring }

/-- Step 1 (Diagonal Contractions):
    V(v₁) · U(u₂) = (v₁ · u₂) e₂. -/
theorem V_mul_U (v u : Vec3 R) :
    mul (V v : ZornMatrix R) (U u) = smul (Vec3.dot v u) e2 := by
  apply zorn_ext <;> { simp [U, V, e2, smul, Vec3.dot, Vec3.cross]; try ring }

/- A mixed-sector identity in the Zorn product; this theorem does not define
or assert a Clifford representation. -/
theorem mixed_sector_anticommutator (u v : Vec3 R) :
    add (mul (U u : ZornMatrix R) (V v)) (mul (V v) (U u)) =
    smul (Vec3.dot u v) one := by
  rw [U_mul_V, V_mul_U, Vec3.dot_comm v u]
  apply zorn_ext <;> { simp [add, smul, e1, e2, one]; try ring }

/-- Step 2 (Vorticity / Curl Off-Diagonal Products):
    U(u₁) · U(u₂) = V(u₁ × u₂). -/
theorem U_mul_U (u1 u2 : Vec3 R) :
    mul (U u1 : ZornMatrix R) (U u2) = V (Vec3.cross u1 u2) := by
  apply zorn_ext <;> { simp [U, V, Vec3.dot, Vec3.cross]; try ring }

/-- Step 2 (Vorticity / Curl Off-Diagonal Products):
    V(v₁) · V(v₂) = - U(v₁ × v₂). -/
theorem V_mul_V (v1 v2 : Vec3 R) :
    mul (V v1 : ZornMatrix R) (V v2) = smul (-1 : R) (U (Vec3.cross v1 v2)) := by
  apply zorn_ext <;> { simp [U, V, smul, Vec3.dot, Vec3.cross]; try ring }

/-- Mixed products with diagonal idempotents:
    e₁ · U(u) = U(u), U(u) · e₂ = U(u), e₂ · U(u) = 0, U(u) · e₁ = 0. -/
theorem e1_mul_U (u : Vec3 R) : mul (e1 : ZornMatrix R) (U u) = U u := by
  apply zorn_ext <;> { simp [e1, U, Vec3.dot, Vec3.cross]; try ring }

theorem U_mul_e2 (u : Vec3 R) : mul (U u : ZornMatrix R) e2 = U u := by
  apply zorn_ext <;> { simp [e2, U, Vec3.dot, Vec3.cross]; try ring }

theorem e2_mul_V (v : Vec3 R) : mul (e2 : ZornMatrix R) (V v) = V v := by
  apply zorn_ext <;> { simp [e2, V, Vec3.dot, Vec3.cross]; try ring }

theorem V_mul_e1 (v : Vec3 R) : mul (V v : ZornMatrix R) e1 = V v := by
  apply zorn_ext <;> { simp [e1, V, Vec3.dot, Vec3.cross]; try ring }

/-! ### Section 5: Conjugation and quadratic norm composition -/

/-- Left product with conjugate reproduces the quadratic norm scalar:
    X̄ · X = det(X) 1. -/
theorem conj_mul_self (X : ZornMatrix R) :
    mul (conj X) X = smul (det X) one := by
  apply zorn_ext <;> { simp [det, Vec3.dot, Vec3.cross]; try ring }

/-- Right product with conjugate reproduces the quadratic norm scalar:
    X · X̄ = det(X) 1. -/
theorem mul_conj_self (X : ZornMatrix R) :
    mul X (conj X) = smul (det X) one := by
  apply zorn_ext <;> { simp [det, Vec3.dot, Vec3.cross]; try ring }

/-- Reverse-order property of octonionic conjugation on products:
    conj(X · Y) = conj(Y) · conj(X). -/
theorem conj_mul (X Y : ZornMatrix R) :
    conj (mul X Y) = mul (conj Y) (conj X) := by
  apply zorn_ext <;> { simp [Vec3.dot, Vec3.cross]; try ring }

/-- Trace inner product theorem:
    Tr(X · Ȳ) = ⟨X, Y⟩. -/
theorem trace_mul_conj (X Y : ZornMatrix R) :
    trace (mul X (conj Y)) = inner X Y := by
  simp [trace, inner, Vec3.dot]
  ring

/- The quadratic norm is multiplicative for this explicitly defined product. -/
theorem zorn_norm_mul (X Y : ZornMatrix R) :
    det (mul X Y) = det X * det Y := by
  simp [det, Vec3.dot, Vec3.cross]
  ring

/-! ### Section 6: Left and right alternativity identities -/

/-- Left Alternativity of the split-octonions:
    X · (X · Y) = (X · X) · Y. -/
theorem left_alternativity (X Y : ZornMatrix R) :
    mul X (mul X Y) = mul (mul X X) Y := by
  apply zorn_ext <;> { simp [Vec3.dot, Vec3.cross]; try ring }

/-- Right Alternativity of the split-octonions:
    (Y · X) · X = Y · (X · X). -/
theorem right_alternativity (X Y : ZornMatrix R) :
    mul (mul Y X) X = mul Y (mul X X) := by
  apply zorn_ext <;> { simp [Vec3.dot, Vec3.cross]; try ring }

/-! ### Section 7: Trace pairing and an automorphism predicate -/

/- A scalar-valued triple pairing. No cyclic or triality invariance is asserted. -/
def zornTriplePairing (X Y Z : ZornMatrix R) : R :=
  trace (mul (mul X Y) (conj Z))

theorem zornTriplePairing_eq_inner (X Y Z : ZornMatrix R) :
    zornTriplePairing X Y Z = inner (mul X Y) Z := by
  rw [zornTriplePairing, trace_mul_conj]

/-- A unital `R`-linear bijection preserving the explicitly defined Zorn
product. This is the automorphism predicate for this nonassociative algebra;
no group classification is asserted. -/
structure IsSplitOctonionAutomorphism (g : ZornMatrix R → ZornMatrix R) : Prop where
  bijective : Function.Bijective g
  map_add : ∀ X Y, g (add X Y) = add (g X) (g Y)
  map_smul : ∀ r X, g (smul r X) = smul r (g X)
  preserves_mul : ∀ X Y, g (mul X Y) = mul (g X) (g Y)
  preserves_one : g one = one

/-- The identity map is an automorphism of the defined Zorn algebra. -/
theorem identity_isSplitOctonionAutomorphism :
    IsSplitOctonionAutomorphism (fun X : ZornMatrix R => X) := by
  refine ⟨Function.bijective_id, ?_, ?_, ?_, rfl⟩
  · intro X Y
    rfl
  · intro r X
    rfl
  · intro X Y
    rfl

end ZornMatrix

end InfoGeometry.SuperGrassmannian.CartanTrialityZorn
