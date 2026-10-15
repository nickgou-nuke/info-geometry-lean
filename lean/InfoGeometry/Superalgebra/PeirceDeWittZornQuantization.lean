import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.Tactic.Ring

/-!
# Peirce–DeWitt Zorn Super-Quantization & Split-Octonion Baryon Confinement

This module formalizes the algebraic synthesis connecting:
1. **Peirce Idempotent Decomposition (`e₁, e₂`)**: The orthogonal chiral/causal projector
   decomposition of a split-composition algebra, together with the **Penrose Chiral Zig-Zag**
   mass determinant mechanism (`N(m_L e₁ + m_R e₂) = m_L m_R` from massless chiral rays
   `N(m_L e₁) = N(m_R e₂) = 0`).
2. **DeWitt `ℤ₂` Super-Grading**: The decomposition of the 8-dimensional Zorn split-octonion
   algebra into its `2`-dimensional **Bosonic / Even** diagonal sector (`Peirce 11 ⊕ Peirce 22`)
   and its `6`-dimensional **Fermionic / Odd** off-diagonal sector (`Peirce 12 ⊕ Peirce 21`).
3. **Canonical Anticommutation Relations (CAR) & Pauli Exclusion**: The off-diagonal Zorn
   generators `U(u) = e₁ X e₂` and `V(v) = e₂ X e₁` obey exact CAR anticommutation
   `{U(u), V(v)} = (u · v) I` and Fermi nilpotency `U(u)² = 0`, `V(v)² = 0` when `u × u = 0`.
4. **Supercolor (`SU(3)_c`) Diquark Fusion & Baryon Singlet Closure**: The non-associative
   cross-product coupling in Zorn multiplication fuses two triplet quarks into an antitriplet
   diquark (`U(u₁) · U(u₂) = V(u₁ × u₂)`, i.e. `3 ⊗ 3 → 3̄`), and three quarks into a
   color-singlet scalar baryon proportional to the 3×3 determinant `u₃ · (u₁ × u₂)`
   (`{U(u₃), U(u₁) · U(u₂)} = det(u₃, u₁, u₂) I`, i.e. `3 ⊗ 3 ⊗ 3 → 1`).
5. **Hurwitz–Zorn Composition Law**: Despite being both non-commutative and non-associative,
   the Zorn split-octonion algebra preserves the exact multiplicative quadratic norm
   `N(X · Y) = N(X) N(Y)`.
6. **Canonical Carrier Isomorphism**: Explicit linear and multiplicative equivalences bridging
   `ColorVec3 R` and `ZornAlgebra R` to `InfoGeometry.Algebra.ZornVec3 R` and
   `InfoGeometry.Algebra.ZornVectorMatrix R`.
-/

namespace InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-! ## Section 1: 3D Supercolor Vector Space (`ColorVec3 R`) & Bridge to `ZornVec3 R` -/

/-- The 3-dimensional color module `R³` carrying the fundamental `3` and antifundamental `3̄`
    off-diagonal components of a Zorn split-octonion vector matrix. -/
@[ext]
structure ColorVec3 (R : Type*) where
  c₁ : R
  c₂ : R
  c₃ : R
  deriving DecidableEq, Repr

namespace ColorVec3

variable {R : Type*} [CommRing R]

/-- Zero 3-vector. -/
@[simp]
def zero : ColorVec3 R := ⟨0, 0, 0⟩

/-- Componentwise addition of 3-vectors. -/
@[simp]
def add (u v : ColorVec3 R) : ColorVec3 R :=
  ⟨u.c₁ + v.c₁, u.c₂ + v.c₂, u.c₃ + v.c₃⟩

/-- Componentwise negation of a 3-vector. -/
@[simp]
def neg (u : ColorVec3 R) : ColorVec3 R :=
  ⟨-u.c₁, -u.c₂, -u.c₃⟩

/-- Componentwise subtraction of a 3-vector. -/
@[simp]
def sub (u v : ColorVec3 R) : ColorVec3 R :=
  ⟨u.c₁ - v.c₁, u.c₂ - v.c₂, u.c₃ - v.c₃⟩

/-- Scalar multiplication on a 3-vector. -/
@[simp]
def smul (k : R) (u : ColorVec3 R) : ColorVec3 R :=
  ⟨k * u.c₁, k * u.c₂, k * u.c₃⟩

instance : Inhabited (ColorVec3 R) := ⟨zero⟩

private def nsmulVec : ℕ → ColorVec3 R → ColorVec3 R
  | 0, _ => zero
  | n + 1, u => add (nsmulVec n u) u

private def zsmulVec : ℤ → ColorVec3 R → ColorVec3 R
  | Int.ofNat n, u => nsmulVec n u
  | Int.negSucc n, u => neg (nsmulVec (n + 1) u)

theorem add_assoc_vec (u v w : ColorVec3 R) : add (add u v) w = add u (add v w) := by
  ext <;> simp [add, _root_.add_assoc]

theorem zero_add_vec (u : ColorVec3 R) : add zero u = u := by
  ext <;> simp [add, zero]

theorem add_zero_vec (u : ColorVec3 R) : add u zero = u := by
  ext <;> simp [add, zero]

theorem sub_eq_add_neg_vec (u v : ColorVec3 R) : sub u v = add u (neg v) := by
  ext <;> simp [sub, add, neg, _root_.sub_eq_add_neg]

theorem neg_add_cancel_vec (u : ColorVec3 R) : add (neg u) u = zero := by
  ext <;> simp [add, neg, zero]

theorem add_comm_vec (u v : ColorVec3 R) : add u v = add v u := by
  ext <;> simp [add, _root_.add_comm]

instance : AddCommGroup (ColorVec3 R) where
  add := add
  add_assoc := add_assoc_vec
  zero := zero
  zero_add := zero_add_vec
  add_zero := add_zero_vec
  nsmul := nsmulVec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg := neg
  sub := sub
  sub_eq_add_neg := sub_eq_add_neg_vec
  zsmul := zsmulVec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  neg_add_cancel := neg_add_cancel_vec
  add_comm := add_comm_vec

theorem one_smul_vec (u : ColorVec3 R) : smul (1 : R) u = u := by
  ext <;> simp [smul]

theorem mul_smul_vec (r s : R) (u : ColorVec3 R) : smul (r * s) u = smul r (smul s u) := by
  ext <;> simp [smul, mul_assoc]

theorem smul_zero_vec (r : R) : smul r (zero : ColorVec3 R) = zero := by
  ext <;> simp [smul, zero]

theorem smul_add_vec (r : R) (u v : ColorVec3 R) : smul r (add u v) = add (smul r u) (smul r v) := by
  ext <;> simp [smul, add, mul_add]

theorem add_smul_vec (r s : R) (u : ColorVec3 R) : smul (r + s) u = add (smul r u) (smul s u) := by
  ext <;> simp [smul, add, add_mul]

theorem zero_smul_vec (u : ColorVec3 R) : smul (0 : R) u = zero := by
  ext <;> simp [smul, zero]

instance : Module R (ColorVec3 R) where
  smul := smul
  one_smul := one_smul_vec
  mul_smul := mul_smul_vec
  smul_zero := smul_zero_vec
  smul_add := smul_add_vec
  add_smul := add_smul_vec
  zero_smul := zero_smul_vec

/-- Red basis color vector `e_r = (1, 0, 0)`. -/
def e_r : ColorVec3 R := ⟨1, 0, 0⟩

/-- Green basis color vector `e_g = (0, 1, 0)`. -/
def e_g : ColorVec3 R := ⟨0, 1, 0⟩

/-- Blue basis color vector `e_b = (0, 0, 1)`. -/
def e_b : ColorVec3 R := ⟨0, 0, 1⟩

/-- Non-degeneracy witness: the red basis color vector over `ℤ` is non-zero. -/
theorem e_r_ne_zero : (e_r : ColorVec3 ℤ) ≠ zero := by
  intro h
  have h1 : (e_r : ColorVec3 ℤ).c₁ = (zero : ColorVec3 ℤ).c₁ := congrArg ColorVec3.c₁ h
  revert h1
  decide

/-- Non-degeneracy witness: distinct color basis vectors over `ℤ` are distinct. -/
theorem e_r_ne_e_g : (e_r : ColorVec3 ℤ) ≠ e_g := by
  intro h
  have h1 : (e_r : ColorVec3 ℤ).c₁ = (e_g : ColorVec3 ℤ).c₁ := congrArg ColorVec3.c₁ h
  revert h1
  decide

/-- Bilinear inner pairing `u · v` between fundamental (`3`) and antifundamental (`3̄`)
    color vectors. -/
def dot (u v : ColorVec3 R) : R :=
  u.c₁ * v.c₁ + u.c₂ * v.c₂ + u.c₃ * v.c₃

/-- Exterior cross product `u × v` implementing `SU(3)_c` diquark antisymmetrization
    `3 × 3 → 3̄` via the Levi-Civita tensor `ε_{ijk}`. -/
def cross (u v : ColorVec3 R) : ColorVec3 R :=
  ⟨u.c₂ * v.c₃ - u.c₃ * v.c₂,
   u.c₃ * v.c₁ - u.c₁ * v.c₃,
   u.c₁ * v.c₂ - u.c₂ * v.c₁⟩

/-- Scalar triple product `det(u, v, w) = u · (v × w)` measuring the `SU(3)_c`
    baryon singlet volume `ε_{ijk} u_i v_j w_k`. -/
def baryonDet (u v w : ColorVec3 R) : R :=
  dot u (cross v w)

/-- Symmetry of the bilinear color dot pairing. -/
theorem dot_comm (u v : ColorVec3 R) : dot u v = dot v u := by
  dsimp [dot]
  ring

/-- Antisymmetry (Pauli exclusion) of the color cross product on identical vectors: `u × u = 0`. -/
@[simp]
theorem cross_self (u : ColorVec3 R) : cross u u = zero := by
  ext <;> dsimp [cross, zero] <;> ring

/-- Anticommutativity of the color cross product: `u × v = -(v × u)`. -/
theorem cross_anticomm (u v : ColorVec3 R) : cross u v = neg (cross v u) := by
  ext <;> dsimp [cross, neg] <;> ring

/-- Total antisymmetry of the baryon determinant under exchange of the first two quarks. -/
theorem baryonDet_antisymm_12 (u v w : ColorVec3 R) :
    baryonDet v u w = -baryonDet u v w := by
  dsimp [baryonDet, dot, cross]
  ring

/-- Total antisymmetry of the baryon determinant under exchange of the last two quarks. -/
theorem baryonDet_antisymm_23 (u v w : ColorVec3 R) :
    baryonDet u w v = -baryonDet u v w := by
  dsimp [baryonDet, dot, cross]
  ring

/-- Cyclic invariance of the baryon determinant. -/
theorem baryonDet_cyclic (u v w : ColorVec3 R) :
    baryonDet u v w = baryonDet v w u := by
  dsimp [baryonDet, dot, cross]
  ring

/-- **3D Lagrange / Binet–Cauchy Identity**:
    `(u₁ × u₂) · (v₁ × v₂) = (u₁ · v₁)(u₂ · v₂) - (u₁ · v₂)(u₂ · v₁)`.
    This algebraic identity underpins the Hurwitz–Zorn quadratic norm composition law. -/
theorem dot_cross_cross (u₁ u₂ v₁ v₂ : ColorVec3 R) :
    dot (cross u₁ u₂) (cross v₁ v₂) =
      dot u₁ v₁ * dot u₂ v₂ - dot u₁ v₂ * dot u₂ v₁ := by
  dsimp [dot, cross]
  ring

/-- Map a structured 3-color vector to the canonical `Fin 3 → R` carrier `ZornVec3 R`. -/
def toZornVec3 (u : ColorVec3 R) : InfoGeometry.Algebra.ZornVec3 R :=
  ![u.c₁, u.c₂, u.c₃]

/-- Reconstruct a structured 3-color vector from `ZornVec3 R`. -/
def fromZornVec3 (v : InfoGeometry.Algebra.ZornVec3 R) : ColorVec3 R :=
  ⟨v 0, v 1, v 2⟩

/-- Explicit `R`-linear equivalence between `ColorVec3 R` and `InfoGeometry.Algebra.ZornVec3 R`. -/
def equivZornVec3 : ColorVec3 R ≃ₗ[R] InfoGeometry.Algebra.ZornVec3 R where
  toFun := toZornVec3
  invFun := fromZornVec3
  left_inv u := by cases u; rfl
  right_inv v := by
    ext i
    fin_cases i <;> rfl
  map_add' u v := by
    ext i
    fin_cases i <;> rfl
  map_smul' r u := by
    ext i
    fin_cases i <;> rfl

/-- `equivZornVec3` preserves the bilinear dot product. -/
theorem equivZornVec3_dot (u v : ColorVec3 R) :
    InfoGeometry.Algebra.ZornVec3.dot (equivZornVec3 u) (equivZornVec3 v) = dot u v := by
  rw [InfoGeometry.Algebra.ZornVec3.dot_eq_sum_coords]
  rfl

/-- `equivZornVec3` intertwines the exterior cross product. -/
theorem equivZornVec3_cross (u v : ColorVec3 R) :
    equivZornVec3 (cross u v) =
      InfoGeometry.Algebra.ZornVec3.cross (equivZornVec3 u) (equivZornVec3 v) := by
  ext i
  fin_cases i <;> rfl

end ColorVec3

/-! ## Section 2: Zorn Split-Octonion Vector Matrix Algebra (`ZornAlgebra R`) & Bridge to `ZornVectorMatrix R` -/

/-- An element of Zorn's 8-dimensional split-octonion vector-matrix algebra over `R`:
    `X = [[a, u], [v, b]]`, where `a, b : R` are diagonal Peirce scalars and
    `u, v : ColorVec3 R` are off-diagonal 3-color vectors. -/
@[ext]
structure ZornAlgebra (R : Type*) where
  a : R
  u : ColorVec3 R
  v : ColorVec3 R
  b : R
  deriving DecidableEq, Repr

namespace ZornAlgebra

variable {R : Type*} [CommRing R]

/-- Zero element of the Zorn algebra. -/
def zero : ZornAlgebra R :=
  ⟨0, ColorVec3.zero, ColorVec3.zero, 0⟩

/-- Multiplicative identity `I = [[1, 0], [0, 1]]` of the Zorn algebra. -/
def one : ZornAlgebra R :=
  ⟨1, ColorVec3.zero, ColorVec3.zero, 1⟩

/-- Componentwise addition in the Zorn algebra. -/
def add (X Y : ZornAlgebra R) : ZornAlgebra R :=
  ⟨X.a + Y.a, ColorVec3.add X.u Y.u, ColorVec3.add X.v Y.v, X.b + Y.b⟩

/-- Componentwise negation in the Zorn algebra. -/
def neg (X : ZornAlgebra R) : ZornAlgebra R :=
  ⟨-X.a, ColorVec3.neg X.u, ColorVec3.neg X.v, -X.b⟩

/-- Componentwise subtraction in the Zorn algebra. -/
def sub (X Y : ZornAlgebra R) : ZornAlgebra R :=
  ⟨X.a - Y.a, ColorVec3.sub X.u Y.u, ColorVec3.sub X.v Y.v, X.b - Y.b⟩

/-- Scalar multiplication on the Zorn algebra. -/
def smul (k : R) (X : ZornAlgebra R) : ZornAlgebra R :=
  ⟨k * X.a, ColorVec3.smul k X.u, ColorVec3.smul k X.v, k * X.b⟩

instance : One (ZornAlgebra R) := ⟨one⟩
instance : Inhabited (ZornAlgebra R) := ⟨zero⟩

private def nsmulZornAlg : ℕ → ZornAlgebra R → ZornAlgebra R
  | 0, _ => zero
  | n + 1, X => add (nsmulZornAlg n X) X

private def zsmulZornAlg : ℤ → ZornAlgebra R → ZornAlgebra R
  | Int.ofNat n, X => nsmulZornAlg n X
  | Int.negSucc n, X => neg (nsmulZornAlg (n + 1) X)

theorem add_assoc_zorn (X Y Z : ZornAlgebra R) : add (add X Y) Z = add X (add Y Z) := by
  ext <;> simp [add, _root_.add_assoc]

theorem zero_add_zorn (X : ZornAlgebra R) : add zero X = X := by
  ext <;> simp [add, zero]

theorem add_zero_zorn (X : ZornAlgebra R) : add X zero = X := by
  ext <;> simp [add, zero]

theorem sub_eq_add_neg_zorn (X Y : ZornAlgebra R) : sub X Y = add X (neg Y) := by
  ext <;> simp [sub, add, neg, _root_.sub_eq_add_neg]

theorem neg_add_cancel_zorn (X : ZornAlgebra R) : add (neg X) X = zero := by
  ext <;> simp [add, neg, zero]

theorem add_comm_zorn (X Y : ZornAlgebra R) : add X Y = add Y X := by
  ext <;> simp [add, _root_.add_comm]

instance : AddCommGroup (ZornAlgebra R) where
  add := add
  add_assoc := add_assoc_zorn
  zero := zero
  zero_add := zero_add_zorn
  add_zero := add_zero_zorn
  nsmul := nsmulZornAlg
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg := neg
  sub := sub
  sub_eq_add_neg := sub_eq_add_neg_zorn
  zsmul := zsmulZornAlg
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  neg_add_cancel := neg_add_cancel_zorn
  add_comm := add_comm_zorn

theorem one_smul_zorn (X : ZornAlgebra R) : smul (1 : R) X = X := by
  ext <;> simp [smul]

theorem mul_smul_zorn (r s : R) (X : ZornAlgebra R) : smul (r * s) X = smul r (smul s X) := by
  ext <;> simp [smul, mul_assoc]

theorem smul_zero_zorn (r : R) : smul r (zero : ZornAlgebra R) = zero := by
  ext <;> simp [smul, zero]

theorem smul_add_zorn (r : R) (X Y : ZornAlgebra R) : smul r (add X Y) = add (smul r X) (smul r Y) := by
  ext <;> simp [smul, add, mul_add]

theorem add_smul_zorn (r s : R) (X : ZornAlgebra R) : smul (r + s) X = add (smul r X) (smul s X) := by
  ext <;> simp [smul, add, add_mul]

theorem zero_smul_zorn (X : ZornAlgebra R) : smul (0 : R) X = zero := by
  ext <;> simp [smul, zero]

instance : Module R (ZornAlgebra R) where
  smul := smul
  one_smul := one_smul_zorn
  mul_smul := mul_smul_zorn
  smul_zero := smul_zero_zorn
  smul_add := smul_add_zorn
  add_smul := add_smul_zorn
  zero_smul := zero_smul_zorn

/-- **Zorn Split-Octonion Multiplication**:
    `[[a₁, u₁], [v₁, b₁]] · [[a₂, u₂], [v₂, b₂]] =`
    `[[a₁ a₂ + u₁ · v₂, b₂ u₁ + a₁ u₂ - v₁ × v₂], [b₁ v₂ + a₂ v₁ + u₁ × u₂, v₁ · u₂ + b₁ b₂]]`. -/
def mul (X Y : ZornAlgebra R) : ZornAlgebra R :=
  { a := X.a * Y.a + ColorVec3.dot X.u Y.v
    u := ColorVec3.add (ColorVec3.smul Y.b X.u)
           (ColorVec3.sub (ColorVec3.smul X.a Y.u) (ColorVec3.cross X.v Y.v))
    v := ColorVec3.add (ColorVec3.smul X.b Y.v)
           (ColorVec3.add (ColorVec3.smul Y.a X.v) (ColorVec3.cross X.u Y.u))
    b := ColorVec3.dot X.v Y.u + X.b * Y.b }

/-- Zorn trace `Tr(X) = a + b`. -/
def trace (X : ZornAlgebra R) : R :=
  X.a + X.b

/-- Zorn quadratic norm (split-octonion determinant) `N(X) = a b - u · v`. -/
def norm (X : ZornAlgebra R) : R :=
  X.a * X.b - ColorVec3.dot X.u X.v

/-- Zorn octonionic conjugation (adjugate involution)
    `X̄ = [[b, -u], [-v, a]]`. -/
def conj (X : ZornAlgebra R) : ZornAlgebra R :=
  ⟨X.b, ColorVec3.neg X.u, ColorVec3.neg X.v, X.a⟩

/-- Commutator `[X, Y] = X · Y - Y · X`. -/
def commutator (X Y : ZornAlgebra R) : ZornAlgebra R :=
  sub (mul X Y) (mul Y X)

/-- Anticommutator (Jordan / CAR bracket) `{X, Y} = X · Y + Y · X`. -/
def anticommutator (X Y : ZornAlgebra R) : ZornAlgebra R :=
  add (mul X Y) (mul Y X)

/-- Associator `[X, Y, Z] = (X · Y) · Z - X · (Y · Z)` measuring non-associativity. -/
def associator (X Y Z : ZornAlgebra R) : ZornAlgebra R :=
  sub (mul (mul X Y) Z) (mul X (mul Y Z))

/-- Left multiplicative identity law `I · X = X`. -/
@[simp]
theorem one_mul (X : ZornAlgebra R) : mul one X = X := by
  ext <;> dsimp [mul, one, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Right multiplicative identity law `X · I = X`. -/
@[simp]
theorem mul_one (X : ZornAlgebra R) : mul X one = X := by
  ext <;> dsimp [mul, one, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Quadratic Cayley–Hamilton / Norm-Conjugation Identity**:
    `X · X̄ = N(X) I`. -/
theorem mul_conj (X : ZornAlgebra R) : mul X (conj X) = smul (norm X) one := by
  ext <;> dsimp [mul, conj, norm, one, smul, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.neg, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Left conjugation identity `X̄ · X = N(X) I`. -/
theorem conj_mul (X : ZornAlgebra R) : mul (conj X) X = smul (norm X) one := by
  ext <;> dsimp [mul, conj, norm, one, smul, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.neg, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Hurwitz–Zorn Composition Law**:
    The quadratic norm on the 8-dimensional non-associative Zorn split-octonion algebra
    is strictly multiplicative: `N(X · Y) = N(X) N(Y)`. -/
theorem norm_mul (X Y : ZornAlgebra R) : norm (mul X Y) = norm X * norm Y := by
  dsimp [norm, mul, ColorVec3.dot, ColorVec3.add, ColorVec3.sub,
    ColorVec3.smul, ColorVec3.cross]
  ring

/-- Map `ZornAlgebra R` to the canonical carrier `InfoGeometry.Algebra.ZornVectorMatrix R`. -/
def toZornVectorMatrix (X : ZornAlgebra R) : InfoGeometry.Algebra.ZornVectorMatrix R :=
  ⟨X.a, ColorVec3.toZornVec3 X.u, ColorVec3.toZornVec3 X.v, X.b⟩

/-- Reconstruct `ZornAlgebra R` from `InfoGeometry.Algebra.ZornVectorMatrix R`. -/
def fromZornVectorMatrix (M : InfoGeometry.Algebra.ZornVectorMatrix R) : ZornAlgebra R :=
  ⟨M.a, ColorVec3.fromZornVec3 M.v, ColorVec3.fromZornVec3 M.w, M.b⟩

/-- Explicit `R`-linear equivalence between `ZornAlgebra R` and
    `InfoGeometry.Algebra.ZornVectorMatrix R`. -/
def equivZornVectorMatrix :
    ZornAlgebra R ≃ₗ[R] InfoGeometry.Algebra.ZornVectorMatrix R where
  toFun := toZornVectorMatrix
  invFun := fromZornVectorMatrix
  left_inv X := by
    rcases X with ⟨a, ⟨u₁, u₂, u₃⟩, ⟨v₁, v₂, v₃⟩, b⟩
    rfl
  right_inv M := by
    ext i
    · rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · rfl
  map_add' X Y := by
    ext i
    · rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · rfl
  map_smul' r X := by
    ext i
    · rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · rfl

/-- `equivZornVectorMatrix` is a multiplicative isomorphism with respect to the canonical
    Zorn product `InfoGeometry.Algebra.ZornVectorMatrix.mul`. -/
theorem equivZornVectorMatrix_mul (X Y : ZornAlgebra R) :
    equivZornVectorMatrix (mul X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (equivZornVectorMatrix X) (equivZornVectorMatrix Y) := by
  ext i
  · change X.a * Y.a + ColorVec3.dot X.u Y.v =
      X.a * Y.a + InfoGeometry.Algebra.ZornVec3.dot
        (ColorVec3.toZornVec3 X.u) (ColorVec3.toZornVec3 Y.v)
    rw [InfoGeometry.Algebra.ZornVec3.dot_eq_sum_coords]
    rfl
  · fin_cases i <;>
      simp [equivZornVectorMatrix, toZornVectorMatrix, mul,
        ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross, ColorVec3.toZornVec3,
        InfoGeometry.Algebra.ZornVectorMatrix.mul, InfoGeometry.Algebra.ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [equivZornVectorMatrix, toZornVectorMatrix, mul,
        ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross, ColorVec3.toZornVec3,
        InfoGeometry.Algebra.ZornVectorMatrix.mul, InfoGeometry.Algebra.ZornVec3.cross] <;>
      ring
  · change ColorVec3.dot X.v Y.u + X.b * Y.b =
      InfoGeometry.Algebra.ZornVec3.dot
        (ColorVec3.toZornVec3 X.v) (ColorVec3.toZornVec3 Y.u) + X.b * Y.b
    rw [InfoGeometry.Algebra.ZornVec3.dot_eq_sum_coords]
    rfl

/-! ## Section 3: Peirce Idempotent Decomposition & Penrose Chiral Zig-Zag Mass Generation -/

/-- Upper-left (left-chiral / causal future) Peirce idempotent `e₁ = [[1, 0], [0, 0]]`. -/
def e₁ : ZornAlgebra R :=
  ⟨1, ColorVec3.zero, ColorVec3.zero, 0⟩

/-- Lower-right (right-chiral / causal past) Peirce idempotent `e₂ = [[0, 0], [0, 1]]`. -/
def e₂ : ZornAlgebra R :=
  ⟨0, ColorVec3.zero, ColorVec3.zero, 1⟩

/-- `e₁` is an idempotent: `e₁² = e₁`. -/
@[simp]
theorem e₁_idempotent : mul (e₁ : ZornAlgebra R) e₁ = e₁ := by
  ext <;> dsimp [mul, e₁, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- `e₂` is an idempotent: `e₂² = e₂`. -/
@[simp]
theorem e₂_idempotent : mul (e₂ : ZornAlgebra R) e₂ = e₂ := by
  ext <;> dsimp [mul, e₂, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Mutual orthogonality of Peirce idempotents: `e₁ · e₂ = 0`. -/
@[simp]
theorem e₁_mul_e₂_zero : mul (e₁ : ZornAlgebra R) e₂ = zero := by
  ext <;> dsimp [mul, e₁, e₂, zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Mutual orthogonality of Peirce idempotents: `e₂ · e₁ = 0`. -/
@[simp]
theorem e₂_mul_e₁_zero : mul (e₂ : ZornAlgebra R) e₁ = zero := by
  ext <;> dsimp [mul, e₁, e₂, zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Partition of unity: `e₁ + e₂ = I`. -/
theorem peirce_partition_of_unity : add (e₁ : ZornAlgebra R) e₂ = one := by
  ext <;> dsimp [add, e₁, e₂, one, ColorVec3.add, ColorVec3.zero] <;> ring

/-- **Penrose Chiral Nullity (Left Ray)**:
    A pure left-chiral mode `m_L e₁` has identically zero quadratic norm (`N(m_L e₁) = 0`). -/
@[simp]
theorem norm_smul_e₁_zero (m_L : R) : norm (smul m_L (e₁ : ZornAlgebra R)) = 0 := by
  dsimp [norm, smul, e₁, ColorVec3.smul, ColorVec3.zero, ColorVec3.dot]
  ring

/-- **Penrose Chiral Nullity (Right Ray)**:
    A pure right-chiral mode `m_R e₂` has identically zero quadratic norm (`N(m_R e₂) = 0`). -/
@[simp]
theorem norm_smul_e₂_zero (m_R : R) : norm (smul m_R (e₂ : ZornAlgebra R)) = 0 := by
  dsimp [norm, smul, e₂, ColorVec3.smul, ColorVec3.zero, ColorVec3.dot]
  ring

/-- **Penrose Zig-Zag Mass Generation**:
    Although each chiral projector ray `m_L e₁` and `m_R e₂` is individually massless/null
    (`N(m_L e₁) = N(m_R e₂) = 0`), their coherent superposition `m_L e₁ + m_R e₂` acquires
    the non-zero quadratic determinant `N(m_L e₁ + m_R e₂) = m_L m_R`. -/
theorem penrose_zigzag_mass_norm (m_L m_R : R) :
    norm (add (smul m_L (e₁ : ZornAlgebra R)) (smul m_R e₂)) = m_L * m_R := by
  dsimp [norm, add, smul, e₁, e₂, ColorVec3.add, ColorVec3.smul, ColorVec3.zero, ColorVec3.dot]
  ring

/-- Peirce `(1,1)` projection `P₁₁(X) = e₁ · (X · e₁)`. -/
def peirce11 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₁ (mul X e₁)

/-- Peirce `(1,2)` projection `P₁₂(X) = e₁ · (X · e₂)`. -/
def peirce12 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₁ (mul X e₂)

/-- Peirce `(2,1)` projection `P₂₁(X) = e₂ · (X · e₁)`. -/
def peirce21 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₂ (mul X e₁)

/-- Peirce `(2,2)` projection `P₂₂(X) = e₂ · (X · e₂)`. -/
def peirce22 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₂ (mul X e₂)

/-- Explicit matrix form of `P₁₁(X) = [[X.a, 0], [0, 0]]`. -/
theorem peirce11_eq (X : ZornAlgebra R) :
    peirce11 X = ⟨X.a, ColorVec3.zero, ColorVec3.zero, 0⟩ := by
  ext <;> dsimp [peirce11, mul, e₁, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Explicit matrix form of `P₁₂(X) = [[0, X.u], [0, 0]]` (upper off-diagonal quark sector). -/
theorem peirce12_eq (X : ZornAlgebra R) :
    peirce12 X = ⟨0, X.u, ColorVec3.zero, 0⟩ := by
  ext <;> dsimp [peirce12, mul, e₁, e₂, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Explicit matrix form of `P₂₁(X) = [[0, 0], [X.v, 0]]` (lower off-diagonal antiquark sector). -/
theorem peirce21_eq (X : ZornAlgebra R) :
    peirce21 X = ⟨0, ColorVec3.zero, X.v, 0⟩ := by
  ext <;> dsimp [peirce21, mul, e₁, e₂, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Explicit matrix form of `P₂₂(X) = [[0, 0], [0, X.b]]`. -/
theorem peirce22_eq (X : ZornAlgebra R) :
    peirce22 X = ⟨0, ColorVec3.zero, ColorVec3.zero, X.b⟩ := by
  ext <;> dsimp [peirce22, mul, e₂, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Peirce Four-Block Completeness Theorem**:
    Every Zorn split-octonion element decomposes uniquely into the sum of its four
    Peirce bigraded components: `P₁₁(X) + P₁₂(X) + P₂₁(X) + P₂₂(X) = X`. -/
theorem peirce_four_block_completeness (X : ZornAlgebra R) :
    add (add (peirce11 X) (peirce12 X)) (add (peirce21 X) (peirce22 X)) = X := by
  rw [peirce11_eq, peirce12_eq, peirce21_eq, peirce22_eq]
  ext <;> dsimp [add, ColorVec3.add, ColorVec3.zero] <;> ring

/-! ## Section 4: DeWitt `ℤ₂` Super-Grading & Superalgebra Parity Laws -/

/-- **DeWitt Bosonic (Even) Projection**:
    `X_even = P₁₁(X) + P₂₂(X) = [[X.a, 0], [0, X.b]]`. -/
def dewittEven (X : ZornAlgebra R) : ZornAlgebra R :=
  add (peirce11 X) (peirce22 X)

/-- **DeWitt Fermionic (Odd) Projection**:
    `X_odd = P₁₂(X) + P₂₁(X) = [[0, X.u], [X.v, 0]]`. -/
def dewittOdd (X : ZornAlgebra R) : ZornAlgebra R :=
  add (peirce12 X) (peirce21 X)

/-- Explicit diagonal form of `dewittEven X`. -/
theorem dewittEven_eq (X : ZornAlgebra R) :
    dewittEven X = ⟨X.a, ColorVec3.zero, ColorVec3.zero, X.b⟩ := by
  rw [dewittEven, peirce11_eq, peirce22_eq]
  ext <;> dsimp [add, ColorVec3.add, ColorVec3.zero] <;> ring

/-- Explicit off-diagonal form of `dewittOdd X`. -/
theorem dewittOdd_eq (X : ZornAlgebra R) :
    dewittOdd X = ⟨0, X.u, X.v, 0⟩ := by
  rw [dewittOdd, peirce12_eq, peirce21_eq]
  ext <;> dsimp [add, ColorVec3.add, ColorVec3.zero] <;> ring

/-- **Peirce–DeWitt Super-Decomposition Completeness**:
    `X_even + X_odd = X`. -/
theorem peirce_dewitt_completeness (X : ZornAlgebra R) :
    add (dewittEven X) (dewittOdd X) = X := by
  rw [dewittEven_eq, dewittOdd_eq]
  ext <;> dsimp [add, ColorVec3.add, ColorVec3.zero] <;> ring

/-- Idempotency of the Bosonic (Even) projector. -/
@[simp]
theorem dewittEven_idem (X : ZornAlgebra R) :
    dewittEven (dewittEven X) = dewittEven X := by
  rw [dewittEven_eq, dewittEven_eq]

/-- Idempotency of the Fermionic (Odd) projector. -/
@[simp]
theorem dewittOdd_idem (X : ZornAlgebra R) :
    dewittOdd (dewittOdd X) = dewittOdd X := by
  rw [dewittOdd_eq, dewittOdd_eq]

/-- Orthogonality of Even and Odd projectors: `Even(Odd(X)) = 0`. -/
@[simp]
theorem dewittEven_odd_zero (X : ZornAlgebra R) :
    dewittEven (dewittOdd X) = zero := by
  rw [dewittOdd_eq, dewittEven_eq]
  rfl

/-- Orthogonality of Odd and Even projectors: `Odd(Even(X)) = 0`. -/
@[simp]
theorem dewittOdd_even_zero (X : ZornAlgebra R) :
    dewittOdd (dewittEven X) = zero := by
  rw [dewittEven_eq, dewittOdd_eq]
  rfl

/-- **Super-Grading Law (Even · Even ⊆ Even)**:
    The product of two Bosonic (Even) Zorn elements has vanishing Fermionic (Odd) part. -/
theorem dewittOdd_mul_even_even (X Y : ZornAlgebra R) :
    dewittOdd (mul (dewittEven X) (dewittEven Y)) = zero := by
  rw [dewittEven_eq, dewittEven_eq, dewittOdd_eq]
  ext <;> dsimp [mul, zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Super-Grading Law (Even · Odd ⊆ Odd)**:
    The product of a Bosonic (Even) and a Fermionic (Odd) Zorn element has vanishing
    Bosonic (Even) part. -/
theorem dewittEven_mul_even_odd (X Y : ZornAlgebra R) :
    dewittEven (mul (dewittEven X) (dewittOdd Y)) = zero := by
  rw [dewittEven_eq, dewittOdd_eq, dewittEven_eq]
  ext <;> dsimp [mul, zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Super-Grading Law (Odd · Even ⊆ Odd)**:
    The product of a Fermionic (Odd) and a Bosonic (Even) Zorn element has vanishing
    Bosonic (Even) part. -/
theorem dewittEven_mul_odd_even (X Y : ZornAlgebra R) :
    dewittEven (mul (dewittOdd X) (dewittEven Y)) = zero := by
  rw [dewittOdd_eq, dewittEven_eq, dewittEven_eq]
  ext <;> dsimp [mul, zero, ColorVec3.zero, ColorVec3.dot, ColorVec3.add,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Bosonic Part of `Odd · Odd` (CAR Inner Pairing)**:
    The Bosonic (Even) part of the product of two Fermionic (Odd) Zorn elements is the
    diagonal inner-product matrix `[[X.u · Y.v, 0], [0, X.v · Y.u]]`. -/
theorem dewittEven_mul_odd_odd (X Y : ZornAlgebra R) :
    dewittEven (mul (dewittOdd X) (dewittOdd Y)) =
      ⟨ColorVec3.dot X.u Y.v, ColorVec3.zero, ColorVec3.zero, ColorVec3.dot X.v Y.u⟩ := by
  rw [dewittOdd_eq, dewittOdd_eq, dewittEven_eq]
  ext <;> dsimp [mul, ColorVec3.zero, ColorVec3.dot] <;> ring

/-- **Fermionic Part of `Odd · Odd` (Octonionic Cross-Product Diquark Anomaly)**:
    Unlike an associative `2×2` supermatrix where `Odd · Odd` has zero Odd part, in the
    non-associative Zorn split-octonion algebra `Odd(Odd(X) · Odd(Y))` equals the exterior
    cross-product diquark/antidiquark channel `[[0, -(X.v × Y.v)], [X.u × Y.u, 0]]`. -/
theorem dewittOdd_mul_odd_odd (X Y : ZornAlgebra R) :
    dewittOdd (mul (dewittOdd X) (dewittOdd Y)) =
      ⟨0, ColorVec3.neg (ColorVec3.cross X.v Y.v), ColorVec3.cross X.u Y.u, 0⟩ := by
  rw [dewittOdd_eq, dewittOdd_eq, dewittOdd_eq]
  ext <;> dsimp [mul, ColorVec3.zero, ColorVec3.add, ColorVec3.sub,
    ColorVec3.neg, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- When the cross products `X.u × Y.u = 0` and `X.v × Y.v = 0` vanish (e.g., on collinear
    color rays or opposite-chirality quark/antiquark pairs), `Odd · Odd` is purely Bosonic (Even). -/
theorem dewittOdd_mul_odd_odd_of_cross_zero (X Y : ZornAlgebra R)
    (hu : ColorVec3.cross X.u Y.u = ColorVec3.zero)
    (hv : ColorVec3.cross X.v Y.v = ColorVec3.zero) :
    dewittOdd (mul (dewittOdd X) (dewittOdd Y)) = zero := by
  rw [dewittOdd_mul_odd_odd, hu, hv]
  ext <;> dsimp [zero, ColorVec3.zero, ColorVec3.neg] <;> ring

/-! ## Section 5: Quantized Zorn Odd Generators, CAR Anticommutation & Supercolor Baryon Confinement -/

/-- Upper-right Peirce `(1,2)` Fermionic creation / quark generator
    `U(u) = [[0, u], [0, 0]]`. -/
def quarkU (u : ColorVec3 R) : ZornAlgebra R :=
  ⟨0, u, ColorVec3.zero, 0⟩

/-- Lower-left Peirce `(2,1)` Fermionic annihilation / antiquark generator
    `V(v) = [[0, 0], [v, 0]]`. -/
def antiquarkV (v : ColorVec3 R) : ZornAlgebra R :=
  ⟨0, ColorVec3.zero, v, 0⟩

/-- Left Peirce chirality of `U(u)`: `e₁ · U(u) = U(u)`. -/
@[simp]
theorem e₁_mul_quarkU (u : ColorVec3 R) : mul e₁ (quarkU u) = quarkU u := by
  ext <;> dsimp [mul, e₁, quarkU, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Right Peirce chirality of `U(u)`: `U(u) · e₂ = U(u)`. -/
@[simp]
theorem quarkU_mul_e₂ (u : ColorVec3 R) : mul (quarkU u) e₂ = quarkU u := by
  ext <;> dsimp [mul, e₂, quarkU, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Left chiral annihilation of `U(u)`: `e₂ · U(u) = 0`. -/
@[simp]
theorem e₂_mul_quarkU (u : ColorVec3 R) : mul e₂ (quarkU u) = zero := by
  ext <;> dsimp [mul, e₂, quarkU, zero, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Right chiral annihilation of `U(u)`: `U(u) · e₁ = 0`. -/
@[simp]
theorem quarkU_mul_e₁ (u : ColorVec3 R) : mul (quarkU u) e₁ = zero := by
  ext <;> dsimp [mul, e₁, quarkU, zero, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Left Peirce chirality of `V(v)`: `e₂ · V(v) = V(v)`. -/
@[simp]
theorem e₂_mul_antiquarkV (v : ColorVec3 R) : mul e₂ (antiquarkV v) = antiquarkV v := by
  ext <;> dsimp [mul, e₂, antiquarkV, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Right Peirce chirality of `V(v)`: `V(v) · e₁ = V(v)`. -/
@[simp]
theorem antiquarkV_mul_e₁ (v : ColorVec3 R) : mul (antiquarkV v) e₁ = antiquarkV v := by
  ext <;> dsimp [mul, e₁, antiquarkV, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Left chiral annihilation of `V(v)`: `e₁ · V(v) = 0`. -/
@[simp]
theorem e₁_mul_antiquarkV (v : ColorVec3 R) : mul e₁ (antiquarkV v) = zero := by
  ext <;> dsimp [mul, e₁, antiquarkV, zero, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- Right chiral annihilation of `V(v)`: `V(v) · e₂ = 0`. -/
@[simp]
theorem antiquarkV_mul_e₂ (v : ColorVec3 R) : mul (antiquarkV v) e₂ = zero := by
  ext <;> dsimp [mul, e₂, antiquarkV, zero, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Theorem 1 (Canonical CAR Quantization in the Zorn Split-Octonion Algebra)**:
    The anticommutator of a quark generator `U(u)` in Peirce `(1,2)` and an antiquark
    generator `V(v)` in Peirce `(2,1)` closes into the Bosonic identity `I = e₁ + e₂`
    weighted by the color inner pairing `u · v`:
    `{U(u), V(v)} = U(u) · V(v) + V(v) · U(u) = (u · v) I`. -/
theorem zorn_car_quantization_exact (u v : ColorVec3 R) :
    anticommutator (quarkU u) (antiquarkV v) = smul (ColorVec3.dot u v) one := by
  ext <;> dsimp [anticommutator, add, mul, quarkU, antiquarkV, smul, one,
    ColorVec3.zero, ColorVec3.dot, ColorVec3.add, ColorVec3.sub,
    ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Pauli Exclusion / Fermi Nilpotency (Quark Sector)**:
    Every single-mode quark generator squares to zero: `U(u) · U(u) = 0`. -/
@[simp]
theorem quarkU_sq_zero (u : ColorVec3 R) : mul (quarkU u) (quarkU u) = zero := by
  ext <;> dsimp [mul, quarkU, zero, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Pauli Exclusion / Fermi Nilpotency (Antiquark Sector)**:
    Every single-mode antiquark generator squares to zero: `V(v) · V(v) = 0`. -/
@[simp]
theorem antiquarkV_sq_zero (v : ColorVec3 R) : mul (antiquarkV v) (antiquarkV v) = zero := by
  ext <;> dsimp [mul, antiquarkV, zero, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Theorem 2 (Supercolor Diquark Fusion `3 ⊗ 3 → 3̄`)**:
    Multiplying two fundamental quark generators `U(u₁)` and `U(u₂)` in the Zorn algebra
    automatically projects onto the antifundamental antiquark sector `V(u₁ × u₂)` via the
    antisymmetric `SU(3)_c` cross product:
    `U(u₁) · U(u₂) = V(u₁ × u₂)`. -/
theorem supercolor_diquark_fusion (u₁ u₂ : ColorVec3 R) :
    mul (quarkU u₁) (quarkU u₂) = antiquarkV (ColorVec3.cross u₁ u₂) := by
  ext <;> dsimp [mul, quarkU, antiquarkV, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Dual Antidiquark Fusion (`3̄ ⊗ 3̄ → 3`)**:
    Multiplying two antifundamental antiquark generators `V(v₁)` and `V(v₂)` projects onto
    the negative fundamental quark sector `-U(v₁ × v₂)`:
    `V(v₁) · V(v₂) = -U(v₁ × v₂)`. -/
theorem supercolor_antidiquark_fusion (v₁ v₂ : ColorVec3 R) :
    mul (antiquarkV v₁) (antiquarkV v₂) = neg (quarkU (ColorVec3.cross v₁ v₂)) := by
  ext <;> dsimp [mul, quarkU, antiquarkV, neg, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.add, ColorVec3.sub, ColorVec3.neg, ColorVec3.smul, ColorVec3.cross] <;> ring

/-- **Theorem 3 (Color-Singlet Baryon Vertex Closure `3 ⊗ 3 ⊗ 3 → 1`)**:
    Combining a third quark `U(u₃)` with the diquark state `U(u₁) · U(u₂)` via the CAR
    anticommutator closes into the Bosonic color-singlet identity `I` multiplied by the
    totally antisymmetric 3×3 determinant `det(u₃, u₁, u₂) = u₃ · (u₁ × u₂)`:
    `{U(u₃), U(u₁) · U(u₂)} = det(u₃, u₁, u₂) I`. -/
theorem supercolor_baryon_singlet_closure (u₁ u₂ u₃ : ColorVec3 R) :
    anticommutator (quarkU u₃) (mul (quarkU u₁) (quarkU u₂)) =
      smul (ColorVec3.baryonDet u₃ u₁ u₂) one := by
  rw [supercolor_diquark_fusion, zorn_car_quantization_exact]
  rfl

/-- **Canonical RGB Baryon Unit Normalization**:
    For the three orthonormal color basis states `e_r, e_g, e_b`, the baryon vertex
    anticommutator yields the exact multiplicative identity `I` of the Zorn algebra:
    `{U(e_r), U(e_g) · U(e_b)} = I`. -/
theorem rgb_baryon_singlet_unit :
    anticommutator (quarkU (ColorVec3.e_r : ColorVec3 R))
      (mul (quarkU ColorVec3.e_g) (quarkU ColorVec3.e_b)) = one := by
  rw [supercolor_baryon_singlet_closure]
  ext <;> dsimp [smul, one, ColorVec3.baryonDet, ColorVec3.dot, ColorVec3.cross,
    ColorVec3.e_r, ColorVec3.e_g, ColorVec3.e_b, ColorVec3.smul, ColorVec3.zero] <;> ring

/-- **Theorem 4a (Non-Commutative Witness over `ℤ`)**:
    The Zorn algebra is non-commutative: `[e₁, U(e_r)] = U(e_r) ≠ 0`. -/
theorem zorn_noncommutative_witness :
    commutator (e₁ : ZornAlgebra ℤ) (quarkU ColorVec3.e_r) ≠ zero := by
  intro h
  have h1 : (commutator (e₁ : ZornAlgebra ℤ) (quarkU ColorVec3.e_r)).u.c₁ =
      (zero : ZornAlgebra ℤ).u.c₁ :=
    congrArg (fun X => X.u.c₁) h
  revert h1
  decide

/-- **Theorem 4b (Non-Associative Octonionic Witness over `ℤ`)**:
    The Zorn split-octonion algebra is genuinely non-associative:
    `(U(e_r) · U(e_g)) · V(e_r) - U(e_r) · (U(e_g) · V(e_r)) ≠ 0`. -/
theorem zorn_nonassociative_witness :
    associator
      (quarkU (ColorVec3.e_r : ColorVec3 ℤ))
      (quarkU ColorVec3.e_g)
      (antiquarkV ColorVec3.e_r) ≠ zero := by
  intro h
  have h1 :
      (associator
        (quarkU (ColorVec3.e_r : ColorVec3 ℤ))
        (quarkU ColorVec3.e_g)
        (antiquarkV ColorVec3.e_r)).u.c₂ =
      (zero : ZornAlgebra ℤ).u.c₂ :=
    congrArg (fun X => X.u.c₂) h
  revert h1
  decide

end ZornAlgebra

end InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

namespace InfoGeometry.Superalgebra.PeirceZorn

export InfoGeometry.Superalgebra.PeirceDeWittZornQuantization (ColorVec3 ZornAlgebra)

end InfoGeometry.Superalgebra.PeirceZorn

