import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic

/-!
# arXiv:1603.09063 split-algebra nucleus

This file records a small theorem-safe kernel from Fioresi--Latini--Marrani,
"Klein and Conformal Superspaces, Split Algebras and Spinor Orbits"
(arXiv:1603.09063v2).

It formalizes only the finite coordinate identities from §2, §5, and §6:

* split complex numbers `α + jβ`, with `j² = 1`;
* conjugation and norm `α² - β²`;
* the lightlike idempotent-like elements `E = 1 + j`, `Ebar = 1 - j`;
* the `D = (2,2)` Hermitian `2 × 2` determinant identity
  `det [[x₊, a], [ā, x₋]] = x₁² + x₂² - x₃² - x₄²`;
* split quaternions in the paper's basis `α + jβ + kγ + (kj)δ`;
* the `D = (3,3)` Hermitian determinant identity from equation (6.2).

No global theorem about `Spin(2,2)`, `Spin(3,3)`, conformal superspace,
or spinor-orbit classification is claimed here.
-/

namespace InfoGeometry.Clifford.Arxiv160309063

/-- Split-complex coordinate model `a + j b`, over `ℚ` for exact arithmetic. -/
structure SplitC where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace SplitC

/-- Addition in coordinates. -/
def add (x y : SplitC) : SplitC :=
  ⟨x.re + y.re, x.im + y.im⟩

/-- Negation in coordinates. -/
def neg (x : SplitC) : SplitC :=
  ⟨-x.re, -x.im⟩

/-- Multiplication with `j² = 1`. -/
def mul (x y : SplitC) : SplitC :=
  ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re⟩

/-- Conjugation `a + jb ↦ a - jb`. -/
def conj (x : SplitC) : SplitC :=
  ⟨x.re, -x.im⟩

/-- Split-complex norm `a² - b²`. -/
def norm (x : SplitC) : ℚ :=
  x.re * x.re - x.im * x.im

/-- Scalar embedding. -/
def scalar (r : ℚ) : SplitC :=
  ⟨r, 0⟩

/-- The unit `1`. -/
def one : SplitC := scalar 1

/-- The generator `j`. -/
def j : SplitC := ⟨0, 1⟩

/-- The lightlike element `E = 1 + j` from equation (2.6). -/
def E : SplitC := ⟨1, 1⟩

/-- The conjugate lightlike element `Ebar = 1 - j`. -/
def Ebar : SplitC := ⟨1, -1⟩

/-- Coordinate extensionality helper. -/
theorem ext {x y : SplitC} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem j_sq : mul j j = one := by
  simp [mul, j, one, scalar]

@[simp] theorem conj_conj (x : SplitC) : conj (conj x) = x := by
  cases x
  simp [conj]

/-- Equation (2.3): `a * ā = |a|²`. -/
theorem mul_conj_eq_norm (x : SplitC) :
    mul x (conj x) = scalar (norm x) := by
  cases x
  simp [mul, conj, scalar, norm]
  ring_nf
  repeat constructor

/-- Equation (2.6): `E² = 2E`. -/
theorem E_sq : mul E E = ⟨2, 2⟩ := by
  norm_num [mul, E]

/-- Conjugate form of equation (2.6): `Ebar² = 2Ebar`. -/
theorem Ebar_sq : mul Ebar Ebar = ⟨2, -2⟩ := by
  norm_num [mul, Ebar]

/-- Equation (2.7): the two lightlike directions annihilate. -/
theorem E_mul_Ebar : mul E Ebar = ⟨0, 0⟩ := by
  norm_num [mul, E, Ebar]

/-- Equation (2.8): `(α + jβ) E = (α + β) E`. -/
theorem mul_E (a b : ℚ) :
    mul ⟨a, b⟩ E = ⟨a + b, a + b⟩ := by
  apply SplitC.ext <;> simp [mul, E]

/-- Conjugate companion: `(α + jβ) Ebar = (α - β) Ebar`. -/
theorem mul_Ebar (a b : ℚ) :
    mul ⟨a, b⟩ Ebar = ⟨a - b, -(a - b)⟩ := by
  apply SplitC.ext
  · simp [mul, Ebar]
    ring
  · simp [mul, Ebar]
    ring

/-- Equation (2.9): exact light-cone decomposition over `ℚ`. -/
theorem lightcone_decomposition (a b : ℚ) :
    add (mul (scalar ((a + b) / 2)) E) (mul (scalar ((a - b) / 2)) Ebar) = ⟨a, b⟩ := by
  apply SplitC.ext
  · simp [add, mul, scalar, E, Ebar]
    ring
  · simp [add, mul, scalar, E, Ebar]
    ring

/-- Determinant of the paper's `J₂(C_s)` matrix in equation (5.4). -/
def klein22HermitianDet (x1 x2 x3 x4 : ℚ) : ℚ :=
  let xp := x1 + x4
  let xm := x1 - x4
  let a : SplitC := ⟨x3, x2⟩
  xp * xm - norm a

/-- Equation (5.6): the `J₂(C_s)` determinant is the `(2,2)` quadratic form. -/
theorem klein22HermitianDet_eq_quadratic (x1 x2 x3 x4 : ℚ) :
    klein22HermitianDet x1 x2 x3 x4 = x1 ^ 2 + x2 ^ 2 - x3 ^ 2 - x4 ^ 2 := by
  simp [klein22HermitianDet, norm]
  ring

end SplitC

/--
Split-quaternion coordinate model in the paper's basis
`α + jβ + kγ + (kj)δ`, over `ℚ` for exact arithmetic.
-/
structure SplitH where
  alpha : ℚ
  beta : ℚ
  gamma : ℚ
  delta : ℚ
  deriving DecidableEq, Repr

namespace SplitH

/-- Addition in coordinates. -/
def add (x y : SplitH) : SplitH :=
  ⟨x.alpha + y.alpha, x.beta + y.beta, x.gamma + y.gamma, x.delta + y.delta⟩

/-- Negation in coordinates. -/
def neg (x : SplitH) : SplitH :=
  ⟨-x.alpha, -x.beta, -x.gamma, -x.delta⟩

/--
Multiplication in the paper's basis `1, j, k, kj`, with
`j²=1`, `k²=-1`, `(kj)²=1`, and `k*j=kj`.
-/
def mul (x y : SplitH) : SplitH :=
  ⟨x.alpha * y.alpha - x.gamma * y.gamma + x.beta * y.beta + x.delta * y.delta,
    x.alpha * y.beta - x.gamma * y.delta + x.beta * y.alpha + x.delta * y.gamma,
    x.alpha * y.gamma + x.gamma * y.alpha - x.beta * y.delta + x.delta * y.beta,
    x.alpha * y.delta + x.gamma * y.beta - x.beta * y.gamma + x.delta * y.alpha⟩

/-- Conjugation from equation (2.13). -/
def star (x : SplitH) : SplitH :=
  ⟨x.alpha, -x.beta, -x.gamma, -x.delta⟩

/-- Split-quaternion norm from equation (2.14). -/
def norm (x : SplitH) : ℚ :=
  x.alpha * x.alpha + x.gamma * x.gamma - x.beta * x.beta - x.delta * x.delta

/-- Scalar embedding. -/
def scalar (r : ℚ) : SplitH :=
  ⟨r, 0, 0, 0⟩

/-- The unit `1`. -/
def one : SplitH := scalar 1

/-- Paper generator `j`, with `j² = 1`. -/
def j : SplitH := ⟨0, 1, 0, 0⟩

/-- Paper generator `k`, with `k² = -1`. -/
def k : SplitH := ⟨0, 0, 1, 0⟩

/-- Paper generator `kj`. -/
def kj : SplitH := ⟨0, 0, 0, 1⟩

/-- Coordinate extensionality helper. -/
theorem ext {x y : SplitH}
    (ha : x.alpha = y.alpha) (hb : x.beta = y.beta)
    (hg : x.gamma = y.gamma) (hd : x.delta = y.delta) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem j_sq : mul j j = one := by
  norm_num [mul, j, one, scalar]

@[simp] theorem k_sq : mul k k = neg one := by
  norm_num [mul, k, neg, one, scalar]

@[simp] theorem kj_sq : mul kj kj = one := by
  norm_num [mul, kj, one, scalar]

@[simp] theorem k_mul_j : mul k j = kj := by
  norm_num [mul, k, j, kj]

@[simp] theorem j_mul_k : mul j k = neg kj := by
  norm_num [mul, j, k, kj, neg]

@[simp] theorem k_mul_kj : mul k kj = neg j := by
  norm_num [mul, k, kj, j, neg]

@[simp] theorem kj_mul_k : mul kj k = j := by
  norm_num [mul, k, kj, j]

@[simp] theorem kj_mul_j : mul kj j = k := by
  norm_num [mul, kj, j, k]

@[simp] theorem j_mul_kj : mul j kj = neg k := by
  norm_num [mul, j, kj, k, neg]

/-- Split-quaternion multiplication is associative in this coordinate model. -/
theorem mul_assoc (x y z : SplitH) : mul (mul x y) z = mul x (mul y z) := by
  cases x
  cases y
  cases z
  simp [mul]
  ring_nf
  repeat constructor

/-- Equation (2.14): `h h* = |h|²`. -/
theorem mul_star_eq_norm (x : SplitH) :
    mul x (star x) = scalar (norm x) := by
  cases x
  simp [mul, star, scalar, norm]
  ring_nf
  repeat constructor

/-- Determinant of the paper's `J₂(H_s)` matrix in equation (6.1). -/
def klein33HermitianDet (x1 x2 x3 x4 x5 x6 : ℚ) : ℚ :=
  let xhatp := x3 + x6
  let xhatm := x3 - x6
  let z : SplitH := ⟨x5, x1, x4, x2⟩
  xhatp * xhatm - norm z

/-- Equation (6.2): the `J₂(H_s)` determinant is the `(3,3)` quadratic form. -/
theorem klein33HermitianDet_eq_quadratic (x1 x2 x3 x4 x5 x6 : ℚ) :
    klein33HermitianDet x1 x2 x3 x4 x5 x6 =
      x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 := by
  simp [klein33HermitianDet, norm]
  ring

end SplitH

namespace SplitC

/-! ## J₂(C_s) Hermitian matrices (Section 5) -/

/-- J₂(C_s) Hermitian matrix (eq 5.4): [[x₊, a], [ā, x₋]] with entries in Cs. -/
structure Herm2x2Cs where
  xp : ℚ  -- x₊ = x₁ + x₄
  xm : ℚ  -- x₋ = x₁ - x₄
  a : SplitC  -- a = x₃ + jx₂

/-- Trace reversal X̃ (eq 5.5): [[x₋, -a], [-ā, x₊]]. -/
def traceReversal (X : Herm2x2Cs) : Herm2x2Cs :=
  ⟨X.xm, X.xp, SplitC.neg X.a⟩

/-- Determinant of J₂(C_s) matrix (eq 5.6). -/
def hermitianDet (X : Herm2x2Cs) : ℚ :=
  X.xp * X.xm - SplitC.norm X.a

/-- The determinant equals the (2,2) quadratic form with explicit witnesses. -/
theorem hermitianDet_eq_quadratic_components (x1 x2 x3 x4 : ℚ) :
    hermitianDet ({
      xp := x1 + x4,
      xm := x1 - x4,
      a := ⟨x3, x2⟩
    } : Herm2x2Cs) = x1 ^ 2 + x2 ^ 2 - x3 ^ 2 - x4 ^ 2 := by
  simp [hermitianDet, norm]
  ring

end SplitC

namespace SplitH

/-! ## Z-map to M₂(C_s) (eq 2.18) -/

/-- The Z-map embedding Hs into M₂(C_s) from equation (2.18). -/
def toMat2x2Cs (h : SplitH) : SplitC × SplitC × SplitC × SplitC :=
  let z11 : SplitC := ⟨h.alpha, h.beta⟩
  let z12 : SplitC := ⟨h.gamma, h.delta⟩
  let z21 : SplitC := ⟨-h.gamma, -h.delta⟩
  let z22 : SplitC := ⟨h.alpha, -h.beta⟩
  (z11, z12, z21, z22)

/-- The Z-map determinant (the `det(Z(M))` condition from eq 6.6). -/
def mat2x2Det (h : SplitH) : ℚ :=
  let (z11, z12, z21, z22) := toMat2x2Cs h
  SplitC.norm (SplitC.mul z11 z22) - SplitC.norm (SplitC.mul z12 z21)

/-! ## J₂(H_s) Hermitian matrices (Section 6) -/

/-- J₂(H_s) Hermitian matrix (eq 6.1): [[x̂₊, z], [z*, x̂₋]] with entries in Hs. -/
structure Herm2x2Hs where
  xhatp : ℚ  -- x̂₊ = x³ + x⁶
  xhatm : ℚ  -- x̂₋ = x³ - x⁶
  z : SplitH  -- z = x⁵ + jx¹ + kx⁴ + (kj)x²

/-- Determinant of J₂(H_s) matrix (eq 6.2). -/
def hermitianDet (X : Herm2x2Hs) : ℚ :=
  X.xhatp * X.xhatm - SplitH.norm X.z

/-- The determinant equals the (3,3) quadratic form with explicit witnesses. -/
theorem hermitianDet_eq_quadratic_components (x1 x2 x3 x4 x5 x6 : ℚ) :
    hermitianDet ({
      xhatp := x3 + x6,
      xhatm := x3 - x6,
      z := SplitH.mk x5 x1 x4 x2
    } : Herm2x2Hs) = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 - x4 ^ 2 - x5 ^ 2 - x6 ^ 2 := by
  simp [hermitianDet, norm]
  ring

end SplitH

/-- The 4×4 symplectic form Ω = [[0,I₂],[-I₂,0]] from equation (6.12). -/
def symplecticForm4x4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

end InfoGeometry.Clifford.Arxiv160309063
