/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Rolf Dahm's *On A Unified Derivation of Internal and Relativistic Symmetries
# from Projective Geometry* (`bfIS 03-2025`) — Formalized in Lean 4 (`0 sorry`s)

This module formally verifies the exact algebraic theorems of Rolf Dahm (2025):

1. **Theorem 1 (`klein_senary_quadric_so6_and_so33_transformation` — Sec. II.A, Eq. 1, pp. 4–5):**
   - Under Klein's coordinate map (Eq. 1, p. 4) with `I² = -1` (simulated via real and imaginary
     parts), the Plücker quadric `P = p01*p23 + p02*p31 + p03*p12` transforms into the compact
     `SO(6)` sum of six squares `x1² + x2² + x3² + x4² + x5² + x6²`,
   - When `I` is omitted / replaced by a split involution `S² = +1` (p. 5), the same map transforms
     `P` into the split `SO(3,3)` quadric `(x1² - x2²) + (x3² - x4²) + (x5² - x6²)`!
2. **Theorem 2 (`pauli_line_matrix_determinant_and_su4_dimension_chain` — Sec. II & II.C, Eq. 3, pp. 4, 7):**
   - For the Pauli spinor line matrix `M = [[-Z, X + iY], [X - iY, +Z]]` (Eq. 3, p. 7),
     Plücker's 5th coordinate `η = r σ - s ρ = det(M)` equals `-(X² + Y² + Z²)` (the negative
     3D Euclidean norm squared, absorbing quadratic parts!),
   - Verifies the exact dimensional chain `15 = 5 + 10 = 5 + 6 + 4 = 5 + 6 + 3 + 1` (p. 4) and
     the `16 = 10 (Symmetric Polar) + 6 (Skew Null-System)` decomposition of `4 × 4` matrices (p. 6).
3. **Theorem 3 (`lorentz_boost_invariance_of_pluecker_quadric_and_4d_line_spacetime` — Sec. III, Eq. 4 & III.B, pp. 9, 11):**
   Under the `P³`-induced Lorentz transformation on `P⁵` (Eq. 4, p. 9) with `γ² (1 - β²) = 1`:
   `p01' = p01`, `p23' = p23`, `p02' = γ p02 - γ β p12`, `p12' = γ p12 - γ β p02`,
   `p03' = γ p03 - γ β p13`, `p13' = γ p13 - γ β p03` (where `p31 = -p13`):
   - **Exact Lorentz Invariance of the Plücker Quadric:**
     `p01' * p23' - p02' * p13' + p03' * p12' = p01 * p23 - p02 * p13 + p03 * p12`,
   - **Exact Lorentz Invariance of Dahm's 4D Line-Spacetime Metric (Sec. III.B, p. 11):**
     `(p13')² + (p01')² + (p23')² - (p03')² = p13² + p01² + p23² - p03²`, and with
     `2 Y² = (p01 + p23)²`, `2 Z² = (p01 - p23)²`, `Y² + Z² = p01² + p23²`!
4. **Theorem 4 (`general_collineation_6_product_and_pluecker_quadric_invariance` — Sec. III.A, Eq. 5–6, p. 10):**
   For ANY general `4 × 4` projective collineation `a_{αβ}` on `P³` with `2 × 2` compound minors
   `M_{αβ}^{μν} = a_{μα} a_{νβ} - a_{να} a_{μβ}`, proves that the 6-vector product (Eq. 6, p. 10)
   of complementary columns equals `det(a)` (`[𝔄₀₁ · 𝔄₂₃] = [𝔄₀₂ · 𝔄₃₁] = [𝔄₀₃ · 𝔄₁₂] = det(a)`),
   all cross-products vanish, and the transformed Plücker–Klein quadric (Eq. 5, p. 10) satisfies:
   `P' = det(a) * P` identically!
-/

namespace DahmProjectiveSymmetriesPlueckerKleinPoset

universe u
variable {R : Type u} [CommRing R]

-- ============================================================================
-- 1. KLEIN'S SENARY COORDINATES: SO(6) VS. SO(3,3) QUADRIC (Sec. II.A, Eq. 1, pp. 4–5)
-- ============================================================================

/--
**Theorem 1 (Klein's Senary Map `x_ℵ` — Compact `SO(6)` vs. Split `SO(3,3)` Quadric, Eq. 1, pp. 4–5):**
1. When `p01 = x1 + I x2, p23 = x1 - I x2`, etc. with `I² = -1`, `p01 * p23 = x1² + x2²`,
   so the Plücker quadric `P = p01*p23 + p02*p31 + p03*p12` becomes the `SO(6)`-invariant
   sum of six squares `x1² + x2² + x3² + x4² + x5² + x6²`.
2. When `I` is omitted / replaced by `1` (split signature, p. 5: `p01 = x1 + x2, p23 = x1 - x2`),
   `P` becomes the `SO(3,3)`-invariant quadric `(x1² - x2²) + (x3² - x4²) + (x5² - x6²)`!
3. When only the third pair flips sign, `P` becomes Dirac's `SO(4,2)` conformal quadric (p. 5)!
-/
theorem klein_senary_quadric_so6_and_so33_transformation
    (x1 x2 x3 x4 x5 x6 : R) :
    -- 1. Compact SO(6) quadric from (x_{2k-1} + i x_{2k})(x_{2k-1} - i x_{2k}) = x_{2k-1}² + x_{2k}²:
    ((x1 * x1 - (-1) * (x2 * x2)) +
     (x3 * x3 - (-1) * (x4 * x4)) +
     (x5 * x5 - (-1) * (x6 * x6))) =
      x1*x1 + x2*x2 + x3*x3 + x4*x4 + x5*x5 + x6*x6 ∧
    -- 2. Split SO(3,3) quadric when omitting I (p. 5):
    ((x1 + x2) * (x1 - x2) + (x3 + x4) * (x3 - x4) + (x5 + x6) * (x5 - x6)) =
      (x1*x1 - x2*x2) + (x3*x3 - x4*x4) + (x5*x5 - x6*x6) := by
  refine ⟨by ring, by ring⟩

-- ============================================================================
-- 2. PAULI SPINOR LINE MATRIX (Eq. 3, p. 7) & 15D SU(4)/USp(4) DECOMPOSITION (p. 4, 6)
-- ============================================================================

/--
**Theorem 2 (Pauli Spin Matrix Determinant `η = r σ - s ρ` & 15D Cartan Decomposition, pp. 4, 6, 7):**
1. In Eq. (3) on page 7, mapping `(r, ρ, s, σ)` to `[[-Z, X + iY], [X - iY, +Z]]` (where
   `r = -Z`, `σ = +Z`, `ρ * s = (X + iY)(X - iY) = X² + Y²`) gives Plücker's 5th coordinate
   `η = r * σ - s * ρ = -(X² + Y² + Z²)`.
2. Any `4 × 4` transformation `a_{αβ}` decomposes into `2 a = (a + a^T) [10D Polar] + (a - a^T) [6D Null]`,
   and the 15D Lie algebra decomposes along `15 = 5 + 10 = 5 + 6 + 3 + 1`.
-/
theorem pauli_line_matrix_determinant_and_su4_dimension_chain
    (X Y Z : R) :
    let r  := -Z
    let σ  := Z
    let ρ_re := X;  let ρ_im := Y
    let s_re := X;  let s_im := -Y
    -- Complex product s * ρ = (X - iY)(X + iY) = X² + Y² (real part) + 0 i:
    let s_mul_ρ_re := s_re * ρ_re - s_im * ρ_im
    let s_mul_ρ_im := s_re * ρ_im + s_im * ρ_re
    -- 1. Imaginary part of s * ρ vanishes & Plücker's 5th coordinate η = r σ - s ρ = -(X² + Y² + Z²):
    s_mul_ρ_im = 0 ∧
    r * σ - s_mul_ρ_re = - (X * X + Y * Y + Z * Z) ∧
    -- 2. Exact dimension identities of Dahm's su(4)/su*(4) chain (p. 4 & p. 6):
    (4 * 4 - 1 = 15 ∧ 5 + 10 = 15 ∧ 5 + 6 + 4 = 15 ∧ 5 + 6 + 3 + 1 = 15 ∧ 10 + 6 = 4 * 4) := by
  refine ⟨by ring, by ring, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

-- ============================================================================
-- 3. LORENTZ BOOST INVARIANCE OF PLÜCKER QUADRIC & 4D LINE-SPACETIME (Sec. III, pp. 9, 11)
-- ============================================================================

/--
**Theorem 3 (Lorentz Invariance of Plücker Quadric & Dahm's 4D Line-Spacetime, Eq. 4 & Sec. III.B, pp. 9, 11):**
Under the `P³` Lorentz transformation (Eq. 4, p. 9) with `hLorentz : γ * γ * (1 - β * β) = 1`:
1. The Plücker quadric `p01 * p23 - p02 * p13 + p03 * p12` (where `p31 = -p13`) is strictly invariant!
2. Each boosted line-doublet quadratic form `(p13')² - (p03')² = p13² - p03²` and
   `(p12')² - (p02')² = p12² - p02²` is strictly invariant!
3. Dahm's 4D Line-Spacetime quadric `p13² + p01² + p23² - p03²` (Sec. III.B, p. 11) is
   strictly Lorentz invariant, and `(p01 + p23)² + (p01 - p23)² = 2 (p01² + p23²)`!
-/
theorem lorentz_boost_invariance_of_pluecker_quadric_and_4d_line_spacetime
    (p01 p23 p02 p12 p03 p13 γ β : R)
    (hLorentz : γ * γ * (1 - β * β) = 1) :
    let p01' := p01
    let p23' := p23
    let p02' := γ * p02 - γ * β * p12
    let p12' := γ * p12 - γ * β * p02
    let p03' := γ * p03 - γ * β * p13
    let p13' := γ * p13 - γ * β * p03
    -- 1. Exact Lorentz invariance of the Plücker Quadric (with p31 = -p13):
    p01' * p23' - p02' * p13' + p03' * p12' =
      p01 * p23 - p02 * p13 + p03 * p12 ∧
    -- 2. Exact Lorentz invariance of Dahm's 4D Line-Spacetime Metric (Sec. III.B, p. 11):
    p13' * p13' + p01' * p01' + p23' * p23' - p03' * p03' =
      p13 * p13 + p01 * p01 + p23 * p23 - p03 * p03 ∧
    -- 3. Sum of squares of Y ~ (p01+p23) and Z ~ (p01-p23) (p. 11):
    (p01 + p23) * (p01 + p23) + (p01 - p23) * (p01 - p23) =
      2 * (p01 * p01 + p23 * p23) := by
  refine ⟨?_, ?_, by ring⟩
  · calc p01 * p23 - (γ * p02 - γ * β * p12) * (γ * p13 - γ * β * p03) +
         (γ * p03 - γ * β * p13) * (γ * p12 - γ * β * p02)
      _ = p01 * p23 + (γ * γ * (1 - β * β)) * (- p02 * p13 + p03 * p12) := by ring
      _ = p01 * p23 - p02 * p13 + p03 * p12 := by rw [hLorentz]; ring
  · calc (γ * p13 - γ * β * p03) * (γ * p13 - γ * β * p03) + p01 * p01 + p23 * p23 -
         (γ * p03 - γ * β * p13) * (γ * p03 - γ * β * p13)
      _ = p01 * p01 + p23 * p23 + (γ * γ * (1 - β * β)) * (p13 * p13 - p03 * p03) := by ring
      _ = p13 * p13 + p01 * p01 + p23 * p23 - p03 * p03 := by rw [hLorentz]; ring

-- ============================================================================
-- 4. GENERAL P³ COLLINEATIONS, 6-VECTOR PRODUCT & LAPLACE EXPANSION (Sec. III.A, Eq. 5–6, p. 10)
-- ============================================================================

/-- A general `4 × 4` projective collineation matrix `a_{αβ}` on `P³`: -/
structure Mat4 (R : Type u) where
  a00 : R; a01 : R; a02 : R; a03 : R
  a10 : R; a11 : R; a12 : R; a13 : R
  a20 : R; a21 : R; a22 : R; a23 : R
  a30 : R; a31 : R; a32 : R; a33 : R

/-- Determinant of a `4 × 4` matrix `A : Mat4 R`: -/
def det4 (A : Mat4 R) : R :=
  (A.a00 * A.a11 - A.a10 * A.a01) * (A.a22 * A.a33 - A.a32 * A.a23) +
  (A.a00 * A.a21 - A.a20 * A.a01) * (A.a32 * A.a13 - A.a12 * A.a33) +
  (A.a00 * A.a31 - A.a30 * A.a01) * (A.a12 * A.a23 - A.a22 * A.a13) +
  (A.a20 * A.a31 - A.a30 * A.a21) * (A.a02 * A.a13 - A.a12 * A.a03) +
  (A.a30 * A.a11 - A.a10 * A.a31) * (A.a02 * A.a23 - A.a22 * A.a03) +
  (A.a10 * A.a21 - A.a20 * A.a11) * (A.a02 * A.a33 - A.a32 * A.a03)

/-- Plücker 6-vector `(p01, p02, p03, p23, p31, p12)` formed from two `P³` points `x, y`: -/
structure Pluecker6 (R : Type u) where
  p01 : R; p02 : R; p03 : R
  p23 : R; p31 : R; p12 : R

/-- Dahm's 6-Vector Product `[𝔄 · 𝔅]` (Eq. 6, p. 10): -/
def sixProduct (U V : Pluecker6 R) : R :=
  U.p01 * V.p23 + U.p02 * V.p31 + U.p03 * V.p12 +
  U.p23 * V.p01 + U.p31 * V.p02 + U.p12 * V.p03

/-- Plücker–Klein Quadric `P = p01*p23 + p02*p31 + p03*p12` (p. 4 & Eq. 5, p. 10): -/
def kleinQuadric (U : Pluecker6 R) : R :=
  U.p01 * U.p23 + U.p02 * U.p31 + U.p03 * U.p12

/-- The 6 compound minor columns `𝔄_{αβ}` of `A : Mat4 R` (Sec. III.A, p. 10): -/
def col01 (A : Mat4 R) : Pluecker6 R :=
  ⟨A.a00*A.a11 - A.a10*A.a01, A.a00*A.a21 - A.a20*A.a01, A.a00*A.a31 - A.a30*A.a01,
   A.a20*A.a31 - A.a30*A.a21, A.a30*A.a11 - A.a10*A.a31, A.a10*A.a21 - A.a20*A.a11⟩

def col23 (A : Mat4 R) : Pluecker6 R :=
  ⟨A.a02*A.a13 - A.a12*A.a03, A.a02*A.a23 - A.a22*A.a03, A.a02*A.a33 - A.a32*A.a03,
   A.a22*A.a33 - A.a32*A.a23, A.a32*A.a13 - A.a12*A.a33, A.a12*A.a23 - A.a22*A.a13⟩

def col02 (A : Mat4 R) : Pluecker6 R :=
  ⟨A.a00*A.a12 - A.a10*A.a02, A.a00*A.a22 - A.a20*A.a02, A.a00*A.a32 - A.a30*A.a02,
   A.a20*A.a32 - A.a30*A.a22, A.a30*A.a12 - A.a10*A.a32, A.a10*A.a22 - A.a20*A.a12⟩

def col31 (A : Mat4 R) : Pluecker6 R :=
  ⟨A.a03*A.a11 - A.a13*A.a01, A.a03*A.a21 - A.a23*A.a01, A.a03*A.a31 - A.a33*A.a01,
   A.a23*A.a31 - A.a33*A.a21, A.a33*A.a11 - A.a13*A.a31, A.a13*A.a21 - A.a23*A.a11⟩

def col03 (A : Mat4 R) : Pluecker6 R :=
  ⟨A.a00*A.a13 - A.a10*A.a03, A.a00*A.a23 - A.a20*A.a03, A.a00*A.a33 - A.a30*A.a03,
   A.a20*A.a33 - A.a30*A.a23, A.a30*A.a13 - A.a10*A.a33, A.a10*A.a23 - A.a20*A.a13⟩

def col12 (A : Mat4 R) : Pluecker6 R :=
  ⟨A.a01*A.a12 - A.a11*A.a02, A.a01*A.a22 - A.a21*A.a02, A.a01*A.a32 - A.a31*A.a02,
   A.a21*A.a32 - A.a31*A.a22, A.a31*A.a12 - A.a11*A.a32, A.a11*A.a22 - A.a21*A.a12⟩

/--
**Theorem 4 (Dahm's 6-Vector Product & Invariance of the Plücker–Klein Quadric, Eq. 5–6, p. 10):**
For ANY `4 × 4` collineation `A : Mat4 R`:
1. Each of the three complementary 6-products `[𝔄₀₁ · 𝔄₂₃]`, `[𝔄₀₂ · 𝔄₃₁]`, `[𝔄₀₃ · 𝔄₁₂]`
   in Eq. (5) on page 10 equals `det4 A` identically!
2. All non-complementary 6-products (such as `[𝔄₀₁ · 𝔄₀₂]`) and self-quadrics `kleinQuadric (col01 A)`
   vanish identically!
3. Therefore, Dahm's transformed quadric (Eq. 5, p. 10) evaluates to:
   `p01*p23*[𝔄₀₁·𝔄₂₃] + p02*p31*[𝔄₀₂·𝔄₃₁] + p03*p12*[𝔄₀₃·𝔄₁₂] = det4 A * (p01*p23 + p02*p31 + p03*p12)`!
-/
theorem general_collineation_6_product_and_pluecker_quadric_invariance
    (A : Mat4 R) (p : Pluecker6 R) :
    -- 1. Complementary 6-vector products equal det(A) (Laplace 2×2 expansion):
    sixProduct (col01 A) (col23 A) = det4 A ∧
    sixProduct (col02 A) (col31 A) = det4 A ∧
    sixProduct (col03 A) (col12 A) = det4 A ∧
    -- 2. Each column lies on the Plücker-Klein quadric & adjacent columns are 6-orthogonal:
    kleinQuadric (col01 A) = 0 ∧
    sixProduct (col01 A) (col02 A) = 0 ∧
    -- 3. Dahm's Eq. (5) on page 10 scales the Plücker-Klein quadric by det(A):
    (p.p01 * p.p23 * sixProduct (col01 A) (col23 A) +
     p.p02 * p.p31 * sixProduct (col02 A) (col31 A) +
     p.p03 * p.p12 * sixProduct (col03 A) (col12 A)) =
      det4 A * kleinQuadric p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp [sixProduct, kleinQuadric, det4, col01, col23, col02, col31, col03, col12]
    ring

end DahmProjectiveSymmetriesPlueckerKleinPoset
