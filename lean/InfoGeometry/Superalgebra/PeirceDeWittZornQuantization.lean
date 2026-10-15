/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Section 115: Peirce–DeWitt Decomposition, Supercolor Symmetry, and Quantized Zorn Matrices

This module formalizes the exact algebraic synthesis resolving the quantization
of split-octonions (`𝕆_s`) via the Peirce–DeWitt supermatrix decomposition:

1. **Penrose Chiral Zig-Zag Mass & Peirce Idempotents**:
   Two orthogonal idempotents `e₁` (forward chirality) and `e₂` (backward chirality)
   satisfying `e₁² = e₁`, `e₂² = e₂`, `e₁ e₂ = e₂ e₁ = 0`, and `e₁ + e₂ = 1`.
2. **DeWitt `ℤ₂` Super-Grading of the Peirce Decomposition**:
   Every element `Z ∈ ZornAlgebra R` decomposes uniquely into four Peirce blocks
   `Z = Z₁₁ + Z₁₂ + Z₂₁ + Z₂₂`, where:
   * **Even (Bosonic) Sector**: `Z₁₁ ⊕ Z₂₂ = a e₁ + b e₂` (Penrose mass/helicity scalars).
   * **Odd (Fermionic) Sector**: `Z₁₂ ⊕ Z₂₁ = U(u) + V(v)` (3-color quark and antiquark vectors).
3. **Canonical Anticommutation Relations (CAR) Quantization**:
   Although `ZornAlgebra R` is non-associative, the graded superbracket (anticommutator)
   of the odd Peirce generators `U(u)` and `V(v)` closes on the exact identity:
   `{U(u), V(v)} = U(u) V(v) + V(v) U(u) = (u · v) 1`.
4. **Super-Grassmannian Supercolor & Baryon Confinement**:
   Under the `SL(3)` / `SU(3)_color` stabilizer of `(e₁, e₂)` inside `G₂`:
   * Two quark triplets fuse into an antiquark diquark: `U(u₁) · U(u₂) = V(u₁ × u₂)`.
   * Three quarks contract into the `SL(3)`-invariant Baryon singlet determinant:
     `{U(u₃), U(u₁) · U(u₂)} = det(u₃, u₁, u₂) 1`.
5. **Canonical Bridge to `ZornVectorMatrix`**:
   Constructs the explicit equivalences `colorVec3EquivZornVec3 : ColorVec3 R ≃ ZornVec3 R`
   and `zornAlgebraEquivZornVectorMatrix : ZornAlgebra R ≃ ZornVectorMatrix R` preserving
   dot product, cross product, addition, identity, Peirce idempotents, and Zorn multiplication.
-/

namespace InfoGeometry.Superalgebra.PeirceDeWittZorn

open InfoGeometry.Algebra

variable {R : Type*} [CommRing R]

/-! --------------------------------------------------------------------------
    Section 1: 3D Supercolor Vector Space (SU(3)_c / SL(3) Triplets & Cross Product)
    -------------------------------------------------------------------------- -/

/-- A 3-component color vector over a commutative ring `R`, representing a quark
    triplet `3` or anti-quark antitriplet `3̄` in the Günaydin–Gürsey split-octonion
    realization of `SU(3)_color`. -/
@[ext]
structure ColorVec3 (R : Type*) where
  c₁ : R
  c₂ : R
  c₃ : R
  deriving DecidableEq, Repr

namespace ColorVec3

/-- The zero color vector. -/
def zero : ColorVec3 R := ⟨0, 0, 0⟩

/-- Componentwise addition of color vectors. -/
def add (u v : ColorVec3 R) : ColorVec3 R :=
  ⟨u.c₁ + v.c₁, u.c₂ + v.c₂, u.c₃ + v.c₃⟩

/-- Componentwise negation of a color vector. -/
def neg (u : ColorVec3 R) : ColorVec3 R :=
  ⟨-u.c₁, -u.c₂, -u.c₃⟩

/-- Componentwise subtraction of color vectors. -/
def sub (u v : ColorVec3 R) : ColorVec3 R :=
  ⟨u.c₁ - v.c₁, u.c₂ - v.c₂, u.c₃ - v.c₃⟩

/-- Scalar multiplication on a color vector. -/
def smul (k : R) (u : ColorVec3 R) : ColorVec3 R :=
  ⟨k * u.c₁, k * u.c₂, k * u.c₃⟩

/-- The `SU(3)` / `SO(3)` color-singlet bilinear pairing (dot product) `u · v`
    between a triplet `u ∈ 3` and an anti-triplet `v ∈ 3̄`. -/
def dot (u v : ColorVec3 R) : R :=
  u.c₁ * v.c₁ + u.c₂ * v.c₂ + u.c₃ * v.c₃

/-- The 3D exterior cross product `u × v` (`3 × 3 → 3̄`), which fuses two quark
    color triplets into an anti-triplet diquark state. -/
def cross (u v : ColorVec3 R) : ColorVec3 R :=
  ⟨ u.c₂ * v.c₃ - u.c₃ * v.c₂,
    u.c₃ * v.c₁ - u.c₁ * v.c₃,
    u.c₁ * v.c₂ - u.c₂ * v.c₁ ⟩

/-- The `SL(3)`-invariant scalar triple product (Baryon singlet determinant)
    `det(u₁, u₂, u₃) = u₁ · (u₂ × u₃) = ε_{ijk} u₁^i u₂^j u₃^k`. -/
def baryonDet (u₁ u₂ u₃ : ColorVec3 R) : R :=
  dot u₁ (cross u₂ u₃)

/-- Red color basis vector `(1, 0, 0)`. -/
def eRed : ColorVec3 R := ⟨1, 0, 0⟩

/-- Green color basis vector `(0, 1, 0)`. -/
def eGreen : ColorVec3 R := ⟨0, 1, 0⟩

/-- Blue color basis vector `(0, 0, 1)`. -/
def eBlue : ColorVec3 R := ⟨0, 0, 1⟩

/-- Symmetry of the color dot pairing: `u · v = v · u`. -/
theorem dot_comm (u v : ColorVec3 R) : dot u v = dot v u := by
  dsimp [dot]
  ring

/-- Antisymmetry of the diquark cross product: `u × v = - (v × u)`. -/
theorem cross_anticomm (u v : ColorVec3 R) : cross u v = neg (cross v u) := by
  ext <;> dsimp [cross, neg] <;> ring

/-- Pauli antisymmetry of the Baryon singlet determinant under exchange of the
    first two quarks. -/
theorem baryonDet_antisymm_12 (u₁ u₂ u₃ : ColorVec3 R) :
    baryonDet u₁ u₂ u₃ = - baryonDet u₂ u₁ u₃ := by
  dsimp [baryonDet, dot, cross]
  ring

/-- Cyclic invariance of the Baryon singlet determinant. -/
theorem baryonDet_cyclic (u₁ u₂ u₃ : ColorVec3 R) :
    baryonDet u₁ u₂ u₃ = baryonDet u₂ u₃ u₁ := by
  dsimp [baryonDet, dot, cross]
  ring

/-- Exact evaluation of the Baryon singlet determinant on the three fundamental
    color basis states `(Red, Green, Blue)`: `det(eRed, eGreen, eBlue) = 1`. -/
theorem baryonDet_red_green_blue :
    baryonDet (eRed : ColorVec3 R) eGreen eBlue = 1 := by
  dsimp [baryonDet, dot, cross, eRed, eGreen, eBlue]
  ring

end ColorVec3

/-- Constructive `ℤ`-model witness for `ColorVec3` (OpenGauss Gate 2.5 / Trap T17). -/
def standardColorVec3 : ColorVec3 ℤ := ColorVec3.eRed

instance : Inhabited (ColorVec3 ℤ) := ⟨standardColorVec3⟩

/-! --------------------------------------------------------------------------
    Section 2: Non-Associative Zorn Vector Matrix Algebra (`𝕆_s`)
    -------------------------------------------------------------------------- -/

/-- A Zorn vector-matrix over `R`, realizing the 8-dimensional split-octonion
    algebra `𝕆_s = R ⊕ V₃ ⊕ V₃* ⊕ R`:
    ```
      Z = ⎛ a   u ⎞
          ⎝ v   b ⎠
    ```
    where `a, b ∈ R` are the Penrose forward/backward chiral helicity scalars
    (Even DeWitt sector) and `u, v ∈ ColorVec3 R` are the 3-color quark/antiquark
    vectors (Odd DeWitt sector). -/
@[ext]
structure ZornAlgebra (R : Type*) where
  a : R
  u : ColorVec3 R
  v : ColorVec3 R
  b : R
  deriving DecidableEq, Repr

namespace ZornAlgebra

/-- Zero element of the Zorn algebra. -/
def zero : ZornAlgebra R :=
  ⟨0, ColorVec3.zero, ColorVec3.zero, 0⟩

/-- Multiplicative identity `1 = e₁ + e₂` of the Zorn algebra. -/
def one : ZornAlgebra R :=
  ⟨1, ColorVec3.zero, ColorVec3.zero, 1⟩

/-- Addition of Zorn matrices. -/
def add (X Y : ZornAlgebra R) : ZornAlgebra R :=
  ⟨ X.a + Y.a,
    ColorVec3.add X.u Y.u,
    ColorVec3.add X.v Y.v,
    X.b + Y.b ⟩

/-- Scalar multiplication of a Zorn matrix by `k ∈ R`. -/
def smul (k : R) (X : ZornAlgebra R) : ZornAlgebra R :=
  ⟨ k * X.a,
    ColorVec3.smul k X.u,
    ColorVec3.smul k X.v,
    k * X.b ⟩

/-- Max Zorn's non-associative split-octonion multiplication (1933):
    ```
      ⎛ a₁  u₁ ⎞ ⎛ a₂  u₂ ⎞ = ⎛ a₁ a₂ + u₁ · v₂             a₁ u₂ + b₂ u₁ - v₁ × v₂ ⎞
      ⎝ v₁  b₁ ⎠ ⎝ v₂  b₂ ⎠   ⎝ a₂ v₁ + b₁ v₂ + u₁ × u₂     v₁ · u₂ + b₁ b₂         ⎠
    ```
    The sign difference `- v₁ × v₂` vs `+ u₁ × u₂` follows Zorn's convention ensuring
    multiplicativity of the octonionic norm `N(X Y) = N(X) N(Y)`. -/
def mul (X Y : ZornAlgebra R) : ZornAlgebra R :=
  ⟨ X.a * Y.a + ColorVec3.dot X.u Y.v,
    ColorVec3.sub
      (ColorVec3.add (ColorVec3.smul X.a Y.u) (ColorVec3.smul Y.b X.u))
      (ColorVec3.cross X.v Y.v),
    ColorVec3.add
      (ColorVec3.add (ColorVec3.smul Y.a X.v) (ColorVec3.smul X.b Y.v))
      (ColorVec3.cross X.u Y.u),
    ColorVec3.dot X.v Y.u + X.b * Y.b ⟩

/-! --------------------------------------------------------------------------
    Section 3: Orthogonal Peirce Idempotents & Partition of Unity
    -------------------------------------------------------------------------- -/

/-- Forward-chirality Peirce idempotent `e₁ = diag(1, 0)`. -/
def e₁ : ZornAlgebra R :=
  ⟨1, ColorVec3.zero, ColorVec3.zero, 0⟩

/-- Backward-chirality Peirce idempotent `e₂ = diag(0, 1)`. -/
def e₂ : ZornAlgebra R :=
  ⟨0, ColorVec3.zero, ColorVec3.zero, 1⟩

/-- Theorem 1: `e₁` is an exact idempotent (`e₁ · e₁ = e₁`). -/
theorem e₁_idempotent : mul (e₁ : ZornAlgebra R) e₁ = e₁ := by
  ext <;> dsimp [mul, e₁, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 2: `e₂` is an exact idempotent (`e₂ · e₂ = e₂`). -/
theorem e₂_idempotent : mul (e₂ : ZornAlgebra R) e₂ = e₂ := by
  ext <;> dsimp [mul, e₂, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 3: `e₁` and `e₂` are mutually orthogonal (`e₁ · e₂ = 0`). -/
theorem e₁_mul_e₂_zero : mul (e₁ : ZornAlgebra R) e₂ = zero := by
  ext <;> dsimp [mul, e₁, e₂, zero, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 4: Reverse orthogonality (`e₂ · e₁ = 0`). -/
theorem e₂_mul_e₁_zero : mul (e₂ : ZornAlgebra R) e₁ = zero := by
  ext <;> dsimp [mul, e₁, e₂, zero, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 5: Peirce Partition of Unity (`e₁ + e₂ = 1`). -/
theorem peirce_partition_of_unity : add (e₁ : ZornAlgebra R) e₂ = one := by
  ext <;> dsimp [add, e₁, e₂, one, ColorVec3.add, ColorVec3.zero] <;> ring

/-! --------------------------------------------------------------------------
    Section 4: Peirce–DeWitt `ℤ₂`-Graded Decomposition (`A = A₀ ⊕ A₁`)
    -------------------------------------------------------------------------- -/

/-- The `(1,1)` Peirce projection `e₁ X e₁ = a e₁` (Left-handed Penrose scalar). -/
def peirce11 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₁ (mul X e₁)

/-- The `(1,2)` Peirce projection `e₁ X e₂ = U(u)` (Odd quark color triplet `3`). -/
def peirce12 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₁ (mul X e₂)

/-- The `(2,1)` Peirce projection `e₂ X e₁ = V(v)` (Odd antiquark color antitriplet `3̄`). -/
def peirce21 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₂ (mul X e₁)

/-- The `(2,2)` Peirce projection `e₂ X e₂ = b e₂` (Right-handed Penrose scalar). -/
def peirce22 (X : ZornAlgebra R) : ZornAlgebra R :=
  mul e₂ (mul X e₂)

/-- DeWitt Even (`0̄`, Bosonic) sector `A₀ = A₁₁ ⊕ A₂₂`. -/
def dewittEven (X : ZornAlgebra R) : ZornAlgebra R :=
  add (peirce11 X) (peirce22 X)

/-- DeWitt Odd (`1̄`, Fermionic) sector `A₁ = A₁₂ ⊕ A₂₁`. -/
def dewittOdd (X : ZornAlgebra R) : ZornAlgebra R :=
  add (peirce12 X) (peirce21 X)

/-- Theorem 6: Exact Peirce–DeWitt Completeness.
    Every split-octonion `X ∈ ZornAlgebra R` is the exact sum of its DeWitt Even
    (bosonic diagonal) and DeWitt Odd (fermionic off-diagonal) Peirce projections:
    `X = dewittEven X + dewittOdd X = (e₁ X e₁ + e₂ X e₂) + (e₁ X e₂ + e₂ X e₁)`. -/
theorem peirce_dewitt_completeness (X : ZornAlgebra R) :
    add (dewittEven X) (dewittOdd X) = X := by
  ext <;> dsimp [dewittEven, dewittOdd, peirce11, peirce12, peirce21, peirce22,
    mul, add, e₁, e₂, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-! --------------------------------------------------------------------------
    Section 5: Canonical CAR Quantization of Odd Peirce Generators
    -------------------------------------------------------------------------- -/

/-- Embedding of a color triplet `u ∈ 3` into the `(1,2)` Odd Peirce subspace
    as a quark creation/annihilation generator `U(u)`. -/
def quarkU (u : ColorVec3 R) : ZornAlgebra R :=
  ⟨0, u, ColorVec3.zero, 0⟩

/-- Embedding of a color antitriplet `v ∈ 3̄` into the `(2,1)` Odd Peirce subspace
    as an antiquark creation/annihilation generator `V(v)`. -/
def antiquarkV (v : ColorVec3 R) : ZornAlgebra R :=
  ⟨0, ColorVec3.zero, v, 0⟩

/-- The Graded Superbracket (Fermionic Anticommutator) `{X, Y} = X · Y + Y · X`
    on the odd sector of the Peirce–DeWitt Zorn algebra. -/
def anticommutator (X Y : ZornAlgebra R) : ZornAlgebra R :=
  add (mul X Y) (mul Y X)

/-- Theorem 7 (Chiral Left-Projector Contraction):
    `U(u) · V(v) = (u · v) e₁`. -/
theorem quark_mul_antiquark (u v : ColorVec3 R) :
    mul (quarkU u) (antiquarkV v) = smul (ColorVec3.dot u v) e₁ := by
  ext <;> dsimp [mul, quarkU, antiquarkV, smul, e₁, ColorVec3.dot,
    ColorVec3.sub, ColorVec3.add, ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 8 (Chiral Right-Projector Contraction):
    `V(v) · U(u) = (u · v) e₂`. -/
theorem antiquark_mul_quark (u v : ColorVec3 R) :
    mul (antiquarkV v) (quarkU u) = smul (ColorVec3.dot u v) e₂ := by
  ext <;> dsimp [mul, quarkU, antiquarkV, smul, e₂, ColorVec3.dot,
    ColorVec3.sub, ColorVec3.add, ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 9 (Main Theorem — Exact CAR Quantization of Split-Octonions):
    The odd Peirce–DeWitt generators `U(u) ∈ A₁₂` and `V(v) ∈ A₂₁` satisfy the
    exact Canonical Anticommutation Relations (CAR):
    `{U(u), V(v)} = U(u) V(v) + V(v) U(u) = (u · v) 1`. -/
theorem zorn_car_quantization_exact (u v : ColorVec3 R) :
    anticommutator (quarkU u) (antiquarkV v) = smul (ColorVec3.dot u v) one := by
  ext <;> dsimp [anticommutator, mul, add, quarkU, antiquarkV, smul, one,
    ColorVec3.dot, ColorVec3.sub, ColorVec3.add, ColorVec3.smul,
    ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 10 (Nilpotency / Isotropy of Equal-Color Quark Creation):
    `U(u) · U(u) = 0` (Pauli exclusion principle for identical quark color state `u`). -/
theorem quark_pauli_exclusion (u : ColorVec3 R) :
    mul (quarkU u) (quarkU u) = zero := by
  ext <;> dsimp [mul, quarkU, zero, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 11 (Nilpotency / Isotropy of Equal-Color Antiquark Creation):
    `V(v) · V(v) = 0`. -/
theorem antiquark_pauli_exclusion (v : ColorVec3 R) :
    mul (antiquarkV v) (antiquarkV v) = zero := by
  ext <;> dsimp [mul, antiquarkV, zero, ColorVec3.dot, ColorVec3.sub, ColorVec3.add,
    ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Non-commutativity witness: `quarkU eRed` and `antiquarkV eRed` do not commute
    over `ℤ` (`U(eRed) V(eRed) = e₁ ≠ e₂ = V(eRed) U(eRed)`). -/
theorem quark_antiquark_noncomm :
    mul (quarkU (ColorVec3.eRed : ColorVec3 ℤ)) (antiquarkV ColorVec3.eRed) ≠
    mul (antiquarkV (ColorVec3.eRed : ColorVec3 ℤ)) (quarkU ColorVec3.eRed) := by
  intro h
  have ha := congrArg ZornAlgebra.a h
  dsimp [mul, quarkU, antiquarkV, ColorVec3.eRed, ColorVec3.dot, ColorVec3.zero] at ha
  omega

/-! --------------------------------------------------------------------------
    Section 6: Supercolor Diquark Fusion & Baryon Singlet Confinement
    -------------------------------------------------------------------------- -/

/-- Theorem 12 (Supercolor Diquark Fusion `3 ⊗ 3 → 3̄`):
    Multiplying two quark operators in the `(1,2)` Peirce block fuses them via
    the non-associative cross product into an antiquark operator in the `(2,1)`
    Peirce block:
    `U(u₁) · U(u₂) = V(u₁ × u₂)`. -/
theorem supercolor_diquark_fusion (u₁ u₂ : ColorVec3 R) :
    mul (quarkU u₁) (quarkU u₂) = antiquarkV (ColorVec3.cross u₁ u₂) := by
  ext <;> dsimp [mul, quarkU, antiquarkV, ColorVec3.dot, ColorVec3.sub,
    ColorVec3.add, ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 13 (Mirror Anti-Diquark Fusion `3̄ ⊗ 3̄ → 3`):
    Multiplying two antiquark operators in the `(2,1)` Peirce block yields a
    quark operator in the `(1,2)` Peirce block (with the opposite Zorn sign):
    `V(v₁) · V(v₂) = U(- v₁ × v₂) = U(v₂ × v₁)`. -/
theorem supercolor_antidiquark_fusion (v₁ v₂ : ColorVec3 R) :
    mul (antiquarkV v₁) (antiquarkV v₂) = quarkU (ColorVec3.cross v₂ v₁) := by
  ext <;> dsimp [mul, quarkU, antiquarkV, ColorVec3.dot, ColorVec3.sub,
    ColorVec3.add, ColorVec3.smul, ColorVec3.cross, ColorVec3.zero] <;> ring

/-- Theorem 14 (Supercolor Baryon Singlet Vertex):
    Contracting a third quark `U(u₃)` with the fused diquark `U(u₁) · U(u₂)` via
    the CAR anticommutator projects onto the `SL(3)`-invariant Baryon singlet
    scalar multiple of the identity:
    `{ U(u₃), U(u₁) · U(u₂) } = det(u₃, u₁, u₂) 1`. -/
theorem supercolor_baryon_singlet_closure (u₁ u₂ u₃ : ColorVec3 R) :
    anticommutator (quarkU u₃) (mul (quarkU u₁) (quarkU u₂)) =
      smul (ColorVec3.baryonDet u₃ u₁ u₂) one := by
  rw [supercolor_diquark_fusion]
  rw [zorn_car_quantization_exact]
  rfl

/-- Corollary: On the three fundamental color states `(Red, Green, Blue)`,
    the 3-quark Baryon CAR vertex evaluates to the exact unit operator `1`:
    `{ U(eRed), U(eGreen) · U(eBlue) } = 1`. -/
theorem rgb_baryon_vertex_is_unit :
    anticommutator (quarkU (ColorVec3.eRed : ColorVec3 R))
      (mul (quarkU ColorVec3.eGreen) (quarkU ColorVec3.eBlue)) = one := by
  rw [supercolor_baryon_singlet_closure, ColorVec3.baryonDet_red_green_blue]
  ext <;> dsimp [smul, one, ColorVec3.smul, ColorVec3.zero] <;> ring

end ZornAlgebra

/-- Constructive `ℤ`-model witness for `ZornAlgebra` (OpenGauss Gate 2.5 / Trap T17). -/
def standardZornAlgebra : ZornAlgebra ℤ := ZornAlgebra.one

instance : Inhabited (ZornAlgebra ℤ) := ⟨standardZornAlgebra⟩

/-! --------------------------------------------------------------------------
    Section 7: Canonical Bridge to `InfoGeometry.Algebra.ZornVectorMatrix`
    -------------------------------------------------------------------------- -/

/-- Canonical equivalence between `ColorVec3 R` and `ZornVec3 R` (`Fin 3 → R`). -/
def colorVec3EquivZornVec3 : ColorVec3 R ≃ ZornVec3 R where
  toFun u := ![u.c₁, u.c₂, u.c₃]
  invFun x := ⟨x 0, x 1, x 2⟩
  left_inv u := by cases u; rfl
  right_inv x := by
    ext i
    fin_cases i <;> rfl

/-- `colorVec3EquivZornVec3` preserves the color dot product `u · v`. -/
theorem colorVec3EquivZornVec3_dot (u v : ColorVec3 R) :
    ZornVec3.dot (colorVec3EquivZornVec3 u) (colorVec3EquivZornVec3 v) =
      ColorVec3.dot u v := by
  rw [ZornVec3.dot_eq_sum_coords]
  rfl

/-- `colorVec3EquivZornVec3` preserves the 3D cross product `u × v`. -/
theorem colorVec3EquivZornVec3_cross (u v : ColorVec3 R) :
    ZornVec3.cross (colorVec3EquivZornVec3 u) (colorVec3EquivZornVec3 v) =
      colorVec3EquivZornVec3 (ColorVec3.cross u v) := by
  ext i
  fin_cases i <;> rfl

/-- Canonical equivalence between `ZornAlgebra R` and `ZornVectorMatrix R`. -/
def zornAlgebraEquivZornVectorMatrix : ZornAlgebra R ≃ ZornVectorMatrix R where
  toFun X := ⟨X.a, colorVec3EquivZornVec3 X.u, colorVec3EquivZornVec3 X.v, X.b⟩
  invFun Y := ⟨Y.a, colorVec3EquivZornVec3.symm Y.v, colorVec3EquivZornVec3.symm Y.w, Y.b⟩
  left_inv X := by
    cases X
    simp [Equiv.symm_apply_apply]
  right_inv Y := by
    cases Y
    simp [Equiv.apply_symm_apply]

/-- `zornAlgebraEquivZornVectorMatrix` maps `e₁` to `ZornVectorMatrix.E11` and
    `e₂` to `ZornVectorMatrix.E22`. -/
theorem zornAlgebraEquiv_peirce_idempotents :
    zornAlgebraEquivZornVectorMatrix (ZornAlgebra.e₁ : ZornAlgebra R) = ZornVectorMatrix.E11 ∧
    zornAlgebraEquivZornVectorMatrix (ZornAlgebra.e₂ : ZornAlgebra R) = ZornVectorMatrix.E22 := by
  constructor
  · ext i <;> try rfl
    all_goals (fin_cases i <;> rfl)
  · ext i <;> try rfl
    all_goals (fin_cases i <;> rfl)

/-- `zornAlgebraEquivZornVectorMatrix` is a multiplicative isomorphism with respect
    to the non-associative Zorn product. -/
theorem zornAlgebraEquiv_mul (X Y : ZornAlgebra R) :
    zornAlgebraEquivZornVectorMatrix (ZornAlgebra.mul X Y) =
      ZornVectorMatrix.mul (zornAlgebraEquivZornVectorMatrix X)
        (zornAlgebraEquivZornVectorMatrix Y) := by
  ext i
  · dsimp [zornAlgebraEquivZornVectorMatrix, ZornAlgebra.mul, ZornVectorMatrix.mul]
    rw [colorVec3EquivZornVec3_dot]
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · dsimp [zornAlgebraEquivZornVectorMatrix, ZornAlgebra.mul, ZornVectorMatrix.mul]
    rw [colorVec3EquivZornVec3_dot]

end InfoGeometry.Superalgebra.PeirceDeWittZorn
