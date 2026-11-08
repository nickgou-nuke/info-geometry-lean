/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight

/-!
# Zorn Split-Octonion Peircian Matrix Algebra and 5-Graded Fock–Hodge Duality on `Fin 8`

This module bridges the 5-graded fermionic Fock space representation on `Fin 8`
(`SuperGrassmannianFiveGradedEightByEight`) with Zorn's split-octonion vector-matrix algebra
$$\begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & b \end{pmatrix}, \qquad
  a, b \in R,\ \mathbf{u}, \mathbf{v} \in R^3$$
by identifying the 8-dimensional exterior Fock basis
$\Lambda^\bullet(\mathbb{R}^3) = \Lambda^0 \oplus \Lambda^1 \oplus \Lambda^2 \oplus \Lambda^3$
with the four Peircian components $(a, \mathbf{u}, \mathbf{v}, b)$:

1. **Section 1 — Cyclic Hodge-Dual Grade $\pm 2$ Bivectors, Chiral Volume Operators & Peircian Idempotents on `Fin 8`**:
   - Reuses the exact $8 \times 8$ creation and annihilation matrices `gPlus1Z` and `gMinus1Z` from
     `SuperGrassmannianFiveGradedEightByEight`.
   - Defines the cyclic Hodge-dual bivector creation basis
     `gPlus2Hodge k = gPlus1 (hodgePair k).1 * gPlus1 (hodgePair k).2`
     ($(a_1^\dagger a_2^\dagger, a_2^\dagger a_0^\dagger, a_0^\dagger a_1^\dagger)$) and its
     transpose annihilation basis `gMinus2Hodge k = (gPlus2Hodge k)ᵀ`.
   - Defines the top-degree chiral volume creation operator
     `chiralTopCreate = gPlus1 0 * gPlus1 1 * gPlus1 2` ($a_0^\dagger a_1^\dagger a_2^\dagger$),
     its adjoint `chiralTopAnnihilate = gMinus1 2 * gMinus1 1 * gMinus1 0` ($a_2 a_1 a_0$), and
     the two complementary Peircian idempotents
     `vacuumIdempotent = chiralTopAnnihilate * chiralTopCreate` ($e_1 = |0\rangle\langle 0|$) and
     `topStateIdempotent = chiralTopCreate * chiralTopAnnihilate` ($e_2 = |\Omega\rangle\langle\Omega|$).

2. **Section 2 — Kernel-Certified Peircian Idempotent & Hodge–Fock Duality Theorems on `Fin 8`**:
   - Proves idempotency and mutual orthogonality of `vacuumIdempotent` and `topStateIdempotent`
     (`vacuumIdempotent_sq`, `topStateIdempotent_sq`, `vacuum_mul_topState_zero`,
     `topState_mul_vacuum_zero`) and their exact elementary-matrix characterizations
     `vacuumIdempotent_eq_single` ($E_{0,0}$) and `topStateIdempotent_eq_single` ($E_{7,7}$).
   - Proves exact Hodge–Fock column duality on `Fin 8`: acting with the cyclic bivector
     `gPlus2Hodge k` on the vacuum column $0$ agrees entrywise with acting with the single-mode
     annihilation operator `gMinus1 k` on the top-state column $7$
     (`hodge_fock_gPlus2_vac_eq_gMinus1_top`), and dually `gMinus2Hodge k r 7 = gPlus1 k r 0`
     (`hodge_fock_gMinus2_top_eq_gPlus1_vac`).
   - Proves the Zorn inner-product Peircian projections
     `zorn_innerProduct_vac_projection` ($a_2 a_1 a_0 \cdot a_j^\dagger \cdot (\star a_k^\dagger) = \delta_{jk} e_1$)
     and `zorn_innerProduct_top_projection` ($a_0^\dagger a_1^\dagger a_2^\dagger \cdot (\star a_j) \cdot a_k = \delta_{jk} e_2$).

3. **Section 3 — Zorn's Split-Octonion Vector-Matrix Algebra, `Fin 8` Basis Equivalence & Norm Multiplicativity**:
   - Defines `ZornSplitOctonion R` with Peircian components $(a, u, v, b)$, explicit equivalence
     `fin8ZornEquiv R : (Fin 8 → R) ≃ ZornSplitOctonion R` mapping binary occupation indices
     $\{0\}, \{4, 2, 1\}, \{3, -5, 6\}, \{7\}$ to $(a, u, v, b)$, Zorn multiplication `zornMul`,
     and the split quadratic norm `zornNorm z = a b - u ⋅ v`.
   - Proves exact coordinate-chart alignment `fin8ToZorn_gPlus1_vac` and
     `fin8ToZorn_gPlus2Hodge_vac` sending the vacuum columns of `gPlus1 k` and `gPlus2Hodge k` to
     the standard basis vectors of `u` and `v`.
   - Proves exact norm multiplicativity (the 8-square split-composition identity)
     `zornNorm_mul (x y : ZornSplitOctonion R) : zornNorm (zornMul x y) = zornNorm x * zornNorm y`
     over any commutative ring `R`, together with explicit non-commutativity `zornMul_noncomm`.

## Scope Note

Sections 1 and 2 establish finite $8 \times 8$ integer matrix identities on `Fin 8` via kernel
evaluation (`decide`), and Section 3 establishes the algebraic equivalence
`(Fin 8 → R) ≃ ZornSplitOctonion R` and the polynomial composition identity `zornNorm_mul` over
any `CommRing R`.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge

open InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight

/-!
### Section 1 — Grade $\pm 1$, Cyclic Hodge-Dual Grade $\pm 2$, Chiral Volume Operators & Peircian Idempotents on `Fin 8`
-/

/-- First fermionic creation operator $a_0^\dagger$ on `Fin 8` (reused from `SuperGrassmannianFiveGradedEightByEight`). -/
abbrev cDag0 : Matrix (Fin 8) (Fin 8) ℤ :=
  SuperGrassmannianFiveGradedEightByEight.fockCreate0Z

/-- Second fermionic creation operator $a_1^\dagger$ on `Fin 8` (reused from `SuperGrassmannianFiveGradedEightByEight`). -/
abbrev cDag1 : Matrix (Fin 8) (Fin 8) ℤ :=
  SuperGrassmannianFiveGradedEightByEight.fockCreate1Z

/-- Third fermionic creation operator $a_2^\dagger$ on `Fin 8` (reused from `SuperGrassmannianFiveGradedEightByEight`). -/
abbrev cDag2 : Matrix (Fin 8) (Fin 8) ℤ :=
  SuperGrassmannianFiveGradedEightByEight.fockCreate2Z

/-- Grade-$+1$ Fock creation family $a_k^\dagger$ for $k \in \mathrm{Fin}\ 3$. -/
abbrev gPlus1 : Fin 3 → Matrix (Fin 8) (Fin 8) ℤ :=
  SuperGrassmannianFiveGradedEightByEight.gPlus1Z

/-- Grade-$-1$ Fock annihilation family $a_k = (a_k^\dagger)^T$ for $k \in \mathrm{Fin}\ 3$. -/
abbrev gMinus1 : Fin 3 → Matrix (Fin 8) (Fin 8) ℤ :=
  SuperGrassmannianFiveGradedEightByEight.gMinus1Z

/-- Cyclic Hodge-dual pair map $k \mapsto (k+1 \bmod 3,\ k+2 \bmod 3)$ on `Fin 3`:
$0 \mapsto (1, 2)$, $1 \mapsto (2, 0)$, $2 \mapsto (0, 1)$. -/
def hodgePair : Fin 3 → Fin 3 × Fin 3
  | 0 => (1, 2)
  | 1 => (2, 0)
  | 2 => (0, 1)

/-- Cyclic Hodge-dual grade-$+2$ bivector creation basis
$(\star a^\dagger)_k = a_{(k+1)\bmod 3}^\dagger a_{(k+2)\bmod 3}^\dagger$ on `Fin 8`:
`gPlus2Hodge 0 = a₁† a₂†`, `gPlus2Hodge 1 = a₂† a₀†`, `gPlus2Hodge 2 = a₀† a₁†`. -/
def gPlus2Hodge (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  gPlus1 (hodgePair k).1 * gPlus1 (hodgePair k).2

/-- Cyclic Hodge-dual grade-$-2$ bivector annihilation basis
$(\star a)_k = (\mathrm{gPlus2Hodge}\ k)^T$ on `Fin 8`. -/
def gMinus2Hodge (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  (gPlus2Hodge k)ᵀ

/-- Top-degree chiral volume creation operator $\Omega^\dagger = a_0^\dagger a_1^\dagger a_2^\dagger$
mapping the vacuum $|0\rangle$ (index `0`) to the filled state $|7\rangle$ (index `7`). -/
def chiralTopCreate : Matrix (Fin 8) (Fin 8) ℤ :=
  gPlus1 0 * gPlus1 1 * gPlus1 2

/-- Top-degree chiral volume annihilation operator $\Omega = a_2 a_1 a_0$
mapping the filled state $|7\rangle$ (index `7`) back to the vacuum $|0\rangle$ (index `0`). -/
def chiralTopAnnihilate : Matrix (Fin 8) (Fin 8) ℤ :=
  gMinus1 2 * gMinus1 1 * gMinus1 0

/-- Vacuum Peircian idempotent $e_1 = \Omega \Omega^\dagger = a_2 a_1 a_0 a_0^\dagger a_1^\dagger a_2^\dagger$
projecting onto the $\Lambda^0$ vacuum line $|0\rangle\langle 0|$. -/
def vacuumIdempotent : Matrix (Fin 8) (Fin 8) ℤ :=
  chiralTopAnnihilate * chiralTopCreate

/-- Top-state Peircian idempotent $e_2 = \Omega^\dagger \Omega = a_0^\dagger a_1^\dagger a_2^\dagger a_2 a_1 a_0$
projecting onto the $\Lambda^3$ filled volume line $|7\rangle\langle 7|$. -/
def topStateIdempotent : Matrix (Fin 8) (Fin 8) ℤ :=
  chiralTopCreate * chiralTopAnnihilate

/-!
### Section 2 — Kernel-Verified Peircian Idempotent & Hodge–Fock Duality Theorems on `Fin 8`
-/

/-- `vacuumIdempotent` is an idempotent projector: $e_1^2 = e_1$. -/
theorem vacuumIdempotent_sq :
    vacuumIdempotent * vacuumIdempotent = vacuumIdempotent := by
  decide

/-- `topStateIdempotent` is an idempotent projector: $e_2^2 = e_2$. -/
theorem topStateIdempotent_sq :
    topStateIdempotent * topStateIdempotent = topStateIdempotent := by
  decide

/-- Left orthogonality of the vacuum and top-state Peircian idempotents: $e_1 e_2 = 0$. -/
theorem vacuum_mul_topState_zero :
    vacuumIdempotent * topStateIdempotent = 0 := by
  decide

/-- Right orthogonality of the top-state and vacuum Peircian idempotents: $e_2 e_1 = 0$. -/
theorem topState_mul_vacuum_zero :
    topStateIdempotent * vacuumIdempotent = 0 := by
  decide

/-- Strict non-commutativity of the top-degree chiral volume operators:
$\Omega^\dagger \Omega \ne \Omega \Omega^\dagger$. -/
theorem chiralTopCreate_mul_chiralTopAnnihilate_ne_comm :
    chiralTopCreate * chiralTopAnnihilate ≠ chiralTopAnnihilate * chiralTopCreate := by
  decide

/-- `vacuumIdempotent` is the elementary matrix unit `Matrix.single 0 0 1` at index `(0, 0)`. -/
theorem vacuumIdempotent_eq_single :
    vacuumIdempotent = Matrix.single (0 : Fin 8) (0 : Fin 8) (1 : ℤ) := by
  decide

/-- `topStateIdempotent` is the elementary matrix unit `Matrix.single 7 7 1` at index `(7, 7)`. -/
theorem topStateIdempotent_eq_single :
    topStateIdempotent = Matrix.single (7 : Fin 8) (7 : Fin 8) (1 : ℤ) := by
  decide

/-- The `(0, 0)` entry of `vacuumIdempotent` is `1`. -/
theorem vacuumIdempotent_zero_zero :
    vacuumIdempotent 0 0 = 1 := by
  decide

/-- The `(7, 7)` entry of `topStateIdempotent` is `1`. -/
theorem topStateIdempotent_seven_seven :
    topStateIdempotent 7 7 = 1 := by
  decide

/-- **Hodge–Fock Bivector-to-Hole Duality ($\Lambda^2 |0\rangle = \Lambda^{-1} |7\rangle$)**:
For every mode $k \in \mathrm{Fin}\ 3$ and basis row $r \in \mathrm{Fin}\ 8$, the vacuum column $0$
of the cyclic Hodge bivector creation operator `gPlus2Hodge k` equals the top-state column $7$
of the single-mode annihilation operator `gMinus1 k`. -/
theorem hodge_fock_gPlus2_vac_eq_gMinus1_top (k : Fin 3) (r : Fin 8) :
    gPlus2Hodge k r 0 = gMinus1 k r 7 := by
  revert k r
  decide

/-- **Dual Hodge–Fock Hole-to-Particle Identity ($\Lambda^{-2} |7\rangle = \Lambda^1 |0\rangle$)**:
For every mode $k \in \mathrm{Fin}\ 3$ and basis row $r \in \mathrm{Fin}\ 8$, the top-state column $7$
of `gMinus2Hodge k` equals the vacuum column $0$ of `gPlus1 k`. -/
theorem hodge_fock_gMinus2_top_eq_gPlus1_vac (k : Fin 3) (r : Fin 8) :
    gMinus2Hodge k r 7 = gPlus1 k r 0 := by
  revert k r
  decide

/-- **Zorn Off-Diagonal Inner Product into the Vacuum Idempotent $e_1$**:
Multiplying the 1-form creation operator `gPlus1 j` by the cyclic Hodge 2-form creation operator
`gPlus2Hodge k` and projecting with `chiralTopAnnihilate` yields $\delta_{jk} e_1$:
$$\Omega \cdot a_j^\dagger \cdot (\star a^\dagger)_k = \delta_{jk}\, e_1.$$ -/
theorem zorn_innerProduct_vac_projection (j k : Fin 3) :
    chiralTopAnnihilate * gPlus1 j * gPlus2Hodge k =
      (if j = k then (1 : ℤ) else 0) • vacuumIdempotent := by
  revert j k
  decide

/-- **Zorn Off-Diagonal Inner Product into the Top-State Idempotent $e_2$**:
Multiplying the top-degree chiral volume creation operator `chiralTopCreate` on the left of the
cyclic Hodge 2-form annihilation operator `gMinus2Hodge j` and the 1-form annihilation operator
`gMinus1 k` yields $\delta_{jk} e_2$:
$$\Omega^\dagger \cdot (\star a)_j \cdot a_k = \delta_{jk}\, e_2.$$ -/
theorem zorn_innerProduct_top_projection (j k : Fin 3) :
    chiralTopCreate * gMinus2Hodge j * gMinus1 k =
      (if j = k then (1 : ℤ) else 0) • topStateIdempotent := by
  revert j k
  decide

/-!
### Section 3 — Zorn's Split-Octonion Vector-Matrix Algebra & `Fin 8` Spinor Equivalence
-/

/-- Zorn's vector-matrix representation of a split-octonion over a ring `R`:
$$\begin{pmatrix} a & \mathbf{u} \\ \mathbf{v} & b \end{pmatrix}, \qquad
  a \in \Lambda^0,\ \mathbf{u} \in \Lambda^1 \cong R^3,\ \mathbf{v} \in \Lambda^2 \cong R^3,\ b \in \Lambda^3.$$ -/
@[ext]
structure ZornSplitOctonion (R : Type*) where
  /-- Vacuum $\Lambda^0$ scalar component along $e_1 = |0\rangle\langle 0|$. -/
  a : R
  /-- Grade-$+1$ particle vector $\mathbf{u} \in R^3$ spanning $\Lambda^1$. -/
  u : Fin 3 → R
  /-- Grade-$+2$ Hodge-bivector / hole vector $\mathbf{v} \in R^3$ spanning $\Lambda^2$. -/
  v : Fin 3 → R
  /-- Top-state $\Lambda^3$ volume scalar component along $e_2 = |7\rangle\langle 7|$. -/
  b : R

/-- Constructive non-trivial witness for `ZornSplitOctonion ℤ` (Gate 2.5 / Trap T17). -/
def canonicalZornSplitOctonion : ZornSplitOctonion ℤ where
  a := 1
  u := ![1, 0, 0]
  v := ![0, 1, 0]
  b := 1

instance {R : Type*} [Zero R] : Inhabited (ZornSplitOctonion R) :=
  ⟨⟨0, fun _ => 0, fun _ => 0, 0⟩⟩

/-- 3D Euclidean dot product $\mathbf{x} \cdot \mathbf{y} = x_0 y_0 + x_1 y_1 + x_2 y_2$ on `Fin 3 → R`. -/
def vec3Dot {R : Type*} [CommRing R] (x y : Fin 3 → R) : R :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- 3D exterior / cross product $\mathbf{x} \times \mathbf{y}$ on `Fin 3 → R`. -/
def vec3Cross {R : Type*} [CommRing R] (x y : Fin 3 → R) : Fin 3 → R :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

/-- Maps an 8-component Fock spinor $\psi : \mathrm{Fin}\ 8 \to R$ to its Zorn split-octonion
components aligned with the mode creation indices (`0 ↦ 4`, `1 ↦ 2`, `2 ↦ 1`) of `gPlus1` and
the Jordan–Wigner signs (`3, -5, 6`) of `gPlus2Hodge`:
- `a = ψ 0` (vacuum $|000\rangle$),
- `u = ![ψ 4, ψ 2, ψ 1]` (1-particle states created by `gPlus1 0, 1, 2`),
- `v = ![ψ 3, -ψ 5, ψ 6]` (2-particle Hodge-dual states created by `gPlus2Hodge 0, 1, 2`),
- `b = ψ 7` (3-particle top state $|111\rangle$). -/
def fin8ToZorn {R : Type*} [Neg R] (ψ : Fin 8 → R) : ZornSplitOctonion R where
  a := ψ 0
  u := ![ψ 4, ψ 2, ψ 1]
  v := ![ψ 3, -ψ 5, ψ 6]
  b := ψ 7

/-- Inverse map reconstructing the 8-component Fock spinor `Fin 8 → R` from a `ZornSplitOctonion R`. -/
def zornToFin8 {R : Type*} [Neg R] (z : ZornSplitOctonion R) : Fin 8 → R :=
  ![z.a, z.u 2, z.u 1, z.v 0, z.u 0, -z.v 1, z.v 2, z.b]

/-- `zornToFin8` is a left inverse to `fin8ToZorn`. -/
theorem fin8ToZorn_left_inv {R : Type*} [InvolutiveNeg R] (ψ : Fin 8 → R) :
    zornToFin8 (fin8ToZorn ψ) = ψ := by
  ext i
  fin_cases i <;> simp [fin8ToZorn, zornToFin8]

/-- `zornToFin8` is a right inverse to `fin8ToZorn`. -/
theorem fin8ToZorn_right_inv {R : Type*} [InvolutiveNeg R] (z : ZornSplitOctonion R) :
    fin8ToZorn (zornToFin8 z) = z := by
  ext i
  · rfl
  · fin_cases i <;> simp [fin8ToZorn, zornToFin8]
  · fin_cases i <;> simp [fin8ToZorn, zornToFin8]
  · rfl

/-- Canonical equivalence `(Fin 8 → R) ≃ ZornSplitOctonion R` identifying the 8-dimensional
3-qubit Fock space with Zorn's split-octonion vector-matrix algebra. -/
def fin8ZornEquiv (R : Type*) [InvolutiveNeg R] : (Fin 8 → R) ≃ ZornSplitOctonion R where
  toFun := fin8ToZorn
  invFun := zornToFin8
  left_inv := fin8ToZorn_left_inv
  right_inv := fin8ToZorn_right_inv

/-- **Coordinate-Chart Alignment for Grade-$+1$ Creation (`gPlus1 k`)**:
`fin8ToZorn` maps the vacuum column of `gPlus1 k` to the $k$-th standard basis vector of `u`. -/
theorem fin8ToZorn_gPlus1_vac (k j : Fin 3) :
    (fin8ToZorn (fun r => gPlus1 k r 0)).u j = if j = k then 1 else 0 := by
  revert k j
  decide

/-- **Coordinate-Chart Alignment for Cyclic Grade-$+2$ Creation (`gPlus2Hodge k`)**:
`fin8ToZorn` maps the vacuum column of `gPlus2Hodge k` to the $k$-th standard basis vector of `v`. -/
theorem fin8ToZorn_gPlus2Hodge_vac (k j : Fin 3) :
    (fin8ToZorn (fun r => gPlus2Hodge k r 0)).v j = if j = k then 1 else 0 := by
  revert k j
  decide

/-- Zorn's vector-matrix multiplication on `ZornSplitOctonion R`:
$$\begin{pmatrix} a_1 & \mathbf{u}_1 \\ \mathbf{v}_1 & b_1 \end{pmatrix}
  \begin{pmatrix} a_2 & \mathbf{u}_2 \\ \mathbf{v}_2 & b_2 \end{pmatrix} =
  \begin{pmatrix}
    a_1 a_2 + \mathbf{u}_1 \cdot \mathbf{v}_2 &
    a_1 \mathbf{u}_2 + b_2 \mathbf{u}_1 - \mathbf{v}_1 \times \mathbf{v}_2 \\
    a_2 \mathbf{v}_1 + b_1 \mathbf{v}_2 + \mathbf{u}_1 \times \mathbf{u}_2 &
    b_1 b_2 + \mathbf{v}_1 \cdot \mathbf{u}_2
  \end{pmatrix}.$$ -/
def zornMul {R : Type*} [CommRing R] (x y : ZornSplitOctonion R) : ZornSplitOctonion R where
  a := x.a * y.a + vec3Dot x.u y.v
  u := fun i => x.a * y.u i + y.b * x.u i - vec3Cross x.v y.v i
  v := fun i => y.a * x.v i + x.b * y.v i + vec3Cross x.u y.u i
  b := x.b * y.b + vec3Dot x.v y.u

/-- Split-signature quadratic norm (Zorn determinant)
$N(z) = a b - \mathbf{u} \cdot \mathbf{v}$ on `ZornSplitOctonion R`. -/
def zornNorm {R : Type*} [CommRing R] (z : ZornSplitOctonion R) : R :=
  z.a * z.b - vec3Dot z.u z.v

/-- **Zorn Split-Octonion Norm Composition Identity ($N(x y) = N(x) N(y)$)**:
Over any commutative ring `R`, the quadratic form `zornNorm` is multiplicative under `zornMul`. -/
theorem zornNorm_mul {R : Type*} [CommRing R] (x y : ZornSplitOctonion R) :
    zornNorm (zornMul x y) = zornNorm x * zornNorm y := by
  unfold zornNorm zornMul vec3Dot vec3Cross
  dsimp
  ring

/-- First basis test element in `ZornSplitOctonion ℤ` for non-commutativity certification. -/
def zornBasisE1 : ZornSplitOctonion ℤ :=
  ⟨1, ![1, 0, 0], ![0, 0, 0], 0⟩

/-- Second basis test element in `ZornSplitOctonion ℤ` for non-commutativity certification. -/
def zornBasisE2 : ZornSplitOctonion ℤ :=
  ⟨0, ![0, 1, 0], ![0, 0, 0], 0⟩

/-- **Non-Commutativity of Zorn's Split-Octonion Multiplication**:
`zornMul zornBasisE1 zornBasisE2 ≠ zornMul zornBasisE2 zornBasisE1`. -/
theorem zornMul_noncomm :
    zornMul zornBasisE1 zornBasisE2 ≠ zornMul zornBasisE2 zornBasisE1 := by
  intro h
  have h1 : (zornMul zornBasisE1 zornBasisE2).u 1 = (zornMul zornBasisE2 zornBasisE1).u 1 :=
    congrFun (congrArg ZornSplitOctonion.u h) 1
  revert h1
  decide

end InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
