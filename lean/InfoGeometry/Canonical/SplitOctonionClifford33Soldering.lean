/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone

/-!
# The Cl(3,3) Soldering Form and Peirce Coordinate Sectors on the Zorn Carrier

This module realises the "soldering form" of the split-octonion vector-matrix carrier
$\mathbb{O}_s$ over the owner carriers of
`InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone` and
`InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge`. It reuses `ZornSplitOctonion R`,
`ParaKahlerVec R`, `embedVec`, `primalSheet`, `dualSheet`, `zornAdd`, `zornSmul`, `zornZero`,
`zornOne`, `zornE0`, `zornE1`, `paraKahlerMetric`, `fin8ToZorn`, `zornToFin8`,
`fin8ToZorn_right_inv`, `fin8ToZorn_left_inv`, and the already-certified anticommutator
`zorn_anticommutator_eq_paraKahlerMetric_smul_one`. No duplicate carrier is introduced.

1. **Bilinearity, unit laws and Peirce idempotents of `zornMul`**:
   `zornMul_add_left`, `zornMul_add_right`, `zornMul_smul_left`, `zornMul_smul_right`,
   `zornZero_mul`, `zornMul_zornZero`, `zornOne_mul`, `zornMul_zornOne`,
   `zornE0_sq`, `zornE1_sq`, `zornE0_mul_zornE1`, `zornE1_mul_zornE0`, `zornE0_add_zornE1`.
   Together with `zornLeftAct_add`/`zornLeftAct_smul` and `zornRightAct_add`/
   `zornRightAct_smul` these certify that the left- and right-multiplication operators
   $L_x(y) = x \star y$ and $R_x(y) = y \star x$ are $\mathbb{R}$-linear on the 8D ket space.

2. **Honest `8 \times 8` real matrices for `L_x` and `R_x`**:
   `fin8ToZorn_add`/`fin8ToZorn_smul` and `zornToFin8_zornAdd`/`zornToFin8_zornSmul` make
   the Fock chart `fin8ZornEquiv` compatible with the Zorn algebra structure, so
   `zornLeftActFin8` and `zornRightActFin8` are genuine
   $\mathbb{R}$-linear endomorphisms of $\mathbb{R}^8 = \mathrm{Fin}\ 8 \to \mathbb{R}$, and
   `zornLeftActMatrix`/`zornRightActMatrix` are the corresponding real
   `Matrix (Fin 8) (Fin 8) ℝ` in the standard coordinate basis
   `Pi.single j 1`. `zornLeftActMatrix_zornOne` and `zornRightActMatrix_zornOne` certify
   that the matrix of $L_1$ (resp. $R_1$) is the `8 × 8` identity matrix `I₈`.

3. **The Cl(3,3) Soldering Law** (Section 3):
   - `zorn_leftAct_clifford33_soldering`: the composed left-multiplication operators
     satisfy $\iota(z_1) \star (\iota(z_2) \star y) + \iota(z_2) \star (\iota(z_1) \star y)
     = g(z_1, z_2) \bullet y$.
   - `zorn_leftMul_clifford33_soldering`: the map-valued reading
     $(\iota(z_1) \star \iota(z_2)) \star y + (\iota(z_2) \star \iota(z_1)) \star y
     = g(z_1, z_2) \bullet y$.
   - `zorn_rightAct_clifford33_soldering` and `zorn_rightMul_clifford33_soldering`: the
     analogous right-action laws.
   - `zorn_leftActFin8_clifford33`, `zorn_rightActFin8_clifford33`,
     `zorn_leftActMatrix_clifford33`, `zorn_rightActMatrix_clifford33`: composition of the
     generator actions satisfies the Clifford anticommutator law on `ℝ⁸` and its matrices.
   - `zorn_leftAct_comp_ne_leftAct_mul` and `zorn_rightAct_comp_ne_rightAct_mul`: explicit
     witnesses that non-associativity keeps $L_x \circ L_z \neq L_{x \star z}$ and
     $R_x \circ R_z \neq R_{z \star x}$.

4. **Peirce coordinate-sector maps** (Section 4):
   `peirceKetBra00`, `peirceKetBra01`, `peirceKetBra10`, `peirceKetBra11` and the theorems
   `peirce_ketbra_00`, `peirce_ketbra_01`, `peirce_ketbra_10`, `peirce_ketbra_11` evaluate
   $\Pi_{ij}(y) = e_i \star (y \star e_j) = L_{e_i} R_{e_j} y$ on the four exterior Fock
   grades, and `peirce_ketbra_completeness` proves the
   $8 = 1 \oplus 3 \oplus 3 \oplus 1 = \Lambda^0 \oplus \Lambda^1 \oplus \Lambda^2 \oplus \Lambda^3$
   resolution.

## Scope Note

The algebraic laws of Sections 1, 3 and 4 are stated over an arbitrary commutative ring
`CommRing R`. Section 2 and the operator/matrix clauses of Section 3 are stated over `ℝ`,
which is where the `Matrix (Fin 8) (Fin 8) ℝ` carrier and the `Fin 8` Fock chart are
available. This module asserts the **Cl(3,3) anticommutator** for the multiplication
operators; it does **not** assert an isomorphism $\mathrm{Cl}(3,3) \cong M_8(\mathbb{R})$,
does not identify $L_{\iota(z)}$ with the Jordan–Wigner Majorana Kronecker strings of
`InfoGeometry.Clifford.Cl33FiniteJWMajoranaMatrix` (no proved map is given here), and does
not claim that the isotropy sheets are maximal. The `Fin 8` Fock carrier equivalence is
purely an equivalence of vector spaces: `zornLeftAct_comp_ne_leftAct_mul` and
`zorn_rightAct_comp_ne_rightAct_mul` record that the Zorn product is not associative and
hence cannot be transferred to that carrier as an associative product.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionClifford33Soldering

open scoped Matrix
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone

/-!
## Section 1: Bilinearity, Unit Laws, Peirce Idempotents, and the Multiplication Operators
-/

section ZornBilinearity

variable {R : Type*} [CommRing R]

/-- `zornMul` is additive in its left argument. -/
theorem zornMul_add_left (x y z : ZornSplitOctonion R) :
    zornMul (zornAdd x y) z = zornAdd (zornMul x z) (zornMul y z) := by
  ext k
  · dsimp [zornAdd, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornAdd, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornAdd, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornAdd, zornMul, vec3Dot]
    ring

/-- `zornMul` is additive in its right argument. -/
theorem zornMul_add_right (x y z : ZornSplitOctonion R) :
    zornMul x (zornAdd y z) = zornAdd (zornMul x y) (zornMul x z) := by
  ext k
  · dsimp [zornAdd, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornAdd, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornAdd, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornAdd, zornMul, vec3Dot]
    ring

/-- `zornMul` is homogeneous in its left argument. -/
theorem zornMul_smul_left (c : R) (x y : ZornSplitOctonion R) :
    zornMul (zornSmul c x) y = zornSmul c (zornMul x y) := by
  ext k
  · dsimp [zornSmul, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornSmul, zornMul, vec3Dot]
    ring

/-- `zornMul` is homogeneous in its right argument. -/
theorem zornMul_smul_right (c : R) (x y : ZornSplitOctonion R) :
    zornMul x (zornSmul c y) = zornSmul c (zornMul x y) := by
  ext k
  · dsimp [zornSmul, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornSmul, zornMul, vec3Dot]
    ring

/-- `zornZero` is absorbing on the left. -/
theorem zornZero_mul (y : ZornSplitOctonion R) : zornMul zornZero y = zornZero := by
  ext k
  · dsimp [zornZero, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornZero, zornMul, vec3Dot]
    ring

/-- `zornZero` is absorbing on the right. -/
theorem zornMul_zornZero (x : ZornSplitOctonion R) : zornMul x zornZero = zornZero := by
  ext k
  · dsimp [zornZero, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornZero, zornMul, vec3Dot]
    ring

/-- `zornOne` is a left unit for `zornMul`. -/
theorem zornOne_mul (y : ZornSplitOctonion R) : zornMul zornOne y = y := by
  ext k
  · dsimp [zornOne, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornOne, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornOne, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornOne, zornMul, vec3Dot]
    ring

/-- `zornOne` is a right unit for `zornMul`. -/
theorem zornMul_zornOne (x : ZornSplitOctonion R) : zornMul x zornOne = x := by
  ext k
  · dsimp [zornOne, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornOne, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornOne, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornOne, zornMul, vec3Dot]
    ring

/-- The upper-left Peirce idempotent `e_0` satisfies `e_0^2 = e_0`. -/
theorem zornE0_sq : zornMul (R := R) zornE0 zornE0 = zornE0 := by
  ext k
  · dsimp [zornE0, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornE0, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornE0, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornE0, zornMul, vec3Dot]
    ring

/-- The lower-right Peirce idempotent `e_1` satisfies `e_1^2 = e_1`. -/
theorem zornE1_sq : zornMul (R := R) zornE1 zornE1 = zornE1 := by
  ext k
  · dsimp [zornE1, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornE1, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornE1, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornE1, zornMul, vec3Dot]
    ring

/-- The two Peirce idempotents are mutually orthogonal on the left. -/
theorem zornE0_mul_zornE1 : zornMul (R := R) zornE0 zornE1 = zornZero := by
  ext k
  · dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot]
    ring

/-- The two Peirce idempotents are mutually orthogonal on the right. -/
theorem zornE1_mul_zornE0 : zornMul (R := R) zornE1 zornE0 = zornZero := by
  ext k
  · dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [zornE0, zornE1, zornZero, zornMul, vec3Dot]
    ring

/-- The Zorn identity splits as `e_0 + e_1`. -/
theorem zornE0_add_zornE1 : zornAdd (R := R) zornE0 zornE1 = zornOne := by
  ext k
  · dsimp [zornE0, zornE1, zornOne, zornAdd]
    ring
  · fin_cases k <;> (dsimp [zornE0, zornE1, zornOne, zornAdd]; ring)
  · fin_cases k <;> (dsimp [zornE0, zornE1, zornOne, zornAdd]; ring)
  · dsimp [zornE0, zornE1, zornOne, zornAdd]
    ring

/-- **Left multiplication operator `L_x(y) = x ⋆ y` on the 8D ket carrier.** -/
def zornLeftAct (x y : ZornSplitOctonion R) : ZornSplitOctonion R := zornMul x y

/-- **Right multiplication operator `R_x(y) = y ⋆ x` on the 8D ket carrier.** -/
def zornRightAct (x y : ZornSplitOctonion R) : ZornSplitOctonion R := zornMul y x

/-- `L_x` is additive in the ket. -/
theorem zornLeftAct_add (x y φ : ZornSplitOctonion R) :
    zornLeftAct x (zornAdd y φ) = zornAdd (zornLeftAct x y) (zornLeftAct x φ) := by
  unfold zornLeftAct
  exact zornMul_add_right x y φ

/-- `L_x` is homogeneous in the ket. -/
theorem zornLeftAct_smul (c : R) (x y : ZornSplitOctonion R) :
    zornLeftAct x (zornSmul c y) = zornSmul c (zornLeftAct x y) := by
  unfold zornLeftAct
  exact zornMul_smul_right c x y

/-- `R_x` is additive in the ket. -/
theorem zornRightAct_add (x y φ : ZornSplitOctonion R) :
    zornRightAct x (zornAdd y φ) = zornAdd (zornRightAct x y) (zornRightAct x φ) := by
  unfold zornRightAct
  exact zornMul_add_left y φ x

/-- `R_x` is homogeneous in the ket. -/
theorem zornRightAct_smul (c : R) (x y : ZornSplitOctonion R) :
    zornRightAct x (zornSmul c y) = zornSmul c (zornRightAct x y) := by
  unfold zornRightAct
  exact zornMul_smul_left c y x

end ZornBilinearity

/-!
## Section 2: Left and Right Multiplication as Honest 8x8 Real Matrices
-/

section RealOperator

variable {R : Type*} [CommRing R]

/-- `zornToFin8` is additive on `zornAdd`. -/
theorem zornToFin8_zornAdd (x y : ZornSplitOctonion R) :
    zornToFin8 (zornAdd x y) = fun i => zornToFin8 x i + zornToFin8 y i := by
  funext i
  fin_cases i <;> simp [zornToFin8, zornAdd, add_comm]

/-- `zornToFin8` is homogeneous on `zornSmul`. -/
theorem zornToFin8_zornSmul (c : R) (x : ZornSplitOctonion R) :
    zornToFin8 (zornSmul c x) = fun i => c * zornToFin8 x i := by
  funext i
  fin_cases i <;> simp [zornToFin8, zornSmul]

/-- `fin8ToZorn` is additive. -/
theorem fin8ToZorn_add (ψ φ : Fin 8 → R) :
    fin8ToZorn (ψ + φ) = zornAdd (fin8ToZorn ψ) (fin8ToZorn φ) := by
  ext k
  · rfl
  · fin_cases k <;> simp [fin8ToZorn, zornAdd, add_comm]
  · fin_cases k <;> simp [fin8ToZorn, zornAdd, add_comm]
  · rfl

/-- `fin8ToZorn` is homogeneous. -/
theorem fin8ToZorn_smul (c : R) (ψ : Fin 8 → R) :
    fin8ToZorn (c • ψ) = zornSmul c (fin8ToZorn ψ) := by
  ext k
  · rfl
  · fin_cases k <;> simp [fin8ToZorn, zornSmul]
  · fin_cases k <;> simp [fin8ToZorn, zornSmul]
  · rfl

/-- The left-multiplication operator `L_x` transported to the 8-component Fock ket space
`Fin 8 → ℝ` as an `ℝ`-linear endomorphism of `ℝ⁸`. -/
def zornLeftActFin8 (x : ZornSplitOctonion ℝ) : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun ψ := zornToFin8 (zornMul x (fin8ToZorn ψ))
  map_add' ψ φ := by
    rw [fin8ToZorn_add, zornMul_add_right, zornToFin8_zornAdd]
    rfl
  map_smul' c ψ := by
    rw [fin8ToZorn_smul, zornMul_smul_right, zornToFin8_zornSmul]
    rfl

/-- The right-multiplication operator `R_x` transported to the 8-component Fock ket space
`Fin 8 → ℝ` as an `ℝ`-linear endomorphism of `ℝ⁸`. -/
def zornRightActFin8 (x : ZornSplitOctonion ℝ) : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun ψ := zornToFin8 (zornMul (fin8ToZorn ψ) x)
  map_add' ψ φ := by
    rw [fin8ToZorn_add, zornMul_add_left, zornToFin8_zornAdd]
    rfl
  map_smul' c ψ := by
    rw [fin8ToZorn_smul, zornMul_smul_left, zornToFin8_zornSmul]
    rfl

/-- The genuine `8 × 8` real matrix of the left multiplication `L_x`, in the standard
coordinate basis `Pi.single j 1` of `ℝ⁸`. -/
def zornLeftActMatrix (x : ZornSplitOctonion ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)) (zornLeftActFin8 x)

/-- The genuine `8 × 8` real matrix of the right multiplication `R_x`, in the standard
coordinate basis `Pi.single j 1` of `ℝ⁸`. -/
def zornRightActMatrix (x : ZornSplitOctonion ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)) (zornRightActFin8 x)

/-- `zornLeftActFin8` turns `zornAdd` into operator addition. -/
theorem zornLeftActFin8_add (x y : ZornSplitOctonion ℝ) :
    zornLeftActFin8 (zornAdd x y) = zornLeftActFin8 x + zornLeftActFin8 y := by
  ext ψ
  simp [zornLeftActFin8, zornMul_add_left, zornToFin8_zornAdd]

/-- `zornLeftActFin8` is homogeneous. -/
theorem zornLeftActFin8_smul (c : ℝ) (x : ZornSplitOctonion ℝ) :
    zornLeftActFin8 (zornSmul c x) = c • zornLeftActFin8 x := by
  ext ψ
  simp [zornLeftActFin8, zornMul_smul_left, zornToFin8_zornSmul]

/-- `zornRightActFin8` turns `zornAdd` into operator addition. -/
theorem zornRightActFin8_add (x y : ZornSplitOctonion ℝ) :
    zornRightActFin8 (zornAdd x y) = zornRightActFin8 x + zornRightActFin8 y := by
  ext ψ
  simp [zornRightActFin8, zornMul_add_right, zornToFin8_zornAdd]

/-- `zornRightActFin8` is homogeneous. -/
theorem zornRightActFin8_smul (c : ℝ) (x : ZornSplitOctonion ℝ) :
    zornRightActFin8 (zornSmul c x) = c • zornRightActFin8 x := by
  ext ψ
  simp [zornRightActFin8, zornMul_smul_right, zornToFin8_zornSmul]

/-- `L_{1}` is the identity `8 × 8` real operator `I₈`. -/
theorem zornLeftActFin8_zornOne :
    zornLeftActFin8 (zornOne : ZornSplitOctonion ℝ) = LinearMap.id := by
  ext ψ
  simp [zornLeftActFin8, zornOne_mul, fin8ToZorn_left_inv]

/-- `R_{1}` is the identity `8 × 8` real operator `I₈`. -/
theorem zornRightActFin8_zornOne :
    zornRightActFin8 (zornOne : ZornSplitOctonion ℝ) = LinearMap.id := by
  ext ψ
  simp [zornRightActFin8, zornMul_zornOne, fin8ToZorn_left_inv]

/-- The `8 × 8` real matrix of `L_1` is the `8 × 8` identity matrix. -/
theorem zornLeftActMatrix_zornOne : zornLeftActMatrix (zornOne : ZornSplitOctonion ℝ) = 1 := by
  simp [zornLeftActMatrix, zornLeftActFin8_zornOne, LinearMap.toMatrix_id]

/-- The `8 × 8` real matrix of `R_1` is the `8 × 8` identity matrix. -/
theorem zornRightActMatrix_zornOne : zornRightActMatrix (zornOne : ZornSplitOctonion ℝ) = 1 := by
  simp [zornRightActMatrix, zornRightActFin8_zornOne, LinearMap.toMatrix_id]

end RealOperator

/-!
## Section 3: The Cl(3,3) Soldering Law
-/

section CliffordSoldering

variable {R : Type*} [CommRing R]

/-- **Theorem 15 (Cl(3,3) Soldering Law, left multiplication operators).**
Composing the left-multiplication operators `L_x(y) = x ⋆ y` as functions,
`L_{ι(z₁)} ∘ L_{ι(z₂)}` acts on the ket by the right-nested product
`ι(z₁) ⋆ (ι(z₂) ⋆ y)`. For any two pure phase-space vectors
`z₁, z₂ ∈ V = T⁺ ⊕ T⁻` and every ket `y ∈ 𝕆_s`:
`ι(z₁) ⋆ (ι(z₂) ⋆ y) + ι(z₂) ⋆ (ι(z₁) ⋆ y) = g(z₁, z₂) • y`. -/
theorem zorn_leftAct_clifford33_soldering (z₁ z₂ : ParaKahlerVec R) (y : ZornSplitOctonion R) :
    zornAdd (zornMul (embedVec z₁) (zornMul (embedVec z₂) y))
            (zornMul (embedVec z₂) (zornMul (embedVec z₁) y)) =
      zornSmul (paraKahlerMetric z₁ z₂) y := by
  ext k
  · dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross]
    ring
  · fin_cases k <;>
      (dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross];
        ring)
  · fin_cases k <;>
      (dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross];
        ring)
  · dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross]
    ring

/-- **Theorem 15-map (Cl(3,3) Soldering Law for the map-valued left action).**
The map-valued representation `z ↦ L_z` on the 8D ket space obeys the same law read on
the left-nested products, i.e. `L_{ι(z₁)⋆ι(z₂)} + L_{ι(z₂)⋆ι(z₁)} = g(z₁, z₂) L₁`. -/
theorem zorn_leftMul_clifford33_soldering (z₁ z₂ : ParaKahlerVec R) (y : ZornSplitOctonion R) :
    zornAdd (zornMul (zornMul (embedVec z₁) (embedVec z₂)) y)
            (zornMul (zornMul (embedVec z₂) (embedVec z₁)) y) =
      zornSmul (paraKahlerMetric z₁ z₂) y := by
  rw [← zornMul_add_left, zorn_anticommutator_eq_paraKahlerMetric_smul_one,
    zornMul_smul_left, zornOne_mul]

/-- **Theorem 16 (Cl(3,3) Soldering Law, right multiplication operators).**
Composing the right-multiplication operators `R_x(y) = y ⋆ x` as functions,
`R_{ι(z₁)} ∘ R_{ι(z₂)}` acts on the ket by the left-nested product
`(y ⋆ ι(z₁)) ⋆ ι(z₂)`, and
`(y ⋆ ι(z₁)) ⋆ ι(z₂) + (y ⋆ ι(z₂)) ⋆ ι(z₁) = g(z₁, z₂) • y`. -/
theorem zorn_rightAct_clifford33_soldering (z₁ z₂ : ParaKahlerVec R) (y : ZornSplitOctonion R) :
    zornAdd (zornMul (zornMul y (embedVec z₁)) (embedVec z₂))
            (zornMul (zornMul y (embedVec z₂)) (embedVec z₁)) =
      zornSmul (paraKahlerMetric z₁ z₂) y := by
  ext k
  · dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross]
    ring
  · fin_cases k <;>
      (dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross];
        ring)
  · fin_cases k <;>
      (dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross];
        ring)
  · dsimp [zornAdd, zornMul, embedVec, zornSmul, paraKahlerMetric, vec3Dot, vec3Cross]
    ring

/-- **Theorem 16-map (Cl(3,3) Soldering Law for the map-valued right action).** -/
theorem zorn_rightMul_clifford33_soldering (z₁ z₂ : ParaKahlerVec R) (y : ZornSplitOctonion R) :
    zornAdd (zornMul y (zornMul (embedVec z₁) (embedVec z₂)))
            (zornMul y (zornMul (embedVec z₂) (embedVec z₁))) =
      zornSmul (paraKahlerMetric z₁ z₂) y := by
  rw [← zornMul_add_right, zorn_anticommutator_eq_paraKahlerMetric_smul_one,
    zornMul_smul_right, zornMul_zornOne]

/-- **Theorem 15' (Cl(3,3) Soldering Law on the `ℝ⁸` operator carrier, left action).**
The compositions `L_{ι(z₁)} ∘ L_{ι(z₂)}` and `L_{ι(z₂)} ∘ L_{ι(z₁)}` satisfy the Clifford
anticommutator law on the Fock ket space. -/
theorem zorn_leftActFin8_clifford33 (z₁ z₂ : ParaKahlerVec ℝ) :
    (zornLeftActFin8 (embedVec z₁)).comp (zornLeftActFin8 (embedVec z₂))
        + (zornLeftActFin8 (embedVec z₂)).comp (zornLeftActFin8 (embedVec z₁))
      = (paraKahlerMetric z₁ z₂ : ℝ) • LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext i
  have h := zorn_leftAct_clifford33_soldering z₁ z₂ (fin8ToZorn ψ)
  have h' := congrArg zornToFin8 h
  rw [zornToFin8_zornAdd, zornToFin8_zornSmul] at h'
  simpa [zornLeftActFin8, LinearMap.comp_apply, fin8ToZorn_right_inv] using congrFun h' i

/-- **Theorem 16' (Cl(3,3) Soldering Law on the `ℝ⁸` operator carrier, right action).**
The compositions of right actions satisfy the Clifford anticommutator law on the Fock ket
space. -/
theorem zorn_rightActFin8_clifford33 (z₁ z₂ : ParaKahlerVec ℝ) :
    (zornRightActFin8 (embedVec z₂)).comp (zornRightActFin8 (embedVec z₁))
        + (zornRightActFin8 (embedVec z₁)).comp (zornRightActFin8 (embedVec z₂))
      = (paraKahlerMetric z₁ z₂ : ℝ) • LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext i
  have h := zorn_rightAct_clifford33_soldering z₁ z₂ (fin8ToZorn ψ)
  have h' := congrArg zornToFin8 h
  rw [zornToFin8_zornAdd, zornToFin8_zornSmul] at h'
  simpa [zornRightActFin8, LinearMap.comp_apply, fin8ToZorn_right_inv] using congrFun h' i

/-- **Theorem 15'' (Cl(3,3) Soldering Law on genuine real `8 × 8` matrices, left action).**
The sum of the `8 × 8` real *matrices* of `L_{ι(z₁)⋆ι(z₂)}` and `L_{ι(z₂)⋆ι(z₁)}` is
`g(z₁, z₂) • I₈`. -/
theorem zorn_leftActMatrix_clifford33 (z₁ z₂ : ParaKahlerVec ℝ) :
    zornLeftActMatrix (embedVec z₁) * zornLeftActMatrix (embedVec z₂)
        + zornLeftActMatrix (embedVec z₂) * zornLeftActMatrix (embedVec z₁)
      = paraKahlerMetric z₁ z₂ • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  let b := Pi.basisFun ℝ (Fin 8)
  have h := congrArg (LinearMap.toMatrixAlgEquiv b)
    (zorn_leftActFin8_clifford33 z₁ z₂)
  simpa [zornLeftActMatrix, LinearMap.toMatrix_comp b b b,
    Module.End.mul_eq_comp] using h

/-- **Theorem 16'' (Cl(3,3) Soldering Law on genuine real `8 × 8` matrices, right action).** -/
theorem zorn_rightActMatrix_clifford33 (z₁ z₂ : ParaKahlerVec ℝ) :
    zornRightActMatrix (embedVec z₂) * zornRightActMatrix (embedVec z₁)
        + zornRightActMatrix (embedVec z₁) * zornRightActMatrix (embedVec z₂)
      = paraKahlerMetric z₁ z₂ • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  let b := Pi.basisFun ℝ (Fin 8)
  have h := congrArg (LinearMap.toMatrixAlgEquiv b)
    (zorn_rightActFin8_clifford33 z₁ z₂)
  simpa [zornRightActMatrix, LinearMap.toMatrix_comp b b b,
    Module.End.mul_eq_comp] using h

/-- **Non-associativity defect (composition is not multiplication of operators, left
action).** On an explicit witness, `L_{ι(z₁)} ∘ L_{ι(z₂)}` differs from
`L_{ι(z₁) ⋆ ι(z₂)}`. Non-associativity of `zornMul` means the operators `L_x` do **not**
form a representation of the Zorn algebra, even though their anticommutator is exactly the
Cl(3,3) law. -/
theorem zorn_leftAct_comp_ne_leftAct_mul :
    zornLeftAct (embedVec (primalSheet (![1, 0, 0] : Fin 3 → ℝ)))
        (zornLeftAct (embedVec (dualSheet (![1, 0, 0] : Fin 3 → ℝ)))
          ⟨2, ![0, 1, 0], ![0, 0, 1], 3⟩)
      ≠ zornLeftAct (zornMul (embedVec (primalSheet (![1, 0, 0] : Fin 3 → ℝ)))
          (embedVec (dualSheet (![1, 0, 0] : Fin 3 → ℝ))))
        ⟨2, ![0, 1, 0], ![0, 0, 1], 3⟩ := by
  intro h
  have hval := congrArg (fun w : ZornSplitOctonion ℝ => w.u 1) h
  norm_num [zornLeftAct, zornMul, embedVec, primalSheet, dualSheet, vec3Dot, vec3Cross] at hval

/-- **Non-associativity defect (composition is not multiplication of operators, right
action).** -/
theorem zorn_rightAct_comp_ne_rightAct_mul :
    zornRightAct (embedVec (primalSheet (![1, 0, 0] : Fin 3 → ℝ)))
        (zornRightAct (embedVec (dualSheet (![1, 0, 0] : Fin 3 → ℝ)))
          ⟨2, ![0, 1, 0], ![0, 0, 1], 3⟩)
      ≠ zornRightAct (zornMul (embedVec (dualSheet (![1, 0, 0] : Fin 3 → ℝ)))
          (embedVec (primalSheet (![1, 0, 0] : Fin 3 → ℝ))))
        ⟨2, ![0, 1, 0], ![0, 0, 1], 3⟩ := by
  intro h
  have hval := congrArg (fun w : ZornSplitOctonion ℝ => w.u 1) h
  norm_num [zornRightAct, zornMul, embedVec, primalSheet, dualSheet, vec3Dot, vec3Cross] at hval

end CliffordSoldering

/-!
## Section 4: Peirce Ket-Bra Ideal Projectors `Π_{ij} = e_i ⋆ (y ⋆ e_j)`
-/

section PeirceProjectors

variable {R : Type*} [CommRing R]

/-- Vacuum ket-bra sector projector `Π₀₀(y) = e₀ ⋆ (y ⋆ e₀) = L_{e₀} R_{e₀} y`. -/
def peirceKetBra00 (y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornMul zornE0 (zornMul y zornE0)

/-- Primal-sheet ket-bra sector projector `Π₀₁(y) = e₀ ⋆ (y ⋆ e₁) = L_{e₀} R_{e₁} y`. -/
def peirceKetBra01 (y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornMul zornE0 (zornMul y zornE1)

/-- Dual-sheet ket-bra sector projector `Π₁₀(y) = e₁ ⋆ (y ⋆ e₀) = L_{e₁} R_{e₀} y`. -/
def peirceKetBra10 (y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornMul zornE1 (zornMul y zornE0)

/-- Top-state ket-bra sector projector `Π₁₁(y) = e₁ ⋆ (y ⋆ e₁) = L_{e₁} R_{e₁} y`. -/
def peirceKetBra11 (y : ZornSplitOctonion R) : ZornSplitOctonion R :=
  zornMul zornE1 (zornMul y zornE1)

/-- **Theorem 17a (vacuum sector `Λ⁰ ≅ ℝ`).** `Π₀₀` extracts the `|000⟩⟨000|` scalar
`a • e₀`. -/
theorem peirce_ketbra_00 (y : ZornSplitOctonion R) :
    peirceKetBra00 y = zornSmul y.a zornE0 := by
  ext k
  · dsimp [peirceKetBra00, zornE0, zornSmul, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [peirceKetBra00, zornE0, zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [peirceKetBra00, zornE0, zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [peirceKetBra00, zornE0, zornSmul, zornMul, vec3Dot]
    ring

/-- **Theorem 17b (primal sheet `T⁺ ≅ Λ¹`).** `Π₀₁` extracts the 1-particle sector
`ι(u, 0)`. -/
theorem peirce_ketbra_01 (y : ZornSplitOctonion R) :
    peirceKetBra01 y = embedVec (primalSheet y.u) := by
  ext k
  · dsimp [peirceKetBra01, zornE0, zornE1, embedVec, primalSheet, zornMul, vec3Dot]
    ring
  · fin_cases k <;>
      (dsimp [peirceKetBra01, zornE0, zornE1, embedVec, primalSheet, zornMul, vec3Dot,
        vec3Cross]; ring)
  · fin_cases k <;>
      (dsimp [peirceKetBra01, zornE0, zornE1, embedVec, primalSheet, zornMul, vec3Dot,
        vec3Cross]; ring)
  · dsimp [peirceKetBra01, zornE0, zornE1, embedVec, primalSheet, zornMul, vec3Dot]
    ring

/-- **Theorem 17c (dual sheet `T⁻ ≅ Λ²`).** `Π₁₀` extracts the 2-particle Hodge-dual
sector `ι(0, v)`. -/
theorem peirce_ketbra_10 (y : ZornSplitOctonion R) :
    peirceKetBra10 y = embedVec (dualSheet y.v) := by
  ext k
  · dsimp [peirceKetBra10, zornE0, zornE1, embedVec, dualSheet, zornMul, vec3Dot]
    ring
  · fin_cases k <;>
      (dsimp [peirceKetBra10, zornE0, zornE1, embedVec, dualSheet, zornMul, vec3Dot,
        vec3Cross]; ring)
  · fin_cases k <;>
      (dsimp [peirceKetBra10, zornE0, zornE1, embedVec, dualSheet, zornMul, vec3Dot,
        vec3Cross]; ring)
  · dsimp [peirceKetBra10, zornE0, zornE1, embedVec, dualSheet, zornMul, vec3Dot]
    ring

/-- **Theorem 17d (top state `Λ³ ≅ ℝ`).** `Π₁₁` extracts the `|111⟩⟨111|` scalar
`b • e₁`. -/
theorem peirce_ketbra_11 (y : ZornSplitOctonion R) :
    peirceKetBra11 y = zornSmul y.b zornE1 := by
  ext k
  · dsimp [peirceKetBra11, zornE1, zornSmul, zornMul, vec3Dot]
    ring
  · fin_cases k <;> (dsimp [peirceKetBra11, zornE1, zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · fin_cases k <;> (dsimp [peirceKetBra11, zornE1, zornSmul, zornMul, vec3Dot, vec3Cross]; ring)
  · dsimp [peirceKetBra11, zornE1, zornSmul, zornMul, vec3Dot]
    ring

/-- **Theorem 18 (completeness of the `8 = 1 ⊕ 3 ⊕ 3 ⊕ 1` ket-bra resolution).**
Every ket `y ∈ 𝕆_s ≅ Λ⁰ ⊕ Λ¹ ⊕ Λ² ⊕ Λ³` is the exact sum of its four Peirce ket-bra
ideal projections. -/
theorem peirce_ketbra_completeness (y : ZornSplitOctonion R) :
    zornAdd (zornAdd (peirceKetBra00 y) (peirceKetBra01 y))
            (zornAdd (peirceKetBra10 y) (peirceKetBra11 y)) = y := by
  rw [peirce_ketbra_00, peirce_ketbra_01, peirce_ketbra_10, peirce_ketbra_11]
  ext k
  · dsimp [zornE0, zornE1, embedVec, primalSheet, dualSheet, zornAdd, zornSmul]
    ring
  · fin_cases k <;>
      (dsimp [zornE0, zornE1, embedVec, primalSheet, dualSheet, zornAdd, zornSmul]; ring)
  · fin_cases k <;>
      (dsimp [zornE0, zornE1, embedVec, primalSheet, dualSheet, zornAdd, zornSmul]; ring)
  · dsimp [zornE0, zornE1, embedVec, primalSheet, dualSheet, zornAdd, zornSmul]
    ring

end PeirceProjectors

end InfoGeometry.Canonical.SplitOctonionClifford33Soldering
