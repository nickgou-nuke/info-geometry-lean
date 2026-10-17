/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Physics.CPTAtom
import InfoGeometry.Algebra.ChakravalaGA

/-!
# Explicit $8 \times 8$ Five-Graded Fock Superalgebra Representation

This module constructs an explicit, faithful $8 \times 8$ matrix representation of the
5-graded Lie superalgebra
$$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0
  \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$$
on the 3-mode fermionic Fock space $\bigwedge \mathbb{R}^3 \cong \mathbb{R}^8$ (`Fin 8`),
first over `ℤ` for kernel-checked `decide` evaluation and then lifted via
`(Int.castRingHom ℝ).mapMatrix` to `Matrix (Fin 8) (Fin 8) ℝ`:

1. **Grade $\pm 1$ Fermionic Creation & Annihilation Generators**:
   - Three nilpotent creation matrices `fockCreate0Z`, `fockCreate1Z`, `fockCreate2Z`
     spanning $\mathfrak{g}_{+1}$ and their transposes `gMinus1Z k = (gPlus1Z k)ᵀ`
     spanning $\mathfrak{g}_{-1}$, satisfying the canonical anticommutation relations
     `{a_j†, a_k} = δ_{jk} I_8`, `{a_j†, a_k†} = 0`, and `{a_j, a_k} = 0`.

2. **Unified $\mathbb{Z}_2$-Graded Superbracket & Non-Vanishing Grade $\pm 2$ Bivectors**:
   - `Z2Grade` is unified with `ChakravalaGA.Parity`, and `superBracketZ` / `superBracketR`
     are proved equal to `ChakravalaGA.superBracket`.
   - The three oriented bivector creation generators `gPlus2Z p = gPlus1Z p₁ * gPlus1Z p₂`
     and annihilation generators `gMinus2Z p = gMinus1Z p₂ * gMinus1Z p₁` are proved
     strictly non-zero (`gPlus2Z_ne_zero`, `gMinus2Z_ne_zero`).

3. **5-Graded Superbracket Closure & Nilpotency of Degree $\ge 4$**:
   - Vanishing top-grade brackets $[\mathfrak{g}_{+1}, \mathfrak{g}_{+2}] = 0$,
     $[\mathfrak{g}_{-1}, \mathfrak{g}_{-2}] = 0$, $[\mathfrak{g}_{+2}, \mathfrak{g}_{+2}] = 0$,
     and $[\mathfrak{g}_{-2}, \mathfrak{g}_{-2}] = 0$.
   - Mixed contraction $[\mathfrak{g}_{-1}, \mathfrak{g}_{+2}] \subseteq \mathfrak{g}_{+1}$
     given by `[a_i, a_{p₁}† a_{p₂}†] = δ_{i,p₁} a_{p₂}† - δ_{i,p₂} a_{p₁}†`.
   - Fourfold creation nilpotency `gPlus1Z i * gPlus1Z j * gPlus1Z k * gPlus1Z l = 0`.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight

open ChakravalaGA

/-!
## Section 1: Exact Integer $8 \times 8$ Fock Creation ($\mathfrak{g}_{+1}$) & Annihilation ($\mathfrak{g}_{-1}$) Matrices
-/

/-- First fermionic creation operator $a_0^\dagger$ on the 8-dimensional Fock space over `ℤ`. -/
def fockCreate0Z : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      1,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  0,  0,  0,  0,  0,  0;
      0,  0,  1,  0,  0,  0,  0,  0;
      0,  0,  0,  1,  0,  0,  0,  0 ]

/-- Second fermionic creation operator $a_1^\dagger$ on the 8-dimensional Fock space over `ℤ`. -/
def fockCreate1Z : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      1,  0,  0,  0,  0,  0,  0,  0;
      0,  1,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0, -1,  0,  0,  0;
      0,  0,  0,  0,  0, -1,  0,  0 ]

/-- Third fermionic creation operator $a_2^\dagger$ on the 8-dimensional Fock space over `ℤ`. -/
def fockCreate2Z : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 0,  0,  0,  0,  0,  0,  0,  0;
      1,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0, -1,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0, -1,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  0,  0;
      0,  0,  0,  0,  0,  0,  1,  0 ]

/-- Indexed family of grade-$+1$ Fock creation generators $a_k^\dagger \in \mathfrak{g}_{+1}$. -/
def gPlus1Z : Fin 3 → Matrix (Fin 8) (Fin 8) ℤ
  | 0 => fockCreate0Z
  | 1 => fockCreate1Z
  | 2 => fockCreate2Z

/-- Indexed family of grade-$-1$ Fock annihilation generators $a_k = (a_k^\dagger)^T \in \mathfrak{g}_{-1}$. -/
def gMinus1Z (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  (gPlus1Z k)ᵀ

/-- Symmetric Majorana combinations $\gamma_k^+ = a_k^\dagger + a_k$ of signature $+1$. -/
def majoranaPlusZ (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  gPlus1Z k + gMinus1Z k

/-- Skew-symmetric Majorana combinations $\gamma_k^- = a_k^\dagger - a_k$ of signature $-1$. -/
def majoranaMinusZ (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  gPlus1Z k - gMinus1Z k

/-!
## Section 2: $\mathbb{Z}_2$-Graded Superbracket & Grade $\pm 2$ Bivector Basis on `Fin 8`
-/

/-- Canonical $\mathbb{Z}_2$-grading unified with `ChakravalaGA.Parity`. -/
abbrev Z2Grade := ChakravalaGA.Parity

/-- Explicit $\mathbb{Z}_2$-graded superbracket on $8 \times 8$ integer matrices. -/
def superBracketZ (p q : Z2Grade) (A B : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  match p, q with
  | .odd, .odd => A * B + B * A
  | _, _ => A * B - B * A

/-- `superBracketZ` agrees identically with `ChakravalaGA.superBracket` over `ℤ`. -/
theorem superBracketZ_eq_chakravala (p q : Z2Grade) (A B : Matrix (Fin 8) (Fin 8) ℤ) :
    superBracketZ p q A B = ChakravalaGA.superBracket (R := ℤ) p q A B := by
  cases p <;> cases q
  · exact (ChakravalaGA.superBracket_bosonic (R := ℤ) A B).symm
  · exact (ChakravalaGA.superBracket_even_odd (R := ℤ) A B).symm
  · exact (ChakravalaGA.superBracket_odd_even (R := ℤ) A B).symm
  · exact (ChakravalaGA.superBracket_fermionic (R := ℤ) A B).symm

/-- Enumeration of the three oriented mode pairs `(0, 1)`, `(1, 2)`, `(0, 2)` spanning $\bigwedge^2 \mathbb{R}^3$. -/
def bivectorPair : Fin 3 → Fin 3 × Fin 3
  | 0 => (0, 1)
  | 1 => (1, 2)
  | 2 => (0, 2)

/-- Grade-$+2$ bivector creation generators $a_{p_1}^\dagger a_{p_2}^\dagger \in \mathfrak{g}_{+2}$. -/
def gPlus2Z (p : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  gPlus1Z (bivectorPair p).1 * gPlus1Z (bivectorPair p).2

/-- Grade-$-2$ bivector annihilation generators $a_{p_2} a_{p_1} \in \mathfrak{g}_{-2}$. -/
def gMinus2Z (p : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  gMinus1Z (bivectorPair p).2 * gMinus1Z (bivectorPair p).1

/-- Grade-$0$ Levi subalgebra generators $[a_j^\dagger, a_k] = a_j^\dagger a_k - a_k a_j^\dagger \in \mathfrak{g}_0$. -/
def gZeroLeviZ (j k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  gPlus1Z j * gMinus1Z k - gMinus1Z k * gPlus1Z j

/-!
## Section 3: Kernel-Certified 5-Graded Closure Theorems over `ℤ`
-/

/-- Canonical anticommutation relation $\{a_j^\dagger, a_k\} = \delta_{jk} I_8$ between $\mathfrak{g}_{+1}$ and $\mathfrak{g}_{-1}$. -/
theorem gPlus1_gMinus1_odd_superBracketZ (j k : Fin 3) :
    superBracketZ .odd .odd (gPlus1Z j) (gMinus1Z k) =
      (if j = k then (1 : ℤ) else 0) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  revert j k
  decide

/-- Creation operators in $\mathfrak{g}_{+1}$ pairwise anticommute: $\{a_j^\dagger, a_k^\dagger\} = 0$. -/
theorem gPlus1_gPlus1_odd_superBracketZ (j k : Fin 3) :
    superBracketZ .odd .odd (gPlus1Z j) (gPlus1Z k) = 0 := by
  revert j k
  decide

/-- Annihilation operators in $\mathfrak{g}_{-1}$ pairwise anticommute: $\{a_j, a_k\} = 0$. -/
theorem gMinus1_gMinus1_odd_superBracketZ (j k : Fin 3) :
    superBracketZ .odd .odd (gMinus1Z j) (gMinus1Z k) = 0 := by
  revert j k
  decide

/-- The commutator of two creation operators in $\mathfrak{g}_{+1}$ equals twice the corresponding
grade-$+2$ bivector generator in $\mathfrak{g}_{+2}$. -/
theorem gPlus1_skewCommutator_eq_two_gPlus2Z (p : Fin 3) :
    gPlus1Z (bivectorPair p).1 * gPlus1Z (bivectorPair p).2 -
      gPlus1Z (bivectorPair p).2 * gPlus1Z (bivectorPair p).1 =
      (2 : ℤ) • gPlus2Z p := by
  revert p
  decide

/-- Every grade-$+2$ bivector generator `gPlus2Z p` is non-zero. -/
theorem gPlus2Z_ne_zero (p : Fin 3) : gPlus2Z p ≠ 0 := by
  revert p
  decide

/-- Explicit non-commutativity witness for the grade-$+1$ Fock creation generators:
`fockCreate0Z * fockCreate1Z ≠ fockCreate1Z * fockCreate0Z`. -/
theorem fockCreate0Z_mul_fockCreate1Z_ne_comm :
    fockCreate0Z * fockCreate1Z ≠ fockCreate1Z * fockCreate0Z := by
  decide

/-- Every grade-$-2$ bivector generator `gMinus2Z p` is non-zero. -/
theorem gMinus2Z_ne_zero (p : Fin 3) : gMinus2Z p ≠ 0 := by
  revert p
  decide

/-- Grade $+1$ and grade $+2$ commute: $[\mathfrak{g}_{+1}, \mathfrak{g}_{+2}] = 0$ (grade $+3$ vanishes). -/
theorem gPlus1_gPlus2_superBracket_zeroZ (i p : Fin 3) :
    superBracketZ .odd .even (gPlus1Z i) (gPlus2Z p) = 0 := by
  revert i p
  decide

/-- Grade $-1$ and grade $-2$ commute: $[\mathfrak{g}_{-1}, \mathfrak{g}_{-2}] = 0$ (grade $-3$ vanishes). -/
theorem gMinus1_gMinus2_superBracket_zeroZ (i p : Fin 3) :
    superBracketZ .odd .even (gMinus1Z i) (gMinus2Z p) = 0 := by
  revert i p
  decide

/-- Grade $+2$ generators pairwise commute: $[\mathfrak{g}_{+2}, \mathfrak{g}_{+2}] = 0$ (grade $+4$ vanishes). -/
theorem gPlus2_gPlus2_superBracket_zeroZ (p q : Fin 3) :
    superBracketZ .even .even (gPlus2Z p) (gPlus2Z q) = 0 := by
  revert p q
  decide

/-- Grade $-2$ generators pairwise commute: $[\mathfrak{g}_{-2}, \mathfrak{g}_{-2}] = 0$ (grade $-4$ vanishes). -/
theorem gMinus2_gMinus2_superBracket_zeroZ (p q : Fin 3) :
    superBracketZ .even .even (gMinus2Z p) (gMinus2Z q) = 0 := by
  revert p q
  decide

/-- **Mixed Grade Contraction $[\mathfrak{g}_{-1}, \mathfrak{g}_{+2}] \subseteq \mathfrak{g}_{+1}$**:
The superbracket of an annihilation operator $a_i \in \mathfrak{g}_{-1}$ with a bivector creation
operator $a_{p_1}^\dagger a_{p_2}^\dagger \in \mathfrak{g}_{+2}$ lands in $\mathfrak{g}_{+1}$ via
interior contraction: $[a_i, a_{p_1}^\dagger a_{p_2}^\dagger] = \delta_{i, p_1} a_{p_2}^\dagger - \delta_{i, p_2} a_{p_1}^\dagger$. -/
theorem gMinus1_gPlus2_superBracket_in_gPlus1Z (i p : Fin 3) :
    superBracketZ .odd .even (gMinus1Z i) (gPlus2Z p) =
      (if i = (bivectorPair p).1 then (1 : ℤ) else 0) • gPlus1Z (bivectorPair p).2 -
        (if i = (bivectorPair p).2 then (1 : ℤ) else 0) • gPlus1Z (bivectorPair p).1 := by
  revert i p
  decide

/-- Any fourfold product of grade-$+1$ Fock creation operators on $\bigwedge \mathbb{R}^3$ vanishes. -/
theorem gPlus1_fourfold_mul_zeroZ (i j k l : Fin 3) :
    gPlus1Z i * gPlus1Z j * gPlus1Z k * gPlus1Z l = 0 := by
  revert i j k l
  decide

/-!
## Section 4: Lifting All 5-Graded Closure Theorems to `Matrix (Fin 8) (Fin 8) ℝ`
-/

noncomputable section

/-- Real $8 \times 8$ grade-$+1$ Fock creation generator lifted from `gPlus1Z`. -/
def gPlus1R (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (gPlus1Z k)

/-- Real $8 \times 8$ grade-$-1$ Fock annihilation generator lifted from `gMinus1Z`. -/
def gMinus1R (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (gMinus1Z k)

/-- Real $8 \times 8$ grade-$+2$ bivector creation generator lifted from `gPlus2Z`. -/
def gPlus2R (p : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (gPlus2Z p)

/-- Real $8 \times 8$ grade-$-2$ bivector annihilation generator lifted from `gMinus2Z`. -/
def gMinus2R (p : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (gMinus2Z p)

/-- Real $8 \times 8$ grade-$0$ Levi subalgebra generator lifted from `gZeroLeviZ`. -/
def gZeroLeviR (j k : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (gZeroLeviZ j k)

/-- $\mathbb{Z}_2$-graded superbracket on $8 \times 8$ real matrices. -/
def superBracketR (p q : Z2Grade) (A B : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  match p, q with
  | .odd, .odd => A * B + B * A
  | _, _ => A * B - B * A

/-- `superBracketR` agrees identically with `ChakravalaGA.superBracket` over `ℝ`. -/
theorem superBracketR_eq_chakravala (p q : Z2Grade) (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    superBracketR p q A B = ChakravalaGA.superBracket (R := ℝ) p q A B := by
  cases p <;> cases q
  · exact (ChakravalaGA.superBracket_bosonic (R := ℝ) A B).symm
  · exact (ChakravalaGA.superBracket_even_odd (R := ℝ) A B).symm
  · exact (ChakravalaGA.superBracket_odd_even (R := ℝ) A B).symm
  · exact (ChakravalaGA.superBracket_fermionic (R := ℝ) A B).symm

/-- Entrywise integer-to-real matrix casting intertwines `superBracketZ` and `superBracketR`. -/
theorem mapMatrix_superBracketZ (p q : Z2Grade) (A B : Matrix (Fin 8) (Fin 8) ℤ) :
    (Int.castRingHom ℝ).mapMatrix (superBracketZ p q A B) =
      superBracketR p q ((Int.castRingHom ℝ).mapMatrix A) ((Int.castRingHom ℝ).mapMatrix B) := by
  cases p <;> cases q <;>
    simp [superBracketZ, superBracketR, map_add, map_sub, map_mul]

/-- Entrywise integer-to-real matrix casting converts integer scalar multiplication to real
scalar multiplication. -/
theorem mapMatrix_zsmul (c : ℤ) (M : Matrix (Fin 8) (Fin 8) ℤ) :
    (Int.castRingHom ℝ).mapMatrix (c • M) = (c : ℝ) • (Int.castRingHom ℝ).mapMatrix M := by
  ext i j
  exact Int.cast_mul c (M i j)

/-- Over `ℝ`, the commutator of the grade-$+1$ creation generators for pair `p` equals twice the
grade-$+2$ bivector generator `gPlus2R p`. -/
theorem gPlus1R_commutator_eq_gPlus2R (p : Fin 3) :
    gPlus1R (bivectorPair p).1 * gPlus1R (bivectorPair p).2 -
      gPlus1R (bivectorPair p).2 * gPlus1R (bivectorPair p).1 =
      (2 : ℝ) • gPlus2R p := by
  have h := congrArg ((Int.castRingHom ℝ).mapMatrix) (gPlus1_skewCommutator_eq_two_gPlus2Z p)
  rw [map_sub, map_mul, map_mul, mapMatrix_zsmul] at h
  exact h

/-- Over `ℝ`, grade $+1$ and grade $+2$ supercommute: $[\mathfrak{g}_{+1}, \mathfrak{g}_{+2}] = 0$. -/
theorem gPlus1R_gPlus2R_superBracket_zero (i p : Fin 3) :
    superBracketR .odd .even (gPlus1R i) (gPlus2R p) = 0 := by
  dsimp [gPlus1R, gPlus2R]
  rw [← mapMatrix_superBracketZ, gPlus1_gPlus2_superBracket_zeroZ i p, map_zero]

/-- Over `ℝ`, grade $-1$ and grade $-2$ supercommute: $[\mathfrak{g}_{-1}, \mathfrak{g}_{-2}] = 0$. -/
theorem gMinus1R_gMinus2R_superBracket_zero (i p : Fin 3) :
    superBracketR .odd .even (gMinus1R i) (gMinus2R p) = 0 := by
  dsimp [gMinus1R, gMinus2R]
  rw [← mapMatrix_superBracketZ, gMinus1_gMinus2_superBracket_zeroZ i p, map_zero]

/-- Over `ℝ`, grade $+2$ bivector generators pairwise commute: $[\mathfrak{g}_{+2}, \mathfrak{g}_{+2}] = 0$. -/
theorem gPlus2R_gPlus2R_superBracket_zero (p q : Fin 3) :
    superBracketR .even .even (gPlus2R p) (gPlus2R q) = 0 := by
  dsimp [gPlus2R]
  rw [← mapMatrix_superBracketZ, gPlus2_gPlus2_superBracket_zeroZ p q, map_zero]

/-- Over `ℝ`, grade $-2$ bivector generators pairwise commute: $[\mathfrak{g}_{-2}, \mathfrak{g}_{-2}] = 0$. -/
theorem gMinus2R_gMinus2R_superBracket_zero (p q : Fin 3) :
    superBracketR .even .even (gMinus2R p) (gMinus2R q) = 0 := by
  dsimp [gMinus2R]
  rw [← mapMatrix_superBracketZ, gMinus2_gMinus2_superBracket_zeroZ p q, map_zero]

/-- Over `ℝ`, the mixed grade superbracket $[\mathfrak{g}_{-1}, \mathfrak{g}_{+2}]$ contracts into
$\mathfrak{g}_{+1}$. -/
theorem gMinus1R_gPlus2R_superBracket_in_gPlus1R (i p : Fin 3) :
    superBracketR .odd .even (gMinus1R i) (gPlus2R p) =
      (if i = (bivectorPair p).1 then (1 : ℝ) else 0) • gPlus1R (bivectorPair p).2 -
        (if i = (bivectorPair p).2 then (1 : ℝ) else 0) • gPlus1R (bivectorPair p).1 := by
  dsimp [gMinus1R, gPlus2R, gPlus1R]
  rw [← mapMatrix_superBracketZ, gMinus1_gPlus2_superBracket_in_gPlus1Z i p,
    map_sub, mapMatrix_zsmul, mapMatrix_zsmul]
  push_cast
  rfl

/-- Over `ℝ`, any fourfold product of grade-$+1$ Fock creation operators vanishes. -/
theorem gPlus1R_fourfold_mul_zero (i j k l : Fin 3) :
    gPlus1R i * gPlus1R j * gPlus1R k * gPlus1R l = 0 := by
  dsimp [gPlus1R]
  rw [← map_mul, ← map_mul, ← map_mul, gPlus1_fourfold_mul_zeroZ i j k l, map_zero]

/-- First real $8 \times 8$ grade-$+1$ Fock creation matrix $a_0^\dagger$. -/
def fockCreate0R : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix fockCreate0Z

/-- Second real $8 \times 8$ grade-$+1$ Fock creation matrix $a_1^\dagger$. -/
def fockCreate1R : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix fockCreate1Z

/-- Explicit non-commutativity witness for the real $8 \times 8$ Fock creation generators:
`fockCreate0R * fockCreate1R ≠ fockCreate1R * fockCreate0R`. -/
theorem fockCreate0R_mul_fockCreate1R_ne_comm :
    fockCreate0R * fockCreate1R ≠ fockCreate1R * fockCreate0R := by
  intro h
  apply fockCreate0Z_mul_fockCreate1Z_ne_comm
  ext i j
  have hij : ((Int.castRingHom ℝ).mapMatrix (fockCreate0Z * fockCreate1Z)) i j =
      ((Int.castRingHom ℝ).mapMatrix (fockCreate1Z * fockCreate0Z)) i j := by
    rw [map_mul, map_mul]
    exact congr_fun (congr_fun h i) j
  exact Int.cast_injective hij

end

end InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight
