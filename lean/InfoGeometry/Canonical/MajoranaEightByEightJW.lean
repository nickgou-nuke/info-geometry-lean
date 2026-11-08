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
# Explicit $8 \times 8$ Jordan–Wigner Majorana Representation of $\mathrm{Cl}(3,3)$ and 3-Mode Para-Kähler CAR Algebra

This module constructs the explicit $8 \times 8$ Jordan–Wigner matrix representation of the
split-signature Clifford algebra $\mathrm{Cl}(3,3)$ and the 3-mode Para-Kähler fermionic CAR
algebra on the 3-qubit spinor space $\mathbb{R}^8$ (`Fin 8 → ℝ`):

1. **Section 1 — Integer Kernel Carrier (`Matrix (Fin 8) (Fin 8) ℤ`)**:
   - Defines the six explicit $8 \times 8$ Jordan–Wigner Majorana matrices
     `gamma1PlusZ`, `gamma1MinusZ`, `gamma2PlusZ`, `gamma2MinusZ`, `gamma3PlusZ`, `gamma3MinusZ`
     corresponding to the tensor products:
     $$\gamma_1^+ = X \otimes I_2 \otimes I_2, \qquad \gamma_1^- = E \otimes I_2 \otimes I_2,$$
     $$\gamma_2^+ = Z \otimes X \otimes I_2, \qquad \gamma_2^- = Z \otimes E \otimes I_2,$$
     $$\gamma_3^+ = Z \otimes Z \otimes X, \qquad \gamma_3^- = Z \otimes Z \otimes E,$$
     where $X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$,
     $E = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$, and
     $Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$.
   - Bundles the six generators into `majoranaGenZ : Fin 6 → Matrix (Fin 8) (Fin 8) ℤ` with
     split metric signature `majoranaSignatureZ : Fin 6 → ℤ` ($(+1, -1, +1, -1, +1, -1)$) and
     certifies the complete $\mathrm{Cl}(3,3)$ Clifford relations (`majoranaGenZ_sq`,
     `majoranaGenZ_pairwise_anticomm`, `majoranaGenZ_clifford_superBracket`) and scaled 3-mode
     CAR relations (`twoFockCreate8Z_sq`, `twoFockAnnihilate8Z_sq`, `twoFockCreate8Z_anticomm`,
     `twoFockAnnihilate8Z_anticomm`, `twoFockCreate8Z_twoFockAnnihilate8Z_superBracket`) via
     kernel `decide`.

2. **Section 2 — Real $8 \times 8$ Spinor Representation (`Matrix (Fin 8) (Fin 8) ℝ`)**:
   - Lifts `majoranaGenZ` to `majoranaGenR : Fin 6 → Matrix (Fin 8) (Fin 8) ℝ` via
     `(Int.castRingHom ℝ).mapMatrix`, proving the real $\mathrm{Cl}(3,3)$ odd-odd superbracket law
     `majoranaGenR_clifford_superBracket`:
     $$\\gamma_a, \gamma_b\_{\mathrm{odd},\mathrm{odd}} = 2 \eta_{ab} I_8.$$

3. **Section 3 — 3-Mode Isotropic Para-Kähler Creation & Annihilation Operators (`fockCreate8`, `fockAnnihilate8`)**:
   - Reconstructs the three isotropic creation operators
     $c_k^\dagger = \frac{1}{2}(\gamma_k^+ + \gamma_k^-)$ (`fockCreate8 k`) and three isotropic
     annihilation operators $c_k = \frac{1}{2}(\gamma_k^+ - \gamma_k^-)$ (`fockAnnihilate8 k`)
     for $k \in \mathrm{Fin}\ 3$.
   - Proves the complete 3-mode Para-Kähler CAR algebra on `Matrix (Fin 8) (Fin 8) ℝ`:
     $$(c_k^\dagger)^2 = 0, \quad c_k^2 = 0, \quad \c_j^\dagger, c_k^\dagger\ = 0, \quad
       \c_j, c_k\ = 0, \quad \c_j^\dagger, c_k\ = \delta_{jk} I_8.$$

## Scope Note

This module formalizes the finite 3-mode ($2^3 = 8$-dimensional) Jordan–Wigner matrix
representation of $\mathrm{Cl}(3,3)$ and the 3-mode CAR algebra on `Matrix (Fin 8) (Fin 8) ℤ` and
`Matrix (Fin 8) (Fin 8) ℝ`.
-/

namespace InfoGeometry.Canonical.MajoranaEightByEightJW

open Matrix

/-!
### Section 1 — Explicit $8 \times 8$ Jordan–Wigner Majorana Matrices on `Fin 8` (Integer Kernel Carrier)
-/

/-- First even Majorana generator $\gamma_1^+ = X \otimes I_2 \otimes I_2$ on `Fin 8`. -/
def gamma1PlusZ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- First skew Majorana generator $\gamma_1^- = E \otimes I_2 \otimes I_2$ on `Fin 8`,
where $E = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. -/
def gamma1MinusZ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- Second even Majorana generator $\gamma_2^+ = Z \otimes X \otimes I_2$ on `Fin 8`. -/
def gamma2PlusZ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0]

/-- Second skew Majorana generator $\gamma_2^- = Z \otimes E \otimes I_2$ on `Fin 8`. -/
def gamma2MinusZ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0]

/-- Third even Majorana generator $\gamma_3^+ = Z \otimes Z \otimes X$ on `Fin 8`. -/
def gamma3PlusZ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- Third skew Majorana generator $\gamma_3^- = Z \otimes Z \otimes E$ on `Fin 8`. -/
def gamma3MinusZ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, -1, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- Indexed family of the 6 Jordan–Wigner Majorana generators of $\mathrm{Cl}(3,3)$ over `ℤ`:
$(\gamma_1^+, \gamma_1^-, \gamma_2^+, \gamma_2^-, \gamma_3^+, \gamma_3^-)$. -/
def majoranaGenZ : Fin 6 → Matrix (Fin 8) (Fin 8) ℤ
  | ⟨0, _⟩ => gamma1PlusZ
  | ⟨1, _⟩ => gamma1MinusZ
  | ⟨2, _⟩ => gamma2PlusZ
  | ⟨3, _⟩ => gamma2MinusZ
  | ⟨4, _⟩ => gamma3PlusZ
  | ⟨5, _⟩ => gamma3MinusZ

/-- Split metric signature $\eta_a \in \{+1, -1\}$ of the 6 Majorana generators:
$\eta = (+1, -1, +1, -1, +1, -1)$. -/
def majoranaSignatureZ : Fin 6 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => -1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => -1

/-- Fermionic anticommutator $\{A, B\} = A B + B A$ on `Matrix (Fin 8) (Fin 8) ℤ`. -/
def oddSuperBracketZ (A B : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  A * B + B * A

/-- `oddSuperBracketZ` coincides with `ChakravalaGA.superBracket (R := ℤ) .odd .odd`. -/
theorem oddSuperBracketZ_eq_superBracket (A B : Matrix (Fin 8) (Fin 8) ℤ) :
    oddSuperBracketZ A B = ChakravalaGA.superBracket (R := ℤ) .odd .odd A B :=
  (ChakravalaGA.superBracket_fermionic A B).symm

/-- **Split-Signature Square Law on `Fin 8` over `ℤ`**:
Each Majorana generator squares to $\eta_a I_8$: $(\gamma_a)^2 = \eta_a I_8$. -/
theorem majoranaGenZ_sq (a : Fin 6) :
    majoranaGenZ a * majoranaGenZ a =
      majoranaSignatureZ a • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  revert a
  decide

/-- **Pairwise Anticommutation of Distinct Majorana Generators on `Fin 8` over `ℤ`**:
For $a \ne b$, $\gamma_a \gamma_b + \gamma_b \gamma_a = 0$. -/
theorem majoranaGenZ_pairwise_anticomm (a b : Fin 6) (hab : a ≠ b) :
    oddSuperBracketZ (majoranaGenZ a) (majoranaGenZ b) = 0 := by
  revert hab
  revert a b
  decide

/-- Explicit matrix anticommutator form $\gamma_a \gamma_b + \gamma_b \gamma_a = 0$ for $a \ne b$. -/
theorem majoranaGenZ_mul_add_mul_eq_zero (a b : Fin 6) (hab : a ≠ b) :
    majoranaGenZ a * majoranaGenZ b + majoranaGenZ b * majoranaGenZ a = 0 :=
  majoranaGenZ_pairwise_anticomm a b hab

/-- **Strict Non-Commutativity of Distinct Majorana Generators on `Fin 8`**:
For any two distinct generators $a \ne b$ in `Fin 6`, $\gamma_a \gamma_b \ne \gamma_b \gamma_a$. -/
theorem majoranaGenZ_noncomm (a b : Fin 6) (hab : a ≠ b) :
    majoranaGenZ a * majoranaGenZ b ≠ majoranaGenZ b * majoranaGenZ a := by
  revert hab
  revert a b
  decide

/-- Concrete non-commutativity witness $\gamma_1^+ \gamma_1^- \ne \gamma_1^- \gamma_1^+$. -/
theorem gamma1PlusZ_mul_gamma1MinusZ_ne_comm :
    gamma1PlusZ * gamma1MinusZ ≠ gamma1MinusZ * gamma1PlusZ := by
  decide

/-- **Full $\mathrm{Cl}(3,3)$ Clifford Superbracket Table on `Fin 8` over `ℤ`**:
For all $a, b \in \mathrm{Fin}\ 6$, $\gamma_a \gamma_b + \gamma_b \gamma_a = 2 \delta_{ab} \eta_a I_8$. -/
theorem majoranaGenZ_clifford_superBracket (a b : Fin 6) :
    oddSuperBracketZ (majoranaGenZ a) (majoranaGenZ b) =
      (if a = b then 2 * majoranaSignatureZ a else 0) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  revert a b
  decide

/-- Even Majorana index $2k \in \mathrm{Fin}\ 6$ associated with fermion mode $k \in \mathrm{Fin}\ 3$. -/
def modeEvenIdx (k : Fin 3) : Fin 6 :=
  ⟨2 * k.val, by omega⟩

/-- Odd Majorana index $2k + 1 \in \mathrm{Fin}\ 6$ associated with fermion mode $k \in \mathrm{Fin}\ 3$. -/
def modeOddIdx (k : Fin 3) : Fin 6 :=
  ⟨2 * k.val + 1, by omega⟩

/-- Unscaled integer Para-Kähler creation matrix $2 c_k^\dagger = \gamma_k^+ + \gamma_k^-$
for mode $k \in \mathrm{Fin}\ 3$. -/
def twoFockCreate8Z (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  majoranaGenZ (modeEvenIdx k) + majoranaGenZ (modeOddIdx k)

/-- Unscaled integer Para-Kähler annihilation matrix $2 c_k = \gamma_k^+ - \gamma_k^-$
for mode $k \in \mathrm{Fin}\ 3$. -/
def twoFockAnnihilate8Z (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℤ :=
  majoranaGenZ (modeEvenIdx k) - majoranaGenZ (modeOddIdx k)

/-- Nilpotency $(2 c_k^\dagger)^2 = 0$ for each mode $k \in \mathrm{Fin}\ 3$. -/
theorem twoFockCreate8Z_sq (k : Fin 3) :
    twoFockCreate8Z k * twoFockCreate8Z k = 0 := by
  revert k
  decide

/-- Nilpotency $(2 c_k)^2 = 0$ for each mode $k \in \mathrm{Fin}\ 3$. -/
theorem twoFockAnnihilate8Z_sq (k : Fin 3) :
    twoFockAnnihilate8Z k * twoFockAnnihilate8Z k = 0 := by
  revert k
  decide

/-- Pairwise anticommutation $\{2 c_j^\dagger, 2 c_k^\dagger\} = 0$ for all $j, k \in \mathrm{Fin}\ 3$. -/
theorem twoFockCreate8Z_anticomm (j k : Fin 3) :
    oddSuperBracketZ (twoFockCreate8Z j) (twoFockCreate8Z k) = 0 := by
  revert j k
  decide

/-- Pairwise anticommutation $\{2 c_j, 2 c_k\} = 0$ for all $j, k \in \mathrm{Fin}\ 3$. -/
theorem twoFockAnnihilate8Z_anticomm (j k : Fin 3) :
    oddSuperBracketZ (twoFockAnnihilate8Z j) (twoFockAnnihilate8Z k) = 0 := by
  revert j k
  decide

/-- Canonical anticommutator $\{2 c_j^\dagger, 2 c_k\} = 4 \delta_{jk} I_8$ over `ℤ` for all
$j, k \in \mathrm{Fin}\ 3$. -/
theorem twoFockCreate8Z_twoFockAnnihilate8Z_superBracket (j k : Fin 3) :
    oddSuperBracketZ (twoFockCreate8Z j) (twoFockAnnihilate8Z k) =
      (if j = k then (4 : ℤ) else 0) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  revert j k
  decide

/-!
### Section 2 — Lifting to Real $8 \times 8$ Matrices (`Matrix (Fin 8) (Fin 8) ℝ`)
-/

/-- Real $8 \times 8$ Jordan–Wigner Majorana generator $\gamma_a \in M_8(\mathbb{R})$ obtained by
casting `majoranaGenZ a` along `Int.castRingHom ℝ`. -/
def majoranaGenR (a : Fin 6) : Matrix (Fin 8) (Fin 8) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (majoranaGenZ a)

/-- Real $8 \times 8$ generator $\gamma_1^+ = X \otimes I_2 \otimes I_2$. -/
def gamma1PlusR : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR ⟨0, by decide⟩

/-- Real $8 \times 8$ generator $\gamma_1^- = E \otimes I_2 \otimes I_2$. -/
def gamma1MinusR : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR ⟨1, by decide⟩

/-- Real $8 \times 8$ generator $\gamma_2^+ = Z \otimes X \otimes I_2$. -/
def gamma2PlusR : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR ⟨2, by decide⟩

/-- Real $8 \times 8$ generator $\gamma_2^- = Z \otimes E \otimes I_2$. -/
def gamma2MinusR : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR ⟨3, by decide⟩

/-- Real $8 \times 8$ generator $\gamma_3^+ = Z \otimes Z \otimes X$. -/
def gamma3PlusR : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR ⟨4, by decide⟩

/-- Real $8 \times 8$ generator $\gamma_3^- = Z \otimes Z \otimes E$. -/
def gamma3MinusR : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR ⟨5, by decide⟩

/-- Split metric signature $\eta_a \in \{+1, -1\} \subset \mathbb{R}$ of `majoranaGenR a`. -/
def majoranaSignatureR (a : Fin 6) : ℝ :=
  (majoranaSignatureZ a : ℝ)

/-- Fermionic anticommutator $\{A, B\} = A B + B A$ on `Matrix (Fin 8) (Fin 8) ℝ`. -/
def oddSuperBracketR (A B : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  A * B + B * A

/-- `oddSuperBracketR` coincides with `ChakravalaGA.superBracket (R := ℝ) .odd .odd`. -/
theorem oddSuperBracketR_eq_superBracket (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    oddSuperBracketR A B = ChakravalaGA.superBracket (R := ℝ) .odd .odd A B :=
  (ChakravalaGA.superBracket_fermionic A B).symm

/-- Casting an integer-scaled matrix `c • A` to `Matrix (Fin 8) (Fin 8) ℝ` equals `(c : ℝ) • mapMatrix A`. -/
theorem mapMatrix_zsmul (c : ℤ) (A : Matrix (Fin 8) (Fin 8) ℤ) :
    (Int.castRingHom ℝ).mapMatrix (c • A) =
      (c : ℝ) • (Int.castRingHom ℝ).mapMatrix A := by
  ext i j
  exact Int.cast_mul c (A i j)

/-- `(Int.castRingHom ℝ).mapMatrix` intertwines `oddSuperBracketZ` with `ChakravalaGA.superBracket .odd .odd`. -/
theorem mapMatrix_oddSuperBracketZ (A B : Matrix (Fin 8) (Fin 8) ℤ) :
    (Int.castRingHom ℝ).mapMatrix (oddSuperBracketZ A B) =
      ChakravalaGA.superBracket (R := ℝ) .odd .odd
        ((Int.castRingHom ℝ).mapMatrix A)
        ((Int.castRingHom ℝ).mapMatrix B) := by
  dsimp [oddSuperBracketZ]
  rw [ChakravalaGA.superBracket_fermionic, map_add, map_mul, map_mul]

/-- **Real Split-Signature Square Law on `Fin 8`**:
Each real $8 \times 8$ Majorana generator satisfies $(\gamma_a)^2 = \eta_a I_8$. -/
theorem majoranaGenR_sq (a : Fin 6) :
    majoranaGenR a * majoranaGenR a =
      majoranaSignatureR a • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  dsimp [majoranaGenR, majoranaSignatureR]
  rw [← map_mul, majoranaGenZ_sq a, mapMatrix_zsmul, map_one]

/-- **Pairwise Anticommutation of Distinct Real Majorana Generators on `Fin 8`**:
For $a \ne b$, `[majoranaGenR a, majoranaGenR b]_{odd,odd} = 0`. -/
theorem majoranaGenR_pairwise_anticomm (a b : Fin 6) (hab : a ≠ b) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (majoranaGenR a) (majoranaGenR b) = 0 := by
  dsimp [majoranaGenR]
  rw [← mapMatrix_oddSuperBracketZ, majoranaGenZ_pairwise_anticomm a b hab, map_zero]

/-- Concrete real anticommutator witness $\gamma_1^+ \gamma_1^- + \gamma_1^- \gamma_1^+ = 0$
on `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem gamma1PlusR_anticomm_gamma1MinusR :
    gamma1PlusR * gamma1MinusR + gamma1MinusR * gamma1PlusR = 0 := by
  rw [← ChakravalaGA.superBracket_fermionic (R := ℝ)]
  exact majoranaGenR_pairwise_anticomm ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)

/-- **Full $\mathrm{Cl}(3,3)$ Clifford Odd-Odd Superbracket Identity on `Matrix (Fin 8) (Fin 8) ℝ`**:
For all $a, b \in \mathrm{Fin}\ 6$,
`ChakravalaGA.superBracket .odd .odd (majoranaGenR a) (majoranaGenR b) = (if a = b then 2 * majoranaSignatureR a else 0) • 1`. -/
theorem majoranaGenR_clifford_superBracket (a b : Fin 6) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (majoranaGenR a) (majoranaGenR b) =
      (if a = b then 2 * majoranaSignatureR a else 0) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  dsimp [majoranaGenR]
  rw [← mapMatrix_oddSuperBracketZ, majoranaGenZ_clifford_superBracket a b,
    mapMatrix_zsmul, map_one]
  congr 1
  by_cases hab : a = b
  · simp [hab, majoranaSignatureR]
  · simp [hab]

/-!
### Section 3 — Recovering the 3 Isotropic Para-Kähler Creation/Annihilation Pairs on `Fin 8` & Full 3-Mode CAR Algebra
-/

/-- Isotropic Para-Kähler creation matrix $c_k^\dagger = \frac{1}{2}(\gamma_k^+ + \gamma_k^-)$
on `Matrix (Fin 8) (Fin 8) ℝ` for mode $k \in \mathrm{Fin}\ 3$. -/
noncomputable def fockCreate8 (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 / 2 : ℝ) • (majoranaGenR (modeEvenIdx k) + majoranaGenR (modeOddIdx k))

/-- Isotropic Para-Kähler annihilation matrix $c_k = \frac{1}{2}(\gamma_k^+ - \gamma_k^-)$
on `Matrix (Fin 8) (Fin 8) ℝ` for mode $k \in \mathrm{Fin}\ 3$. -/
noncomputable def fockAnnihilate8 (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 / 2 : ℝ) • (majoranaGenR (modeEvenIdx k) - majoranaGenR (modeOddIdx k))

/-- `fockCreate8 k` is `(1 / 2 : ℝ)` times the real cast of `twoFockCreate8Z k`. -/
theorem fockCreate8_eq_half_mapMatrix (k : Fin 3) :
    fockCreate8 k = (1 / 2 : ℝ) • (Int.castRingHom ℝ).mapMatrix (twoFockCreate8Z k) := by
  dsimp [fockCreate8, twoFockCreate8Z, majoranaGenR]
  rw [map_add]

/-- `fockAnnihilate8 k` is `(1 / 2 : ℝ)` times the real cast of `twoFockAnnihilate8Z k`. -/
theorem fockAnnihilate8_eq_half_mapMatrix (k : Fin 3) :
    fockAnnihilate8 k = (1 / 2 : ℝ) • (Int.castRingHom ℝ).mapMatrix (twoFockAnnihilate8Z k) := by
  dsimp [fockAnnihilate8, twoFockAnnihilate8Z, majoranaGenR]
  rw [map_sub]

/-- Bilinear scaling of `ChakravalaGA.superBracket .odd .odd` on half-scaled integer matrices. -/
theorem oddSuperBracketR_half_smul (A B : Matrix (Fin 8) (Fin 8) ℤ) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        ((1 / 2 : ℝ) • (Int.castRingHom ℝ).mapMatrix A)
        ((1 / 2 : ℝ) • (Int.castRingHom ℝ).mapMatrix B) =
      ((1 / 2 : ℝ) * (1 / 2 : ℝ)) •
        (Int.castRingHom ℝ).mapMatrix (oddSuperBracketZ A B) := by
  rw [ChakravalaGA.superBracket_fermionic, smul_mul_smul_comm, smul_mul_smul_comm,
    ← smul_add, ← map_mul, ← map_mul, ← map_add]
  rfl

/-- **Isotropic Nilpotency of the 3-Mode Creation Operators**:
For each mode $k \in \mathrm{Fin}\ 3$, $(c_k^\dagger)^2 = 0$ in `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem fockCreate8_sq (k : Fin 3) :
    fockCreate8 k * fockCreate8 k = 0 := by
  rw [fockCreate8_eq_half_mapMatrix, smul_mul_smul_comm, ← map_mul,
    twoFockCreate8Z_sq k, map_zero, smul_zero]

/-- **Isotropic Nilpotency of the 3-Mode Annihilation Operators**:
For each mode $k \in \mathrm{Fin}\ 3$, $c_k^2 = 0$ in `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem fockAnnihilate8_sq (k : Fin 3) :
    fockAnnihilate8 k * fockAnnihilate8 k = 0 := by
  rw [fockAnnihilate8_eq_half_mapMatrix, smul_mul_smul_comm, ← map_mul,
    twoFockAnnihilate8Z_sq k, map_zero, smul_zero]

/-- **Lagrangian Isotropy of the Primal Creation Sheet ($\c_j^\dagger, c_k^\dagger\ = 0$)**:
All creation modes anticommute pairwise under `ChakravalaGA.superBracket .odd .odd`. -/
theorem fockCreate8_oddSuperBracket_zero (j k : Fin 3) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (fockCreate8 j) (fockCreate8 k) = 0 := by
  rw [fockCreate8_eq_half_mapMatrix, fockCreate8_eq_half_mapMatrix,
    oddSuperBracketR_half_smul, twoFockCreate8Z_anticomm j k, map_zero, smul_zero]

/-- **Lagrangian Isotropy of the Covector Annihilation Sheet ($\c_j, c_k\ = 0$)**:
All annihilation modes anticommute pairwise under `ChakravalaGA.superBracket .odd .odd`. -/
theorem fockAnnihilate8_oddSuperBracket_zero (j k : Fin 3) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (fockAnnihilate8 j) (fockAnnihilate8 k) = 0 := by
  rw [fockAnnihilate8_eq_half_mapMatrix, fockAnnihilate8_eq_half_mapMatrix,
    oddSuperBracketR_half_smul, twoFockAnnihilate8Z_anticomm j k, map_zero, smul_zero]

/-- **Full 3-Mode Para-Kähler CAR Odd-Odd Superbracket Kronecker Delta Law**:
For all $j, k \in \mathrm{Fin}\ 3$,
`ChakravalaGA.superBracket .odd .odd (fockCreate8 j) (fockAnnihilate8 k) = (if j = k then 1 else 0) • 1`. -/
theorem fockCreate8_fockAnnihilate8_oddSuperBracket (j k : Fin 3) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (fockCreate8 j) (fockAnnihilate8 k) =
      (if j = k then (1 : ℝ) else 0) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [fockCreate8_eq_half_mapMatrix, fockAnnihilate8_eq_half_mapMatrix,
    oddSuperBracketR_half_smul, twoFockCreate8Z_twoFockAnnihilate8Z_superBracket j k,
    mapMatrix_zsmul, map_one, smul_smul]
  congr 1
  by_cases hjk : j = k
  · norm_num [hjk]
  · norm_num [hjk]

/-- Same-mode CAR normalization: $\c_k^\dagger, c_k\ = I_8$ for every $k \in \mathrm{Fin}\ 3$. -/
theorem fockCreate8_fockAnnihilate8_same_mode (k : Fin 3) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (fockCreate8 k) (fockAnnihilate8 k) =
      (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [fockCreate8_fockAnnihilate8_oddSuperBracket k k]
  simp

/-- Cross-mode CAR anticommutation: $\c_j^\dagger, c_k\ = 0$ for $j \ne k$ in $\mathrm{Fin}\ 3$. -/
theorem fockCreate8_fockAnnihilate8_diff_mode (j k : Fin 3) (hjk : j ≠ k) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd (fockCreate8 j) (fockAnnihilate8 k) = 0 := by
  rw [fockCreate8_fockAnnihilate8_oddSuperBracket j k]
  simp [hjk]

end InfoGeometry.Canonical.MajoranaEightByEightJW
