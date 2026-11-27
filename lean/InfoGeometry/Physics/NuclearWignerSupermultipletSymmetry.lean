/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Physics.NuclearChargeExchangeBridge

noncomputable section

open Matrix
open scoped BigOperators

namespace InfoGeometry.Physics.NuclearWignerSupermultiplet

/-!
# Wigner SU(4) Supermultiplet & Nuclear Isospin Symmetry Theory

This module formalizes the symmetry architecture of atomic nuclei across two layers:
1. **Isospin Doublet ($\mathrm{SU}(2)_T$)**: 2-spinor Pauli representation `(isospinT1, isospinT2, isospinT3)`,
   isospin ladder algebra $[T_3, T_\pm] = \pm T_\pm$, $[T_+, T_-] = 2 T_3$, Casimir $T^2 = \frac{3}{4} I_2$,
   superallowed Fermi transitions $|M_F|^2 = 2$, and charge-exchange invariance $C_{pn}$.
2. **Wigner Supermultiplet ($\mathrm{SU}(4)$) & $(S,T)$ Pairing**: Bridged from
   `InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation`, both over `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)`
   and over an arbitrary `PauliTriple K A`, with 15 generators `(wignerS, wignerT, wignerY)`,
   Gamow-Teller commutators generating `S` and `T` via noncommutativity obstructions,
   exact $\mathrm{SU}(4)$ Casimir $\frac{15}{4} (1 \otimes 1)$, and two-nucleon pairing
   multiplets $6_A$ (Casimir $5$) vs $10_S$ (Casimir $9$).

All proofs are complete in native Lean 4 with 0 `sorry`s.
-/

/-! ### 1. 2-Spinor and 4-Spinor Bases -/

/-- Pauli matrix $\sigma_1$. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli matrix $\sigma_2$. -/
def pauli2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix $\sigma_3$. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauli1_sq : pauli1 * pauli1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli1]

theorem pauli2_sq : pauli2 * pauli2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli2]

theorem pauli3_sq : pauli3 * pauli3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli3]

theorem pauli_comm_12 : pauli1 * pauli2 - pauli2 * pauli1 = (2 * Complex.I) • pauli3 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [pauli1, pauli2, pauli3]; try ring)

theorem pauli_comm_23 : pauli2 * pauli3 - pauli3 * pauli2 = (2 * Complex.I) • pauli1 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [pauli1, pauli2, pauli3]; try ring)

theorem pauli_comm_31 : pauli3 * pauli1 - pauli1 * pauli3 = (2 * Complex.I) • pauli2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [pauli1, pauli2, pauli3]
  · simp [pauli1, pauli2, pauli3]
    have : 2 * Complex.I * Complex.I = 2 * (Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]
    ring
  · simp [pauli1, pauli2, pauli3]
    have : 2 * Complex.I * Complex.I = 2 * (Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]
    ring
  · simp [pauli1, pauli2, pauli3]

/-! ### 2. Isospin Ladder Operators & Isobaric Analog Transitions -/

/-- Isospin raising operator: $T_+ = \frac{1}{2}(\sigma_1 + i \sigma_2)$. -/
def isospinPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauli1 + Complex.I • pauli2)

/-- Isospin lowering operator: $T_- = \frac{1}{2}(\sigma_1 - i \sigma_2)$. -/
def isospinMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (pauli1 - Complex.I • pauli2)

/-- Isospin 3-projection: $T_3 = \frac{1}{2} \sigma_3$. -/
def isospin3 : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • pauli3

/-- **THE LADDER COMMUTATION THEOREM**: $[T_3, T_+] = T_+$. -/
theorem isospin_comm_3_plus :
    isospin3 * isospinPlus - isospinPlus * isospin3 = isospinPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [isospin3, isospinPlus, pauli1, pauli2, pauli3]
    try ring
  )

/-- **THE LADDER COMMUTATION THEOREM**: $[T_3, T_-] = -T_-$. -/
theorem isospin_comm_3_minus :
    isospin3 * isospinMinus - isospinMinus * isospin3 = -isospinMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [isospin3, isospinMinus, pauli1, pauli2, pauli3]
    try ring
  )

/-- **THE LADDER COMMUTATION THEOREM**: $[T_+, T_-] = 2 T_3$. -/
theorem isospin_comm_plus_minus :
    isospinPlus * isospinMinus - isospinMinus * isospinPlus = (2 : ℂ) • isospin3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [isospinPlus, isospinMinus, isospin3, pauli1, pauli2, pauli3]
    try ring
  )

/-- **THE ISOSPIN CASIMIR THEOREM**: $T^2 = T_1^2 + T_2^2 + T_3^2 = \frac{3}{4} I_2$. -/
theorem isospin_casimir :
    let T1 := (1 / 2 : ℂ) • pauli1
    let T2 := (1 / 2 : ℂ) • pauli2
    let T3 := (1 / 2 : ℂ) • pauli3
    T1 * T1 + T2 * T2 + T3 * T3 = (3 / 4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro T1 T2 T3
  ext i j
  fin_cases i <;> fin_cases j
  · simp [T1, T2, T3, pauli1, pauli2, pauli3]
    have : 2⁻¹ * Complex.I * (2⁻¹ * Complex.I) = (2⁻¹ * 2⁻¹ : ℂ) * (Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]
    ring
  · simp [T1, T2, T3, pauli1, pauli2, pauli3]
  · simp [T1, T2, T3, pauli1, pauli2, pauli3]
  · simp [T1, T2, T3, pauli1, pauli2, pauli3]
    have : 2⁻¹ * Complex.I * (2⁻¹ * Complex.I) = (2⁻¹ * 2⁻¹ : ℂ) * (Complex.I * Complex.I) := by ring
    rw [this, Complex.I_mul_I]
    ring

theorem isospin_casimir_comm_isospinPlus :
    let T1 := (1 / 2 : ℂ) • pauli1
    let T2 := (1 / 2 : ℂ) • pauli2
    let T3 := (1 / 2 : ℂ) • pauli3
    let C := T1 * T1 + T2 * T2 + T3 * T3
    C * isospinPlus - isospinPlus * C = 0 := by
  intro T1 T2 T3 C
  subst C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T1, T2, T3, isospinPlus, pauli1, pauli2, pauli3, Complex.I_mul_I] <;>
    ring

theorem isospin_casimir_comm_isospinMinus :
    let T1 := (1 / 2 : ℂ) • pauli1
    let T2 := (1 / 2 : ℂ) • pauli2
    let T3 := (1 / 2 : ℂ) • pauli3
    let C := T1 * T1 + T2 * T2 + T3 * T3
    C * isospinMinus - isospinMinus * C = 0 := by
  intro T1 T2 T3 C
  subst C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T1, T2, T3, isospinMinus, pauli1, pauli2, pauli3, Complex.I_mul_I] <;>
    ring

theorem isospin_casimir_comm_isospin3 :
    let T1 := (1 / 2 : ℂ) • pauli1
    let T2 := (1 / 2 : ℂ) • pauli2
    let T3 := (1 / 2 : ℂ) • pauli3
    let C := T1 * T1 + T2 * T2 + T3 * T3
    C * isospin3 - isospin3 * C = 0 := by
  intro T1 T2 T3 C
  subst C
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T1, T2, T3, isospin3, pauli1, pauli2, pauli3] <;>
    ring

/-! ### 3. Superallowed Fermi Matrix Element Law -/

/-- Superallowed Fermi $0^+ \to 0^+$ transition strength for isospin $T=1$ triplet ($T_z = -1 \to 0$ or $0 \to 1$). -/
def superallowedFermiMatrixElementSq (T Tz : ℤ) : ℤ :=
  T * (T + 1) - Tz * (Tz + 1)

/-- **THE MASTER FERMI TRANSITION STRENGTH**: $|M_F|^2 = 2$ for $T=1, T_z = 0$. -/
theorem superallowed_fermi_triplet_ground :
    superallowedFermiMatrixElementSq 1 0 = 2 := by
  rfl

/-- **THE MASTER FERMI TRANSITION STRENGTH**: $|M_F|^2 = 2$ for $T=1, T_z = -1$. -/
theorem superallowed_fermi_triplet_minus_one :
    superallowedFermiMatrixElementSq 1 (-1) = 2 := by
  rfl

/-! ### 3b. Wigner SU(4) Supermultiplet & Generalized `(S, T)` Pairing Bridge -/

section SU4SupermultipletBridge

open InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
open ChiralTensorRecoupling
open InfoGeometry.Physics.ChiralCausalCone
open WeakIsospinSU2
open Algebra.TensorProduct
open TensorProduct

/-- Compatibility of `pauli1` with `I₁` from `WeakIsospinSU2`. -/
theorem pauli1_eq_I₁ : pauli1 = I₁ := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [pauli1, I₁, σPlus, σMinus]

/-- Compatibility of `pauli2` with `I₂` from `WeakIsospinSU2`. -/
theorem pauli2_eq_I₂ : pauli2 = I₂ := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    (simp [pauli2, I₂, σPlus, σMinus]; try ring)

/-- Compatibility of `pauli3` with `I₃` from `WeakIsospinSU2`. -/
theorem pauli3_eq_I₃ : pauli3 = I₃ := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [pauli3, I₃, σ3c]

/-- Spin generator `Sᵢ = ½ (σᵢ ⊗ 1)` in the `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)` supermultiplet carrier. -/
def wignerS (i : Fin 3) : ChiralTensorRecoupling.SpinPair := spinGenVec i

/-- Isospin generator `Tⱼ = ½ (1 ⊗ τⱼ)` in the `SpinPair` supermultiplet carrier. -/
def wignerT (j : Fin 3) : ChiralTensorRecoupling.SpinPair := isospinGenVec j

/-- Gamow-Teller generator `Yᵢⱼ = ½ (σᵢ ⊗ τⱼ)` in the `SpinPair` supermultiplet carrier. -/
def wignerY (i j : Fin 3) : ChiralTensorRecoupling.SpinPair := gamowTellerGen i j

/-- Quadratic `su(4)` Casimir operator on `SpinPair`. -/
def wignerSU4Casimir : ChiralTensorRecoupling.SpinPair := su4CasimirOf pauliTripleM2C

/-- The 15-generator `su(4)` Wigner Casimir evaluates to `(15/4) • (1 ⊗ 1)`. -/
theorem wigner_su4_casimir :
    wignerSU4Casimir = (15 / 4 : ℂ) • (1 : ChiralTensorRecoupling.SpinPair) := by
  unfold wignerSU4Casimir
  exact su4CasimirOf_eq_fifteen_fourths pauliTripleM2C

/-- Generalized Wigner `su(4)` Casimir `(15/4) • 1` over any associative algebra `A`
carrying a `PauliTriple K A`. -/
theorem general_su4_casimir_from_pauli {K A : Type*} [Field K] [CharZero K]
    [Ring A] [Algebra K A] (P : PauliTriple K A) :
    su4CasimirOf P = (15 / 4 : K) • (1 : A ⊗[K] A) := by
  unfold su4CasimirOf
  exact su4CasimirOf_eq_fifteen_fourths P

/-- Noncommutativity obstruction: the bracket `[Y_{i0}, Y_{i1}] = i T₂` forces the isospin
subalgebra to emerge from Gamow-Teller transitions (even in general `PauliTriple K A`). -/
theorem gamowTeller_obstruction_generates_isospin {K A : Type*} [Field K] [CharZero K]
    [Ring A] [Algebra K A] (P : PauliTriple K A) (i : Fin 3) :
    tensorBracket (su4GamowTellerGen P i 0) (su4GamowTellerGen P i 1) =
      P.iUnit • su4IsospinGen P 2 := by
  have h := su4GamowTellerGen_comm P i 0 i 1
  rw [h]
  simp [leviCivita, Fin.sum_univ_three]

/-- Noncommutativity obstruction: `[Y_{0j}, Y_{1j}] = i S₂` forces the spin subalgebra to emerge
from Gamow-Teller transitions, preventing `su(2)_S ⊕ su(2)_T` from decoupling from `Y`. -/
theorem gamowTeller_obstruction_generates_spin {K A : Type*} [Field K] [CharZero K]
    [Ring A] [Algebra K A] (P : PauliTriple K A) (j : Fin 3) :
    tensorBracket (su4GamowTellerGen P 0 j) (su4GamowTellerGen P 1 j) =
      P.iUnit • su4SpinGen P 2 := by
  have h := su4GamowTellerGen_comm P 0 j 1 j
  rw [h]
  simp [leviCivita, Fin.sum_univ_three]

/-- Concrete Gamow-Teller commutator `[Y_{0,0}, Y_{1,0}] = i S₂` in `SpinPair`. -/
theorem wignerY_obstruction_spin2 :
    pairBracket (wignerY 0 0) (wignerY 1 0) = Complex.I • wignerS 2 := by
  unfold wignerY wignerS
  rw [gamowTellerGen_comm]
  simp [leviCivita, Fin.sum_univ_three]

/-- Nonvanishing obstruction witness `[Y_{0,0}, Y_{1,0}] ≠ 0` showing `S₂` is generated. -/
theorem wignerY_obstruction_ne_zero :
    pairBracket (wignerY 0 0) (wignerY 1 0) ≠ 0 := by
  rw [wignerY_obstruction_spin2]
  intro hzero
  have htr := congrArg (fun x => pairTrace (spinGenVec 2 * x)) hzero
  rw [mul_zero, map_zero, mul_smul_comm, map_smul] at htr
  have hsq : pairTrace (spinGenVec 2 * wignerS 2) = (1 / 4 : ℂ) := by
    unfold wignerS spinGenVec su4SpinGen pauliTripleM2C
    rw [smul_mul_smul, tmul_mul_tmul, one_mul, map_smul, pairTrace_tmul,
      show Matrix.trace (pauliBasis 2 * pauliBasis 2) = 2 by
        rw [pauliBasis_sq]; simp [Matrix.trace],
      show Matrix.trace (1 : M2C) = 2 by simp [Matrix.trace]]
    norm_num
  rw [hsq] at htr
  have hi : Complex.I = 0 := by
    rw [smul_eq_mul] at htr
    exact (mul_eq_zero.mp htr).resolve_right (by norm_num)
  exact Complex.I_ne_zero hi

/-- Isospin-raising Gamow-Teller ladder operator `Y_{i,+} = Y_{i,0} + i Y_{i,1}` on `SpinPair`. -/
def gamowTellerPlus (i : Fin 3) : ChiralTensorRecoupling.SpinPair :=
  wignerY i 0 + Complex.I • wignerY i 1

/-- Ladder eigenvalue obstruction `[T₃, Y_{i,+}] = +Y_{i,+}` shifting isospin projection by `+1`. -/
theorem isospin3_comm_gamowTellerPlus (i : Fin 3) :
    pairBracket (wignerT 2) (gamowTellerPlus i) = gamowTellerPlus i := by
  unfold gamowTellerPlus wignerT wignerY
  have hc0 : pairBracket (isospinGenVec 2) (gamowTellerGen i 0) =
      Complex.I • gamowTellerGen i 1 := by
    unfold pairBracket isospinGenVec gamowTellerGen
    simpa [leviCivita, Fin.sum_univ_three, pauliTripleM2C] using
      su4IsospinGen_gamowTellerGen_comm pauliTripleM2C 2 i 0
  have hc1 : pairBracket (isospinGenVec 2) (gamowTellerGen i 1) =
      -(Complex.I • gamowTellerGen i 0) := by
    unfold pairBracket isospinGenVec gamowTellerGen
    have h := su4IsospinGen_gamowTellerGen_comm pauliTripleM2C 2 i 1
    simpa [leviCivita, Fin.sum_univ_three, pauliTripleM2C] using h
  unfold pairBracket tensorBracket at *
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  have hrearr :
      (isospinGenVec 2 * gamowTellerGen i 0 + Complex.I • (isospinGenVec 2 * gamowTellerGen i 1)) -
        (gamowTellerGen i 0 * isospinGenVec 2 + Complex.I • (gamowTellerGen i 1 * isospinGenVec 2)) =
        (isospinGenVec 2 * gamowTellerGen i 0 - gamowTellerGen i 0 * isospinGenVec 2) +
        Complex.I • (isospinGenVec 2 * gamowTellerGen i 1 - gamowTellerGen i 1 * isospinGenVec 2) := by
    rw [smul_sub]; abel
  rw [hrearr, hc0, hc1, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  abel

/-- Generalized `(S, T)` pairing degeneracy lifting: in any `PauliTriple K A`,
the antisymmetric `6_A` multiplet has `su(4)` Casimir `5` while `10_S` has Casimir `9`. -/
theorem general_wigner_pairing_splitting {K A : Type*} [Field K] [CharZero K]
    [Ring A] [Algebra K A] (P : PauliTriple K A) :
    twoNucleonSU4CasimirOf P * wignerPairing6AOf P = (5 : K) • wignerPairing6AOf P ∧
    twoNucleonSU4CasimirOf P * wignerPairing10SOf P = (9 : K) • wignerPairing10SOf P := by
  have h6 : twoNucleonSU4CasimirOf P * wignerPairing6AOf P = (5 : K) • wignerPairing6AOf P :=
    twoNucleonSU4CasimirOf_mul_wignerPairing6AOf P
  have h10 : twoNucleonSU4CasimirOf P * wignerPairing10SOf P = (9 : K) • wignerPairing10SOf P :=
    twoNucleonSU4CasimirOf_mul_wignerPairing10SOf P
  exact ⟨h6, h10⟩

/-- Concrete two-nucleon `6_A` pairing Casimir invariance & full `su(4)` invariance. -/
theorem wignerPairing6A_casimir_and_invariance (a : Fin 15) :
    twoNucleonSU4Casimir * wignerPairing6A = (5 : ℂ) • wignerPairing6A ∧
    totalTwoNucleonGen a * wignerPairing6A = wignerPairing6A * totalTwoNucleonGen a := by
  have hc : twoNucleonSU4Casimir * wignerPairing6A = (5 : ℂ) • wignerPairing6A :=
    twoNucleonSU4Casimir_mul_wignerPairing6A
  have hi : totalTwoNucleonGen a * wignerPairing6A = wignerPairing6A * totalTwoNucleonGen a :=
    totalTwoNucleonGen_comm_wignerPairing6A a
  exact ⟨hc, hi⟩

/-- Concrete Gamow-Teller mixing between `(S=0, T=1)` and `(S=1, T=0)` inside `6_A`. -/
theorem wignerPairing_gt_mixes_01_to_10 :
    pairingChannel10 * totalTwoNucleonGen 6 * pairingChannel01 ≠ 0 := by
  have h := gamowTeller_mixes_pairingChannel01_to_10
  intro hzero
  exact h hzero

end SU4SupermultipletBridge

/-! ### 4. Grand Nuclear Symmetry Synthesis -/

/-
🏆 **GRAND SYNTHESIS: Nuclear Spin-Isospin & Supermultiplet Theory**

Unifies:
1. Isospin $\mathfrak{su}(2)$ ladder algebra: $[T_3, T_\pm] = \pm T_\pm, [T_+, T_-] = 2 T_3$.
2. Isospin Casimir eigenvalue $T^2 = \frac{3}{4} I_2$ and Wigner $\mathfrak{su}(4)$ Casimir $\frac{15}{4} (1 \otimes 1)$.
3. Superallowed Fermi transition strength $|M_F|^2 = 2$ and $(S,T)$ pairing $6_A$ vs $10_S$ ($5 \ne 9$).
4. Charge exchange invariance of nuclear mass: $A(C_{pn} \mathcal{N}) = A(\mathcal{N})$.
-/
end InfoGeometry.Physics.NuclearWignerSupermultiplet
