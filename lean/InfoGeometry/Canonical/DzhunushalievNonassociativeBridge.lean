/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.AkivisIdentity
import InfoGeometry.Algebra.AkivisLeftRegularBridge
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
import Mathlib.Tactic

/-!
# Dzhunushaliev Nonassociative Bridge (arXiv:0805.3221v6)

Repository-native Lean 4 audit and bridge formalization of Vladimir Dzhunushaliev,
*"Hidden structures in quantum mechanics"* (arXiv:0805.3221v6, 2008), connecting directly to
the existing nonassociative Akivis/Zorn/Nambu/Clifford owners in `InfoGeometry`:

1. **Part 1 — Universal Nonassociative Identities, Myung's Theorem, & Alternative Obstructions
   (`Eqs. 35–40`)**:
   Reuses `InfoGeometry.Algebra.akivisBracket`, `akivisJacobiator`,
   `akivisBracket_leibniz_defect_eq_associators`, `akivis_identity`, and
   `NonAssocDerivation.IsLeibniz` over arbitrary `[NonUnitalNonAssocRing A]`:
   - `comm_leibniz_eq_assoc`: universal derivation-associator defect identity (characteristic-free).
   - `myung_leibniz_implies_flexible_and_lieAdmissible` & `myung_of_isLeibniz_comm`: Myung's
     necessity theorem showing every Lie/Leibniz-derivation commutator ring is flexible and
     Lie-admissible.
   - `alternating_of_left_right_alternative` & `alternative_leibniz_and_jacobi`: exact
     quantitative obstructions in any alternative ring (`ℤ`-module formulation, valid in arbitrary
     characteristic): Leibniz defect `= -3 • (x, y, z)` and Jacobiator `= 6 • (x, y, z)`.

2. **Part 2 — Exact Kernel Audit of Table I (`pp. 2–3`, Eqs. 17–26)**:
   Formalizes the printed multiplication table `table1BasisMul` verbatim (`[q₁, q₂] = +2 q₃` vs.
   `[q₄, q₅] = -2 q₃`, `(q₄, q₅, q₆) = 2 q₇`) and proves `dzhunushaliev_table1_audit` by
   kernel reduction (`decide`), exhibiting the hidden **non-alternativity bug**:
   `(q₁, q₂, q₅) = 0`, whereas `(q₁, q₅, q₂) = -2 q₄ ≠ 0`, violating `(a, b, c) + (a, c, b) = 0`.

3. **Part 3 — Repaired Split-Octonion Realization Directly on `ZornVectorMatrix`**:
   Realizes `qSpin i = V i - U i` (`i = 1, 2, 3`), `qSpace i = U i + V i` (`q_{i+3}`), and
   `qCut7 = E₂₂ - E₁₁` (`q₇ = -Γ_cut`) directly on `InfoGeometry.Algebra.ZornVectorMatrix R`:
   - Over arbitrary possibly noncommutative `[Ring R]` (`dzhunushaliev_zorn_basis_laws_ring`),
     establishing `q_i² = -1`, `q_{i+3}² = +1`, `q₇² = +1`, associative quaternion spin
     commutators `[q₁, q₂] = 2 q₃`, hyperbolic spin decomposition `[q₄, q₅] = 2 q₃` with
     `q₄ q₅ = +q₃`, `(q₄, q₅, q₆) = 2 q₇`, and a concrete `Matrix (Fin 2) (Fin 2) ℂ`
     noncommutative coefficient witness.
   - Over `[CommRing R]` (`repaired_zorn_dzhunushaliev_laws`), combining exact alternativity via
     `zorn_left_alternative`/`zorn_right_alternative`, exact composition norm via
     `ZornVectorMatrix.norm_mul`, left-nested `akivisJacobiator q₄ q₅ q₆ = 12 • q₇`, and
     Heisenberg Leibniz defect `= -6 • q₇`.

4. **Part 4 — Associative Matrix Impossibility vs. Real `Cl(3,1) ≅ M₄(ℝ)` Nambu Realization
   (`Eqs. 29–31`)**:
   - `associative_ring_associator_zero`: proves `(x, y, z) = 0` in every associative `[Ring B]`,
     ruling out linear associative matrix representations of `(P^μ, P^ν, P^ρ) ≠ 0`.
   - `diracGamma_nambuBracket3_hodge_realization`: realizes the Hodge-dual ternary relation in real
     `Cl(3,1) ≅ M₄(ℝ)` (`DiracSpinCasimirNambuModulesBridge`) via the alternating Nambu 3-bracket
     `nambuBracket3`, alongside nonvanishing Lorentz commutators `[γ_μ, γ_ν] = 2 γ_μ γ_ν`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & UNIVERSAL RING THEOREMS
* `comm_leibniz_eq_assoc`, `myung_leibniz_implies_flexible_and_lieAdmissible`, `myung_of_isLeibniz_comm`
* `alternating_of_left_right_alternative`, `alternative_leibniz_and_jacobi`
* `dzhunushaliev_table1_audit`
* `dzhunushaliev_zorn_basis_laws_ring`, `dzhunushaliev_zorn_mat2c_associator_ne_zero`
* `repaired_zorn_dzhunushaliev_laws`
* `associative_ring_associator_zero`, `diracGamma_nambuBracket3_hodge_realization`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `myung_leibniz_implies_flexible_and_lieAdmissible` and `alternative_leibniz_and_jacobi`
  derive flexibility / Lie-admissibility / `(−3, 6)`-obstructions from explicit Leibniz or
  alternativity hypotheses on `[NonUnitalNonAssocRing A]`.

#### BUCKET 3: OPEN CLOSURE DEBT
* No physical gauge/field dynamics, infinite-dimensional Fock/C*-GNS split-octonion extensions, or
  non-linearizable nonassociative infinite operator algebras are claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.DzhunushalievNonassociativeBridge

open InfoGeometry.Algebra
open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
open Matrix

/-! ### Part 1: Universal Nonassociative Identities, Myung's Theorem, & Alternative Obstructions -/

section NonAssociativeUniversal

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- **Universal Derivation–Associator Identity (Characteristic-Free)**:
In any nonassociative ring `A`, the failure of `[z, -]` to satisfy the Leibniz derivation law is
`[z, x y] - x [z, y] - [z, x] y = (x, z, y) - (z, x, y) - (x, y, z)`.
Directly bridges `InfoGeometry.Algebra.akivisBracket_leibniz_defect_eq_associators`. -/
theorem comm_leibniz_eq_assoc (x y z : A) :
    akivisBracket z (x * y) - x * akivisBracket z y - akivisBracket z x * y =
      _root_.associator x z y - _root_.associator z x y - _root_.associator x y z :=
  akivisBracket_leibniz_defect_eq_associators x y z

/-- **Myung's Theorem (Necessity Direction, Eqs. 38–40, Characteristic-Free)**:
If the commutator `akivisBracket z` is a derivation for all `z : A`
(`akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y`), then `A` is
necessarily:
1. **Flexible**: `(x, y, z) = -(z, y, x)` (`Eq. 39`);
2. **Lie-admissible**: `akivisJacobiator x y z = 0` (`Eq. 40`). -/
theorem myung_leibniz_implies_flexible_and_lieAdmissible
    (hLeib : ∀ x y z : A,
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y) :
    (∀ x y z : A, _root_.associator x y z = -_root_.associator z y x) ∧
    (∀ x y z : A, akivisJacobiator x y z = 0) := by
  constructor
  · intro x y z
    have h1 : _root_.associator x z y - _root_.associator z x y - _root_.associator x y z = 0 := by
      rw [← comm_leibniz_eq_assoc, hLeib x y z]
      abel
    have h2 : _root_.associator z x y - _root_.associator x z y - _root_.associator z y x = 0 := by
      rw [← comm_leibniz_eq_assoc, hLeib z y x]
      abel
    have hsum : -(_root_.associator x y z + _root_.associator z y x) = 0 := by
      calc -(_root_.associator x y z + _root_.associator z y x)
          = (_root_.associator x z y - _root_.associator z x y - _root_.associator x y z) +
            (_root_.associator z x y - _root_.associator x z y - _root_.associator z y x) := by
              abel
        _ = 0 + 0 := by rw [h1, h2]
        _ = 0 := add_zero 0
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.mp hsum)
  · intro x y z
    have hc1 :
        akivisBracket z (akivisBracket x y) =
          akivisBracket x (akivisBracket z y) + akivisBracket (akivisBracket z x) y := by
      unfold akivisBracket
      rw [mul_sub, sub_mul]
      have hxy := hLeib x y z
      have hyx := hLeib y x z
      unfold akivisBracket at hxy hyx
      calc z * (x * y) - z * (y * x) - ((x * y) * z - (y * x) * z)
          = (z * (x * y) - (x * y) * z) - (z * (y * x) - (y * x) * z) := by abel
        _ = (x * (z * y - y * z) + (z * x - x * z) * y) -
            (y * (z * x - x * z) + (z * y - y * z) * x) := by rw [hxy, hyx]
        _ = (x * (z * y - y * z) - (z * y - y * z) * x) +
            ((z * x - x * z) * y - y * (z * x - x * z)) := by abel
    have hmn : ∀ u v : A, akivisBracket u (-v) = -akivisBracket u v := by
      intro u v
      unfold akivisBracket
      rw [mul_neg, neg_mul]
      abel
    unfold akivisJacobiator
    calc akivisBracket (akivisBracket x y) z + akivisBracket (akivisBracket y z) x +
          akivisBracket (akivisBracket z x) y
        = -akivisBracket z (akivisBracket x y) + (-akivisBracket x (akivisBracket y z)) +
            akivisBracket (akivisBracket z x) y := by
              rw [akivisBracket_swap (akivisBracket x y) z,
                akivisBracket_swap (akivisBracket y z) x]
      _ = -(akivisBracket x (akivisBracket z y) + akivisBracket (akivisBracket z x) y) +
            (-akivisBracket x (akivisBracket y z)) + akivisBracket (akivisBracket z x) y := by
              rw [hc1]
      _ = -(akivisBracket x (-akivisBracket y z) + akivisBracket (akivisBracket z x) y) +
            (-akivisBracket x (akivisBracket y z)) + akivisBracket (akivisBracket z x) y := by
              rw [akivisBracket_swap z y]
      _ = -(-(akivisBracket x (akivisBracket y z)) + akivisBracket (akivisBracket z x) y) +
            (-akivisBracket x (akivisBracket y z)) + akivisBracket (akivisBracket z x) y := by
              rw [hmn]
      _ = 0 := by abel

section ModuleLeibniz

variable {R : Type*} [Ring R] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left commutator endomorphism `x ↦ akivisBracket z x` in `Module.End R A`. -/
def adLeft (z : A) : Module.End R A where
  toFun x := akivisBracket z x
  map_add' x y := by simp only [akivisBracket, mul_add, add_mul]; abel
  map_smul' r x := by
    simp only [akivisBracket, RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

@[simp]
theorem adLeft_apply (z x : A) : adLeft (R := R) z x = akivisBracket z x := rfl

/-- Bridge from `InfoGeometry.Algebra.NonAssocDerivation.IsLeibniz R A (adLeft z)` to Myung's
necessity theorem. -/
theorem myung_of_isLeibniz_comm
    (hLeib : ∀ z : A, NonAssocDerivation.IsLeibniz R A (adLeft (R := R) z)) :
    (∀ x y z : A, _root_.associator x y z = -_root_.associator z y x) ∧
    (∀ x y z : A, akivisJacobiator x y z = 0) :=
  myung_leibniz_implies_flexible_and_lieAdmissible fun x y z => by
    simpa [adLeft_apply, add_comm] using hLeib z x y

end ModuleLeibniz

/-- Polarization helper: in any `[NonUnitalNonAssocRing A]` (without `Module ℝ A` or characteristic
hypotheses), left and right alternativity imply full skew-symmetry of `_root_.associator` in
adjacent slots. -/
theorem alternating_of_left_right_alternative
    (hLeft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hRight : ∀ x y : A, (y * x) * x = y * (x * x)) :
    (∀ a b c : A, _root_.associator a b c = -_root_.associator b a c) ∧
    (∀ a b c : A, _root_.associator a b c = -_root_.associator a c b) := by
  constructor
  · intro a b c
    have haa : _root_.associator a a c = 0 :=
      sub_eq_zero.mpr (hLeft a c)
    have hbb : _root_.associator b b c = 0 :=
      sub_eq_zero.mpr (hLeft b c)
    have hab : _root_.associator (a + b) (a + b) c = 0 :=
      sub_eq_zero.mpr (hLeft (a + b) c)
    have hexp :
        _root_.associator (a + b) (a + b) c =
          _root_.associator a a c + _root_.associator a b c +
            _root_.associator b a c + _root_.associator b b c := by
      simp only [_root_.associator_apply, add_mul, mul_add]
      abel
    rw [hab, haa, hbb, zero_add, add_zero] at hexp
    exact eq_neg_of_add_eq_zero_left hexp.symm
  · intro a b c
    have hbb : _root_.associator a b b = 0 :=
      sub_eq_zero.mpr (hRight b a)
    have hcc : _root_.associator a c c = 0 :=
      sub_eq_zero.mpr (hRight c a)
    have hbc : _root_.associator a (b + c) (b + c) = 0 :=
      sub_eq_zero.mpr (hRight (b + c) a)
    have hexp :
        _root_.associator a (b + c) (b + c) =
          _root_.associator a b b + _root_.associator a b c +
            _root_.associator a c b + _root_.associator a c c := by
      simp only [_root_.associator_apply, add_mul, mul_add]
      abel
    rw [hbc, hbb, hcc, zero_add, add_zero] at hexp
    exact eq_neg_of_add_eq_zero_left hexp.symm

/-- **Alternative Algebra Leibniz & Jacobi Obstruction Theorem (`ℤ`-Module Form)**:
In any alternative ring (using `_root_.associator`, `akivisBracket`, and `akivisJacobiator` from
`InfoGeometry.Algebra.AkivisIdentity`):
1. The Heisenberg Leibniz defect is `[z, xy] - x[z, y] - [z, x]y = -3 • (x, y, z)`.
2. The Jacobiator is `akivisJacobiator x y z = 6 • (x, y, z)`. -/
theorem alternative_leibniz_and_jacobi
    (hAlt12 : ∀ a b c : A, _root_.associator a b c = -_root_.associator b a c)
    (hAlt23 : ∀ a b c : A, _root_.associator a b c = -_root_.associator a c b)
    (x y z : A) :
    (akivisBracket z (x * y) - x * akivisBracket z y - akivisBracket z x * y =
      -(3 : ℤ) • _root_.associator x y z) ∧
    (akivisJacobiator x y z = (6 : ℤ) • _root_.associator x y z) := by
  have h1 : _root_.associator x z y = -_root_.associator x y z := hAlt23 x z y
  have h2 : _root_.associator z x y = _root_.associator x y z := by
    rw [hAlt12 z x y, hAlt23 x z y, neg_neg]
  have h3 : _root_.associator y z x = _root_.associator x y z := by
    rw [hAlt23 y z x, hAlt12 y x z, neg_neg]
  have h4 : _root_.associator y x z = -_root_.associator x y z := hAlt12 y x z
  have h5 : _root_.associator z y x = -_root_.associator x y z := by
    rw [hAlt12 z y x, hAlt23 y z x, neg_neg, hAlt12 y x z]
  constructor
  · rw [comm_leibniz_eq_assoc, h1, h2]
    have hsm :
        -(3 : ℤ) • _root_.associator x y z =
          -(_root_.associator x y z + _root_.associator x y z + _root_.associator x y z) := by
      have h3sm : (3 : ℤ) • _root_.associator x y z =
          _root_.associator x y z + _root_.associator x y z + _root_.associator x y z := by
        rw [show (3 : ℤ) = 1 + 1 + 1 by norm_num, add_zsmul, add_zsmul, one_zsmul]
      rw [neg_smul, h3sm]
    rw [hsm]
    abel
  · rw [akivis_identity x y z, h1, h2, h3, h4, h5]
    have h6sm :
        (6 : ℤ) • _root_.associator x y z =
          (_root_.associator x y z + _root_.associator x y z + _root_.associator x y z) -
          (-_root_.associator x y z + -_root_.associator x y z + -_root_.associator x y z) := by
      rw [show (6 : ℤ) = 1 + 1 + 1 + 1 + 1 + 1 by norm_num]
      simp only [add_zsmul, one_zsmul]
      abel
    rw [h6sm]
    abel

end NonAssociativeUniversal

/-! ### Part 2: Kernel Audit of Dzhunushaliev Table I (pp. 2–3, Eqs. 17–26) -/

/-- Raw multiplication of basis vectors `Fin 8` (`0 ↦ 1`, `1..7 ↦ q₁..q₇`) from Table I of
arXiv:0805.3221v6 (page 3). -/
def table1BasisMul (i j : Fin 8) : Int × Fin 8 :=
  match i, j with
  | 0, k => (1, k)
  | k, 0 => (1, k)
  | 1, 1 => (-1, 0) | 1, 2 => (1, 3)  | 1, 3 => (-1, 2) | 1, 4 => (-1, 7) | 1, 5 => (1, 6)  | 1, 6 => (-1, 5) | 1, 7 => (1, 4)
  | 2, 1 => (-1, 3) | 2, 2 => (-1, 0) | 2, 3 => (1, 1)  | 2, 4 => (-1, 6) | 2, 5 => (-1, 7) | 2, 6 => (1, 4)  | 2, 7 => (1, 5)
  | 3, 1 => (1, 2)  | 3, 2 => (-1, 1) | 3, 3 => (-1, 0) | 3, 4 => (1, 5)  | 3, 5 => (-1, 4) | 3, 6 => (-1, 7) | 3, 7 => (1, 6)
  | 4, 1 => (1, 7)  | 4, 2 => (1, 6)  | 4, 3 => (-1, 5) | 4, 4 => (1, 0)  | 4, 5 => (-1, 3) | 4, 6 => (1, 2)  | 4, 7 => (1, 1)
  | 5, 1 => (-1, 6) | 5, 2 => (1, 7)  | 5, 3 => (1, 4)  | 5, 4 => (1, 3)  | 5, 5 => (1, 0)  | 5, 6 => (-1, 1) | 5, 7 => (1, 2)
  | 6, 1 => (1, 5)  | 6, 2 => (-1, 4) | 6, 3 => (1, 7)  | 6, 4 => (-1, 2) | 6, 5 => (1, 1)  | 6, 6 => (1, 0)  | 6, 7 => (1, 3)
  | 7, 1 => (-1, 4) | 7, 2 => (-1, 5) | 7, 3 => (-1, 6) | 7, 4 => (-1, 1) | 7, 5 => (-1, 2) | 7, 6 => (-1, 3) | 7, 7 => (1, 0)
  | _, _ => (1, 0)

def table1SignedMul (x y : Int × Fin 8) : Int × Fin 8 :=
  let p := table1BasisMul x.2 y.2
  (x.1 * y.1 * p.1, p.2)

/-- **Table I Audit Theorem (Kernel `decide`, no `native_decide`)**:
1. Reproduces Eq. (18) (`q₁ q₂ = +q₃`, `q₂ q₁ = -q₃`) and Eq. (17) (`q₄ q₅ = -q₃`, `q₅ q₄ = +q₃`).
2. Reproduces Eq. (19) (`(q₄ q₅) q₆ = +q₇` and `q₄ (q₅ q₆) = -q₇`, hence `(q₄, q₅, q₆) = 2 q₇`).
3. **Non-Alternativity Bug**: Because Eq. (17) and Eq. (18) assign opposite commutator orientations,
   Table I fails alternativity on `(q₁, q₂, q₅)`: `(q₁ q₂) q₅ = -q₄ = q₁ (q₂ q₅)` (associator `0`),
   whereas `(q₁ q₅) q₂ = -q₄` and `q₁ (q₅ q₂) = +q₄`, so `(q₁, q₂, q₅) + (q₁, q₅, q₂) = -2 q₄ ≠ 0`. -/
theorem dzhunushaliev_table1_audit :
    (table1BasisMul 1 2 = (1, 3) ∧ table1BasisMul 2 1 = (-1, 3)) ∧
    (table1BasisMul 4 5 = (-1, 3) ∧ table1BasisMul 5 4 = (1, 3)) ∧
    (table1SignedMul (table1BasisMul 4 5) (1, 6) = (1, 7) ∧
     table1SignedMul (1, 4) (table1BasisMul 5 6) = (-1, 7)) ∧
    (table1SignedMul (table1BasisMul 1 2) (1, 5) = (-1, 4) ∧
     table1SignedMul (1, 1) (table1BasisMul 2 5) = (-1, 4)) ∧
    (table1SignedMul (table1BasisMul 1 5) (1, 2) = (-1, 4) ∧
     table1SignedMul (1, 1) (table1BasisMul 5 2) = (1, 4)) := by
  decide

/-! ### Part 3: Repaired Split-Octonion Realization Directly on `ZornVectorMatrix` -/

section ZornSplitOctonionRealization

/-- Observable quaternion spin generators `q_i = v_i⁻ - u_i⁺` (`i = 0, 1, 2`) on
`InfoGeometry.Algebra.ZornVectorMatrix R`. -/
def qSpin (R : Type*) [Ring R] (i : Fin 3) : ZornVectorMatrix R :=
  ZornVectorMatrix.V i - ZornVectorMatrix.U i

/-- Unobservable hyperbolic generators `q_{i+3} = u_i⁺ + v_i⁻` (`i = 0, 1, 2`) on
`InfoGeometry.Algebra.ZornVectorMatrix R`. -/
def qSpace (R : Type*) [Ring R] (i : Fin 3) : ZornVectorMatrix R :=
  ZornVectorMatrix.U i + ZornVectorMatrix.V i

/-- Chiral-cut generator `q₇ = e_- - e_+` (`= -Γ_cut`) on `ZornVectorMatrix R`. -/
def qCut7 (R : Type*) [Ring R] : ZornVectorMatrix R :=
  ZornVectorMatrix.E22 - ZornVectorMatrix.E11

section ArbitraryRing

variable {R : Type*} [Ring R]

private lemma zvm_add_a (X Y : ZornVectorMatrix R) : (X + Y).a = X.a + Y.a := rfl
private lemma zvm_add_v (X Y : ZornVectorMatrix R) (i : Fin 3) : (X + Y).v i = X.v i + Y.v i := rfl
private lemma zvm_add_w (X Y : ZornVectorMatrix R) (i : Fin 3) : (X + Y).w i = X.w i + Y.w i := rfl
private lemma zvm_add_b (X Y : ZornVectorMatrix R) : (X + Y).b = X.b + Y.b := rfl
private lemma zvm_sub_a (X Y : ZornVectorMatrix R) : (X - Y).a = X.a - Y.a := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg X.a Y.a).symm
private lemma zvm_sub_v (X Y : ZornVectorMatrix R) (i : Fin 3) : (X - Y).v i = X.v i - Y.v i := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg (X.v i) (Y.v i)).symm
private lemma zvm_sub_w (X Y : ZornVectorMatrix R) (i : Fin 3) : (X - Y).w i = X.w i - Y.w i := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg (X.w i) (Y.w i)).symm
private lemma zvm_sub_b (X Y : ZornVectorMatrix R) : (X - Y).b = X.b - Y.b := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg X.b Y.b).symm

private lemma zvm_nsmul_a (n : ℕ) (X : ZornVectorMatrix R) : (n • X).a = n • X.a := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, zvm_add_a, ih, succ_nsmul]
private lemma zvm_nsmul_v (n : ℕ) (X : ZornVectorMatrix R) (i : Fin 3) : (n • X).v i = n • X.v i := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, zvm_add_v, ih, succ_nsmul]
private lemma zvm_nsmul_w (n : ℕ) (X : ZornVectorMatrix R) (i : Fin 3) : (n • X).w i = n • X.w i := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, zvm_add_w, ih, succ_nsmul]
private lemma zvm_nsmul_b (n : ℕ) (X : ZornVectorMatrix R) : (n • X).b = n • X.b := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, zvm_add_b, ih, succ_nsmul]

private lemma zvm_zsmul_a (k : ℤ) (X : ZornVectorMatrix R) : (k • X).a = k • X.a := by
  cases k with
  | ofNat n => simpa using zvm_nsmul_a n X
  | negSucc n =>
      rw [Int.negSucc_eq, neg_zsmul, neg_zsmul, ZornVectorMatrix.neg_a',
        ← Nat.cast_succ, natCast_zsmul, natCast_zsmul, zvm_nsmul_a]
private lemma zvm_zsmul_v (k : ℤ) (X : ZornVectorMatrix R) (i : Fin 3) : (k • X).v i = k • X.v i := by
  cases k with
  | ofNat n => simpa using zvm_nsmul_v n X i
  | negSucc n =>
      rw [Int.negSucc_eq, neg_zsmul, neg_zsmul, ZornVectorMatrix.neg_v',
        ← Nat.cast_succ, natCast_zsmul, natCast_zsmul, zvm_nsmul_v]
private lemma zvm_zsmul_w (k : ℤ) (X : ZornVectorMatrix R) (i : Fin 3) : (k • X).w i = k • X.w i := by
  cases k with
  | ofNat n => simpa using zvm_nsmul_w n X i
  | negSucc n =>
      rw [Int.negSucc_eq, neg_zsmul, neg_zsmul, ZornVectorMatrix.neg_w',
        ← Nat.cast_succ, natCast_zsmul, natCast_zsmul, zvm_nsmul_w]
private lemma zvm_zsmul_b (k : ℤ) (X : ZornVectorMatrix R) : (k • X).b = k • X.b := by
  cases k with
  | ofNat n => simpa using zvm_nsmul_b n X
  | negSucc n =>
      rw [Int.negSucc_eq, neg_zsmul, neg_zsmul, ZornVectorMatrix.neg_b',
        ← Nat.cast_succ, natCast_zsmul, natCast_zsmul, zvm_nsmul_b]

/-- **Repaired Dzhunushaliev Split-Octonion Basis Laws over an Arbitrary Possibly Noncommutative
Coefficient Ring `[Ring R]`**:
All basis algebraic laws hold directly in `ZornVectorMatrix R` using integer/central structure
constants, requiring **no commutativity** of `R`. Note `ZornVectorMatrix.commutatorJacobiator` is
right-nested (`[X,[Y,Z]]+...`), so `commutatorJacobiator q₄ q₅ q₆ = -12 • q₇`. -/
private lemma qSpin_sq (i : Fin 3) : qSpin R i * qSpin R i = -ZornVectorMatrix.one := by
  fin_cases i <;>
    { ext j <;> (try fin_cases j) <;>
      simp [qSpin, zvm_mul_def, ZornVectorMatrix.mul, ZornVectorMatrix.one,
        ZornVectorMatrix.neg, ZornVectorMatrix.U, ZornVectorMatrix.V,
        ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] }

private lemma qSpace_sq (i : Fin 3) : qSpace R i * qSpace R i = ZornVectorMatrix.one := by
  fin_cases i <;>
    { ext j <;> (try fin_cases j) <;>
      simp [qSpace, zvm_mul_def, ZornVectorMatrix.mul, ZornVectorMatrix.one,
        ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot,
        ZornVec3.cross] }

private lemma qCut7_sq : qCut7 R * qCut7 R = ZornVectorMatrix.one := by
  ext j <;> (try fin_cases j) <;>
    simp [qCut7, zvm_mul_def, ZornVectorMatrix.mul, ZornVectorMatrix.one,
      ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma qSpin_comm_01 :
    ZornVectorMatrix.commutator (qSpin R 0) (qSpin R 1) = (2 : ℤ) • qSpin R 2 := by
  ext j <;> (try fin_cases j) <;>
    simp [ZornVectorMatrix.commutator, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.add, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b, two_zsmul]

private lemma qSpin_assoc_012 :
    ZornVectorMatrix.associator (qSpin R 0) (qSpin R 1) (qSpin R 2) = 0 := by
  ext j <;> (try fin_cases j) <;>
    simp [ZornVectorMatrix.associator, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.add, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma qSpace_mul_01 : qSpace R 0 * qSpace R 1 = qSpin R 2 := by
  ext j <;> (try fin_cases j) <;>
    simp [qSpace, qSpin, zvm_mul_def, ZornVectorMatrix.mul, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma qSpace_comm_01 :
    ZornVectorMatrix.commutator (qSpace R 0) (qSpace R 1) = (2 : ℤ) • qSpin R 2 := by
  ext j <;> (try fin_cases j) <;>
    simp [ZornVectorMatrix.commutator, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
      ZornVectorMatrix.add, qSpace, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b, two_zsmul]

private lemma qSpin_mul_qSpace (i : Fin 3) : qSpin R i * qSpace R i = qCut7 R := by
  fin_cases i <;>
    { ext j <;> (try fin_cases j) <;>
      simp [qSpin, qSpace, qCut7, zvm_mul_def, ZornVectorMatrix.mul,
        ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
        ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] }

private lemma qSpace_mul_qSpin (i : Fin 3) : qSpace R i * qSpin R i = -qCut7 R := by
  fin_cases i <;>
    { ext j <;> (try fin_cases j) <;>
      simp [qSpin, qSpace, qCut7, zvm_mul_def, ZornVectorMatrix.mul,
        ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
        ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] }

private lemma qSpace_mul_12 : qSpace R 1 * qSpace R 2 = qSpin R 0 := by
  ext j <;> (try fin_cases j) <;>
    simp [qSpace, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.add,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma qSpace_mul_21 : qSpace R 2 * qSpace R 1 = -qSpin R 0 := by
  ext j <;> (try fin_cases j) <;>
    simp [qSpace, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.add,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma qSpace_mul_20 : qSpace R 2 * qSpace R 0 = qSpin R 1 := by
  ext j <;> (try fin_cases j) <;>
    simp [qSpace, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.add,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma qSpace_mul_02 : qSpace R 0 * qSpace R 2 = -qSpin R 1 := by
  ext j <;> (try fin_cases j) <;>
    simp [qSpace, qSpin, ZornVectorMatrix.mul, ZornVectorMatrix.add,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]

private lemma zorn_commutator_two_zsmul (X Y : ZornVectorMatrix R) :
    ZornVectorMatrix.commutator X ((2 : ℤ) • Y) = (2 : ℤ) • ZornVectorMatrix.commutator X Y := by
  change X * ((2 : ℤ) • Y) - ((2 : ℤ) • Y) * X = (2 : ℤ) • (X * Y - Y * X)
  rw [two_zsmul, two_zsmul]
  have h1 : X * (Y + Y) = X * Y + X * Y := by
    ext i <;> (try fin_cases i) <;>
      simp [ZornVectorMatrix.mul, ZornVectorMatrix.add, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;> noncomm_ring
  have h2 : (Y + Y) * X = Y * X + Y * X := by
    ext i <;> (try fin_cases i) <;>
      simp [ZornVectorMatrix.mul, ZornVectorMatrix.add, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;> noncomm_ring
  rw [h1, h2]
  abel

theorem dzhunushaliev_zorn_basis_laws_ring (i : Fin 3) :
    (qSpin R i * qSpin R i = -ZornVectorMatrix.one) ∧
    (qSpace R i * qSpace R i = ZornVectorMatrix.one) ∧
    (qCut7 R * qCut7 R = ZornVectorMatrix.one) ∧
    (ZornVectorMatrix.commutator (qSpin R 0) (qSpin R 1) = (2 : ℤ) • qSpin R 2) ∧
    (ZornVectorMatrix.associator (qSpin R 0) (qSpin R 1) (qSpin R 2) = 0) ∧
    (qSpace R 0 * qSpace R 1 = qSpin R 2) ∧
    (ZornVectorMatrix.commutator (qSpace R 0) (qSpace R 1) = (2 : ℤ) • qSpin R 2) ∧
    (ZornVectorMatrix.associator (qSpace R 0) (qSpace R 1) (qSpace R 2) = (2 : ℤ) • qCut7 R) ∧
    (ZornVectorMatrix.commutatorJacobiator (qSpace R 0) (qSpace R 1) (qSpace R 2) =
      -(12 : ℤ) • qCut7 R) := by
  have h8 : ZornVectorMatrix.associator (qSpace R 0) (qSpace R 1) (qSpace R 2) = (2 : ℤ) • qCut7 R := by
    change (qSpace R 0 * qSpace R 1) * qSpace R 2 - qSpace R 0 * (qSpace R 1 * qSpace R 2) =
      (2 : ℤ) • qCut7 R
    rw [qSpace_mul_01, qSpace_mul_12, qSpin_mul_qSpace 2, qSpace_mul_qSpin 0,
      sub_neg_eq_add, two_zsmul]
  have hc12 : ZornVectorMatrix.commutator (qSpace R 1) (qSpace R 2) = (2 : ℤ) • qSpin R 0 := by
    change qSpace R 1 * qSpace R 2 - qSpace R 2 * qSpace R 1 = (2 : ℤ) • qSpin R 0
    rw [qSpace_mul_12, qSpace_mul_21, sub_neg_eq_add, two_zsmul]
  have hc20 : ZornVectorMatrix.commutator (qSpace R 2) (qSpace R 0) = (2 : ℤ) • qSpin R 1 := by
    change qSpace R 2 * qSpace R 0 - qSpace R 0 * qSpace R 2 = (2 : ℤ) • qSpin R 1
    rw [qSpace_mul_20, qSpace_mul_02, sub_neg_eq_add, two_zsmul]
  have hqs_comm : ∀ k : Fin 3,
      ZornVectorMatrix.commutator (qSpace R k) (qSpin R k) = -(2 : ℤ) • qCut7 R := by
    intro k
    change qSpace R k * qSpin R k - qSpin R k * qSpace R k = -(2 : ℤ) • qCut7 R
    rw [qSpace_mul_qSpin k, qSpin_mul_qSpace k]
    simp only [two_zsmul, neg_smul]
    abel
  have h9 : ZornVectorMatrix.commutatorJacobiator (qSpace R 0) (qSpace R 1) (qSpace R 2) =
      -(12 : ℤ) • qCut7 R := by
    change ZornVectorMatrix.commutator (qSpace R 0) (ZornVectorMatrix.commutator (qSpace R 1) (qSpace R 2)) +
      (ZornVectorMatrix.commutator (qSpace R 1) (ZornVectorMatrix.commutator (qSpace R 2) (qSpace R 0)) +
       ZornVectorMatrix.commutator (qSpace R 2) (ZornVectorMatrix.commutator (qSpace R 0) (qSpace R 1))) =
      -(12 : ℤ) • qCut7 R
    rw [hc12, hc20, qSpace_comm_01, zorn_commutator_two_zsmul, zorn_commutator_two_zsmul,
      zorn_commutator_two_zsmul, hqs_comm 0, hqs_comm 1, hqs_comm 2]
    simp only [smul_smul, ← add_zsmul]
    norm_num
  exact ⟨qSpin_sq i, qSpace_sq i, qCut7_sq, qSpin_comm_01, qSpin_assoc_012,
    qSpace_mul_01, qSpace_comm_01, h8, h9⟩

/-- Noncommutative operator-ring witness (`R = Matrix (Fin 2) (Fin 2) ℂ`): the unobservable
triple `(q₄, q₅, q₆)` has strictly nonzero associator in `ZornVectorMatrix (Matrix (Fin 2) (Fin 2) ℂ)`. -/
theorem dzhunushaliev_zorn_mat2c_associator_ne_zero :
    (∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A) ∧
    ZornVectorMatrix.associator
      (qSpace (Matrix (Fin 2) (Fin 2) ℂ) 0)
      (qSpace (Matrix (Fin 2) (Fin 2) ℂ) 1)
      (qSpace (Matrix (Fin 2) (Fin 2) ℂ) 2) ≠ 0 := by
  constructor
  · refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  · intro h0
    have ha := congrArg ZornVectorMatrix.a h0
    rw [(dzhunushaliev_zorn_basis_laws_ring (R := Matrix (Fin 2) (Fin 2) ℂ) 0).2.2.2.2.2.2.2.1] at ha
    rw [zvm_zsmul_a, qCut7, zvm_sub_a, ZornVectorMatrix.zero_a] at ha
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) ha
    simp [ZornVectorMatrix.E11, ZornVectorMatrix.E22] at h00

/-- Standalone `M₂(ℂ)` non-commutativity witness for the `ZornVectorMatrix` coefficient carrier. -/
theorem dzhunushaliev_mat2c_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  dzhunushaliev_zorn_mat2c_associator_ne_zero.1

end ArbitraryRing

section CommRingSynthesis

variable {R : Type*} [CommRing R]

/-- **Repaired Alternative Split-Octonion Realization directly on `ZornVectorMatrix R`**:
Combines exact alternativity (via `zorn_left_alternative` and `zorn_right_alternative`), exact
composition norm (`ZornVectorMatrix.norm_mul`), the quaternion/hyperbolic spin decomposition,
left-nested `akivisJacobiator q₄ q₅ q₆ = 12 • q₇`, and Heisenberg Leibniz defect `= -6 • q₇`. -/
theorem repaired_zorn_dzhunushaliev_laws (x y z : ZornVectorMatrix R) (i : Fin 3) :
    (_root_.associator x y z = -_root_.associator y x z) ∧
    (_root_.associator x y z = -_root_.associator x z y) ∧
    (ZornVectorMatrix.norm (x * y) = ZornVectorMatrix.norm x * ZornVectorMatrix.norm y) ∧
    (qSpin R i * qSpin R i = -ZornVectorMatrix.one) ∧
    (qSpace R i * qSpace R i = ZornVectorMatrix.one) ∧
    (akivisBracket (qSpin R 0) (qSpin R 1) = (2 : ℤ) • qSpin R 2) ∧
    (_root_.associator (qSpin R 0) (qSpin R 1) (qSpin R 2) = 0) ∧
    (akivisBracket (qSpace R 0) (qSpace R 1) = (2 : ℤ) • qSpin R 2) ∧
    (_root_.associator (qSpace R 0) (qSpace R 1) (qSpace R 2) = (2 : ℤ) • qCut7 R) ∧
    (akivisJacobiator (qSpace R 0) (qSpace R 1) (qSpace R 2) = (12 : ℤ) • qCut7 R) ∧
    (akivisBracket (qSpace R 2) (qSpace R 0 * qSpace R 1) -
      qSpace R 0 * akivisBracket (qSpace R 2) (qSpace R 1) -
      akivisBracket (qSpace R 2) (qSpace R 0) * qSpace R 1 = -(6 : ℤ) • qCut7 R) := by
  have hAlt := alternating_of_left_right_alternative
    (zorn_left_alternative (R := R)) (zorn_right_alternative (R := R))
  have hBasis := dzhunushaliev_zorn_basis_laws_ring (R := R) i
  have hAssoc456 : _root_.associator (qSpace R 0) (qSpace R 1) (qSpace R 2) = (2 : ℤ) • qCut7 R :=
    hBasis.2.2.2.2.2.2.2.1
  have hLJ := alternative_leibniz_and_jacobi hAlt.1 hAlt.2 (qSpace R 0) (qSpace R 1) (qSpace R 2)
  refine ⟨hAlt.1 x y z, hAlt.2 x y z, ZornVectorMatrix.norm_mul x y,
    hBasis.1, hBasis.2.1, hBasis.2.2.2.1, hBasis.2.2.2.2.1, hBasis.2.2.2.2.2.2.1, hAssoc456, ?_, ?_⟩
  · rw [hLJ.2, hAssoc456, smul_smul]
    norm_num
  · rw [hLJ.1, hAssoc456, smul_smul]
    norm_num

end CommRingSynthesis

end ZornSplitOctonionRealization

/-! ### Part 4: Associative Impossibility vs. Real `Cl(3,1) ≅ M₄(ℝ)` Nambu Realization (Eqs. 29–31) -/

section Finding2AssociativeVsNambu

/-- **Associative Impossibility (Answering Question 1, Eqs. 29–31)**:
In every associative `[Ring B]` (including every linear matrix algebra or `B(H)` bounded operator
algebra), the ternary associator `_root_.associator x y z` vanishes identically, so no associative
representation can realize `(P^μ, P^ν, P^ρ) ≠ 0`. -/
theorem associative_ring_associator_zero {B : Type*} [Ring B] :
    (∀ x y z : B, _root_.associator x y z = 0) ∧
    ¬ ∃ P0 P1 P2 : B, _root_.associator P0 P1 P2 ≠ 0 := by
  have h0 : ∀ x y z : B, _root_.associator x y z = 0 := by
    intro x y z
    simp [_root_.associator_apply, mul_assoc]
  exact ⟨h0, fun ⟨P0, P1, P2, hne⟩ => hne (h0 P0 P1 P2)⟩

private theorem clifford_anticomm_nambu {B : Type*} [Ring B] {a b c : B}
    (hab : a * b + b * a = 0) (hbc : b * c + c * b = 0) (hca : c * a + a * c = 0) :
    nambuBracket3 a b c = (6 : ℕ) • (a * b * c) := by
  have hba : b * a = -(a * b) := eq_neg_of_add_eq_zero_right hab
  have hcb : c * b = -(b * c) := eq_neg_of_add_eq_zero_right hbc
  have hac : c * a = -(a * c) := eq_neg_of_add_eq_zero_left hca
  unfold nambuBracket3
  rw [hba, hcb, hac]
  calc (a * b - -(a * b)) * c + (b * c - -(b * c)) * a + (-(a * c) - a * c) * b
      = (a * b + a * b) * c + (b * c + b * c) * a - (a * c + a * c) * b := by noncomm_ring
    _ = 2 * (a * b * c) + 2 * (b * (c * a)) - 2 * (a * (c * b)) := by noncomm_ring
    _ = 2 * (a * b * c) + 2 * (b * (-(a * c))) - 2 * (a * (-(b * c))) := by rw [hac, hcb]
    _ = 2 * (a * b * c) - 2 * ((b * a) * c) + 2 * (a * b * c) := by noncomm_ring
    _ = 2 * (a * b * c) - 2 * ((-(a * b)) * c) + 2 * (a * b * c) := by rw [hba]
    _ = 6 * (a * b * c) := by noncomm_ring
    _ = (6 : ℕ) • (a * b * c) := by rw [nsmul_eq_mul]; rfl

/-- **Real `Cl(3,1) ≅ M₄(ℝ)` Nambu Hodge-Dual Realization (`Eqs. 29–31` Repaired via Nambu
3-Bracket)**:
Replaces the impossible associative associator with `nambuBracket3` on `diracGamma0..3` from
`DiracSpinCasimirNambuModulesBridge`, proving all four Hodge-dual ternary identities with
`diracOmega4 = γ₀ γ₁ γ₂ γ₃`, nonvanishing of `nambuBracket3 diracGamma0 diracGamma1 diracGamma2`,
and nonvanishing Lorentz commutators `[γ_μ, γ_ν] = 2 γ_μ γ_ν`. -/
theorem diracGamma_nambuBracket3_hodge_realization :
    (nambuBracket3 diracGamma0 diracGamma1 diracGamma2 = (6 : ℝ) • (diracOmega4 * diracGamma3)) ∧
    (nambuBracket3 diracGamma1 diracGamma2 diracGamma3 = (6 : ℝ) • (diracOmega4 * diracGamma0)) ∧
    (nambuBracket3 diracGamma0 diracGamma2 diracGamma3 = (6 : ℝ) • (diracOmega4 * diracGamma1)) ∧
    (nambuBracket3 diracGamma0 diracGamma1 diracGamma3 = -(6 : ℝ) • (diracOmega4 * diracGamma2)) ∧
    (nambuBracket3 diracGamma0 diracGamma1 diracGamma2 ≠ 0) ∧
    (akivisBracket diracGamma0 diracGamma1 = (2 : ℝ) • (diracGamma0 * diracGamma1)) ∧
    (akivisBracket diracGamma1 diracGamma2 = (2 : ℝ) • (diracGamma1 * diracGamma2)) ∧
    (akivisBracket diracGamma0 diracGamma1 ≠ 0) := by
  obtain ⟨h00, h11, h22, h33, h01, h02, h03, h12, h13, h23⟩ := diracGamma_clifford_relations
  have h10 : diracGamma1 * diracGamma0 + diracGamma0 * diracGamma1 = 0 := by rw [add_comm, h01]
  have h20 : diracGamma2 * diracGamma0 + diracGamma0 * diracGamma2 = 0 := by rw [add_comm, h02]
  have h30 : diracGamma3 * diracGamma0 + diracGamma0 * diracGamma3 = 0 := by rw [add_comm, h03]
  have h21 : diracGamma2 * diracGamma1 + diracGamma1 * diracGamma2 = 0 := by rw [add_comm, h12]
  have h31 : diracGamma3 * diracGamma1 + diracGamma1 * diracGamma3 = 0 := by rw [add_comm, h13]
  have h32 : diracGamma3 * diracGamma2 + diracGamma2 * diracGamma3 = 0 := by rw [add_comm, h23]
  have ha01 : diracGamma1 * diracGamma0 = -(diracGamma0 * diracGamma1) := eq_neg_of_add_eq_zero_right h01
  have ha02 : diracGamma2 * diracGamma0 = -(diracGamma0 * diracGamma2) := eq_neg_of_add_eq_zero_right h02
  have ha03 : diracGamma3 * diracGamma0 = -(diracGamma0 * diracGamma3) := eq_neg_of_add_eq_zero_right h03
  have ha12 : diracGamma2 * diracGamma1 = -(diracGamma1 * diracGamma2) := eq_neg_of_add_eq_zero_right h12
  have ha13 : diracGamma3 * diracGamma1 = -(diracGamma1 * diracGamma3) := eq_neg_of_add_eq_zero_right h13
  have ha23 : diracGamma3 * diracGamma2 = -(diracGamma2 * diracGamma3) := eq_neg_of_add_eq_zero_right h23
  have hw3 : diracOmega4 * diracGamma3 = diracGamma0 * diracGamma1 * diracGamma2 := by
    dsimp [diracOmega4]
    rw [mul_assoc (diracGamma0 * diracGamma1 * diracGamma2), h33, mul_one]
  have hw0 : diracOmega4 * diracGamma0 = diracGamma1 * diracGamma2 * diracGamma3 := by
    dsimp [diracOmega4]
    calc (diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3) * diracGamma0
        = diracGamma0 * diracGamma1 * diracGamma2 * (diracGamma3 * diracGamma0) := by noncomm_ring
      _ = -(diracGamma0 * diracGamma1 * (diracGamma2 * diracGamma0) * diracGamma3) := by
          rw [ha03]; noncomm_ring
      _ = diracGamma0 * (diracGamma1 * diracGamma0) * diracGamma2 * diracGamma3 := by
          rw [ha02]; noncomm_ring
      _ = -((diracGamma0 * diracGamma0) * diracGamma1 * diracGamma2 * diracGamma3) := by
          rw [ha01]; noncomm_ring
      _ = diracGamma1 * diracGamma2 * diracGamma3 := by rw [h00]; noncomm_ring
  have hw1 : diracOmega4 * diracGamma1 = diracGamma0 * diracGamma2 * diracGamma3 := by
    dsimp [diracOmega4]
    calc (diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3) * diracGamma1
        = diracGamma0 * diracGamma1 * diracGamma2 * (diracGamma3 * diracGamma1) := by noncomm_ring
      _ = -(diracGamma0 * diracGamma1 * (diracGamma2 * diracGamma1) * diracGamma3) := by
          rw [ha13]; noncomm_ring
      _ = diracGamma0 * (diracGamma1 * diracGamma1) * diracGamma2 * diracGamma3 := by
          rw [ha12]; noncomm_ring
      _ = diracGamma0 * diracGamma2 * diracGamma3 := by rw [h11]; noncomm_ring
  have hw2 : diracOmega4 * diracGamma2 = -(diracGamma0 * diracGamma1 * diracGamma3) := by
    dsimp [diracOmega4]
    calc (diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3) * diracGamma2
        = diracGamma0 * diracGamma1 * diracGamma2 * (diracGamma3 * diracGamma2) := by noncomm_ring
      _ = -(diracGamma0 * diracGamma1 * (diracGamma2 * diracGamma2) * diracGamma3) := by
          rw [ha23]; noncomm_ring
      _ = -(diracGamma0 * diracGamma1 * diracGamma3) := by rw [h22]; noncomm_ring
  have hN012 : nambuBracket3 diracGamma0 diracGamma1 diracGamma2 = (6 : ℝ) • (diracOmega4 * diracGamma3) := by
    rw [clifford_anticomm_nambu h01 h12 h20, hw3, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  have hN123 : nambuBracket3 diracGamma1 diracGamma2 diracGamma3 = (6 : ℝ) • (diracOmega4 * diracGamma0) := by
    rw [clifford_anticomm_nambu h12 h23 h31, hw0, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  have hN023 : nambuBracket3 diracGamma0 diracGamma2 diracGamma3 = (6 : ℝ) • (diracOmega4 * diracGamma1) := by
    rw [clifford_anticomm_nambu h02 h23 h30, hw1, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  have hN013 : nambuBracket3 diracGamma0 diracGamma1 diracGamma3 = -(6 : ℝ) • (diracOmega4 * diracGamma2) := by
    rw [clifford_anticomm_nambu h01 h13 h30, hw2, smul_neg, neg_smul, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  have h012_ne : nambuBracket3 diracGamma0 diracGamma1 diracGamma2 ≠ 0 := by
    intro h0
    have hmul : (nambuBracket3 diracGamma0 diracGamma1 diracGamma2) *
        (diracGamma2 * diracGamma1 * diracGamma0) = 0 := by rw [h0, zero_mul]
    rw [hN012, hw3, smul_mul_assoc] at hmul
    have hinv : (diracGamma0 * diracGamma1 * diracGamma2) *
        (diracGamma2 * diracGamma1 * diracGamma0) = -1 := by
      calc (diracGamma0 * diracGamma1 * diracGamma2) * (diracGamma2 * diracGamma1 * diracGamma0)
          = diracGamma0 * diracGamma1 * (diracGamma2 * diracGamma2) * diracGamma1 * diracGamma0 := by
              noncomm_ring
        _ = diracGamma0 * (diracGamma1 * diracGamma1) * diracGamma0 := by
              rw [h22]; noncomm_ring
        _ = diracGamma0 * diracGamma0 := by rw [h11]; noncomm_ring
        _ = -1 := h00
    rw [hinv, smul_neg] at hmul
    have h00' := congrFun (congrFun hmul (0, 0)) (0, 0)
    simp at h00'
  have hC01 : akivisBracket diracGamma0 diracGamma1 = (2 : ℝ) • (diracGamma0 * diracGamma1) := by
    unfold akivisBracket
    rw [ha01, sub_neg_eq_add, ← two_smul ℝ]
  have hC12 : akivisBracket diracGamma1 diracGamma2 = (2 : ℝ) • (diracGamma1 * diracGamma2) := by
    unfold akivisBracket
    rw [ha12, sub_neg_eq_add, ← two_smul ℝ]
  have hC01_ne : akivisBracket diracGamma0 diracGamma1 ≠ 0 := by
    intro h0
    have hmul : akivisBracket diracGamma0 diracGamma1 * (diracGamma1 * diracGamma0) = 0 := by
      rw [h0, zero_mul]
    rw [hC01, smul_mul_assoc] at hmul
    have hinv : (diracGamma0 * diracGamma1) * (diracGamma1 * diracGamma0) = -1 := by
      calc (diracGamma0 * diracGamma1) * (diracGamma1 * diracGamma0)
          = diracGamma0 * (diracGamma1 * diracGamma1) * diracGamma0 := by noncomm_ring
        _ = diracGamma0 * diracGamma0 := by rw [h11]; noncomm_ring
        _ = -1 := h00
    rw [hinv, smul_neg] at hmul
    have h00' := congrFun (congrFun hmul (0, 0)) (0, 0)
    simp at h00'
  exact ⟨hN012, hN123, hN023, hN013, h012_ne, hC01, hC12, hC01_ne⟩

end Finding2AssociativeVsNambu

end InfoGeometry.Canonical.DzhunushalievNonassociativeBridge
