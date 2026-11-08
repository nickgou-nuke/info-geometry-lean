/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Finite Parafermion Spin Arithmetic and Character-Sum Identities

## i. Overview

This owner proves selected integer spin-numerator calculations, finite residue
checks for actions on `ZMod`-style representatives, an integer remainder
identity, and conditional unnormalized character-sum identities. The Boolean
residue calculations are finite models; this file does not construct
cyclotomic field automorphisms, modular tensor categories, or physical
condensation data.

## ii. Key results

* `zfSpinNum_charge_conjugation` and `zfSpinNum_half_period_even` prove
  algebraic identities for the declared numerator function.
* `parafermion_and_vortex_spin_numerator_examples` checks the displayed small
  integer examples.
* The finite residue-action theorems check only the moduli in their types;
  modulus 24 is delegated to the native cyclotomic Galois owner.
* `cyclic_character_sum_ring_identities` proves ring
  identities under explicit power equations.

## iii. Table of contents

1. Spin numerator arithmetic and examples
2. Finite residue actions and modular calculations
3. Additive remainder identity
4. Conditional character-sum ring identities

## iv. References

* `InfoGeometry.Topology.CFT.ConformalSpin` for a repository rational-spin type.
* `InfoGeometry.Canonical.Cyclotomic24GaloisNative` constructs
  `Gal(ℚ(ζ₂₄)/ℚ) ≃* (ZMod 24)ˣ`, its action on 24th roots, and proves the
  Galois group has exponent two.
* `InfoGeometry.Canonical.FiveGradedKantorTanakaOspGunaydinGurseyContactPoset`
  contains a finite modulus-24 unit calculation.
* `InfoGeometry.Arithmetic.CyclotomicGalois.zeta_is_primitive_root` is an
  existing Mathlib-backed primitive-root result.

The cited owners are context and reuse candidates; this file does not claim a
proved bridge to their structures.

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `zfSpinNum_charge_conjugation`, `zfSpinNum_half_period_even`,
  `parafermion_and_vortex_spin_numerator_examples`.
- `negation_action_fixes_iff_two_mul_eq_zero`, `scalar_action_invariant_of_unit_sq_eq_one`,
  `finite_unit_action_fixed_residues`, `quadratic_residue_invariance_selected_moduli`.
- `spin_numerator_remainder_zero_iff_zero_remainder`.
- `cyclic_character_sum_ring_identities`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Ring character-sum identities hold in any associative ring `[Ring B]` under explicit power
  hypotheses `hΩ : Ω * (Ω * Ω) = 1` and `hU : U * (U * (U * U)) = 1`.

#### BUCKET 3 — Open / Unformalized
- Cyclotomic field Galois representations, modular tensor categories, and analytic Verlinde
  diagonalization are outside the scope of this finite arithmetic and ring-identity owner.
-/
namespace ParafermionCondensationGaloisCharacterPoset

-- ============================================================================
-- NODE 𝔊ℭ₁ & 𝔊ℭ₂: Zamolodchikov–Fateev Parafermion Spins & Majorana Vortex Ladder
-- ============================================================================

/--
Scaled conformal spin `zfSpinNum κ l = l * (κ - l)` of the `l`-th `ℤ_κ` parafermion
current `ψ_l` (where `h_l = l * (κ - l) / κ`).
-/
def zfSpinNum (κ l : ℕ) : ℕ := l * (κ - l)

/--
Universal charge-conjugation symmetry of the Zamolodchikov–Fateev parafermion spin numerator:
for every `κ : ℕ` and `l ≤ κ`, `zfSpinNum κ (κ - l) = zfSpinNum κ l`.
-/
theorem zfSpinNum_charge_conjugation (κ l : ℕ) (hl : l ≤ κ) :
    zfSpinNum κ (κ - l) = zfSpinNum κ l := by
  dsimp [zfSpinNum]
  rw [Nat.sub_sub_self hl, Nat.mul_comm]

/--
In every `ℤ_{4k}` parafermion family, the half-period sector `l = 2k` has scaled spin
`zfSpinNum (4 * k) (2 * k) = k * (4 * k)`, which is an exact integer multiple of the
conductor `4 * k` (corresponding to integer spin `h_{2k} = k ∈ ℤ`).
-/
theorem zfSpinNum_half_period_even (k : ℕ) :
    zfSpinNum (4 * k) (2 * k) = k * (4 * k) := by
  dsimp [zfSpinNum]
  have hsub : 4 * k - 2 * k = 2 * k := by omega
  rw [hsub]
  ring

/--
**Selected parafermion and vortex spin-numerator examples:**
1. **Charge-Conjugation Symmetry:** `zfSpinNum κ l = zfSpinNum κ (κ - l)` for all `l ≤ κ`.
2. **SYK / `ℤ₄` Quartet (`κ = 4`):** `l = 1` and `l = 3` have fractional spin numerator `3`
   (`h = 3/4 = Δ_O`, with dual `1 - 3/4 = 1/4 = Δ_χ`), whereas the paired parafermion `l = 2`
   has `zfSpinNum 4 2 = 4 = 1 * 4` (integer spin numerator).
3. **`ℤ₃` Color Parafermions (`κ = 3`):** `l = 1, 2` have `zfSpinNum 3 l = 2` (`h = 2/3`),
   so the displayed 3-fold sum is `3 * 2 = 6 = 2 * 3`.
4. **Majorana Vortex Ladder (`h_N = N / 16`):** `N = 8` gives `8 * 2 = 16` (`h = 1/2`, Galois-fixed
   fermion-spin numerator) and `N = 16` gives `16 = 1 * 16` (integer-spin numerator).
-/
theorem parafermion_and_vortex_spin_numerator_examples
    (κ l : ℕ) (hl : l ≤ κ) :
    zfSpinNum κ (κ - l) = zfSpinNum κ l ∧
    -- 1. SYK / ℤ₄ parafermion spin numerators (over denominator κ = 4):
    zfSpinNum 4 0 = 0 ∧
    zfSpinNum 4 1 = 3 ∧
    zfSpinNum 4 2 = 4 ∧
    zfSpinNum 4 3 = 3 ∧
    -- 2. ℤ₄ l = 2 is an exact integer multiple of κ = 4 (h₂ = 1):
    zfSpinNum 4 2 % 4 = 0 ∧
    zfSpinNum 4 1 % 4 ≠ 0 ∧
    -- 3. ℤ₃ parafermion spin numerators (over denominator κ = 3) & 3-quark baryon closure:
    zfSpinNum 3 1 = 2 ∧
    zfSpinNum 3 2 = 2 ∧
    (3 * zfSpinNum 3 1) % 3 = 0 ∧
    -- 4. Majorana vortex 16-fold E₈ condensation:
    (8 * 2) % 16 = 0 ∧
    16 % 16 = 0 := by
  refine ⟨zfSpinNum_charge_conjugation κ l hl, by decide⟩

-- ============================================================================
-- NODE 𝔊ℭ₃ & 𝔊ℭ₄: Selected Finite Residue Actions
-- ============================================================================

/--
Finite Boolean check: every enumerated `k < N` coprime to `N` fixes the residue `m`.
This definition does not construct a cyclotomic field or a Galois automorphism.
-/
def residueActionFixesAllUnits (N : ℕ) (m : Fin N) : Bool :=
  (List.range N).all (fun k =>
    if Nat.gcd k N == 1 then
      (k * m.val) % N == m.val
    else
      true)

/--
Finite Boolean check of the residue action `m ↦ k² * m mod N` for enumerated units.
-/
def quadraticResidueActionInvariant (N : ℕ) : Bool :=
  (List.range N).all (fun m =>
    (List.range N).all (fun k =>
      if Nat.gcd k N == 1 then
        (k * k * m) % N == m
      else
        true))

/--
In a ring `[Ring R]`, the scalar action `m ↦ (-1) * m` fixes `m` if and only if
`(2 : R) * m = 0`. This is not a rationality theorem about cyclotomic fields.
-/
theorem negation_action_fixes_iff_two_mul_eq_zero
    {R : Type*} [Ring R] (m : R) :
    (-1 : R) * m = m ↔ (2 : R) * m = 0 := by
  constructor
  · intro h
    calc
      (2 : R) * m = m + m := two_mul m
      _ = (-1 : R) * m + m := by rw [h]
      _ = -m + m := by rw [neg_one_mul]
      _ = 0 := neg_add_cancel m
  · intro h
    have hm : m + m = 0 := by
      rw [← two_mul]
      exact h
    calc
      (-1 : R) * m = -m := neg_one_mul m
      _ = -m + (m + m) := by rw [hm, add_zero]
      _ = m := neg_add_cancel_left m m

/--
If `k * k = 1` in a ring, then both `(k * k) * m` and `((-k) * (-k)) * m` fix every `m`.
This is a ring identity, without a modular-category interpretation.
-/
theorem scalar_action_invariant_of_unit_sq_eq_one
    {R : Type*} [Ring R] (k m : R) (hk : k * k = 1) :
    (k * k) * m = m ∧ ((-k) * (-k)) * m = m := by
  refine ⟨by rw [hk, one_mul], ?_⟩
  rw [neg_mul_neg, hk, one_mul]

/--
**Finite residue-action checks:** at the explicit moduli in the statement, enumeration
shows which residues are fixed. This does not establish a general Galois descent theorem.
-/
theorem finite_unit_action_fixed_residues
    {R : Type*} [Ring R] (m_ring : R) :
    ((-1 : R) * m_ring = m_ring ↔ (2 : R) * m_ring = 0) ∧
    -- 1. At N = 4: residues 0 and 2 are fixed by the enumerated unit action:
    (∀ m : Fin 4, residueActionFixesAllUnits 4 m = true ↔ (m.val == 0 || m.val == 2) = true) ∧
    -- 2. At N = 16: residues 0 and 8 are fixed by the enumerated unit action:
    (∀ m : Fin 16, residueActionFixesAllUnits 16 m = true ↔ (m.val == 0 || m.val == 8) = true) ∧
    -- 3. At N = 8: residues 0 and 4 are fixed by the enumerated unit action:
    (∀ m : Fin 8, residueActionFixesAllUnits 8 m = true ↔ (m.val == 0 || m.val == 4) = true) := by
  refine ⟨negation_action_fixes_iff_two_mul_eq_zero m_ring, by decide⟩

/--
**Finite quadratic residue checks:** this theorem concerns only the moduli listed in its
conclusion. It is not a classification of all moduli or a modular S-matrix theorem.
-/
theorem quadratic_residue_invariance_selected_moduli
    {R : Type*} [Ring R] (k m_ring : R) (hk : k * k = 1) :
    ((k * k) * m_ring = m_ring ∧ ((-k) * (-k)) * m_ring = m_ring) ∧
    quadraticResidueActionInvariant 2  = true ∧
    quadraticResidueActionInvariant 3  = true ∧
    quadraticResidueActionInvariant 4  = true ∧
    quadraticResidueActionInvariant 6  = true ∧
    quadraticResidueActionInvariant 8  = true ∧
    quadraticResidueActionInvariant 12 = true ∧
    -- Failure outside divisors of 24:
    quadraticResidueActionInvariant 5  = false ∧
    quadraticResidueActionInvariant 16 = false := by
  refine ⟨scalar_action_invariant_of_unit_sq_eq_one k m_ring hk, by decide⟩

-- ============================================================================
-- NODE 𝔊ℭ₅: Marín-Salvador Balancing & Mutual Locality of Condensing Parafermions
-- ============================================================================

/--
An additive modular-remainder expression. No braiding or fusion operation is defined here.
-/
def spinNumeratorRemainder (N : Int) (m_ab m_a m_b : Int) : Int :=
  (m_ab - m_a - m_b) % N

/--
**Modular remainder identity:** after unfolding, vanishing of `spinNumeratorRemainder N m_ab 0 0`
is equivalent to `m_ab % N = 0`, and shifting `m_ab` by `m_a + m_b` recovers `m_ab % N`.
This is not a categorical balancing theorem.
-/
theorem spin_numerator_remainder_zero_iff_zero_remainder
    (N m_ab m_a m_b : Int) :
    (spinNumeratorRemainder N m_ab 0 0 = 0 ↔ m_ab % N = 0) ∧
    spinNumeratorRemainder N (m_ab + m_a + m_b) m_a m_b = m_ab % N := by
  refine ⟨?_, ?_⟩
  · dsimp [spinNumeratorRemainder]
    simp only [sub_zero]
  · dsimp [spinNumeratorRemainder]
    have hsub : m_ab + m_a + m_b - m_a - m_b = m_ab := by ring
    rw [hsub]

-- ============================================================================
-- NODE 𝔊ℭ₆ & 𝔊ℭ₇: Operator Character Projection & Parafermion Condensation in `[Ring B]`
-- ============================================================================

section OperatorParafermionCondensation
variable {B : Type*} [Ring B]

/--
Unnormalized `ℤ₃` cyclic character sum `cyclicCharacterSum3(Ω) = 1 + Ω + Ω²`.
-/
def cyclicCharacterSum3 (Ω : B) : B := 1 + Ω + Ω * Ω

/--
Unnormalized `ℤ₄` cyclic character sum `cyclicCharacterSum4(U) = 1 + U²`.
-/
def cyclicCharacterSum4 (U : B) : B := 1 + U * U

/--
**Conditional ring identities:** in an associative ring satisfying the stated power equations,
the unnormalized sums obey annihilation, invariance, and quasi-idempotence equations. These
algebraic equations do not establish physical confinement or categorical condensation.
-/
theorem cyclic_character_sum_ring_identities
    (Ω U : B) (hΩ : Ω * (Ω * Ω) = 1) (hU : U * (U * (U * U)) = 1) :
    (1 - Ω) * cyclicCharacterSum3 Ω = 0 ∧
    Ω * cyclicCharacterSum3 Ω = cyclicCharacterSum3 Ω ∧
    cyclicCharacterSum3 Ω * cyclicCharacterSum3 Ω =
      cyclicCharacterSum3 Ω + cyclicCharacterSum3 Ω + cyclicCharacterSum3 Ω ∧
    (U * U) * cyclicCharacterSum4 U = cyclicCharacterSum4 U ∧
    cyclicCharacterSum4 U * cyclicCharacterSum4 U =
      cyclicCharacterSum4 U + cyclicCharacterSum4 U := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [cyclicCharacterSum3]
    simp only [sub_mul, mul_add, one_mul, mul_one, hΩ]
    abel
  · dsimp [cyclicCharacterSum3]
    simp only [mul_add, mul_one, hΩ]
    abel
  · dsimp [cyclicCharacterSum3]
    simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hΩ]
    abel
  · dsimp [cyclicCharacterSum4]
    simp only [mul_add, mul_one, mul_assoc, hU]
    abel
  · dsimp [cyclicCharacterSum4]
    simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hU]
    abel

end OperatorParafermionCondensation

end ParafermionCondensationGaloisCharacterPoset
