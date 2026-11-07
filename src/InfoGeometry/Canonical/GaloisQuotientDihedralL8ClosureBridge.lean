/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cyclotomic12GaloisCorrespondence
import InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets
import InfoGeometry.Canonical.NonAbelianDihedralSymmetry12
import InfoGeometry.Canonical.FiniteCharacterMatrixOrder
import InfoGeometry.GaloisQuotient.GaloisQuotientNonAbelianFourierPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Galois–Quotient–Dihedral Cross-Carrier Closure Bridge (`docs/CROSS_LANE_CLOSURE_SEQUENCE.md` Row L8)

Proves the four concrete cross-carrier obligations of Row L8 in `docs/CROSS_LANE_CLOSURE_SEQUENCE.md`,
connecting `Cyclotomic12GaloisCorrespondence`, `TwelveFoldCyclotomicNative`,
`TwelveFoldGaloisCharacterSets`, `NonAbelianDihedralSymmetry12`, `FiniteCharacterMatrixOrder`,
and `GaloisQuotientNonAbelianFourierPoset`:

1. **Obligation L8(a) — Unit-Group / Galois Action on `Cyclotomic12Field` Roots & `ZMod 12` Harmonic Orbits:**
   - `cyclotomic12_galois_unit_action_and_zmod12_harmonic_orbits` proves that every automorphism
     `σ : Gal(CyclotomicField 12 ℚ / ℚ)` acts on the `k`-th power `ζ ^ k` of any twelfth root of
     unity `ζ ^ 12 = 1` by raising `ζ ^ k` to `(cyclotomic12_galEquivUnits σ).val.val`, and that
     the multiplicative unit action `galoisPower : (ZMod 12)ˣ → ZMod 12 → ZMod 12` partitions
     `ZMod 12` into the exact six divisor-order harmonic orbits `{0}`, `{6}`, `{4, 8}`, `{3, 9}`,
     `{2, 10}`, and `{1, 5, 7, 11}` of cardinalities `φ(1)=1, φ(2)=1, φ(3)=2, φ(4)=2, φ(6)=2, φ(12)=4`.
2. **Obligation L8(b) — Ramanujan Orbit-Trace Integrality & Möbius Formula:**
   - `cyclotomic12_orbit_trace_eq_ramanujan_moebius` proves over any `[CommRing R]` that for any
     primitive twelfth root `ζ : R` satisfying the twelfth cyclotomic polynomial `ζ ^ 4 - ζ ^ 2 + 1 = 0`,
     the Galois orbit sums across the six orbits `{0}`, `{6}`, `{4, 8}`, `{3, 9}`, `{2, 10}`,
     `{1, 5, 7, 11}` coincide identically with the coerced integer Möbius Ramanujan sums
     `(ramanujanSum12 d x : R)`.
3. **Obligation L8(c) — Explicit Dihedral Group Representation into `Matrix (Fin 2) (Fin 2) R` & Peirce Compatibility:**
   - `dihedral4PeirceMatrixRep : DihedralGroup 4 →* Matrix (Fin 2) (Fin 2) R` constructs a native
     group homomorphism into `2 × 2` matrices, and `peirce_matrix_carrier_compatibility_and_dihedral_inversion`
     proves that the abstract Peirce operators `S_P`, `Phi1`, `J1`, and `Rotor2D` evaluated on
     `peirceMatP = !![1, 0; 0, 0]`, `peirceMatX = !![0, 1; 0, 0]`, `peirceMatY = !![0, 0; 1, 0]`
     equal `peirceGradingS`, `peirceSwapPhi`, `!![0, 1; -1, 0]`, and `!![c, s; -s, c]`, with
     dihedral reflection conjugation `dihedral4PeirceMatrixRep (.sr 0) * dihedral4PeirceMatrixRep (.r i) * dihedral4PeirceMatrixRep (.sr 0) = dihedral4PeirceMatrixRep (.r (-i))`.
4. **Obligation L8(d) — Concrete Subgroup-Average Projector `P_H = ½(I₂ + Φ₁)` & Nonvanishing Quotient Variance:**
   - `z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance` constructs the concrete
     subgroup-averaging projector `z2SubgroupAverageProjector half = half • (1 + peirceSwapPhi)`
     in `Matrix (Fin 2) (Fin 2) K` (`2 * half = 1`), proves its idempotence `P_H * P_H = P_H`,
     verifies that the macro-involution `peirceSwapPhi` satisfies `P_H * Φ₁ * P_H = Φ₁ * P_H`
     while the micro-involution `peirceGradingS` satisfies `P_H * S_P * P_H = 0`, and proves that
     for `L = SurprisalOp (u_bar • 1) (delta_u • 1) peirceGradingS` the second-order quotient
     variance defect equals `(delta_u * delta_u) • P_H` and is strictly nonzero whenever
     `delta_u * delta_u * half ≠ 0`.

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `z12HarmonicOrbit`, `cyclotomic12_galois_unit_action_and_zmod12_harmonic_orbits`,
  - `cyclotomic12_orbit_trace_eq_ramanujan_moebius`,
  - `peirceMatP`, `peirceMatX`, `peirceMatY`, `peirceMatJ`, `peirceRotation4Power`, `dihedral4PeirceMatrixRep`,
  - `peirce_matrix_carrier_compatibility_and_dihedral_inversion`,
  - `z2SubgroupAverageProjector`, `z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - In `cyclotomic12_orbit_trace_eq_ramanujan_moebius`, `hζ : ζ ^ 4 - ζ ^ 2 + 1 = 0` is the twelfth cyclotomic polynomial hypothesis.
  - In `z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance`, `h2 : (2 : K) * half = 1` and `hNonzero : delta_u * delta_u * half ≠ 0` supply invertible `2` and nonvanishing slope.
* **BUCKET 3 — Out-of-Scope Empirical Claims:**
  - Neural representation training dynamics remain outside this algebraic bridge owner.
-/

namespace InfoGeometry.Canonical.GaloisQuotientDihedralL8ClosureBridge

open scoped Matrix
open InfoGeometry.Canonical.TwelveFoldCyclotomicNative
open InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets
open InfoGeometry.Canonical.FiniteCharacterMatrixOrder
open GaloisQuotientNonAbelianFourierPoset

-- ============================================================================
-- OBLIGATION L8(a): Cyclotomic-12 Galois Action & ZMod 12 Harmonic Orbits
-- ============================================================================

/-- The Galois orbit of a harmonic frequency `k : ZMod 12` under the multiplicative unit group
`(ZMod 12)ˣ` via `galoisPower`. -/
def z12HarmonicOrbit (k : ZMod 12) : Finset (ZMod 12) :=
  (Finset.univ : Finset (ZMod 12)ˣ).image (fun u => galoisPower u k)

/--
**Theorem L8(a) (`cyclotomic12_galois_unit_action_and_zmod12_harmonic_orbits`):**
1. Every Galois automorphism `σ : Gal(CyclotomicField 12 ℚ / ℚ)` acts on the `k`-th harmonic power
   `ζ ^ k` of any twelfth root of unity `ζ : CyclotomicField 12 ℚ` (`ζ ^ 12 = 1`) via the unit power
   `σ (ζ ^ k) = (ζ ^ k) ^ (cyclotomic12_galEquivUnits σ).val.val`.
2. On `ZMod 12`, the multiplicative action `galoisPower` of `(ZMod 12)ˣ` partitions the 12 frequencies
   into six exact divisor-order orbits `{0}`, `{6}`, `{4, 8}`, `{3, 9}`, `{2, 10}`, and `{1, 5, 7, 11}`
   whose cardinalities equal `φ(1), φ(2), φ(3), φ(4), φ(6), φ(12)` and whose union is `Finset.univ`.
3. Under `sigma5`, `1 ↔ 5` swap while `3` and `6` are fixed.
-/
theorem cyclotomic12_galois_unit_action_and_zmod12_harmonic_orbits
    (σ : Gal(CyclotomicField 12 ℚ / ℚ))
    {ζ : CyclotomicField 12 ℚ} (hζ12 : ζ ^ 12 = 1) (k : ℕ) :
    σ (ζ ^ k) = (ζ ^ k) ^ (cyclotomic12_galEquivUnits σ).val.val ∧
    (z12HarmonicOrbit 0 = {0} ∧
     z12HarmonicOrbit 6 = {6} ∧
     z12HarmonicOrbit 4 = {4, 8} ∧
     z12HarmonicOrbit 3 = {3, 9} ∧
     z12HarmonicOrbit 2 = {2, 10} ∧
     z12HarmonicOrbit 1 = {1, 5, 7, 11}) ∧
    (z12HarmonicOrbit 0).card = Nat.totient 1 ∧
    (z12HarmonicOrbit 6).card = Nat.totient 2 ∧
    (z12HarmonicOrbit 4).card = Nat.totient 3 ∧
    (z12HarmonicOrbit 3).card = Nat.totient 4 ∧
    (z12HarmonicOrbit 2).card = Nat.totient 6 ∧
    (z12HarmonicOrbit 1).card = Nat.totient 12 ∧
    (z12HarmonicOrbit 0 ∪ z12HarmonicOrbit 6 ∪ z12HarmonicOrbit 4 ∪
     z12HarmonicOrbit 3 ∪ z12HarmonicOrbit 2 ∪ z12HarmonicOrbit 1 = Finset.univ) ∧
    (galoisPower sigma5 1 = 5 ∧ galoisPower sigma5 5 = 1 ∧
     galoisPower sigma5 3 = 3 ∧ galoisPower sigma5 6 = 6) := by
  have hpow12 : (ζ ^ k) ^ 12 = 1 := by
    rw [← pow_mul, mul_comm k 12, pow_mul, hζ12, one_pow]
  have hGal : σ (ζ ^ k) = (ζ ^ k) ^ (cyclotomic12_galEquivUnits σ).val.val :=
    cyclotomic12_gal_action_on_twelfth_root σ hpow12
  exact ⟨hGal, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

-- ============================================================================
-- OBLIGATION L8(b): Ramanujan Orbit-Trace Integrality & Möbius Formula
-- ============================================================================

/--
**Theorem L8(b) (`cyclotomic12_orbit_trace_eq_ramanujan_moebius`):**
Over any commutative ring `R`, let `ζ : R` satisfy the twelfth cyclotomic polynomial
`ζ ^ 4 - ζ ^ 2 + 1 = 0`. Then `ζ ^ 6 = -1` and `ζ ^ 12 = 1`, and the Galois orbit sums across
the six divisor shells `d ∈ {1, 2, 3, 4, 6, 12}` evaluate at the fundamental step `x = 1` and
second harmonic step `x = 2` to the exact integer Möbius Ramanujan sums `(ramanujanSum12 d x : R)`:
- Shell `d = 1` (`{0}`): `ζ ^ 0 = (ramanujanSum12 1 1 : R) = 1`,
- Shell `d = 2` (`{6}`): `ζ ^ 6 = (ramanujanSum12 2 1 : R) = -1`,
- Shell `d = 3` (`{4, 8}`): `ζ ^ 4 + ζ ^ 8 = (ramanujanSum12 3 1 : R) = -1`,
- Shell `d = 4` (`{3, 9}`): `ζ ^ 3 + ζ ^ 9 = (ramanujanSum12 4 1 : R) = 0`,
- Shell `d = 6` (`{2, 10}`): `ζ ^ 2 + ζ ^ 10 = (ramanujanSum12 6 1 : R) = 1`,
- Shell `d = 12` (`{1, 5, 7, 11}`):
  - at `x = 1`: `ζ ^ 1 + ζ ^ 5 + ζ ^ 7 + ζ ^ 11 = (ramanujanSum12 12 1 : R) = 0`,
  - at `x = 2`: `ζ ^ 2 + ζ ^ 10 + ζ ^ 14 + ζ ^ 22 = (ramanujanSum12 12 2 : R) = 2`,
  - at `x = 3`: `ζ ^ 3 + ζ ^ 15 + ζ ^ 21 + ζ ^ 33 = (ramanujanSum12 12 3 : R) = 0`,
  - at `x = 4`: `ζ ^ 4 + ζ ^ 20 + ζ ^ 28 + ζ ^ 44 = (ramanujanSum12 12 4 : R) = -2`,
  - at `x = 6`: `ζ ^ 6 + ζ ^ 30 + ζ ^ 42 + ζ ^ 66 = (ramanujanSum12 12 6 : R) = -4`.
-/
theorem cyclotomic12_orbit_trace_eq_ramanujan_moebius
    {R : Type*} [CommRing R] (ζ : R) (hζ : ζ ^ 4 - ζ ^ 2 + 1 = 0) :
    ζ ^ 6 = -1 ∧
    ζ ^ 12 = 1 ∧
    (ζ ^ 0 = (ramanujanSum12 1 1 : R) ∧
     ζ ^ 6 = (ramanujanSum12 2 1 : R) ∧
     ζ ^ 4 + ζ ^ 8 = (ramanujanSum12 3 1 : R) ∧
     ζ ^ 3 + ζ ^ 9 = (ramanujanSum12 4 1 : R) ∧
     ζ ^ 2 + ζ ^ 10 = (ramanujanSum12 6 1 : R) ∧
     ζ ^ 1 + ζ ^ 5 + ζ ^ 7 + ζ ^ 11 = (ramanujanSum12 12 1 : R)) ∧
    (ζ ^ 2 + ζ ^ 10 + ζ ^ 14 + ζ ^ 22 = (ramanujanSum12 12 2 : R) ∧
     ζ ^ 3 + ζ ^ 15 + ζ ^ 21 + ζ ^ 33 = (ramanujanSum12 12 3 : R) ∧
     ζ ^ 4 + ζ ^ 20 + ζ ^ 28 + ζ ^ 44 = (ramanujanSum12 12 4 : R) ∧
     ζ ^ 6 + ζ ^ 30 + ζ ^ 42 + ζ ^ 66 = (ramanujanSum12 12 6 : R)) := by
  have h6 : ζ ^ 6 = -1 := by linear_combination (ζ ^ 2 + 1) * hζ
  have hr1 : ramanujanSum12 1 1 = 1 := by decide
  have hr2 : ramanujanSum12 2 1 = -1 := by decide
  have hr3 : ramanujanSum12 3 1 = -1 := by decide
  have hr4 : ramanujanSum12 4 1 = 0 := by decide
  have hr6 : ramanujanSum12 6 1 = 1 := by decide
  have hr12_1 : ramanujanSum12 12 1 = 0 := by decide
  have hr12_2 : ramanujanSum12 12 2 = 2 := by decide
  have hr12_3 : ramanujanSum12 12 3 = 0 := by decide
  have hr12_4 : ramanujanSum12 12 4 = -2 := by decide
  have hr12_6 : ramanujanSum12 12 6 = -4 := by decide
  rw [hr1, hr2, hr3, hr4, hr6, hr12_1, hr12_2, hr12_3, hr12_4, hr12_6]
  norm_num
  refine ⟨h6,
          by linear_combination (ζ ^ 6 - 1) * h6,
          ⟨h6,
           by linear_combination hζ + (ζ ^ 2) * h6,
           by linear_combination (ζ ^ 3) * h6,
           by linear_combination -hζ + (ζ ^ 4) * h6,
           by linear_combination (ζ + ζ ^ 5) * h6⟩,
          ⟨by linear_combination -2 * hζ + (2 * ζ ^ 4 + (ζ ^ 6 - 1) * (ζ ^ 2 + ζ ^ 10)) * h6,
           by linear_combination ((ζ ^ 3 + ζ ^ 15) * (ζ ^ 12 - ζ ^ 6 + 1)) * h6,
           by linear_combination 2 * hζ +
                (ζ ^ 2 * (ζ ^ 12 - ζ ^ 6 + 1) +
                 ζ ^ 4 * (ζ ^ 18 - ζ ^ 12 + ζ ^ 6 - 1) +
                 ζ ^ 2 * (ζ ^ 36 - ζ ^ 30 + ζ ^ 24 - ζ ^ 18 + ζ ^ 12 - ζ ^ 6 + 1)) * h6,
           by linear_combination
                (1 + (ζ ^ 24 - ζ ^ 18 + ζ ^ 12 - ζ ^ 6 + 1) +
                 (ζ ^ 36 - ζ ^ 30 + ζ ^ 24 - ζ ^ 18 + ζ ^ 12 - ζ ^ 6 + 1) +
                 (ζ ^ 60 - ζ ^ 54 + ζ ^ 48 - ζ ^ 42 + ζ ^ 36 - ζ ^ 30 +
                  ζ ^ 24 - ζ ^ 18 + ζ ^ 12 - ζ ^ 6 + 1)) * h6⟩⟩

-- ============================================================================
-- OBLIGATION L8(c): Explicit Dihedral Representation & 2×2 Peirce Carrier Map
-- ============================================================================

/-- Concrete upper-left idempotent `P = !![1, 0; 0, 0]` in `Matrix (Fin 2) (Fin 2) R`. -/
def peirceMatP {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 0]

/-- Concrete upper-right matrix unit `X = !![0, 1; 0, 0]` in `Matrix (Fin 2) (Fin 2) R`. -/
def peirceMatX {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- Concrete lower-left matrix unit `Y = !![0, 0; 1, 0]` in `Matrix (Fin 2) (Fin 2) R`. -/
def peirceMatY {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- Concrete diagonal grading reflection `S_P = !![1, 0; 0, -1]` in `Matrix (Fin 2) (Fin 2) R`. -/
def peirceMatS {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- Concrete symplectic/complex generator `J₁ = !![0, 1; -1, 0]` in `Matrix (Fin 2) (Fin 2) R`. -/
def peirceMatJ {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, 0]

/-- Anticommutator witness `S_P * J₁ + J₁ * S_P = 0` in `Matrix (Fin 2) (Fin 2) R`. -/
lemma peirceMatS_anticomm_peirceMatJ {R : Type*} [CommRing R] :
    peirceMatS (R := R) * peirceMatJ (R := R) +
      peirceMatJ (R := R) * peirceMatS (R := R) = 0 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [peirceMatS, peirceMatJ]

/-- The four cyclic powers `J₁^k` (`k : ZMod 4`) in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def peirceRotation4Power (i : ZMod 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  if i = 0 then !![1, 0; 0, 1]
  else if i = 1 then !![0, 1; -1, 0]
  else if i = 2 then !![-1, 0; 0, -1]
  else !![0, -1; 1, 0]

/-- Explicit dihedral group representation `DihedralGroup 4 →* Matrix (Fin 2) (Fin 2) ℤ`
into the concrete `2 × 2` Peirce matrix carrier, sending `.r i` to `peirceRotation4Power i`
and `.sr i` to `peirceGradingS * peirceRotation4Power i`. -/
def dihedral4PeirceMatrixRep :
    DihedralGroup 4 →* Matrix (Fin 2) (Fin 2) ℤ where
  toFun
    | .r i => peirceRotation4Power i
    | .sr i => peirceGradingS * peirceRotation4Power i
  map_one' := by decide
  map_mul' x y := by
    cases x with
    | r i =>
      cases y with
      | r j => fin_cases i <;> fin_cases j <;> decide
      | sr j => fin_cases i <;> fin_cases j <;> decide
    | sr i =>
      cases y with
      | r j => fin_cases i <;> fin_cases j <;> decide
      | sr j => fin_cases i <;> fin_cases j <;> decide

/--
**Theorem L8(c) (`peirce_matrix_carrier_compatibility_and_dihedral_inversion`):**
Proves the compatibility map between the abstract Peirce operators (`invS`, `genPhi`, `genJ`, `Rotor2D`)
evaluated on `(peirceMatP, peirceMatX, peirceMatY)` in `Matrix (Fin 2) (Fin 2)` and the concrete
matrix representation `dihedral4PeirceMatrixRep`:
1. `peirceMatP * peirceMatP = peirceMatP`,
2. `invS peirceMatP = peirceGradingS = dihedral4PeirceMatrixRep (.sr 0)`,
3. `genPhi peirceMatP peirceMatX peirceMatY = peirceSwapPhi = dihedral4PeirceMatrixRep (.sr 1)`,
4. `genJ peirceMatP peirceMatX peirceMatY = peirceMatJ = dihedral4PeirceMatrixRep (.r 1)`,
5. Over any `[CommRing R]`, `Rotor2D peirceMatP peirceMatX peirceMatY (c • 1) (s • 1) = !![c, s; -s, c]`,
6. For every `i : ZMod 4`, conjugating `dihedral4PeirceMatrixRep (.r i)` by the reflection
   `dihedral4PeirceMatrixRep (.sr 0)` inverts the rotation to `dihedral4PeirceMatrixRep (.r (-i))`.
-/
theorem peirce_matrix_carrier_compatibility_and_dihedral_inversion
    {R : Type*} [CommRing R] (c s : R) (i : ZMod 4) :
    peirceMatP (R := ℤ) * peirceMatP (R := ℤ) = peirceMatP (R := ℤ) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.invS (peirceMatP (R := ℤ)) =
      peirceGradingS (K := ℤ) ∧
    dihedral4PeirceMatrixRep (.sr 0) = peirceGradingS (K := ℤ) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi (peirceMatP (R := ℤ)) peirceMatX peirceMatY =
      peirceSwapPhi (K := ℤ) ∧
    dihedral4PeirceMatrixRep (.sr 1) = peirceSwapPhi (K := ℤ) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genJ (peirceMatP (R := ℤ)) peirceMatX peirceMatY =
      peirceMatJ (R := ℤ) ∧
    dihedral4PeirceMatrixRep (.r 1) = peirceMatJ (R := ℤ) ∧
    GaloisQuotientNonAbelianFourierPoset.Rotor2D
        (peirceMatP (R := R)) peirceMatX peirceMatY (c • 1) (s • 1) =
      !![c, s; -s, c] ∧
    dihedral4PeirceMatrixRep (.sr 0) *
        dihedral4PeirceMatrixRep (.r i) *
        dihedral4PeirceMatrixRep (.sr 0) =
      dihedral4PeirceMatrixRep (.r (-i)) := by
  have hJ :
      InfoGeometry.OperatorAlgebra.PeirceSpine.genJ
          (peirceMatP (R := R)) peirceMatX peirceMatY =
        peirceMatJ (R := R) := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
        peirceMatP, peirceMatX, peirceMatY, peirceMatJ,
        Matrix.sub_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      norm_num
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · rw [GaloisQuotientNonAbelianFourierPoset.Rotor2D, hJ, smul_mul_assoc, one_mul]
    ext a b; fin_cases a <;> fin_cases b <;> simp [peirceMatJ]
  · fin_cases i <;> decide

-- ============================================================================
-- OBLIGATION L8(d): Concrete Subgroup-Average Projector & Nonvanishing Variance
-- ============================================================================

/-- Concrete `ℤ₂`-subgroup-averaging projector `P_H = ½(I₂ + Φ₁) = !![half, half; half, half]`
in `Matrix (Fin 2) (Fin 2) K` for the reflection subgroup `H = {I₂, Φ₁}`. -/
def z2SubgroupAverageProjector {K : Type*} [CommRing K] (half : K) : Matrix (Fin 2) (Fin 2) K :=
  !![half, half; half, half]

/-- The range of the two-term involution average is exactly the fixed subspace
of the swap involution. This identifies the quotient carrier represented by
`z2SubgroupAverageProjector` on vectors, not just by an idempotent equation. -/
theorem z2Average_fixedVectors_iff
    {K : Type*} [CommRing K] (half : K) (h2 : (2 : K) * half = 1)
    (v : Fin 2 → K) :
    Matrix.mulVec (z2SubgroupAverageProjector half) v = v ↔
      Matrix.mulVec (peirceSwapPhi (K := K)) v = v := by
  have hAvg : z2SubgroupAverageProjector half =
      half • ((1 : Matrix (Fin 2) (Fin 2) K) + peirceSwapPhi (K := K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [z2SubgroupAverageProjector, peirceSwapPhi]
  have hPhiP : peirceSwapPhi (K := K) * z2SubgroupAverageProjector half =
      z2SubgroupAverageProjector half := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [z2SubgroupAverageProjector, peirceSwapPhi, Matrix.mul_apply,
        Fin.sum_univ_two]
  constructor
  · intro hv
    calc
      Matrix.mulVec (peirceSwapPhi (K := K)) v =
          Matrix.mulVec (peirceSwapPhi (K := K))
            (Matrix.mulVec (z2SubgroupAverageProjector half) v) := by rw [hv]
      _ = Matrix.mulVec
          (peirceSwapPhi (K := K) * z2SubgroupAverageProjector half) v := by
            rw [Matrix.mulVec_mulVec]
      _ = v := by rw [hPhiP, hv]
  · intro hv
    rw [hAvg]
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hv]
    have hhalf : half + half = 1 := by simpa [two_mul] using h2
    ext i
    calc
      half * (v i + v i) = (half + half) * v i := by ring
      _ = v i := by rw [hhalf, one_mul]

/--
**Theorem L8(d) (`z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance`):**
For any commutative ring `K` and `half : K` satisfying `(2 : K) * half = 1`:
1. **Subgroup Average Formula & Idempotence:**
   `z2SubgroupAverageProjector half = half • (1 + peirceSwapPhi)` and
   `P_H * P_H = P_H`.
2. **Concrete Macro-Character (`peirceSwapPhi`):**
   `peirceSwapPhi * peirceSwapPhi = 1` and `P_H * peirceSwapPhi * P_H = peirceSwapPhi * P_H`.
3. **Concrete Micro-Character (`peirceGradingS`):**
   `peirceGradingS * peirceGradingS = 1` and `P_H * peirceGradingS * P_H = 0`.
4. **Quotient Surprisal 1st-Order Annihilation & 2nd-Order Variance Survival:**
   For `L = SurprisalOp (u_bar • 1) (delta_u • 1) peirceGradingS`:
   - `P_H * L * P_H = u_bar • P_H`,
   - `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) • P_H`.
5. **Certified Nonvanishing:**
   Whenever `delta_u * delta_u * half ≠ 0`, the second-order quotient variance defect is
   strictly nonzero: `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) ≠ 0`.
-/
theorem z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance
    {K : Type*} [CommRing K] (half u_bar delta_u : K)
    (h2 : (2 : K) * half = 1) :
    let P_H := z2SubgroupAverageProjector half
    let L := GaloisQuotientNonAbelianFourierPoset.SurprisalOp
      (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
      (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
      (peirceGradingS (K := K))
    P_H = half • ((1 : Matrix (Fin 2) (Fin 2) K) + peirceSwapPhi (K := K)) ∧
    P_H * P_H = P_H ∧
    (peirceSwapPhi (K := K) * peirceSwapPhi (K := K) = 1 ∧
     P_H * peirceSwapPhi (K := K) * P_H = peirceSwapPhi (K := K) * P_H) ∧
    (peirceGradingS (K := K) * peirceGradingS (K := K) = 1 ∧
     P_H * peirceGradingS (K := K) * P_H = 0) ∧
    (P_H * L * P_H = u_bar • P_H ∧
     P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) =
       (delta_u * delta_u) • P_H ∧
     (delta_u * delta_u * half ≠ 0 →
       P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) ≠ 0)) := by
  have hAvg :
      z2SubgroupAverageProjector half =
        half • ((1 : Matrix (Fin 2) (Fin 2) K) + peirceSwapPhi (K := K)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [z2SubgroupAverageProjector, peirceSwapPhi]
  have hPH : z2SubgroupAverageProjector half * z2SubgroupAverageProjector half =
      z2SubgroupAverageProjector half := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z2SubgroupAverageProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination half * h2
  have hPhi2 : peirceSwapPhi (K := K) * peirceSwapPhi (K := K) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [peirceSwapPhi]
  have hMacro :
      z2SubgroupAverageProjector half * peirceSwapPhi (K := K) * z2SubgroupAverageProjector half =
        peirceSwapPhi (K := K) * z2SubgroupAverageProjector half := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z2SubgroupAverageProjector, peirceSwapPhi, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination half * h2
  have hS2 : peirceGradingS (K := K) * peirceGradingS (K := K) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [peirceGradingS]
  have hMicro :
      z2SubgroupAverageProjector half * peirceGradingS (K := K) * z2SubgroupAverageProjector half = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [z2SubgroupAverageProjector, peirceGradingS, Matrix.mul_apply, Fin.sum_univ_two]
  have hGen :=
    (GaloisQuotientNonAbelianFourierPoset.quotient_surprisal_normal_form_and_second_order_survival
      (z2SubgroupAverageProjector half)
      (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
      (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
      (peirceGradingS (K := K))
      hPH hS2
      (by simp)
      (by simp)
      (by simp [smul_smul, mul_comm])
      (by simp)
      (by simp)).2 hMicro
  have h1st :
      z2SubgroupAverageProjector half *
          GaloisQuotientNonAbelianFourierPoset.SurprisalOp
            (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
            (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
            (peirceGradingS (K := K)) *
          z2SubgroupAverageProjector half =
        u_bar • z2SubgroupAverageProjector half := by
    simpa [smul_mul_assoc, one_mul] using hGen.1
  have h2nd :
      z2SubgroupAverageProjector half *
          (GaloisQuotientNonAbelianFourierPoset.SurprisalOp
            (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
            (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
            (peirceGradingS (K := K)) *
           GaloisQuotientNonAbelianFourierPoset.SurprisalOp
            (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
            (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
            (peirceGradingS (K := K))) *
          z2SubgroupAverageProjector half -
        (z2SubgroupAverageProjector half *
          GaloisQuotientNonAbelianFourierPoset.SurprisalOp
            (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
            (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
            (peirceGradingS (K := K)) *
          z2SubgroupAverageProjector half) *
        (z2SubgroupAverageProjector half *
          GaloisQuotientNonAbelianFourierPoset.SurprisalOp
            (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
            (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
            (peirceGradingS (K := K)) *
          z2SubgroupAverageProjector half) =
        (delta_u * delta_u) • z2SubgroupAverageProjector half := by
    simpa [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul] using hGen.2
  refine ⟨hAvg, hPH, ⟨hPhi2, hMacro⟩, ⟨hS2, hMicro⟩, ⟨h1st, h2nd, ?_⟩⟩
  intro hNonzero hZero
  rw [h2nd] at hZero
  have h00 := congr_fun (congr_fun hZero 0) 0
  simp [z2SubgroupAverageProjector] at h00
  exact hNonzero h00

/-- On the subspace fixed by the swap involution, the quotient variance operator
acts by the scalar square of the microscopic slope. This combines the explicit
matrix projector with the quotient-compression identity. -/
theorem z2_quotient_variance_acts_as_scalar_on_fixed_vectors
    {K : Type*} [CommRing K] (half u_bar delta_u : K)
    (h2 : (2 : K) * half = 1) (v : Fin 2 → K)
    (hv : Matrix.mulVec (peirceSwapPhi (K := K)) v = v) :
    let P_H := z2SubgroupAverageProjector half
    let L := GaloisQuotientNonAbelianFourierPoset.SurprisalOp
      (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
      (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
      (peirceGradingS (K := K))
    Matrix.mulVec
      (P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H)) v =
        (delta_u * delta_u) • v := by
  let P_H := z2SubgroupAverageProjector half
  let L := GaloisQuotientNonAbelianFourierPoset.SurprisalOp
    (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
    (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
    (peirceGradingS (K := K))
  have hProj := z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance
    half u_bar delta_u h2
  rcases hProj with ⟨_, _, _, _, ⟨_, ⟨hVariance, _⟩⟩⟩
  have hFixed := (z2Average_fixedVectors_iff half h2 v).2 hv
  change Matrix.mulVec
    (z2SubgroupAverageProjector half *
      (GaloisQuotientNonAbelianFourierPoset.SurprisalOp
        (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
        (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
        (peirceGradingS (K := K)) *
       GaloisQuotientNonAbelianFourierPoset.SurprisalOp
        (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
        (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
        (peirceGradingS (K := K))) *
      z2SubgroupAverageProjector half -
      (z2SubgroupAverageProjector half *
        GaloisQuotientNonAbelianFourierPoset.SurprisalOp
          (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
          (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
          (peirceGradingS (K := K)) *
        z2SubgroupAverageProjector half) *
      (z2SubgroupAverageProjector half *
        GaloisQuotientNonAbelianFourierPoset.SurprisalOp
          (u_bar • (1 : Matrix (Fin 2) (Fin 2) K))
          (delta_u • (1 : Matrix (Fin 2) (Fin 2) K))
          (peirceGradingS (K := K)) *
        z2SubgroupAverageProjector half)) v =
      (delta_u * delta_u) • v
  rw [hVariance, Matrix.smul_mulVec, hFixed]

end InfoGeometry.Canonical.GaloisQuotientDihedralL8ClosureBridge
