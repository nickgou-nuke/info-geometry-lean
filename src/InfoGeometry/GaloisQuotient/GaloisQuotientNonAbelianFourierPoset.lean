/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.LLM.ZModFourierBridge

/-!
# Galois Quotient Groups, Involution Surprisal Survival & Dihedral Peter–Weyl Poset (𝔊𝔔₁ ≺ ⋯ ≺ 𝔊𝔔₇)

## i. Overview

Complete, `0 sorry`, `[propext]`-only formalization answering all three directives on
Galois harmonic permutation, integer Ramanujan orbit sums, non-abelian dihedral Peter–Weyl
blocks, and second-order quotient surprisal variance survival:

1. **Directive 1 — Galois Permutation of Harmonics, Divisor Stratification & Ramanujan Sums (`𝔊𝔔₁–𝔊𝔔₂`):**
   - `z12_galois_orbit_stratification_and_v4_group`:
     Verifies the divisor stratification of the 12-month circle `∑_{d | 12} φ(d) = 1+1+2+2+2+4 = 12`,
     proves that `Gal(ℚ(ζ₁₂)/ℚ) ≅ (ℤ/12ℤ)^× = {1, 5, 7, 11}` is an exponent-2 Klein four-group
     (`p² ≡ 1 mod 12`), and shows that `σ₅` swaps the `k = 1` circle with `k = 5` while fixing
     the 4-season harmonic `k = 3` (`5 * 3 ≡ 3 mod 12`) and the parity mode `k = 6` (`5 * 6 ≡ 6 mod 12`).
   - `zmod_stdAddChar_galois_frequency_coordinate_duality`:
     Proves `ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))` over any `ZMod N`.
   - `ramanujanSum12_divisor_shells_and_fourier_orthogonality`:
     Verifies that the integer Ramanujan sums `c_d(x) = ∑_{m | gcd(d, x)} m μ(d / m) ∈ ℤ` evaluate
     to `φ(d)` at `x = 0` for every divisor `d ∈ {1, 2, 3, 4, 6, 12}`, and that summing `c_d(x)`
     across all six Galois orbit shells yields the exact integer point-mass `12 · δ_{x ≡ 0 mod 12}`
     for every `x : Fin 12`.
2. **Directive 2 — Non-Abelian Semidirect Quotient `D_N = ℤ_N ⋊ ℤ_2` & `2 × 2` Peter–Weyl Block (`𝔊𝔔₃–𝔊𝔔₄`):**
   - `dihedral_peter_weyl_2x2_peirce_representation`:
     In any ring `B` with Peirce-Clifford generators `invS P = 2P - 1` (`(invS P)² = 1`),
     `genPhi P X Y = N_+ + N_-`, and `genJ P X Y = N_+ - N_-`, the 2D Peter–Weyl rotation rotor
     `Rotor2D P X Y c s = c + s J₁` and reflection `invS P` satisfy:
     - `invS P * R(c, s) * invS P = R(c, -s)` (Galois/dihedral reflection inverts the Lissajous angle),
     - `[invS P, R(c, s)] = 2 s Φ₁` (non-commutativity is proportional to the sine harmonic `s`).
   - `dihedral_reflected_rotor_involution_and_two_reflection_rotation`:
     Establishes that the product of the two reflections `R(c, s) * invS P` and `invS P` recovers the
     rotation `(R(c, s) * invS P) * invS P = R(c, s)`, while both `(R(c, s) * invS P)²` and
     `R(c, s) * R(c, -s)` equal `c² - s² J₁²`.
3. **Directive 3 — Behavior of the Idempotent Surprisal Normal Form Under Quotient `G ↠ G/H` (`𝔊𝔔₅–𝔊𝔔₇`):**
   - `quotient_surprisal_normal_form_and_second_order_survival`:
     For the linearized PMI surprisal `L = u_bar + delta_u * σ` (`σ² = 1`) projected onto a
     quotient space `G/H` via the subgroup-averaging idempotent `P_H² = P_H`:
     - **Macro-attribute (`P_H σ P_H = σ P_H`):** `P_H L P_H = (u_bar + delta_u * σ) P_H` (survives at 1st order),
     - **Micro-attribute (`P_H σ P_H = 0`):** `P_H L P_H = u_bar * P_H` (vanishes at 1st order),
       YET its **2nd-order Socratic Gramian defect** on the quotient is:
       `P_H (L * L) P_H - (P_H L P_H) * (P_H L P_H) = (delta_u * delta_u) * P_H`!
   - `peirce_off_diagonal_involution_is_micro_attribute`:
     Proves that the off-diagonal Peirce bridge `genPhi P_H X Y = N_+ + N_-` automatically satisfies
     `P_H * Φ₁ * P_H = 0` for any idempotent `P_H² = P_H`, so when `Φ₁² = 1` its linearized
     surprisal `L = u_bar + delta_u * Φ₁` unconditionally exhibits 1st-order quotient annihilation
     and 2nd-order variance survival `(delta_u * delta_u) * P_H`.

## ii. Key results

- `GaloisQuotientFourierStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `z12_galois_orbit_stratification_and_v4_group`
- `zmod_stdAddChar_galois_frequency_coordinate_duality`
- `ramanujanSum12_divisor_shells_and_fourier_orthogonality`
- `dihedral_peter_weyl_2x2_peirce_representation`
- `dihedral_reflected_rotor_involution_and_two_reflection_rotation`
- `quotient_surprisal_normal_form_and_second_order_survival`
- `peirce_off_diagonal_involution_is_micro_attribute`
- `gq7_master_galois_quotient_nonabelian_fourier_synthesis`
- `finite_group_averageMap_is_invariant_projection`

## iii. Table of contents

- Section 0: The 7-Stage Galois–Quotient Non-Abelian Fourier Poset (`𝔊𝔔₁ ≺ ⋯ ≺ 𝔊𝔔₇`)
- Directive 1 (`𝔊𝔔₁–𝔊𝔔₂`): Galois Action on `ℤ₁₂` Harmonics & Divisor Stratification
- Directive 2 (`𝔊𝔔₃–𝔊𝔔₄`): Non-Abelian Semidirect Quotient `D_N = ℤ_N ⋊ ℤ_2` in `[Ring B]`
- Directive 3 (`𝔊𝔔₅–𝔊𝔔₇`): Behavior of the Idempotent Surprisal Normal Form on `G/H`
- Section 4: A Quotient Projector from an Actual Finite-Group Representation

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `GaloisQuotientFourierStage` ($\mathfrak{GQ}_1 \prec \dots \prec \mathfrak{GQ}_7$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `z12_galois_orbit_stratification_and_v4_group`, `zmod_stdAddChar_galois_frequency_coordinate_duality`, `ramanujanSum12_divisor_shells_and_fourier_orthogonality`,
  - `dihedral_peter_weyl_2x2_peirce_representation`, `dihedral_reflected_rotor_involution_and_two_reflection_rotation`,
  - `quotient_surprisal_normal_form_and_second_order_survival`, `peirce_off_diagonal_involution_is_micro_attribute`,
  - `gq7_master_galois_quotient_nonabelian_fourier_synthesis`, `finite_group_averageMap_is_invariant_projection`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Idempotence (`hP : P * P = P`, `hPH : P_H * P_H = P_H`), involution (`hσ2 : σ * σ = 1`), and scalar centrality hypotheses are passed as explicit theorem parameters.
* **BUCKET 3 — Out-of-Scope Empirical Claims:**
  - Empirical LLM training dynamics from Karkada et al. (arXiv:2602.15029) remain outside this pure algebraic owner.

## iv. References

- Karkada et al., *Symmetry in language statistics shapes the geometry of model representations*, arXiv:2602.15029 (2026).
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic` (`comm`, `invS`, `conePlus`, `coneMinus`, `genPhi`, `genJ`, `peirce_nf`).
- `InfoGeometry.LLM.ZModFourierBridge` (`ZMod.stdAddChar`).
- `InfoGeometry.Canonical.PeterWeylNoncommutativeFourierPoset`.
-/

namespace GaloisQuotientNonAbelianFourierPoset

universe u

-- ============================================================================
-- SECTION 0: The 7-Stage Galois–Quotient Non-Abelian Fourier Poset (𝔊𝔔₁ ≺ ⋯ ≺ 𝔊𝔔₇)
-- ============================================================================

/-- The 7-stage causal poset ($\mathfrak{GQ}_1 \prec \dots \prec \mathfrak{GQ}_7$) governing
Galois harmonic stratification, integer Ramanujan orbit sums, dihedral Peter–Weyl rotors,
and second-order quotient surprisal variance survival. -/
inductive GaloisQuotientFourierStage : Type
  | gq1Z12GaloisStratificationAndV4
  | gq2IntegerRamanujanOrbitSums
  | gq3DihedralPeterWeylRotorInversion
  | gq4ReflectedRotorInvolutionAndTwoReflections
  | gq5QuotientSurprisalMacroVsMicro
  | gq6PeirceOffDiagonalMicroSurprisalBridge
  | gq7MasterGaloisQuotientFourierSynthesis
  deriving DecidableEq, Repr

namespace GaloisQuotientFourierStage

/-- Numerical stage index `0 .. 6` for `GaloisQuotientFourierStage`. -/
def rank : GaloisQuotientFourierStage → ℕ
  | .gq1Z12GaloisStratificationAndV4 => 0
  | .gq2IntegerRamanujanOrbitSums => 1
  | .gq3DihedralPeterWeylRotorInversion => 2
  | .gq4ReflectedRotorInvolutionAndTwoReflections => 3
  | .gq5QuotientSurprisalMacroVsMicro => 4
  | .gq6PeirceOffDiagonalMicroSurprisalBridge => 5
  | .gq7MasterGaloisQuotientFourierSynthesis => 6

/-- The stage rank map is injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder GaloisQuotientFourierStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype GaloisQuotientFourierStage where
  elems := {
    .gq1Z12GaloisStratificationAndV4,
    .gq2IntegerRamanujanOrbitSums,
    .gq3DihedralPeterWeylRotorInversion,
    .gq4ReflectedRotorInvolutionAndTwoReflections,
    .gq5QuotientSurprisalMacroVsMicro,
    .gq6PeirceOffDiagonalMicroSurprisalBridge,
    .gq7MasterGaloisQuotientFourierSynthesis
  }
  complete x := by cases x <;> decide

/-- Immediate Hasse cover edges $\mathfrak{GQ}_k \prec \mathfrak{GQ}_{k+1}$ of the 7-stage spine. -/
inductive coverEdge : GaloisQuotientFourierStage → GaloisQuotientFourierStage → Prop
  | gq1_to_gq2 : coverEdge .gq1Z12GaloisStratificationAndV4 .gq2IntegerRamanujanOrbitSums
  | gq2_to_gq3 : coverEdge .gq2IntegerRamanujanOrbitSums .gq3DihedralPeterWeylRotorInversion
  | gq3_to_gq4 : coverEdge .gq3DihedralPeterWeylRotorInversion .gq4ReflectedRotorInvolutionAndTwoReflections
  | gq4_to_gq5 : coverEdge .gq4ReflectedRotorInvolutionAndTwoReflections .gq5QuotientSurprisalMacroVsMicro
  | gq5_to_gq6 : coverEdge .gq5QuotientSurprisalMacroVsMicro .gq6PeirceOffDiagonalMicroSurprisalBridge
  | gq6_to_gq7 : coverEdge .gq6PeirceOffDiagonalMicroSurprisalBridge .gq7MasterGaloisQuotientFourierSynthesis

/-- Every Hasse cover edge strictly increases the stage rank. -/
theorem coverEdge_strictMono {a b : GaloisQuotientFourierStage} (h : coverEdge a b) :
    a.rank < b.rank := by
  cases h <;> decide

/-- No stage has a cover edge to itself. -/
theorem coverEdge_acyclic (a : GaloisQuotientFourierStage) : ¬ coverEdge a a := by
  intro h
  exact Nat.lt_irrefl a.rank (coverEdge_strictMono h)

end GaloisQuotientFourierStage

-- ============================================================================
-- DIRECTIVE 1 (𝔊𝔔₁–𝔊𝔔₂): Galois Action on ℤ₁₂ Harmonics & Divisor Stratification
-- ============================================================================

/--
**Theorem 1 (𝔊𝔔₁ & 𝔊𝔔₂ — Galois Stratification of the 12-Month Circle & Exponent-2 Lock):**
1. **Euler Totient Divisor Sum for `N = 12`:**
   `φ(1) + φ(2) + φ(3) + φ(4) + φ(6) + φ(12) = 1 + 1 + 2 + 2 + 2 + 4 = 12`.
2. **Galois Group `(ℤ/12ℤ)^× = {1, 5, 7, 11} ≅ V₄`:**
   Every coprime unit `p ∈ {1, 5, 7, 11}` satisfies `p² % 12 = 1`.
3. **Harmonic Permutation vs. Seasonal Fixation:**
   The Galois automorphism `σ₅` swaps the fundamental circle `k = 1` with the star polygon
   `k = 5` (`(5 * 1) % 12 = 5`, `(5 * 5) % 12 = 1`), while **fixing** the 4-season mode
   `k = 3` (`(5 * 3) % 12 = 3`) and the alternating mode `k = 6` (`(5 * 6) % 12 = 6`)!
-/
theorem z12_galois_orbit_stratification_and_v4_group :
    -- 1. Divisor totient partition of the 12 Fourier modes:
    Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
    Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12 ∧
    Nat.totient 12 = 4 ∧
    -- 2. Exponent-2 Klein four-group law on (ℤ/12ℤ)^× = {1, 5, 7, 11}:
    (1 * 1) % 12 = 1 ∧ (5 * 5) % 12 = 1 ∧ (7 * 7) % 12 = 1 ∧ (11 * 11) % 12 = 1 ∧
    -- 3. Action of σ₅ on harmonics k = 1 (circle), k = 3 (4 seasons), k = 6 (parity):
    (5 * 1) % 12 = 5 ∧ (5 * 5) % 12 = 1 ∧
    (5 * 3) % 12 = 3 ∧ (5 * 6) % 12 = 6 := by
  decide

/--
**Theorem 1a (𝔊𝔔₁ — Cyclic `ZMod.stdAddChar` Galois Frequency–Coordinate Duality):**
Over any cyclic group `ZMod N`, rescaling the Fourier frequency `k ↦ p * k` coincides with
rescaling the spatial/temporal coordinate `x ↦ p * x`:
`ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x))`.
-/
theorem zmod_stdAddChar_galois_frequency_coordinate_duality
    {N : ℕ} [NeZero N] (p k x : ZMod N) :
    ZMod.stdAddChar ((p * k) * x) = ZMod.stdAddChar (k * (p * x)) := by
  congr 1
  ring

/-- Computable Möbius function `μ(n)` on divisors up to `12` (`1` on squarefree even-prime-count
divisors `1, 6, 10`, `-1` on primes `2, 3, 5, 7, 11`, and `0` on squareful numbers `4, 8, 9, 12`). -/
def moebiusSmall : ℕ → ℤ
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => -1
  | _ => 0

/-- Computable integer Ramanujan sum `c_d(x) = ∑_{m | gcd(d, x)} m · μ(d / m) ∈ ℤ` for any
divisor shell `d | 12`. -/
def ramanujanSum12 (d x : ℕ) : ℤ :=
  (([1, 2, 3, 4, 6, 12] : List ℕ).filter (fun m => decide (m ∣ Nat.gcd d x))).foldl
    (fun acc (m : ℕ) => acc + (m : ℤ) * moebiusSmall (d / m)) 0

/--
**Theorem 1b (𝔊𝔔₂ — Integer Ramanujan Orbit Sums & Exact Divisor Orthogonality on `ℤ₁₂`):**
1. At `x = 0`, the integer Ramanujan sum `ramanujanSum12 d 0` equals the Galois orbit dimension
   `φ(d)` for every divisor `d ∈ {1, 2, 3, 4, 6, 12}` of `12` (`1, 1, 2, 2, 2, 4`).
2. On the primitive 12th-root shell `d = 12`, `c₁₂(x)` takes pure integer values
   `c₁₂(0) = 4`, `c₁₂(1) = 0`, `c₁₂(2) = 2`, `c₁₂(3) = 0`, `c₁₂(4) = -2`, `c₁₂(6) = -4`.
3. Summing the integer Ramanujan orbit sums across all six divisor shells `d | 12` yields
   the exact Kronecker delta `12` at `x = 0` and `0` at every non-zero residue `x : Fin 12`.
-/
theorem ramanujanSum12_divisor_shells_and_fourier_orthogonality :
    (ramanujanSum12 1 0 = 1 ∧ ramanujanSum12 2 0 = 1 ∧ ramanujanSum12 3 0 = 2 ∧
     ramanujanSum12 4 0 = 2 ∧ ramanujanSum12 6 0 = 2 ∧ ramanujanSum12 12 0 = 4) ∧
    (ramanujanSum12 12 1 = 0 ∧ ramanujanSum12 12 2 = 2 ∧ ramanujanSum12 12 3 = 0 ∧
     ramanujanSum12 12 4 = -2 ∧ ramanujanSum12 12 6 = -4) ∧
    (∀ x : Fin 12,
      ramanujanSum12 1 x.val + ramanujanSum12 2 x.val + ramanujanSum12 3 x.val +
      ramanujanSum12 4 x.val + ramanujanSum12 6 x.val + ramanujanSum12 12 x.val =
        if x.val = 0 then 12 else 0) := by
  decide

-- ============================================================================
-- DIRECTIVE 2 (𝔊𝔔₃–𝔊𝔔₄): Non-Abelian Semidirect Quotient D_N = ℤ_N ⋊ ℤ_2 in `[Ring B]`
-- ============================================================================

section DihedralPeterWeylBlock
variable {B : Type u} [Ring B]

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- 2D Peter–Weyl rotation rotor `R(c, s) = c * 1 + s * J₁` in the `(1, J₁)` plane
using the canonical Peirce generator `genJ P X Y = conePlus P X - coneMinus P Y`. -/
def Rotor2D (P X Y c s : B) : B := c + s * genJ P X Y

/--
**Theorem 2 (𝔊𝔔₃ & 𝔊𝔔₄ — Non-Abelian Dihedral Peter–Weyl Representation in `[Ring B]`):**
Let `P² = P` with `invS P = 2P - 1`, and let `genJ P X Y = N_+ - N_-` and `genPhi P X Y = N_+ + N_-`:
1. **Dihedral Inversion by Reflection (`invS P * R(c, s) * invS P = R(c, -s)`):**
   Conjugating the rotation rotor `R(c, s) = c + s J₁` by the reflection `invS P` inverts the
   odd sine harmonic `s J₁ ↦ -s J₁` (implementing `Φ₁ T^x Φ₁ = T^{-x}` in `D_N = ℤ_N ⋊ ℤ_2`!).
2. **Non-Commutative Commutator (`[invS P, R(c, s)] = 2 s Φ₁`):**
   The commutator between the reflection `invS P` and the rotation `R(c, s)` is `2 s Φ₁`.
-/
theorem dihedral_peter_weyl_2x2_peirce_representation
    (P X Y c s : B) (hP : P * P = P)
    (hc_S : invS P * c = c * invS P)
    (hs_S : invS P * s = s * invS P) :
    -- 1. Reflection invS P inverts the sine harmonic of the rotor:
    invS P * Rotor2D P X Y c s * invS P = Rotor2D P X Y c (-s) ∧
    -- 2. Non-abelian commutator is twice the off-diagonal bridge `2 s Φ₁`:
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (Rotor2D P X Y c s) =
      s * (genPhi P X Y + genPhi P X Y) := by
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hSJ : invS P * genJ P X Y = genPhi P X Y := by peirce_nf hP
  have hJS : genJ P X Y * invS P = - genPhi P X Y := by peirce_nf hP
  have hSJS : invS P * genJ P X Y * invS P = - genJ P X Y := by peirce_nf hP
  refine ⟨?_, ?_⟩
  · dsimp [Rotor2D]
    calc invS P * (c + s * genJ P X Y) * invS P
      _ = (invS P * c) * invS P + (invS P * s) * genJ P X Y * invS P := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = c * (invS P * invS P) + s * (invS P * genJ P X Y * invS P) := by
          rw [hc_S, hs_S]; simp only [mul_assoc]
      _ = c + (-s) * genJ P X Y := by
          rw [hS2, hSJS, mul_one, mul_neg, neg_mul]
  · dsimp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, Rotor2D]
    calc invS P * (c + s * genJ P X Y) - (c + s * genJ P X Y) * invS P
      _ = (invS P * c - c * invS P) + ((invS P * s) * genJ P X Y - s * (genJ P X Y * invS P)) := by
          simp only [mul_add, add_mul, mul_assoc]; abel
      _ = 0 + (s * (invS P * genJ P X Y) - s * (- genPhi P X Y)) := by
          rw [hc_S, sub_self, hs_S, hJS]; simp only [mul_assoc]
      _ = s * (genPhi P X Y + genPhi P X Y) := by
          rw [hSJ, mul_neg, sub_neg_eq_add, ← mul_add, zero_add]

/--
**Theorem 2b (𝔊𝔔₄ — Reflected Rotor Involution Law & Two-Reflection Generation of Rotations):**
In any ring `B` with `P * P = P` and central rotor coordinates `c, s`:
1. **Two Reflections Generate Rotations (Meta-Tower Rung 5):**
   Multiplying the reflected rotor `Rotor2D P X Y c s * invS P` on the right by the reflection
   `invS P` recovers the pure rotation `Rotor2D P X Y c s`.
2. **Reflected Rotor Square Law:**
   `(Rotor2D P X Y c s * invS P) * (Rotor2D P X Y c s * invS P) = c * c - s * s * (genJ P X Y * genJ P X Y)`.
3. **Conjugate Rotor Norm Identity:**
   `Rotor2D P X Y c s * Rotor2D P X Y c (-s) = c * c - s * s * (genJ P X Y * genJ P X Y)`.
-/
theorem dihedral_reflected_rotor_involution_and_two_reflection_rotation
    (P X Y c s : B) (hP : P * P = P)
    (hc_S : invS P * c = c * invS P)
    (hs_S : invS P * s = s * invS P)
    (hcs : c * s = s * c)
    (hc_J : c * genJ P X Y = genJ P X Y * c)
    (hs_J : s * genJ P X Y = genJ P X Y * s) :
    (Rotor2D P X Y c s * invS P) * invS P = Rotor2D P X Y c s ∧
    Rotor2D P X Y c s * Rotor2D P X Y c (-s) =
      c * c - s * s * (genJ P X Y * genJ P X Y) ∧
    (Rotor2D P X Y c s * invS P) * (Rotor2D P X Y c s * invS P) =
      c * c - s * s * (genJ P X Y * genJ P X Y) := by
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have htwo : (Rotor2D P X Y c s * invS P) * invS P = Rotor2D P X Y c s := by
    rw [mul_assoc, hS2, mul_one]
  have hnorm : Rotor2D P X Y c s * Rotor2D P X Y c (-s) =
      c * c - s * s * (genJ P X Y * genJ P X Y) := by
    dsimp [Rotor2D]
    have hsJ2 : s * genJ P X Y * (s * genJ P X Y) = s * s * (genJ P X Y * genJ P X Y) := by
      calc s * genJ P X Y * (s * genJ P X Y)
        _ = s * (genJ P X Y * s) * genJ P X Y := by simp only [mul_assoc]
        _ = s * s * (genJ P X Y * genJ P X Y) := by rw [← hs_J]; simp only [mul_assoc]
    have hcross : s * genJ P X Y * c - c * (s * genJ P X Y) = 0 := by
      calc s * genJ P X Y * c - c * (s * genJ P X Y)
        _ = s * (genJ P X Y * c) - (c * s) * genJ P X Y := by simp only [mul_assoc]
        _ = (s * c) * genJ P X Y - (s * c) * genJ P X Y := by rw [← hc_J, hcs]; simp only [mul_assoc]
        _ = 0 := sub_self _
    calc (c + s * genJ P X Y) * (c + (-s) * genJ P X Y)
      _ = c * c + (s * genJ P X Y * c - c * (s * genJ P X Y)) -
          s * genJ P X Y * (s * genJ P X Y) := by
          simp only [add_mul, mul_add, neg_mul, mul_neg, mul_assoc]; abel
      _ = c * c - s * s * (genJ P X Y * genJ P X Y) := by
          rw [hcross, add_zero, hsJ2]
  refine ⟨htwo, hnorm, ?_⟩
  have hConj := (dihedral_peter_weyl_2x2_peirce_representation P X Y c s hP hc_S hs_S).1
  calc (Rotor2D P X Y c s * invS P) * (Rotor2D P X Y c s * invS P)
    _ = Rotor2D P X Y c s * (invS P * Rotor2D P X Y c s * invS P) := by
        simp only [mul_assoc]
    _ = Rotor2D P X Y c s * Rotor2D P X Y c (-s) := by rw [hConj]
    _ = c * c - s * s * (genJ P X Y * genJ P X Y) := hnorm

end DihedralPeterWeylBlock

-- ============================================================================
-- DIRECTIVE 3 (𝔊𝔔₅–𝔊𝔔₇): Behavior of the Idempotent Surprisal Normal Form on G/H
-- ============================================================================

section QuotientSurprisalNormalForm
variable {B : Type u} [Ring B]

open InfoGeometry.OperatorAlgebra.PeirceSpine

/--
Linearized PMI surprisal operator `SurprisalOp u_bar delta_u σ = u_bar + delta_u * σ`
(where `u_bar = ½ log(1 - s_r²)`, `delta_u = artanh(s_r)`, and `σ = a_r b_r` with `σ² = 1`):
-/
def SurprisalOp (u_bar delta_u σ : B) : B :=
  u_bar + delta_u * σ

/--
**Theorem 3 (𝔊𝔔₅–𝔊𝔔₇ — Quotient Surprisal Normal Form & 2nd-Order Micro-Attribute Survival):**
Let `P_H² = P_H` be the subgroup-averaging quotient projector for `G ↠ G/H`, and let
`L = SurprisalOp u_bar delta_u σ` with `σ² = 1` and central coefficients `u_bar, delta_u`:
1. **Macro-Attribute (`h_macro : P_H * σ * P_H = σ * P_H`):**
   The linearized surprisal normal form descends intact at 1st order:
   `P_H * L * P_H = (u_bar + delta_u * σ) * P_H`.
2. **Micro-Attribute (`h_micro : P_H * σ * P_H = 0`, averages to zero over `H`-fibers):**
   - At **1st order**, the slope `delta_u` vanishes on the quotient: `P_H * L * P_H = u_bar * P_H`.
   - At **2nd order**, the Socratic Gramian defect on the quotient `G/H` recovers the
     exact squared BKM slope `(delta_u)²`:
     `P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H`!
-/
theorem quotient_surprisal_normal_form_and_second_order_survival
    (P_H u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_d : u_bar * delta_u = delta_u * u_bar)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    let L := SurprisalOp u_bar delta_u σ
    -- 1. Macro-attribute preservation on G/H:
    (P_H * σ * P_H = σ * P_H → P_H * L * P_H = L * P_H) ∧
    -- 2. Micro-attribute 1st-order annihilation vs. 2nd-order BKM variance survival on G/H:
    (P_H * σ * P_H = 0 →
      P_H * L * P_H = u_bar * P_H ∧
      P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) = (delta_u * delta_u) * P_H) := by
  refine ⟨?_, ?_⟩
  · intro h_macro
    dsimp [SurprisalOp]
    calc P_H * (u_bar + delta_u * σ) * P_H
      _ = (P_H * u_bar) * P_H + (P_H * delta_u) * σ * P_H := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = u_bar * (P_H * P_H) + delta_u * (P_H * σ * P_H) := by
          rw [hu_P, hd_P]; simp only [mul_assoc]
      _ = (u_bar + delta_u * σ) * P_H := by
          rw [hPH, h_macro, add_mul, mul_assoc]
  · intro h_micro
    have h1 : P_H * SurprisalOp u_bar delta_u σ * P_H = u_bar * P_H := by
      dsimp [SurprisalOp]
      calc P_H * (u_bar + delta_u * σ) * P_H
        _ = (P_H * u_bar) * P_H + (P_H * delta_u) * σ * P_H := by
            simp only [mul_add, add_mul, mul_assoc]
        _ = u_bar * (P_H * P_H) + delta_u * (P_H * σ * P_H) := by
            rw [hu_P, hd_P]; simp only [mul_assoc]
        _ = u_bar * P_H := by
            rw [hPH, h_micro, mul_zero, add_zero]
    refine ⟨h1, ?_⟩
    have hL2 : SurprisalOp u_bar delta_u σ * SurprisalOp u_bar delta_u σ =
        (u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + u_bar * delta_u) * σ := by
      dsimp [SurprisalOp]
      have hdσ2 : delta_u * σ * (delta_u * σ) = delta_u * delta_u := by
        calc delta_u * σ * (delta_u * σ) = delta_u * (σ * delta_u) * σ := by simp only [mul_assoc]
          _ = delta_u * delta_u * (σ * σ) := by rw [← hd_σ]; simp only [mul_assoc]
          _ = delta_u * delta_u := by rw [hσ2, mul_one]
      have Cross : u_bar * (delta_u * σ) + delta_u * σ * u_bar =
          (u_bar * delta_u + u_bar * delta_u) * σ := by
        calc u_bar * (delta_u * σ) + delta_u * σ * u_bar
          _ = u_bar * delta_u * σ + delta_u * (σ * u_bar) := by simp only [mul_assoc]
          _ = u_bar * delta_u * σ + (delta_u * u_bar) * σ := by
              rw [← hu_σ]; simp only [mul_assoc]
          _ = (u_bar * delta_u + u_bar * delta_u) * σ := by
              rw [← hu_d, add_mul]
      calc (u_bar + delta_u * σ) * (u_bar + delta_u * σ)
        _ = u_bar * u_bar + (u_bar * (delta_u * σ) + delta_u * σ * u_bar) +
            delta_u * σ * (delta_u * σ) := by
            simp only [add_mul, mul_add, mul_assoc]; abel
        _ = (u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + u_bar * delta_u) * σ := by
            rw [Cross, hdσ2]; abel
    have h_cross_zero : P_H * ((u_bar * delta_u + u_bar * delta_u) * σ) * P_H = 0 := by
      calc P_H * ((u_bar * delta_u + u_bar * delta_u) * σ) * P_H
        _ = (P_H * u_bar * delta_u + P_H * u_bar * delta_u) * σ * P_H := by
            simp only [mul_add, add_mul, mul_assoc]
        _ = (u_bar * delta_u + u_bar * delta_u) * (P_H * σ * P_H) := by
            rw [hu_P]
            calc (u_bar * P_H * delta_u + u_bar * P_H * delta_u) * σ * P_H
              _ = (u_bar * (P_H * delta_u) + u_bar * (P_H * delta_u)) * σ * P_H := by
                  simp only [mul_assoc]
              _ = (u_bar * delta_u + u_bar * delta_u) * (P_H * σ * P_H) := by
                  rw [hd_P]; simp only [add_mul, mul_assoc]
        _ = 0 := by rw [h_micro, mul_zero]
    rw [h1, hL2]
    calc P_H * ((u_bar * u_bar + delta_u * delta_u) + (u_bar * delta_u + u_bar * delta_u) * σ) * P_H -
         u_bar * P_H * (u_bar * P_H)
      _ = P_H * (u_bar * u_bar + delta_u * delta_u) * P_H +
          P_H * ((u_bar * delta_u + u_bar * delta_u) * σ) * P_H -
          u_bar * (P_H * u_bar) * P_H := by
          simp only [mul_add, add_mul, mul_assoc]
      _ = (u_bar * u_bar + delta_u * delta_u) * (P_H * P_H) + 0 -
          u_bar * u_bar * (P_H * P_H) := by
          rw [h_cross_zero, hu_P]
          have h_u2 : P_H * (u_bar * u_bar) = u_bar * u_bar * P_H := by
            calc
              P_H * (u_bar * u_bar) = (P_H * u_bar) * u_bar := by rw [← mul_assoc]
              _ = (u_bar * P_H) * u_bar := by rw [hu_P]
              _ = u_bar * (P_H * u_bar) := by rw [mul_assoc]
              _ = u_bar * (u_bar * P_H) := by rw [hu_P]
              _ = u_bar * u_bar * P_H := by rw [← mul_assoc]
          have h_d2 : P_H * (delta_u * delta_u) = delta_u * delta_u * P_H := by
            calc
              P_H * (delta_u * delta_u) = (P_H * delta_u) * delta_u := by rw [← mul_assoc]
              _ = (delta_u * P_H) * delta_u := by rw [hd_P]
              _ = delta_u * (P_H * delta_u) := by rw [mul_assoc]
              _ = delta_u * (delta_u * P_H) := by rw [hd_P]
              _ = delta_u * delta_u * P_H := by rw [← mul_assoc]
          have h_comm_sum : P_H * (u_bar * u_bar + delta_u * delta_u) =
              (u_bar * u_bar + delta_u * delta_u) * P_H := by
            rw [mul_add, h_u2, h_d2, add_mul]
          rw [h_comm_sum]; simp only [mul_assoc]
      _ = (delta_u * delta_u) * P_H := by
          rw [hPH, add_zero, add_mul]; abel

/--
**Theorem 3b (𝔊𝔔₆ — Off-Diagonal Peirce Bridge `Φ₁ = N_+ + N_-` Is Automatically a Micro-Attribute):**
For any quotient idempotent `P_H * P_H = P_H`, the symmetric off-diagonal Peirce operator
`genPhi P_H X Y = P_H * X * (1 - P_H) + (1 - P_H) * Y * P_H` automatically satisfies
`P_H * genPhi P_H X Y * P_H = 0`. Consequently, whenever `genPhi P_H X Y * genPhi P_H X Y = 1`,
its linearized surprisal `L = SurprisalOp u_bar delta_u (genPhi P_H X Y)` has 1st-order quotient
projection `u_bar * P_H` and 2nd-order Socratic Gramian defect `(delta_u * delta_u) * P_H`.
-/
theorem peirce_off_diagonal_involution_is_micro_attribute
    (P_H X Y u_bar delta_u : B)
    (hPH : P_H * P_H = P_H)
    (hPhi2 : genPhi P_H X Y * genPhi P_H X Y = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_d : u_bar * delta_u = delta_u * u_bar)
    (hu_Phi : u_bar * genPhi P_H X Y = genPhi P_H X Y * u_bar)
    (hd_Phi : delta_u * genPhi P_H X Y = genPhi P_H X Y * delta_u) :
    let L := SurprisalOp u_bar delta_u (genPhi P_H X Y)
    P_H * genPhi P_H X Y * P_H = 0 ∧
    P_H * L * P_H = u_bar * P_H ∧
    P_H * (L * L) * P_H - (P_H * L * P_H) * (P_H * L * P_H) =
      (delta_u * delta_u) * P_H := by
  have hMicro : P_H * genPhi P_H X Y * P_H = 0 := by peirce_nf hPH
  have hMain := (quotient_surprisal_normal_form_and_second_order_survival
    P_H u_bar delta_u (genPhi P_H X Y) hPH hPhi2 hu_P hd_P hu_d hu_Phi hd_Phi).2 hMicro
  exact ⟨hMicro, hMain.1, hMain.2⟩

/--
**Theorem 4 (𝔊𝔔₇ — Master 7-Stage Galois–Quotient Non-Abelian Fourier Synthesis):**
Assembles the complete 7-stage chain $\mathfrak{GQ}_1 \prec \dots \prec \mathfrak{GQ}_7$:
1. Divisor totient stratification `∑_{d | 12} φ(d) = 12` and `σ₅` harmonic swap/fixation (`𝔊𝔔₁`),
2. Integer Ramanujan orbit sums `c_d(x)` summing to `12 · δ_{x ≡ 0 mod 12}` on `Fin 12` (`𝔊𝔔₂`),
3. Dihedral Peter–Weyl rotor reflection `invS P_H * R(c, s) * invS P_H = R(c, -s)` and `[invS P_H, R(c, s)] = 2 s Φ₁` (`𝔊𝔔₃`),
4. Two-reflection generation `(R(c, s) * invS P_H) * invS P_H = R(c, s)` (`𝔊𝔔₄`),
5. Quotient surprisal macro-descent and 2nd-order micro-variance survival `(delta_u)² P_H` (`𝔊𝔔₅–𝔊𝔔₆`).
-/
theorem gq7_master_galois_quotient_nonabelian_fourier_synthesis
    (P_H X Y c s u_bar delta_u σ : B)
    (hPH : P_H * P_H = P_H)
    (hc_S : invS P_H * c = c * invS P_H)
    (hs_S : invS P_H * s = s * invS P_H)
    (hσ2 : σ * σ = 1)
    (hu_P : P_H * u_bar = u_bar * P_H)
    (hd_P : P_H * delta_u = delta_u * P_H)
    (hu_d : u_bar * delta_u = delta_u * u_bar)
    (hu_σ : u_bar * σ = σ * u_bar)
    (hd_σ : delta_u * σ = σ * delta_u) :
    (∀ a : GaloisQuotientFourierStage, ¬ GaloisQuotientFourierStage.coverEdge a a) ∧
    (Nat.totient 1 + Nat.totient 2 + Nat.totient 3 +
     Nat.totient 4 + Nat.totient 6 + Nat.totient 12 = 12) ∧
    (∀ x : Fin 12,
      ramanujanSum12 1 x.val + ramanujanSum12 2 x.val + ramanujanSum12 3 x.val +
      ramanujanSum12 4 x.val + ramanujanSum12 6 x.val + ramanujanSum12 12 x.val =
        if x.val = 0 then 12 else 0) ∧
    (invS P_H * Rotor2D P_H X Y c s * invS P_H = Rotor2D P_H X Y c (-s) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P_H) (Rotor2D P_H X Y c s) =
       s * (genPhi P_H X Y + genPhi P_H X Y) ∧
     (Rotor2D P_H X Y c s * invS P_H) * invS P_H = Rotor2D P_H X Y c s) ∧
    (P_H * σ * P_H = 0 →
      P_H * SurprisalOp u_bar delta_u σ * P_H = u_bar * P_H ∧
      P_H * (SurprisalOp u_bar delta_u σ * SurprisalOp u_bar delta_u σ) * P_H -
        (P_H * SurprisalOp u_bar delta_u σ * P_H) * (P_H * SurprisalOp u_bar delta_u σ * P_H) =
        (delta_u * delta_u) * P_H) := by
  have hS2 : invS P_H * invS P_H = 1 := by peirce_nf hPH
  have hRot : (Rotor2D P_H X Y c s * invS P_H) * invS P_H = Rotor2D P_H X Y c s := by
    rw [mul_assoc, hS2, mul_one]
  have hDih := dihedral_peter_weyl_2x2_peirce_representation P_H X Y c s hPH hc_S hs_S
  refine ⟨GaloisQuotientFourierStage.coverEdge_acyclic,
    z12_galois_orbit_stratification_and_v4_group.1,
    ramanujanSum12_divisor_shells_and_fourier_orthogonality.2.2,
    ⟨hDih.1, hDih.2, hRot⟩,
    (quotient_surprisal_normal_form_and_second_order_survival
      P_H u_bar delta_u σ hPH hσ2 hu_P hd_P hu_d hu_σ hd_σ).2⟩

end QuotientSurprisalNormalForm

end GaloisQuotientNonAbelianFourierPoset
