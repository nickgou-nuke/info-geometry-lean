/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Core.AnticommutingSum
import InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset
import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Pin-(8,8) Split Clifford Generators, Twisted 2O \ 2T Reflection Lift & Triality–Cobordism Cyclotomic Bridge (𝔓𝔐₁ ≺ ⋯ ≺ 𝔓𝔐₄)

## i. Overview

Finite algebraic formalization of the four-stage `Pin_-(8,8)` synthesis ($\mathfrak{PM}_1 \prec \dots \prec \mathfrak{PM}_4$).
This module establishes the finite quaternion reflection identities, $2 \times 2$ split Clifford
parity-time generator relations, and cyclotomic polynomial factorizations over any commutative
ring `[CommRing K]`, bridged to `WignerHurwitzAdamsKTheoryPoset` and `InfoGeometry.Clifford.Cl11TensorTower`.
It does not construct the smooth Lie group $\mathrm{Pin}_-(8,8)$, the topological cobordism group
$\Omega_2^{\mathrm{Pin}_-}(\mathrm{pt})$, or continuous homotopy groups $\pi_3^s$.

1. **Stage 1 (`𝔓𝔐₁` — The `Pin_-` Hyperplane Reflection Lift in `2O \ 2T`):**
   - `Quat.pin_minus_reflection_lift_in_binary_octahedral_coset`:
     Proves that the pure imaginary short root `R = j - k = (0, 0, 1, -1)` (`qNorm R = 2`)
     satisfies the negative reflection square law `R * R = -2 • 1` (representing `(R/√2)² = -1`),
     while its twisted `Pin_-` adjoint action `pinRefl R X = R * X * R` (representing `-R X R̄`)
     executes an improper hyperplane reflection on `Im(ℍ) ≅ K³`:
     `pinRefl R i = 2 • i`, `pinRefl R j = 2 • k`, `pinRefl R k = 2 • j`,
     `pinRefl R (vec3 x y z) = 2 • vec3 x z y`, and `pinRefl R (pinRefl R (vec3 x y z)) = 4 • vec3 x y z`,
     while untwisted conjugation `R * hurwitzW * conj R = 2 • hurwitzW_refl` maps Hurwitz corners to Hurwitz corners.
   - `pinMinusJKUnitRoot_norm_and_square`, `pinMinusJKReflection3_is_orthogonal_improper`, and
     `pinMinusJKUnitRoot_twistedAdjoint_eq_matrix_reflection` specialize to `ℝ`, normalize `R` by `√2`,
     and identify its twisted action on `Im(ℍ) ≅ ℝ³` with an explicit orthogonal matrix of determinant `-1`.
2. **Stage 2 & 3 (`𝔓𝔐₂` & `𝔓𝔐₃` — The `Cl_-(1,1) ≅ Mat₂(K)` Split Brick & Parity-Time Relations):**
   - `Mat2.cl_minus_1_1_split_generators_and_parity_time_d4_relations` and
     `Mat2.cl11_tensor_tower_parity_time_and_idx8_bridge`:
     Realizes the split building block via `parityP` (`P² = -I₂`) and `timeT` (`T² = +I₂`) in `Mat2 K`,
     proving `P * T + T * P = 0`, `P * T = chiralPT`, `chiralPT² = +I₂`, and bridging `Mat2 ℝ` to
     `InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase`, `InfoGeometry.Clifford.Cl11Matrix.Eplus`,
     `InfoGeometry.Clifford.Cl11Matrix.J1`, and `Fintype.card (InfoGeometry.Clifford.TowerMatrix.Idx 8) = 256`.
3. **Stage 4 (`𝔓𝔐₄` — The `Φ₈(x³) = Φ₈(x) Φ₂₄(x)` Cyclotomic Factorization Bridge):**
   - `pin_minus_abk_triality_cyclotomic_bridge` and `pm4_master_pin_minus_88_triality_synthesis`:
     Proves that substituting `x ↦ x³` into `Φ₈(x) = x⁴ + 1` factors as
     `Phi8 (x ^ 3) = Phi8 x * Phi24 x = Phi8 x * Phi6 (x ^ 4)` with `(x ^ 12 - 1) * Phi8 (x ^ 3) = x ^ 24 - 1`
     and Bézout identity `3 * 3 - 1 * 8 = 1`.

## ii. Key results

- `PinMinus88TrialityStage`, `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`
- `Quat.pin_minus_reflection_lift_in_binary_octahedral_coset`,
  `Quat.pin_minus_short_root_product_eq_hurwitz_triality_and_braid_relation`,
  `Quat.binary_octahedral_48_coset_decomposition_and_octahedral_pole_action`
- `pinMinusJKUnitRoot_norm_and_square`, `pinMinusJKReflection3_is_orthogonal_improper`,
  `pinMinusJKUnitRoot_action_eq_matrix_reflection`, `pinMinusJKUnitRoot_twistedAdjoint_eq_matrix_reflection`,
  `pinMinusJKUnitRoot_double_cover_sign_kernel`,
  `quatAdjointMatrix3`, `quatAdjointMatrix3_homomorphism_orthogonality_and_graded_2O_action`
- `Quat.toWHQuat_bridge`
- `Mat2.cl_minus_1_1_split_generators_and_parity_time_d4_relations`
- `Mat2.cl11_tensor_tower_parity_time_and_idx8_bridge`
- `Mat2.cl_minus_3_0_into_split_cl_2_2_kronecker_embedding`,
  `Mat2.clMinus30ToMat4SplitAlgHom`, `Mat2.mat4SplitToMatStage8AlgHom`,
  `Mat2.clMinus30ToMatStage8AlgHom`, `Mat2.clMinus30_into_matStage8_algHom_and_reflection_transport`
- `pin_minus_abk_triality_cyclotomic_bridge`
- `zmod24_chinese_remainder_abk_triality_split`
- `pm4_master_pin_minus_88_triality_synthesis`

## iii. Table of contents

- Section 0: The 4-Stage `Pin_-(8,8)` Triality Poset (`𝔓𝔐₁ ≺ ⋯ ≺ 𝔓𝔐₄`)
- Section 1 (`𝔓𝔐₁`): `Pin_-` Reflection Lift on the Odd Coset `2O \ 2T`
- Section 2 (`𝔓𝔐₂–𝔓𝔐₃`): Split Brick `Cl_-(1,1) ≅ Mat₂(K)` & Parity-Time Relations
- Section 3 (`𝔓𝔐₄`): Cyclotomic Bridge `Φ₈(x³) = Φ₈(x) Φ₂₄(x)` & Master Synthesis

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `PinMinus88TrialityStage` ($\mathfrak{PM}_1 \prec \dots \prec \mathfrak{PM}_4$), `coverEdge`, `coverEdge_strictMono`, `coverEdge_acyclic`,
  - `Quat.pin_minus_reflection_lift_in_binary_octahedral_coset`, `Quat.pin_minus_short_root_product_eq_hurwitz_triality_and_braid_relation`, `Quat.binary_octahedral_48_coset_decomposition_and_octahedral_pole_action`, `Quat.toWHQuat_bridge`,
  - `pinMinusJKUnitRoot_norm_and_square`, `pinMinusJKReflection3_is_orthogonal_improper`, `pinMinusJKUnitRoot_action_eq_matrix_reflection`, `pinMinusJKUnitRoot_twistedAdjoint_eq_matrix_reflection`, `pinMinusJKUnitRoot_double_cover_sign_kernel`, `quatAdjointMatrix3_homomorphism_orthogonality_and_graded_2O_action`,
  - `Mat2.cl_minus_1_1_split_generators_and_parity_time_d4_relations`, `Mat2.cl11_tensor_tower_parity_time_and_idx8_bridge`, `Mat2.cl_minus_3_0_into_split_cl_2_2_kronecker_embedding`, `Mat2.clMinus30_into_matStage8_algHom_and_reflection_transport`,
  - `pin_minus_abk_triality_cyclotomic_bridge`, `zmod24_chinese_remainder_abk_triality_split`, `pm4_master_pin_minus_88_triality_synthesis`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - The abstract quaternion identities assume `[CommRing K]`; the normalized real orthogonal action is specifically over `ℝ`.
* **BUCKET 3 — Out-of-Scope Topological / Lie-Theoretic Claims:**
  - Manifold-level constructions of $\mathrm{Pin}_-(8,8)$, $\mathrm{Spin}(8)$ triality automorphisms on Lie algebras, $\Omega_2^{\mathrm{Pin}_-}(\mathrm{pt}) \cong \mathbb{Z}_8$ cobordism, and $\pi_3^s$ homotopy groups remain outside this finite algebraic owner.

## iv. References

- Karkada et al., *Symmetry in language statistics shapes the geometry of model representations*, arXiv:2602.15029 (2026).
- `InfoGeometry.WignerHurwitzAdamsKTheory.WignerHurwitzAdamsKTheoryPoset`.
- `InfoGeometry.Clifford.Cl11TensorTower`.
-/

namespace PinMinus88TrialityPoset

universe u

-- ============================================================================
-- SECTION 0: The 4-Stage Pin_-(8,8) Triality Poset (𝔓𝔐₁ ≺ ⋯ ≺ 𝔓𝔐₄)
-- ============================================================================

/-- The 4-stage causal poset ($\mathfrak{PM}_1 \prec \dots \prec \mathfrak{PM}_4$) organizing
the `Pin_-` short-root reflection lift in $2O \setminus 2T$, the split $\mathcal{C}\ell_-(1,1)$
matrix generators, the parity-time $D_4$ anticommutation relations and $2^8 = 256$ tensor-stage
dimension, and the $\Phi_8(x^3) = \Phi_8(x)\Phi_{24}(x)$ cyclotomic factorization. -/
inductive PinMinus88TrialityStage : Type
  | pm1PinMinusShortRootReflectionLift
  | pm2SplitCl11ParityTimeGenerators
  | pm3BottPeriodicityAndParityTimeD4Group
  | pm4AbkCobordismTrialityCyclotomicBridge
  deriving DecidableEq, Repr

namespace PinMinus88TrialityStage

/-- Numerical stage index `0 .. 3` for `PinMinus88TrialityStage`. -/
def rank : PinMinus88TrialityStage → ℕ
  | .pm1PinMinusShortRootReflectionLift => 0
  | .pm2SplitCl11ParityTimeGenerators => 1
  | .pm3BottPeriodicityAndParityTimeD4Group => 2
  | .pm4AbkCobordismTrialityCyclotomicBridge => 3

/-- The stage rank map is injective. -/
lemma rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrder : LinearOrder PinMinus88TrialityStage :=
  LinearOrder.lift' rank rank_injective

instance instFintype : Fintype PinMinus88TrialityStage where
  elems := {
    .pm1PinMinusShortRootReflectionLift,
    .pm2SplitCl11ParityTimeGenerators,
    .pm3BottPeriodicityAndParityTimeD4Group,
    .pm4AbkCobordismTrialityCyclotomicBridge
  }
  complete := by intro x; cases x <;> decide

/-- Directed Hasse covering relation on `PinMinus88TrialityStage`. -/
inductive coverEdge : PinMinus88TrialityStage → PinMinus88TrialityStage → Prop
  | pm1_to_pm2 :
      coverEdge .pm1PinMinusShortRootReflectionLift .pm2SplitCl11ParityTimeGenerators
  | pm2_to_pm3 :
      coverEdge .pm2SplitCl11ParityTimeGenerators .pm3BottPeriodicityAndParityTimeD4Group
  | pm3_to_pm4 :
      coverEdge .pm3BottPeriodicityAndParityTimeD4Group .pm4AbkCobordismTrialityCyclotomicBridge

/-- Every covering edge strictly increases stage order (`a < b`). -/
lemma coverEdge_strictMono {a b : PinMinus88TrialityStage} (h : coverEdge a b) :
    a < b := by
  cases h <;> decide

/-- No stage covers itself. -/
lemma coverEdge_acyclic (a : PinMinus88TrialityStage) : ¬ coverEdge a a := by
  intro h
  have := coverEdge_strictMono h
  exact lt_irrefl a this

end PinMinus88TrialityStage

-- ============================================================================
-- SECTION 1 (𝔓𝔐₁): Pin_-(3) ⊂ Pin_-(8,8) Reflection Lift on the Odd Coset 2O \ 2T
-- ============================================================================

/-- Canonical Mathlib quaternion carrier `Quaternion K` (`ℍ[K]`), re-exported from
`WignerHurwitzAdamsKTheoryPoset.Quat K`. -/
abbrev Quat (K : Type u) [CommRing K] : Type u :=
  WignerHurwitzAdamsKTheoryPoset.Quat K

namespace Quat
variable {K : Type u} [CommRing K]

/-- Scalar multiplication `c • q` on `Quat K = Quaternion K`. -/
abbrev smul (c : K) (q : Quat K) : Quat K :=
  WignerHurwitzAdamsKTheoryPoset.Quat.smul c q

/-- Quaternion conjugate `star q = ⟨q.re, -q.imI, -q.imJ, -q.imK⟩` on `Quat K = Quaternion K`. -/
abbrev conj (q : Quat K) : Quat K :=
  WignerHurwitzAdamsKTheoryPoset.Quat.conj q

/-- Quaternion norm-square `Quaternion.normSq q` on `Quat K = Quaternion K`. -/
abbrev qNorm (q : Quat K) : K :=
  WignerHurwitzAdamsKTheoryPoset.Quat.qNorm q

/-- Quaternion unit `1 = ⟨1, 0, 0, 0⟩` in `Quat K = Quaternion K`. -/
abbrev qOne : Quat K := WignerHurwitzAdamsKTheoryPoset.Quat.qOne
/-- Imaginary unit `i = ⟨0, 1, 0, 0⟩` in `Quat K = Quaternion K`. -/
abbrev qi   : Quat K := WignerHurwitzAdamsKTheoryPoset.Quat.qi
/-- Imaginary unit `j = ⟨0, 0, 1, 0⟩` in `Quat K = Quaternion K`. -/
abbrev qj   : Quat K := WignerHurwitzAdamsKTheoryPoset.Quat.qj
/-- Imaginary unit `k = ⟨0, 0, 0, 1⟩` in `Quat K = Quaternion K`. -/
abbrev qk   : Quat K := WignerHurwitzAdamsKTheoryPoset.Quat.qk

/-- Pure 3D spatial vector `⟨0, x, y, z⟩ ∈ Im(ℍ) ≅ K³`. -/
def vec3 (x y z : K) : Quat K := ⟨0, x, y, z⟩

/-- Pure imaginary short root `R = j - k = ⟨0, 0, 1, -1⟩` (`qNorm R = 2`), re-exported from
`WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK`. -/
abbrev reflJK : Quat K := WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK

/-- Primary Hurwitz spinor corner `W = ⟨1, 1, 1, 1⟩` (`qNorm W = 4`). -/
abbrev hurwitzW : Quat K := WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW

/-- Reflected Hurwitz spinor corner `W_refl = ⟨1, -1, -1, -1⟩ = conj hurwitzW` (`qNorm W_refl = 4`)
under untwisted conjugation `R * hurwitzW * conj R`. -/
def hurwitzW_refl : Quat K := ⟨1, -1, -1, -1⟩

/--
Twisted `Pin_-` reflection action on `Im(ℍ)`: for a pure imaginary reflection generator `R`
(where `conj R = -R`), the twisted adjoint `-R * X * conj R` equals `R * X * R`.
-/
def pinRefl (R X : Quat K) : Quat K := R * X * R

/-- Identity map from `Quat K` to `WignerHurwitzAdamsKTheoryPoset.Quat K`. -/
abbrev toWHQuat (q : Quat K) : WignerHurwitzAdamsKTheoryPoset.Quat K := q

/-- Identity map from `WignerHurwitzAdamsKTheoryPoset.Quat K` to `Quat K`. -/
abbrev ofWHQuat (q : WignerHurwitzAdamsKTheoryPoset.Quat K) : Quat K := q

/-- `toWHQuat` is a left-invertible multiplication-, conjugation-, and norm-preserving identity
on `Quat K = Quaternion K`. -/
lemma toWHQuat_bridge (a b : Quat K) :
    ofWHQuat (toWHQuat a) = a ∧
    toWHQuat (a * b) = toWHQuat a * toWHQuat b ∧
    WignerHurwitzAdamsKTheoryPoset.Quat.qNorm (toWHQuat a) = qNorm a := by
  exact ⟨by simp, by simp, by simp [qNorm]⟩

/--
**Theorem 1 (𝔓𝔐₁ — Exact `Pin_-` Hyperplane Reflection Lift of `S₄ \ A₄` in `2O \ 2T`):**
1. **Short Root Norm:** `qNorm reflJK = 2`.
2. **`Pin_-` Negative Reflection Square Law:** `reflJK * reflJK = -2 • 1` (i.e., `(R/√2)² = -1` in `Pin_-`,
   whereas `Pin_+` would require `+1`).
3. **Improper Hyperplane Reflection on `K³` (`det = -1`, fixing `i` and swapping `j ↔ k`):**
   `pinRefl reflJK qi = 2 • qi`, `pinRefl reflJK qj = 2 • qk`, `pinRefl reflJK qk = 2 • qj`.
4. **Twisted Adjoint & Vector Involution Square:** `pinRefl reflJK (vec3 x y z) = -(reflJK * vec3 x y z * conj reflJK) = 2 • vec3 x z y`,
   and applying `pinRefl reflJK` twice restores `+4 • vec3 x y z`, even though `R² = -2 • 1` flips sign.
5. **Untwisted Conjugation Normalization of `2T`:** `reflJK * hurwitzW * conj reflJK = 2 • hurwitzW_refl`
   and `qNorm hurwitzW_refl = 4`.
-/
lemma pin_minus_reflection_lift_in_binary_octahedral_coset (x y z : K) :
    -- 1. Short root norm N(R) = 2:
    qNorm (reflJK : Quat K) = 2 ∧
    -- 2. Pin_- negative square law R² = -2 • 1 ((R/√2)² = -1):
    (reflJK : Quat K) * reflJK = smul (-2) qOne ∧
    -- 3. Twisted Pin_- reflection fixes i and transposes j ↔ k (hyperplane y = z):
    pinRefl (reflJK : Quat K) qi = smul 2 qi ∧
    pinRefl (reflJK : Quat K) qj = smul 2 qk ∧
    pinRefl (reflJK : Quat K) qk = smul 2 qj ∧
    -- 4. General 3D vector reflection (x, y, z) ↦ 2(x, z, y) and involutive square 4(x, y, z):
    pinRefl reflJK (vec3 x y z) = smul 2 (vec3 x z y) ∧
    pinRefl reflJK (pinRefl reflJK (vec3 x y z)) = smul 4 (vec3 x y z) ∧
    -- 5. Untwisted conjugation of Hurwitz corner W by R stays in 2T:
    (reflJK : Quat K) * hurwitzW * conj reflJK = smul 2 hurwitzW_refl := by
  have hPin := WignerHurwitzAdamsKTheoryPoset.Quat.pin_minus_short_root_reflection_identities (K := K)
  refine ⟨hPin.1, hPin.2.1, hPin.2.2.1, hPin.2.2.2.1, hPin.2.2.2.2.1, ?_, ?_, ?_⟩
  · apply Quaternion.ext <;>
      (dsimp [pinRefl, reflJK, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        vec3, smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [pinRefl, reflJK, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        vec3, smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [reflJK, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        hurwitzW, WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW,
        hurwitzW_refl, conj, WignerHurwitzAdamsKTheoryPoset.Quat.conj,
        smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)

/-- Twisted `Pin_-` adjoint identity `pinRefl reflJK (vec3 x y z) = -(reflJK * vec3 x y z * conj reflJK)`
and reflected Hurwitz corner norm `qNorm hurwitzW_refl = 4`. -/
lemma pinRefl_eq_neg_conj_and_hurwitzW_refl_norm (x y z : K) :
    pinRefl reflJK (vec3 x y z) = -(reflJK * vec3 x y z * conj reflJK) ∧
    qNorm (hurwitzW_refl : Quat K) = 4 := by
  refine ⟨?_, ?_⟩
  · apply Quaternion.ext <;>
      (dsimp [pinRefl, reflJK, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        vec3, conj, WignerHurwitzAdamsKTheoryPoset.Quat.conj]; ring)
  · dsimp [qNorm, WignerHurwitzAdamsKTheoryPoset.Quat.qNorm, hurwitzW_refl]
    rw [Quaternion.normSq_def']
    ring

/-- Pure imaginary short root `R_{ij} = i - j = ⟨0, 1, -1, 0⟩` (`qNorm R_{ij} = 2`) in the odd coset `2O \ 2T`. -/
def reflIJ : Quat K := ⟨0, 1, -1, 0⟩

/-- Pure imaginary short root `R_{ki} = k - i = ⟨0, -1, 0, 1⟩` (`qNorm R_{ki} = 2`) in the odd coset `2O \ 2T`. -/
def reflKI : Quat K := ⟨0, -1, 0, 1⟩

/--
**Theorem 1b (𝔓𝔐₁ — Generation of the Hurwitz Triality Corner `W` as a Product of Two `Pin_-(3)` Short-Root Reflections & `S₃` Braid Relation):**
1. **Short-Root Norms & `Pin_-` Negative Squares:**
   `qNorm reflIJ = 2`, `qNorm reflKI = 2`, `reflIJ * reflIJ = smul (-2) qOne`, `reflKI * reflKI = smul (-2) qOne`.
2. **Product of Two `Pin_-` Reflections is the Hurwitz Triality Corner `W = 1 + i + j + k ∈ 2T`:**
   `reflIJ * reflJK = hurwitzW` (`(i - j)(j - k) = 1 + i + j + k`), proving that the order-3 triality
   rotation in `2T` is generated directly by composing two odd-coset `Pin_-` reflections in `2O \ 2T`.
3. **Quaternion `S₃` Coxeter Braid Identity:**
   `reflIJ * reflJK * reflIJ = smul (-2) reflKI` and `reflJK * reflIJ * reflJK = smul (-2) reflKI`.
4. **Coordinate Swap Actions on `vec3 x y z`:**
   `pinRefl reflIJ (vec3 x y z) = smul 2 (vec3 y x z)` and
   `pinRefl reflKI (vec3 x y z) = smul 2 (vec3 z y x)`.
-/
lemma pin_minus_short_root_product_eq_hurwitz_triality_and_braid_relation (x y z : K) :
    qNorm (reflIJ : Quat K) = 2 ∧
    qNorm (reflKI : Quat K) = 2 ∧
    (reflIJ : Quat K) * reflIJ = smul (-2) qOne ∧
    (reflKI : Quat K) * reflKI = smul (-2) qOne ∧
    (reflIJ : Quat K) * reflJK = hurwitzW ∧
    (reflIJ : Quat K) * reflJK * reflIJ = smul (-2) reflKI ∧
    (reflJK : Quat K) * reflIJ * reflJK = smul (-2) reflKI ∧
    pinRefl reflIJ (vec3 x y z) = smul 2 (vec3 y x z) ∧
    pinRefl reflKI (vec3 x y z) = smul 2 (vec3 z y x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [qNorm, WignerHurwitzAdamsKTheoryPoset.Quat.qNorm, reflIJ]
    rw [Quaternion.normSq_def']; ring
  · dsimp [qNorm, WignerHurwitzAdamsKTheoryPoset.Quat.qNorm, reflKI]
    rw [Quaternion.normSq_def']; ring
  · apply Quaternion.ext <;>
      (dsimp [reflIJ, qOne, WignerHurwitzAdamsKTheoryPoset.Quat.qOne,
        smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [reflKI, qOne, WignerHurwitzAdamsKTheoryPoset.Quat.qOne,
        smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [reflIJ, reflJK, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        hurwitzW, WignerHurwitzAdamsKTheoryPoset.Quat.hurwitzW]; ring)
  · apply Quaternion.ext <;>
      (dsimp [reflIJ, reflJK, reflKI, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [reflIJ, reflJK, reflKI, WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
        smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [pinRefl, reflIJ, vec3, smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)
  · apply Quaternion.ext <;>
      (dsimp [pinRefl, reflKI, vec3, smul, WignerHurwitzAdamsKTheoryPoset.Quat.smul]; ring)

/-- Computable `DecidableEq` instance for `Quat R = Quaternion R`. -/
instance instDecidableEqQuat {R : Type u} [CommRing R] [DecidableEq R] : DecidableEq (Quat R) :=
  fun a b =>
    decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
      ⟨fun h => Quaternion.ext_iff.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
       fun h => ⟨congrArg QuaternionAlgebra.re h, congrArg QuaternionAlgebra.imI h,
                 congrArg QuaternionAlgebra.imJ h, congrArg QuaternionAlgebra.imK h⟩⟩

/-- Computable norm-square polynomial `re² + imI² + imJ² + imK²` on `Quat K`, matching `qNorm`. -/
def qNormSq (q : Quat K) : K :=
  q.re * q.re + q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK

/-- `qNorm` agrees identically with the computable polynomial `qNormSq`. -/
lemma qNorm_eq_qNormSq (q : Quat K) : qNorm q = qNormSq q := by
  dsimp [qNorm, WignerHurwitzAdamsKTheoryPoset.Quat.qNorm, qNormSq]
  rw [Quaternion.normSq_def']
  ring

/-- Explicit duplicate-free list of the 24 scaled Hurwitz units `2 · D₂₄ = 2T` in `Quat ℤ` (`qNormSq = 4`):
8 axis units `±2, ±2i, ±2j, ±2k` and 16 corners `(±1, ±1, ±1, ±1)`. -/
def hurwitz24List : List (Quat ℤ) :=
  [ ⟨2, 0, 0, 0⟩, ⟨-2, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, ⟨0, -2, 0, 0⟩,
    ⟨0, 0, 2, 0⟩, ⟨0, 0, -2, 0⟩, ⟨0, 0, 0, 2⟩, ⟨0, 0, 0, -2⟩,
    ⟨1, 1, 1, 1⟩, ⟨1, 1, 1, -1⟩, ⟨1, 1, -1, 1⟩, ⟨1, 1, -1, -1⟩,
    ⟨1, -1, 1, 1⟩, ⟨1, -1, 1, -1⟩, ⟨1, -1, -1, 1⟩, ⟨1, -1, -1, -1⟩,
    ⟨-1, 1, 1, 1⟩, ⟨-1, 1, 1, -1⟩, ⟨-1, 1, -1, 1⟩, ⟨-1, 1, -1, -1⟩,
    ⟨-1, -1, 1, 1⟩, ⟨-1, -1, 1, -1⟩, ⟨-1, -1, -1, 1⟩, ⟨-1, -1, -1, -1⟩ ]

/-- The 24 scaled Hurwitz units `2 · D₂₄ = 2T` as a `Finset (Quat ℤ)`. -/
def hurwitz24Finset : Finset (Quat ℤ) :=
  ⟨Multiset.ofList hurwitz24List, by decide⟩

/-- Explicit duplicate-free list of the 24 scaled odd-coset elements `√2 · (2O \ 2T)` in `Quat ℤ` (`qNormSq = 2`):
all 24 `F₄` short roots with two coordinates in `{-1, 1}` and two coordinates equal to `0`. -/
def oddCoset24List : List (Quat ℤ) :=
  [ ⟨1, 1, 0, 0⟩, ⟨1, -1, 0, 0⟩, ⟨-1, 1, 0, 0⟩, ⟨-1, -1, 0, 0⟩,
    ⟨1, 0, 1, 0⟩, ⟨1, 0, -1, 0⟩, ⟨-1, 0, 1, 0⟩, ⟨-1, 0, -1, 0⟩,
    ⟨1, 0, 0, 1⟩, ⟨1, 0, 0, -1⟩, ⟨-1, 0, 0, 1⟩, ⟨-1, 0, 0, -1⟩,
    ⟨0, 1, 1, 0⟩, ⟨0, 1, -1, 0⟩, ⟨0, -1, 1, 0⟩, ⟨0, -1, -1, 0⟩,
    ⟨0, 0, 1, 1⟩, ⟨0, 0, 1, -1⟩, ⟨0, 0, -1, 1⟩, ⟨0, 0, -1, -1⟩,
    ⟨0, 1, 0, 1⟩, ⟨0, 1, 0, -1⟩, ⟨0, -1, 0, 1⟩, ⟨0, -1, 0, -1⟩ ]

/-- The 24 scaled odd-coset elements `√2 · (2O \ 2T)` as a `Finset (Quat ℤ)`. -/
def oddCoset24Finset : Finset (Quat ℤ) :=
  ⟨Multiset.ofList oddCoset24List, by decide⟩

/-- The 48-element Binary Octahedral finite set `2O = 2T ⊔ (2O \ 2T)` in `Quat ℤ`. -/
def binaryOctahedral48Finset : Finset (Quat ℤ) :=
  ⟨Multiset.ofList (hurwitz24List ++ oddCoset24List), by decide⟩

/-- The 6 octahedral coordinate poles `{±i, ±j, ±k}` in `Im(ℍ_ℤ)`. -/
def octahedralPoles6 : Finset (Quat ℤ) :=
  ⟨Multiset.ofList [qi, -qi, qj, -qj, qk, -qk], by decide⟩

/--
**Theorem 1c (𝔓𝔐₁ — The 48-Element Binary Octahedral Group `2O = 2T ⊔ (2O \ 2T)`, `ℤ₂`-Graded Multiplication & Octahedral Pole Double Cover):**
1. **Exact Coset Cardinalities (`24 + 24 = 48`):**
   `hurwitz24Finset.card = 24`, `oddCoset24Finset.card = 24`, `Disjoint hurwitz24Finset oddCoset24Finset`,
   `binaryOctahedral48Finset = hurwitz24Finset ∪ oddCoset24Finset`,
   `binaryOctahedral48Finset.card = 48`, and `octahedralPoles6.card = 6`.
2. **Norm Separation & Conjugation Closure:**
   Every `u ∈ hurwitz24Finset` has `qNormSq u = 4` and `conj u ∈ hurwitz24Finset`;
   every `v ∈ oddCoset24Finset` has `qNormSq v = 2` and `conj v ∈ oddCoset24Finset`.
3. **Exact `ℤ₂`-Graded Multiplication Law (`2O / 2T ≅ ℤ₂`):**
   - `even * even = 2 • even`: `∀ u₁, u₂ ∈ hurwitz24Finset, ∃ u₃ ∈ hurwitz24Finset, u₁ * u₂ = smul 2 u₃`,
   - `even * odd = 2 • odd` and `odd * even = 2 • odd`,
   - `odd * odd = even`: `∀ v₁, v₂ ∈ oddCoset24Finset, v₁ * v₂ ∈ hurwitz24Finset`.
4. **Octahedral Signed-Permutation Action on `{±i, ±j, ±k}` & `{±2}` Double-Cover Kernel:**
   Every element of `hurwitz24Finset` (scaled by `4`) and `oddCoset24Finset` (scaled by `2`) permutes
   `octahedralPoles6`, and the kernel of the conjugation action on `octahedralPoles6` inside
   `hurwitz24Finset` is `{smul 2 qOne, smul (-2) qOne}` while no element of `oddCoset24Finset` acts trivially.
-/
lemma binary_octahedral_48_coset_decomposition_and_octahedral_pole_action :
    hurwitz24Finset.card = 24 ∧
    oddCoset24Finset.card = 24 ∧
    Disjoint hurwitz24Finset oddCoset24Finset ∧
    binaryOctahedral48Finset = hurwitz24Finset ∪ oddCoset24Finset ∧
    binaryOctahedral48Finset.card = 48 ∧
    octahedralPoles6.card = 6 ∧
    (∀ u ∈ hurwitz24Finset, qNormSq u = 4 ∧ conj u ∈ hurwitz24Finset) ∧
    (∀ v ∈ oddCoset24Finset, qNormSq v = 2 ∧ conj v ∈ oddCoset24Finset) ∧
    (∀ u₁ ∈ hurwitz24Finset, ∀ u₂ ∈ hurwitz24Finset,
      ∃ u₃ ∈ hurwitz24Finset, u₁ * u₂ = smul 2 u₃) ∧
    (∀ u ∈ hurwitz24Finset, ∀ v ∈ oddCoset24Finset,
      (∃ v₁ ∈ oddCoset24Finset, u * v = smul 2 v₁) ∧
      (∃ v₂ ∈ oddCoset24Finset, v * u = smul 2 v₂)) ∧
    (∀ v₁ ∈ oddCoset24Finset, ∀ v₂ ∈ oddCoset24Finset,
      v₁ * v₂ ∈ hurwitz24Finset) ∧
    (∀ u ∈ hurwitz24Finset, ∀ p ∈ octahedralPoles6,
      ∃ p' ∈ octahedralPoles6, u * p * conj u = smul 4 p') ∧
    (∀ v ∈ oddCoset24Finset, ∀ p ∈ octahedralPoles6,
      ∃ p' ∈ octahedralPoles6, v * p * conj v = smul 2 p') ∧
    (∀ u ∈ hurwitz24Finset,
      (∀ p ∈ octahedralPoles6, u * p * conj u = smul 4 p) ↔
        (u = smul 2 qOne ∨ u = smul (-2) qOne)) ∧
    (∀ v ∈ oddCoset24Finset,
      ¬ (∀ p ∈ octahedralPoles6, v * p * conj v = smul 2 p)) := by
  decide

end Quat

/-! ## Typed real reflection map for the Pin-minus short root

The preceding quaternion equations are over an arbitrary commutative ring and
do not by themselves define a real orthogonal transformation.  Here we
specialize to `ℝ`, normalize the root, and identify its twisted action with an
explicit determinant-negative matrix on the imaginary 3-space. -/

open scoped Matrix

/-- The coordinate reflection fixing the `i` axis and interchanging `j` and `k`. -/
def pinMinusJKReflection3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- The coordinate reflection fixing the `k` axis and interchanging `i` and `j`. -/
def pinMinusIJReflection3 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- Explicit non-commutativity witness for `pinMinusJKReflection3` and `pinMinusIJReflection3`. -/
lemma pinMinusJKReflection3_noncomm :
    pinMinusJKReflection3 * pinMinusIJReflection3 ≠
      pinMinusIJReflection3 * pinMinusJKReflection3 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [pinMinusJKReflection3, pinMinusIJReflection3,
    Matrix.mul_apply, Fin.sum_univ_three] at h01

/-- Unit-length quaternion lift of `j-k`, normalized by its Euclidean length. -/
noncomputable def pinMinusJKUnitRoot : Quaternion ℝ :=
  (Real.sqrt 2)⁻¹ • (Quat.reflJK : Quaternion ℝ)

/-- The normalized root has norm-square one and remains a pure imaginary
quaternion, so its negative square is `-1` as required by the `Pin_-`
reflection convention. -/
lemma pinMinusJKUnitRoot_norm_and_square :
    Quaternion.normSq pinMinusJKUnitRoot = 1 ∧
      pinMinusJKUnitRoot * pinMinusJKUnitRoot = (-1 : Quaternion ℝ) ∧
      star pinMinusJKUnitRoot = -pinMinusJKUnitRoot := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by nlinarith [hs2]
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  constructor
  · rw [Quaternion.normSq_def']
    simp [pinMinusJKUnitRoot, Quat.reflJK,
      WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK]
    field_simp
    nlinarith [hs2]
  constructor
  · (apply Quaternion.ext <;>
      simp [pinMinusJKUnitRoot, Quat.reflJK,
        WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK]);
    field_simp;
    nlinarith [hs2]
  · ext <;> simp [pinMinusJKUnitRoot, Quat.reflJK,
      WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK]

/-- The explicit matrix is orthogonal and has determinant `-1`, hence it is
the improper Euclidean reflection across the plane `y=z`. -/
lemma pinMinusJKReflection3_is_orthogonal_improper :
    pinMinusJKReflection3.transpose * pinMinusJKReflection3 = 1 ∧
      Matrix.det pinMinusJKReflection3 = -1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pinMinusJKReflection3, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_three]
  · norm_num [pinMinusJKReflection3, Matrix.det_fin_three,
      Matrix.of_apply]

/-- The normalized `Pin_-` sandwich action of the real quaternion root agrees
with the typed orthogonal reflection matrix on `Im(ℍ) ≅ ℝ³`. -/
lemma pinMinusJKUnitRoot_action_eq_matrix_reflection (v : Fin 3 → ℝ) :
    pinMinusJKUnitRoot *
        WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3 (v 0) (v 1) (v 2) *
        pinMinusJKUnitRoot =
      WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3
        (pinMinusJKReflection3.mulVec v 0)
        (pinMinusJKReflection3.mulVec v 1)
        (pinMinusJKReflection3.mulVec v 2) := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  apply Quaternion.ext <;>
    simp [pinMinusJKUnitRoot, Quat.reflJK,
      WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK,
      WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3,
      pinMinusJKReflection3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  <;> field_simp
  <;> rw [hs2]
  <;> ring

/-- In the `Pin_-` twisted-adjoint convention `x ↦ -r x star(r)`, the unit
root action is the same improper reflection. -/
lemma pinMinusJKUnitRoot_twistedAdjoint_eq_matrix_reflection (v : Fin 3 → ℝ) :
    -(pinMinusJKUnitRoot *
        WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3 (v 0) (v 1) (v 2) *
        star pinMinusJKUnitRoot) =
      WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3
        (pinMinusJKReflection3.mulVec v 0)
        (pinMinusJKReflection3.mulVec v 1)
        (pinMinusJKReflection3.mulVec v 2) := by
  have hstar := pinMinusJKUnitRoot_norm_and_square.2.2
  calc
    _ = pinMinusJKUnitRoot *
          WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3 (v 0) (v 1) (v 2) *
          pinMinusJKUnitRoot := by rw [hstar]; simp [mul_assoc]
    _ = _ := pinMinusJKUnitRoot_action_eq_matrix_reflection v

/-- Double-cover `{±1}` kernel law for the `Pin_-` reflection lift:
both `+pinMinusJKUnitRoot` and `-pinMinusJKUnitRoot` induce the same orthogonal reflection on
`Im(ℍ) ≅ ℝ³`, and a real scalar quaternion `c • 1` acts trivially under `X ↦ U * X * U` on `i`
if and only if `c ^ 2 = 1` (`c = 1 ∨ c = -1`). -/
lemma pinMinusJKUnitRoot_double_cover_sign_kernel (v : Fin 3 → ℝ) (c : ℝ) :
    (-pinMinusJKUnitRoot) *
        WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3 (v 0) (v 1) (v 2) *
        (-pinMinusJKUnitRoot) =
      WignerHurwitzAdamsKTheoryPoset.Quat.imagQuaternion3
        (pinMinusJKReflection3.mulVec v 0)
        (pinMinusJKReflection3.mulVec v 1)
        (pinMinusJKReflection3.mulVec v 2) ∧
    ((c • (1 : Quaternion ℝ)) * (Quat.qi : Quaternion ℝ) * (c • (1 : Quaternion ℝ)) =
        (Quat.qi : Quaternion ℝ) ↔
      (c = 1 ∨ c = -1)) := by
  refine ⟨?_, ?_⟩
  · simp only [neg_mul, mul_neg, neg_neg]
    exact pinMinusJKUnitRoot_action_eq_matrix_reflection v
  · constructor
    · intro h
      have hI := congrArg (fun q : Quaternion ℝ => q.imI) h
      simp [Quat.qi, WignerHurwitzAdamsKTheoryPoset.Quat.qi] at hI
      have hsq : c ^ 2 = 1 := by linear_combination hI
      exact sq_eq_one_iff.mp hsq
    · rintro (rfl | rfl) <;>
        ext <;> simp [Quat.qi, WignerHurwitzAdamsKTheoryPoset.Quat.qi]

/-- $3 \times 3$ grading matrix `diag(1, -1, 0)` on `Matrix (Fin 3) (Fin 3) K`. -/
def mat3Diag12 {K : Type u} [CommRing K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- $3 \times 3$ transposition matrix swapping axes `0 ↔ 1` on `Matrix (Fin 3) (Fin 3) K`. -/
def mat3Swap12 {K : Type u} [CommRing K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- Closed anticommutator witness `{mat3Diag12, mat3Swap12} = 0` on `Matrix (Fin 3) (Fin 3) K`. -/
lemma mat3_diag12_swap12_anticomm {K : Type u} [CommRing K] :
    (mat3Diag12 : Matrix (Fin 3) (Fin 3) K) * mat3Swap12 + mat3Swap12 * mat3Diag12 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat3Diag12, mat3Swap12]

/-- The Cayley–Klein / Euler–Rodrigues $3 \times 3$ matrix representation
`quatAdjointMatrix3 q : Matrix (Fin 3) (Fin 3) K` of the quaternion conjugation action
`v ↦ q * v * conj q` on `Im(ℍ_K) ≅ K³`. -/
def quatAdjointMatrix3 {K : Type u} [CommRing K] (q : Quat K) : Matrix (Fin 3) (Fin 3) K :=
  let w := q.re; let a := q.imI; let b := q.imJ; let c := q.imK
  !![w * w + a * a - b * b - c * c, 2 * (a * b - w * c), 2 * (a * c + w * b);
     2 * (a * b + w * c), w * w - a * a + b * b - c * c, 2 * (b * c - w * a);
     2 * (a * c - w * b), 2 * (b * c + w * a), w * w - a * a - b * b + c * c]

/--
**Theorem 1d (𝔓𝔐₁ — Universal Cayley–Klein / Euler–Rodrigues Homomorphism `ℍ_K → Mat₃(K)`, Scaled Orthogonality & Twisted `Pin_-(3)` Recovery):**
For any `[CommRing K]`, `p, q : Quat K`, and `v : Fin 3 → K`:
1. **Exact Conjugation Representation on `Im(ℍ_K) ≅ K³`:**
   `q * Quat.vec3 (v 0) (v 1) (v 2) * Quat.conj q = Quat.vec3 ((quatAdjointMatrix3 q).mulVec v 0) ((quatAdjointMatrix3 q).mulVec v 1) ((quatAdjointMatrix3 q).mulVec v 2)`.
2. **Multiplicative Homomorphism Law (`M(p * q) = M(p) * M(q)`):**
   `quatAdjointMatrix3 (p * q) = quatAdjointMatrix3 p * quatAdjointMatrix3 q`.
3. **Identity & `{±1}` Double-Cover Kernel:**
   `quatAdjointMatrix3 (Quat.qOne : Quat K) = 1` and `quatAdjointMatrix3 (-Quat.qOne : Quat K) = 1`.
4. **Scaled Orthogonality (`M(q)ᵀ M(q) = qNorm(q)² • I₃`):**
   `(quatAdjointMatrix3 q).transpose * quatAdjointMatrix3 q = (Quat.qNorm q * Quat.qNorm q) • (1 : Matrix (Fin 3) (Fin 3) K)`.
5. **Twisted `Pin_-(3)` Improper Reflection Recovery on `pinMinusJKUnitRoot`:**
   Over `ℝ`, `-quatAdjointMatrix3 pinMinusJKUnitRoot = pinMinusJKReflection3`.
-/
lemma quatAdjointMatrix3_homomorphism_orthogonality_and_graded_2O_action
    {K : Type u} [CommRing K] (p q : Quat K) (v : Fin 3 → K) :
    q * Quat.vec3 (v 0) (v 1) (v 2) * Quat.conj q =
      Quat.vec3 ((quatAdjointMatrix3 q).mulVec v 0)
        ((quatAdjointMatrix3 q).mulVec v 1)
        ((quatAdjointMatrix3 q).mulVec v 2) ∧
    quatAdjointMatrix3 (p * q) = quatAdjointMatrix3 p * quatAdjointMatrix3 q ∧
    quatAdjointMatrix3 (Quat.qOne : Quat K) = 1 ∧
    quatAdjointMatrix3 (-Quat.qOne : Quat K) = 1 ∧
    (quatAdjointMatrix3 q).transpose * quatAdjointMatrix3 q =
      (Quat.qNorm q * Quat.qNorm q) • (1 : Matrix (Fin 3) (Fin 3) K) ∧
    -quatAdjointMatrix3 pinMinusJKUnitRoot = pinMinusJKReflection3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Quaternion.ext <;>
      (simp [quatAdjointMatrix3, Quat.vec3, Quat.conj,
        WignerHurwitzAdamsKTheoryPoset.Quat.conj, Matrix.mulVec, dotProduct, Fin.sum_univ_three];
       ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quatAdjointMatrix3, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quatAdjointMatrix3, Quat.qOne, WignerHurwitzAdamsKTheoryPoset.Quat.qOne]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quatAdjointMatrix3, Quat.qOne, WignerHurwitzAdamsKTheoryPoset.Quat.qOne]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quatAdjointMatrix3, Quat.qNorm, WignerHurwitzAdamsKTheoryPoset.Quat.qNorm,
        Quaternion.normSq_def', Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_three] <;>
      ring
  · have hs2 : (Real.sqrt 2) ^ 2 = 2 :=
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quatAdjointMatrix3, pinMinusJKUnitRoot, Quat.reflJK,
        WignerHurwitzAdamsKTheoryPoset.Quat.pinMinusRootJK, pinMinusJKReflection3] <;>
      field_simp <;>
      nlinarith [hs2]

-- ============================================================================
-- SECTION 2 (𝔓𝔐₂ & 𝔓𝔐₃): Split Brick Cl_-(1,1) ≅ Mat₂(K) & The Pin_-(8,8) P-T Group
-- ============================================================================

/-- Canonical Mathlib $2 \times 2$ matrix carrier `Matrix (Fin 2) (Fin 2) K`. -/
abbrev Mat2 (K : Type u) : Type u := Matrix (Fin 2) (Fin 2) K

namespace Mat2
variable {K : Type u} [CommRing K]

/-- $2 \times 2$ identity matrix `I₂ = (1 : Matrix (Fin 2) (Fin 2) K)`. -/
def I2 : Mat2 K := (1 : Matrix (Fin 2) (Fin 2) K)

/-- Spacelike parity generator `P = E_- = !![0, -1; 1, 0]` in `Cl_-(1,1)` (`Q(P) = +1 ⟹ P² = -I₂`). -/
def parityP : Mat2 K := !![0, -1; 1, 0]

/-- Timelike reversal generator `T = F_+ = !![1, 0; 0, -1]` in `Cl_-(1,1)` (`Q(T) = -1 ⟹ T² = +I₂`). -/
def timeT : Mat2 K := !![1, 0; 0, -1]

/-- Chiral volume / joint `PT` reflection `Γ = P * T = !![0, 1; 1, 0]`. -/
def chiralPT : Mat2 K := !![0, 1; 1, 0]

/-- Identity conversion from `Mat2 K` to `Matrix (Fin 2) (Fin 2) K`. -/
abbrev toMatrix (A : Mat2 K) : Matrix (Fin 2) (Fin 2) K := A

/-- Explicit non-commutativity witness for `parityP` and `timeT` over `ℤ`. -/
lemma parityP_timeT_noncomm :
    (parityP : Mat2 ℤ) * timeT ≠ timeT * parityP := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  revert h01
  decide

/--
**Theorem 2 (𝔓𝔐₂ & 𝔓𝔐₃ — The `Cl_-(1,1) ≅ Mat₂(K)` Split Periodicity Brick & `Pin_-(8,8)` Component Group):**
1. **8-Fold Split Bott Dimension Arithmetic:** `2 ^ 8 = 256`, `256 * 256 = 2 ^ 16`,
   `16 * 15 / 2 = 120`, and `28 + 28 = 56`.
2. **Spacelike `Pin_-` Square Law:** `parityP * parityP = -I₂` (order 4 lift of spatial parity `P`).
3. **Timelike `Pin_-` Square Law:** `timeT * timeT = +I₂` (order 2 lift of time reversal `T`).
4. **Clifford Anticommutation & Joint `PT` Involution:**
   `parityP * timeT + timeT * parityP = 0`, `parityP * timeT = chiralPT`, and `chiralPT * chiralPT = +I₂`!
-/
lemma cl_minus_1_1_split_generators_and_parity_time_d4_relations :
    -- 1. 8-fold Bott periodicity dimensions of Cl_-(8,8) and Spin⁺(8,8):
    2 ^ 8 = 256 ∧ 256 * 256 = 2 ^ 16 ∧ 16 * 15 / 2 = 120 ∧ 28 + 28 = 56 ∧
    -- 2. Spacelike Pin_- reflection squares to -I₂:
    (parityP : Mat2 K) * parityP = -I2 ∧
    -- 3. Timelike Pin_- reflection squares to +I₂:
    (timeT : Mat2 K) * timeT = I2 ∧
    -- 4. Anticommutation P*T + T*P = 0 and joint PT involution (PT)² = +I₂:
    (parityP : Mat2 K) * timeT + timeT * parityP = 0 ∧
    (parityP : Mat2 K) * timeT = chiralPT ∧
    (chiralPT : Mat2 K) * chiralPT = I2 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [parityP, timeT, chiralPT, I2, Matrix.mul_apply, Fin.sum_univ_two]

/--
**Theorem 2b (𝔓𝔐₂ & 𝔓𝔐₃ — Bridge to `InfoGeometry.Clifford.Cl11TensorTower` & `TowerMatrix.Idx 8`):**
1. Under `toMatrix`, `(parityP : Mat2 ℝ)` is `InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase`,
   `(timeT : Mat2 ℝ)` is `InfoGeometry.Clifford.Cl11Matrix.Eplus`, and
   `(chiralPT : Mat2 ℝ)` is `InfoGeometry.Clifford.Cl11Matrix.J1`.
2. At stage `n = 8`, the binary tensor index `InfoGeometry.Clifford.TowerMatrix.Idx 8` of
   `MatStage 8 = Matrix (Idx 8) (Idx 8) ℝ` has exact cardinality `256` (`2^8 = 256`).
-/
lemma cl11_tensor_tower_parity_time_and_idx8_bridge :
    toMatrix (parityP : Mat2 ℝ) = InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase ∧
    toMatrix (timeT : Mat2 ℝ) = InfoGeometry.Clifford.Cl11Matrix.Eplus ∧
    toMatrix (chiralPT : Mat2 ℝ) = InfoGeometry.Clifford.Cl11Matrix.J1 ∧
    Fintype.card (InfoGeometry.Clifford.TowerMatrix.Idx 8) = 256 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, parityP, InfoGeometry.Clifford.Cl11TensorTower.hestenesPhaseBase]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, timeT, InfoGeometry.Clifford.Cl11Matrix.Eplus]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, chiralPT, InfoGeometry.Clifford.Cl11Matrix.J1]
  · have h8 := InfoGeometry.Clifford.TowerMatrix.idx_card_pow_two 8
    norm_num at h8
    exact h8

/-- $4 \times 4$ two-stage split Clifford matrix carrier `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K`
representing $\mathcal{C}\ell_-(1,1) \hat{\otimes} \mathcal{C}\ell_-(1,1) \cong \mathcal{C}\ell_-(2,2)$. -/
abbrev Mat4Split (K : Type u) : Type u :=
  Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K

/-- First $\mathcal{C}\ell_-(3,0)$ generator $\gamma_1 = P \otimes I_2$ inside $\mathcal{C}\ell_-(2,2)$. -/
def clMinus3Gen1 : Mat4Split K :=
  Matrix.kroneckerMap (· * ·) (parityP : Mat2 K) (I2 : Mat2 K)

/-- Second $\mathcal{C}\ell_-(3,0)$ generator $\gamma_2 = \Gamma \otimes P = (PT) \otimes P$ inside $\mathcal{C}\ell_-(2,2)$. -/
def clMinus3Gen2 : Mat4Split K :=
  Matrix.kroneckerMap (· * ·) (chiralPT : Mat2 K) (parityP : Mat2 K)

/-- Third $\mathcal{C}\ell_-(3,0)$ generator $\gamma_3 = T \otimes P$ inside $\mathcal{C}\ell_-(2,2)$. -/
def clMinus3Gen3 : Mat4Split K :=
  Matrix.kroneckerMap (· * ·) (timeT : Mat2 K) (parityP : Mat2 K)

/-- Embedded $\mathrm{Pin}_-(3)$ short-root reflection $R_{23} = \gamma_2 - \gamma_3 = (\Gamma - T) \otimes P$
inside the two-stage split Clifford algebra $\mathcal{C}\ell_-(2,2)$. -/
def clMinus3Refl23 : Mat4Split K :=
  clMinus3Gen2 - clMinus3Gen3

/--
**Theorem 2c (𝔓𝔐₂ & 𝔓𝔐₃ — Constructive Embedding of $\mathcal{C}\ell_-(3,0)$ and $\mathrm{Pin}_-(3)$ Short-Root Reflection into $\mathcal{C}\ell_-(1,1)^{\otimes 2} \cong \mathrm{Mat}_4(K)$):**
1. **Negative Generator Squares ($\gamma_a^2 = -I_4$):**
   `clMinus3Gen1 * clMinus3Gen1 = -1`, `clMinus3Gen2 * clMinus3Gen2 = -1`, `clMinus3Gen3 * clMinus3Gen3 = -1`.
2. **Pairwise Clifford Anticommutation ($\{\gamma_a, \gamma_b\} = 0$ for $a \ne b$):**
   `clMinus3Gen1 * clMinus3Gen2 + clMinus3Gen2 * clMinus3Gen1 = 0`,
   `clMinus3Gen1 * clMinus3Gen3 + clMinus3Gen3 * clMinus3Gen1 = 0`,
   `clMinus3Gen2 * clMinus3Gen3 + clMinus3Gen3 * clMinus3Gen2 = 0`.
3. **Embedded $\mathrm{Pin}_-(3)$ Reflection Compatibility ($R_{23} = \gamma_2 - \gamma_3$):**
   - `clMinus3Refl23 * clMinus3Refl23 = (-2 : K) • 1`,
   - `clMinus3Refl23 * clMinus3Gen1 * clMinus3Refl23 = (2 : K) • clMinus3Gen1` (fixes axis 1),
   - `clMinus3Refl23 * clMinus3Gen2 * clMinus3Refl23 = (2 : K) • clMinus3Gen3` and
     `clMinus3Refl23 * clMinus3Gen3 * clMinus3Refl23 = (2 : K) • clMinus3Gen2` (swaps axes $2 \leftrightarrow 3$).
-/
lemma cl_minus_3_0_into_split_cl_2_2_kronecker_embedding :
    ((clMinus3Gen1 : Mat4Split K) * clMinus3Gen1 = -1 ∧
     (clMinus3Gen2 : Mat4Split K) * clMinus3Gen2 = -1 ∧
     (clMinus3Gen3 : Mat4Split K) * clMinus3Gen3 = -1) ∧
    ((clMinus3Gen1 : Mat4Split K) * clMinus3Gen2 + clMinus3Gen2 * clMinus3Gen1 = 0 ∧
     (clMinus3Gen1 : Mat4Split K) * clMinus3Gen3 + clMinus3Gen3 * clMinus3Gen1 = 0 ∧
     (clMinus3Gen2 : Mat4Split K) * clMinus3Gen3 + clMinus3Gen3 * clMinus3Gen2 = 0) ∧
    ((clMinus3Refl23 : Mat4Split K) * clMinus3Refl23 = (-2 : K) • (1 : Mat4Split K) ∧
     (clMinus3Refl23 : Mat4Split K) * clMinus3Gen1 * clMinus3Refl23 = (2 : K) • clMinus3Gen1 ∧
     (clMinus3Refl23 : Mat4Split K) * clMinus3Gen2 * clMinus3Refl23 = (2 : K) • clMinus3Gen3 ∧
     (clMinus3Refl23 : Mat4Split K) * clMinus3Gen3 * clMinus3Refl23 = (2 : K) • clMinus3Gen2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp [clMinus3Gen1, clMinus3Gen2, clMinus3Gen3, clMinus3Refl23,
        parityP, timeT, chiralPT, I2,
        Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring

/-- The negative-definite 3D quadratic form `Q_{3,0}^-(x) = -x₀² - x₁² - x₂²` on `Fin 3 → K`
governing $\mathcal{C}\ell_-(3,0) = \mathcal{C}\ell(0,3)$. -/
noncomputable abbrev qMinus30 (K : Type u) [CommRing K] : QuadraticForm K (Fin 3 → K) :=
  QuadraticMap.weightedSumSquares K (fun _ : Fin 3 => (-1 : K))

/-- Indexed generator family `γ : Fin 3 → Mat4Split K` for $\mathcal{C}\ell_-(3,0) \hookrightarrow \mathcal{C}\ell_-(2,2)$. -/
def clMinus3GenFamily : Fin 3 → Mat4Split K
  | ⟨0, _⟩ => clMinus3Gen1
  | ⟨1, _⟩ => clMinus3Gen2
  | ⟨2, _⟩ => clMinus3Gen3

/-- Pairwise anticommutation of the indexed family `clMinus3GenFamily`. -/
lemma clMinus3GenFamily_anti (i j : Fin 3) (hne : i ≠ j) :
    (clMinus3GenFamily i : Mat4Split K) * clMinus3GenFamily j +
      clMinus3GenFamily j * clMinus3GenFamily i = 0 := by
  have h := (cl_minus_3_0_into_split_cl_2_2_kronecker_embedding (K := K)).2.1
  fin_cases i <;> fin_cases j
  · exact False.elim (hne rfl)
  · exact h.1
  · exact h.2.1
  · simpa [clMinus3GenFamily, add_comm] using h.1
  · exact False.elim (hne rfl)
  · exact h.2.2
  · simpa [clMinus3GenFamily, add_comm] using h.2.1
  · simpa [clMinus3GenFamily, add_comm] using h.2.2
  · exact False.elim (hne rfl)

/-- Negative-square law `γ_i² = -1` in `algebraMap` form for `CliffordAlgebra.lift`. -/
lemma clMinus3GenFamily_sq (i : Fin 3) :
    (clMinus3GenFamily i : Mat4Split K) * clMinus3GenFamily i =
      algebraMap K (Mat4Split K) ((fun _ : Fin 3 => (-1 : K)) i) := by
  have h := (cl_minus_3_0_into_split_cl_2_2_kronecker_embedding (K := K)).1
  rw [map_neg, map_one]
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Universal `K`-algebra homomorphism `CliffordAlgebra (qMinus30 K) →ₐ[K] Mat4Split K`
constructed via `CliffordAlgebra.lift` and `AnticommutingSum.basis_square`. -/
noncomputable def clMinus30ToMat4SplitAlgHom :
    CliffordAlgebra (qMinus30 K) →ₐ[K] Mat4Split K :=
  CliffordAlgebra.lift (qMinus30 K)
    ⟨(Pi.basisFun K (Fin 3)).constr K (clMinus3GenFamily (K := K)),
      InfoGeometry.Core.AnticommutingSum.basis_square
        (clMinus3GenFamily (K := K)) (fun _ : Fin 3 => (-1 : K))
        clMinus3GenFamily_anti clMinus3GenFamily_sq⟩

/-- Evaluation of `clMinus30ToMat4SplitAlgHom` on any vector `CliffordAlgebra.ι (qMinus30 K) x`. -/
@[simp] lemma clMinus30ToMat4SplitAlgHom_ι (x : Fin 3 → K) :
    clMinus30ToMat4SplitAlgHom (CliffordAlgebra.ι (qMinus30 K) x) =
      ∑ i : Fin 3, x i • (clMinus3GenFamily i : Mat4Split K) := by
  rw [clMinus30ToMat4SplitAlgHom, CliffordAlgebra.lift_ι_apply]
  simp [Module.Basis.constr_apply_fintype]

/-- Evaluation of `clMinus30ToMat4SplitAlgHom` on the three standard basis vectors `e₀, e₁, e₂`. -/
@[simp] lemma clMinus30ToMat4SplitAlgHom_basis (i : Fin 3) :
    clMinus30ToMat4SplitAlgHom (K := K) (CliffordAlgebra.ι (qMinus30 K) (Pi.single i 1)) =
      clMinus3GenFamily i := by
  simp [clMinus30ToMat4SplitAlgHom_ι, Pi.single_apply]

/-- Uniqueness of `clMinus30ToMat4SplitAlgHom`: any `K`-algebra homomorphism from
`CliffordAlgebra (qMinus30 K)` to `Mat4Split K` agreeing on the three standard basis generators
is equal to `clMinus30ToMat4SplitAlgHom`. -/
lemma clMinus30ToMat4SplitAlgHom_unique
    (f : CliffordAlgebra (qMinus30 K) →ₐ[K] Mat4Split K)
    (hf : ∀ i : Fin 3, f (CliffordAlgebra.ι (qMinus30 K) (Pi.single i 1)) = clMinus3GenFamily i) :
    f = clMinus30ToMat4SplitAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply (Pi.basisFun K (Fin 3)).ext
  intro i
  simpa using (hf i).trans (clMinus30ToMat4SplitAlgHom_basis (K := K) i).symm

/-- Explicit index equivalence between `TowerMatrix.Idx 2 = (Idx 0 × Fin 2) × Fin 2` and `Fin 2 × Fin 2`. -/
def idx2EquivFin2ProdFin2 : InfoGeometry.Clifford.TowerMatrix.Idx 2 ≃ Fin 2 × Fin 2 where
  toFun x := (x.1.2, x.2)
  invFun y := ((default, y.1), y.2)
  left_inv x := by
    rcases x with ⟨⟨u, i₁⟩, i₂⟩
    have hu : u = default := Subsingleton.elim u default
    subst hu
    rfl
  right_inv _ := rfl

/-- `ℝ`-algebra isomorphism identifying `Mat4Split ℝ` with `TowerMatrix.Mat 2`. -/
noncomputable def mat4SplitEquivMatStage2 :
    Mat4Split ℝ ≃ₐ[ℝ] InfoGeometry.Clifford.TowerMatrix.Mat 2 :=
  Matrix.reindexAlgEquiv ℝ ℝ idx2EquivFin2ProdFin2.symm

open scoped Kronecker in
/-- One-step Kronecker `ℝ`-algebra homomorphism `A ↦ A ⊗ₖ I₂` from `TowerMatrix.Mat n` to `TowerMatrix.Mat (n + 1)`. -/
noncomputable def matStageStepAlgHom (n : ℕ) :
    InfoGeometry.Clifford.TowerMatrix.Mat n →ₐ[ℝ]
      InfoGeometry.Clifford.TowerMatrix.Mat (n + 1) where
  toFun A := A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    change (A * B) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ))
    rw [← Matrix.mul_kronecker_mul, mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  commutes' r := by
    change (algebraMap ℝ (InfoGeometry.Clifford.TowerMatrix.Mat n) r) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      algebraMap ℝ (InfoGeometry.Clifford.TowerMatrix.Mat (n + 1)) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker, Matrix.one_kronecker_one]
    rfl

open scoped Kronecker in
/-- Every one-step Kronecker tower embedding `A ↦ A ⊗ₖ I₂` is injective. -/
lemma matStageStepAlgHom_injective (n : ℕ) :
    Function.Injective (matStageStepAlgHom n) := by
  intro A B hAB
  ext i j
  have hij : (matStageStepAlgHom n A) (i, (0 : Fin 2)) (j, (0 : Fin 2)) =
      (matStageStepAlgHom n B) (i, (0 : Fin 2)) (j, (0 : Fin 2)) :=
    congr_fun (congr_fun hAB (i, (0 : Fin 2))) (j, (0 : Fin 2))
  change A i j * (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
    B i j * (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 at hij
  simpa using hij

/-- Faithful 6-step Kronecker `ℝ`-algebra homomorphism `A ↦ A ⊗ I₂^{\otimes 6}` from
`Mat4Split ℝ ≅ MatStage 2` into `TowerMatrix.Mat 8` ($\mathcal{C}\ell_-(8,8) \cong \mathrm{Mat}_{256}(\mathbb{R})$). -/
noncomputable def mat4SplitToMatStage8AlgHom :
    Mat4Split ℝ →ₐ[ℝ] InfoGeometry.Clifford.TowerMatrix.Mat 8 :=
  (matStageStepAlgHom 7).comp <|
    (matStageStepAlgHom 6).comp <|
      (matStageStepAlgHom 5).comp <|
        (matStageStepAlgHom 4).comp <|
          (matStageStepAlgHom 3).comp <|
            (matStageStepAlgHom 2).comp mat4SplitEquivMatStage2.toAlgHom

/-- The 6-step Kronecker embedding `Mat4Split ℝ →ₐ[ℝ] TowerMatrix.Mat 8` is injective. -/
lemma mat4SplitToMatStage8AlgHom_injective :
    Function.Injective mat4SplitToMatStage8AlgHom := by
  intro A B hAB
  dsimp [mat4SplitToMatStage8AlgHom] at hAB
  have h7 := matStageStepAlgHom_injective 7 hAB
  have h6 := matStageStepAlgHom_injective 6 h7
  have h5 := matStageStepAlgHom_injective 5 h6
  have h4 := matStageStepAlgHom_injective 4 h5
  have h3 := matStageStepAlgHom_injective 3 h4
  have h2 := matStageStepAlgHom_injective 2 h3
  exact mat4SplitEquivMatStage2.injective h2

/-- Composite universal `ℝ`-algebra homomorphism from `CliffordAlgebra (qMinus30 ℝ)` into
the 8-stage split Clifford matrix algebra `TowerMatrix.Mat 8` ($\mathrm{Mat}_{256}(\mathbb{R})$). -/
noncomputable def clMinus30ToMatStage8AlgHom :
    CliffordAlgebra (qMinus30 ℝ) →ₐ[ℝ] InfoGeometry.Clifford.TowerMatrix.Mat 8 :=
  mat4SplitToMatStage8AlgHom.comp (clMinus30ToMat4SplitAlgHom (K := ℝ))

/-- The $i$-th $\mathcal{C}\ell_-(3,0)$ generator inside `TowerMatrix.Mat 8` ($\mathrm{Mat}_{256}(\mathbb{R})$). -/
noncomputable def clStage8Gen (i : Fin 3) : InfoGeometry.Clifford.TowerMatrix.Mat 8 :=
  clMinus30ToMatStage8AlgHom (CliffordAlgebra.ι (qMinus30 ℝ) (Pi.single i 1))

/-- The embedded $\mathrm{Pin}_-(3)$ short-root reflection $R_{23} = \gamma_2 - \gamma_3$ inside `TowerMatrix.Mat 8`. -/
noncomputable def clStage8Refl23 : InfoGeometry.Clifford.TowerMatrix.Mat 8 :=
  clMinus30ToMatStage8AlgHom (CliffordAlgebra.ι (qMinus30 ℝ) (Pi.single 1 1 - Pi.single 2 1))

/--
**Theorem 2d (𝔓𝔐₂ & 𝔓𝔐₃ — Universal `CliffordAlgebra` Lift & Faithful Kronecker Embedding into `TowerMatrix.Mat 8`):**
1. **Faithfulness:** `Function.Injective mat4SplitToMatStage8AlgHom`.
2. **Stage-8 Generator Images:** `clStage8Gen i = mat4SplitToMatStage8AlgHom (clMinus3GenFamily i)` and
   `clStage8Refl23 = mat4SplitToMatStage8AlgHom clMinus3Refl23`.
3. **Stage-8 $\mathcal{C}\ell_-(3,0)$ Clifford & $\mathrm{Pin}_-(3)$ Reflection Relations in $\mathrm{Mat}_{256}(\mathbb{R})$:**
   - `clStage8Gen i * clStage8Gen i = -1`,
   - `clStage8Gen i * clStage8Gen j + clStage8Gen j * clStage8Gen i = 0` (`i ≠ j`),
   - `clStage8Refl23 * clStage8Refl23 = (-2 : ℝ) • 1`,
   - `clStage8Refl23 * clStage8Gen 0 * clStage8Refl23 = (2 : ℝ) • clStage8Gen 0`,
   - `clStage8Refl23 * clStage8Gen 1 * clStage8Refl23 = (2 : ℝ) • clStage8Gen 2`,
   - `clStage8Refl23 * clStage8Gen 2 * clStage8Refl23 = (2 : ℝ) • clStage8Gen 1`.
-/
lemma clMinus30_into_matStage8_algHom_and_reflection_transport :
    Function.Injective mat4SplitToMatStage8AlgHom ∧
    (∀ i : Fin 3, clStage8Gen i = mat4SplitToMatStage8AlgHom (clMinus3GenFamily i)) ∧
    clStage8Refl23 = mat4SplitToMatStage8AlgHom clMinus3Refl23 ∧
    (∀ i : Fin 3, clStage8Gen i * clStage8Gen i = -1) ∧
    (∀ i j : Fin 3, i ≠ j → clStage8Gen i * clStage8Gen j + clStage8Gen j * clStage8Gen i = 0) ∧
    clStage8Refl23 * clStage8Refl23 = (-2 : ℝ) • (1 : InfoGeometry.Clifford.TowerMatrix.Mat 8) ∧
    clStage8Refl23 * clStage8Gen 0 * clStage8Refl23 = (2 : ℝ) • clStage8Gen 0 ∧
    clStage8Refl23 * clStage8Gen 1 * clStage8Refl23 = (2 : ℝ) • clStage8Gen 2 ∧
    clStage8Refl23 * clStage8Gen 2 * clStage8Refl23 = (2 : ℝ) • clStage8Gen 1 := by
  have hGen : ∀ i : Fin 3, clStage8Gen i = mat4SplitToMatStage8AlgHom (clMinus3GenFamily i) := by
    intro i
    simp [clStage8Gen, clMinus30ToMatStage8AlgHom]
  have hRefl : clStage8Refl23 = mat4SplitToMatStage8AlgHom clMinus3Refl23 := by
    simp [clStage8Refl23, clMinus30ToMatStage8AlgHom, map_sub,
      clMinus3Refl23, clMinus3GenFamily]
  have hEmb := cl_minus_3_0_into_split_cl_2_2_kronecker_embedding (K := ℝ)
  refine ⟨mat4SplitToMatStage8AlgHom_injective, hGen, hRefl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hGen i, ← map_mul]
    have hsq := clMinus3GenFamily_sq (K := ℝ) i
    rw [map_neg, map_one] at hsq
    rw [hsq, map_neg, map_one]
  · intro i j hij
    rw [hGen i, hGen j, ← map_mul, ← map_mul, ← map_add,
      clMinus3GenFamily_anti i j hij, map_zero]
  · rw [hRefl, ← map_mul, hEmb.2.2.1, map_smul, map_one]
  · rw [hRefl, hGen 0, ← map_mul, ← map_mul]
    change mat4SplitToMatStage8AlgHom (clMinus3Refl23 * clMinus3Gen1 * clMinus3Refl23) =
      (2 : ℝ) • mat4SplitToMatStage8AlgHom clMinus3Gen1
    rw [hEmb.2.2.2.1, map_smul]
  · rw [hRefl, hGen 1, hGen 2, ← map_mul, ← map_mul]
    change mat4SplitToMatStage8AlgHom (clMinus3Refl23 * clMinus3Gen2 * clMinus3Refl23) =
      (2 : ℝ) • mat4SplitToMatStage8AlgHom clMinus3Gen3
    rw [hEmb.2.2.2.2.1, map_smul]
  · rw [hRefl, hGen 2, hGen 1, ← map_mul, ← map_mul]
    change mat4SplitToMatStage8AlgHom (clMinus3Refl23 * clMinus3Gen3 * clMinus3Refl23) =
      (2 : ℝ) • mat4SplitToMatStage8AlgHom clMinus3Gen2
    rw [hEmb.2.2.2.2.2, map_smul]

end Mat2

-- ============================================================================
-- SECTION 3 (𝔓𝔐₄): The ℤ₈ (Pin_- ABK) × ℤ₃ (Spin(8) Triality) ≅ ℤ₂₄ (Adams J) Bridge
-- ============================================================================

section PinMinusTrialityAdamsBridge
variable {K : Type u} [CommRing K]

/-- 3rd cyclotomic polynomial `Φ₃(x) = x² + x + 1` (re-exported from `WignerHurwitzAdamsKTheoryPoset.Phi3`). -/
abbrev Phi3  (x : K) : K := WignerHurwitzAdamsKTheoryPoset.Phi3 x

/-- 6th cyclotomic polynomial `Φ₆(x) = x² - x + 1` (re-exported from `WignerHurwitzAdamsKTheoryPoset.Phi6`). -/
abbrev Phi6  (x : K) : K := WignerHurwitzAdamsKTheoryPoset.Phi6 x

/-- 8th cyclotomic polynomial `Φ₈(x) = x⁴ + 1` (re-exported from `WignerHurwitzAdamsKTheoryPoset.Phi8`). -/
abbrev Phi8  (x : K) : K := WignerHurwitzAdamsKTheoryPoset.Phi8 x

/-- 24th cyclotomic polynomial `Φ₂₄(x) = x⁸ - x⁴ + 1` (re-exported from `WignerHurwitzAdamsKTheoryPoset.Phi24`). -/
abbrev Phi24 (x : K) : K := WignerHurwitzAdamsKTheoryPoset.Phi24 x

/--
**Theorem 3 (𝔓𝔐₄ — The `Pin_-` Arf–Brown–Kervaire `ℤ₈` × `Spin(8)` Triality `ℤ₃` ≅ `ℤ₂₄` Cyclotomic Bridge):**
1. **Chinese Remainder Coprimality (`ℤ₈ × ℤ₃ ≅ ℤ₂₄`):** `8 * 3 = 24` and Bézout identity `3 * 3 - 1 * 8 = 1`.
2. **Triality Action on the `Pin_-` 8th Cyclotomic Mode (`x ↦ x³`):**
   Substituting the 3-fold `Spin(8)` triality power `x³` into the `Pin_-` polynomial `Φ₈(x) = x⁴ + 1`
   splits into `Φ₈(x)` times the 24-periodic Adams `J` polynomial `Φ₂₄(x)`:
   `Phi8 (x ^ 3) = Phi8 x * Phi24 x` (`x¹² + 1 = (x⁴ + 1)(x⁸ - x⁴ + 1)`), and in Mathlib's
   `Polynomial.cyclotomic` evaluation form:
   `(Polynomial.cyclotomic 8 K).eval (x ^ 3) = (Polynomial.cyclotomic 8 K).eval x * (Polynomial.cyclotomic 24 K).eval x`.
3. **Equivalence with the Bott–Hurwitz Composition `Φ₈(x) * Φ₆(x⁴)`:**
   `Phi8 (x ^ 3) = Phi8 x * Phi6 (x ^ 4)`, and `(x ^ 12 - 1) * Phi8 (x ^ 3) = x ^ 24 - 1`.
-/
lemma pin_minus_abk_triality_cyclotomic_bridge (x : K) :
    -- 1. Order & Bézout coprimality of ℤ₈ (Pin_-) and ℤ₃ (Spin(8) triality):
    8 * 3 = 24 ∧ 3 * 3 - 1 * 8 = 1 ∧
    -- 2. Triality power x³ applied to Pin_- mode Φ₈ factors into Φ₈(x) * Φ₂₄(x):
    Phi8 (x ^ 3) = Phi8 x * Phi24 x ∧
    -- 3. Equivalence with the Bott-Hurwitz composition Φ₈(x) * Φ₆(x⁴):
    Phi8 (x ^ 3) = Phi8 x * Phi6 (x ^ 4) ∧
    -- 4. 24-periodicity of every root of Φ₈(x³) = 0 (since x¹² = -1 ⟹ x²⁴ = +1):
    (x ^ 12 - 1) * Phi8 (x ^ 3) = x ^ 24 - 1 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩ <;>
  · dsimp [Phi3, Phi6, Phi8, Phi24,
      WignerHurwitzAdamsKTheoryPoset.Phi6, WignerHurwitzAdamsKTheoryPoset.Phi8,
      WignerHurwitzAdamsKTheoryPoset.Phi24]
    ring

/-- Mathlib `Polynomial.cyclotomic` evaluation bridge for `Φ₈(x³) = Φ₈(x) Φ₂₄(x)`. -/
lemma eval_cyclotomic8_cube_eq_mul_cyclotomic24 (x : K) :
    (Polynomial.cyclotomic 8 K).eval (x ^ 3) =
      (Polynomial.cyclotomic 8 K).eval x * (Polynomial.cyclotomic 24 K).eval x := by
  rw [WignerHurwitzAdamsKTheoryPoset.eval_cyclotomic8_eq_Phi8 (x ^ 3),
    WignerHurwitzAdamsKTheoryPoset.eval_cyclotomic8_eq_Phi8 x,
    WignerHurwitzAdamsKTheoryPoset.eval_cyclotomic24_eq_Phi24 x]
  exact (pin_minus_abk_triality_cyclotomic_bridge x).2.2.1

/-- Explicit Chinese Remainder ring isomorphism `ZMod 24 ≃+* ZMod 8 × ZMod 3`
(`ZMod.chineseRemainder`) decomposing the 24-periodic cycle into its coprime `ZMod 8` and `ZMod 3`
orthogonal idempotent components `(9 : ZMod 24) ↦ (1, 0)` and `(16 : ZMod 24) ↦ (0, 1)`. -/
lemma zmod24_chinese_remainder_abk_triality_split :
    let crt : ZMod 24 ≃+* ZMod 8 × ZMod 3 :=
      ZMod.chineseRemainder (by decide : Nat.Coprime 8 3)
    crt (3 : ZMod 24) = (3, 0) ∧
    crt (8 : ZMod 24) = (0, 2) ∧
    crt (9 : ZMod 24) = (1, 0) ∧
    crt (16 : ZMod 24) = (0, 1) ∧
    (9 : ZMod 24) * 9 = 9 ∧
    (16 : ZMod 24) * 16 = 16 ∧
    (9 : ZMod 24) * 16 = 0 ∧
    (9 : ZMod 24) + 16 = 1 := by
  decide

/--
**Theorem 4 (𝔓𝔐₄ — Master 4-Stage `Pin_-(8,8)` Triality Synthesis):**
Unites the 4-stage poset $\mathfrak{PM}_1 \prec \dots \prec \mathfrak{PM}_4$ in one theorem:
1. Acyclicity of `PinMinus88TrialityStage.coverEdge`,
2. Short-root `Pin_-` reflection square law `reflJK * reflJK = -2 • 1`, hyperplane reflection
   `pinRefl reflJK (vec3 x y z) = 2 • vec3 x z y`, Hurwitz triality product `reflIJ * reflJK = hurwitzW`,
   `S₃` braid identity `reflIJ * reflJK * reflIJ = -2 • reflKI`, 48-element binary octahedral coset
   partition `binaryOctahedral48Finset.card = 48`, normalized real unit-root reflection
   `pinMinusJKUnitRoot² = -1` with `det(pinMinusJKReflection3) = -1` and
   `-quatAdjointMatrix3 pinMinusJKUnitRoot = pinMinusJKReflection3` (`𝔓𝔐₁`),
3. Split `Cl_-(1,1)` parity-time relations `parityP² = -I₂`, `timeT² = +I₂`, `parityP * timeT + timeT * parityP = 0`,
   two-stage Kronecker embedding `clMinus3Refl23² = -2 • 1`, faithful 6-step `TowerMatrix.Mat 8`
   homomorphism `Function.Injective Mat2.mat4SplitToMatStage8AlgHom` with
   `Mat2.clStage8Refl23 * Mat2.clStage8Refl23 = (-2 : ℝ) • 1`, and `Fintype.card (TowerMatrix.Idx 8) = 256` (`𝔓𝔐₂–𝔓𝔐₃`),
4. Cyclotomic factorization `Phi8 (x ^ 3) = Phi8 x * Phi24 x = Phi8 x * Phi6 (x ^ 4)`,
   `(x ^ 12 - 1) * Phi8 (x ^ 3) = x ^ 24 - 1`, and Chinese Remainder idempotents `(9 : ZMod 24)` and `(16 : ZMod 24)` (`𝔓𝔐₄`).
-/
lemma pm4_master_pin_minus_88_triality_synthesis (x y z : K) :
    (∀ a : PinMinus88TrialityStage, ¬ PinMinus88TrialityStage.coverEdge a a) ∧
    (Quat.qNorm (Quat.reflJK : Quat K) = 2 ∧
     (Quat.reflJK : Quat K) * Quat.reflJK = Quat.smul (-2) Quat.qOne ∧
     Quat.pinRefl Quat.reflJK (Quat.vec3 x y z) = Quat.smul 2 (Quat.vec3 x z y) ∧
     Quat.pinRefl Quat.reflJK (Quat.pinRefl Quat.reflJK (Quat.vec3 x y z)) =
       Quat.smul 4 (Quat.vec3 x y z) ∧
     (Quat.reflIJ : Quat K) * Quat.reflJK = Quat.hurwitzW ∧
     (Quat.reflIJ : Quat K) * Quat.reflJK * Quat.reflIJ = Quat.smul (-2) Quat.reflKI ∧
     Quat.binaryOctahedral48Finset.card = 48 ∧
     Quaternion.normSq pinMinusJKUnitRoot = 1 ∧
     pinMinusJKUnitRoot * pinMinusJKUnitRoot = (-1 : Quaternion ℝ) ∧
     Matrix.det pinMinusJKReflection3 = -1 ∧
     -quatAdjointMatrix3 pinMinusJKUnitRoot = pinMinusJKReflection3) ∧
    ((Mat2.parityP : Mat2 K) * Mat2.parityP = -Mat2.I2 ∧
     (Mat2.timeT : Mat2 K) * Mat2.timeT = Mat2.I2 ∧
     (Mat2.parityP : Mat2 K) * Mat2.timeT + Mat2.timeT * Mat2.parityP = 0 ∧
     (Mat2.chiralPT : Mat2 K) * Mat2.chiralPT = Mat2.I2 ∧
     (Mat2.clMinus3Refl23 : Mat2.Mat4Split K) * Mat2.clMinus3Refl23 =
       (-2 : K) • (1 : Mat2.Mat4Split K) ∧
     Function.Injective Mat2.mat4SplitToMatStage8AlgHom ∧
     Mat2.clStage8Refl23 * Mat2.clStage8Refl23 =
       (-2 : ℝ) • (1 : InfoGeometry.Clifford.TowerMatrix.Mat 8) ∧
     Fintype.card (InfoGeometry.Clifford.TowerMatrix.Idx 8) = 256) ∧
    (8 * 3 = 24 ∧ 3 * 3 - 1 * 8 = 1 ∧
     Phi8 (x ^ 3) = Phi8 x * Phi24 x ∧
     Phi8 (x ^ 3) = Phi8 x * Phi6 (x ^ 4) ∧
     (x ^ 12 - 1) * Phi8 (x ^ 3) = x ^ 24 - 1 ∧
     (9 : ZMod 24) * 16 = 0 ∧ (9 : ZMod 24) + 16 = 1) := by
  have hRefl := Quat.pin_minus_reflection_lift_in_binary_octahedral_coset x y z
  have hBraid := Quat.pin_minus_short_root_product_eq_hurwitz_triality_and_braid_relation x y z
  have h48 := Quat.binary_octahedral_48_coset_decomposition_and_octahedral_pole_action
  have hUnit := pinMinusJKUnitRoot_norm_and_square
  have hOrth := pinMinusJKReflection3_is_orthogonal_improper
  have hAdj := quatAdjointMatrix3_homomorphism_orthogonality_and_graded_2O_action
    (Quat.qOne : Quat ℝ) (Quat.qOne : Quat ℝ) (fun _ => (0 : ℝ))
  have hPT := Mat2.cl_minus_1_1_split_generators_and_parity_time_d4_relations (K := K)
  have hCl3 := Mat2.cl_minus_3_0_into_split_cl_2_2_kronecker_embedding (K := K)
  have hSt8 := Mat2.clMinus30_into_matStage8_algHom_and_reflection_transport
  have hIdx8 := Mat2.cl11_tensor_tower_parity_time_and_idx8_bridge
  have hCyc := pin_minus_abk_triality_cyclotomic_bridge x
  have hCRT := zmod24_chinese_remainder_abk_triality_split
  exact ⟨PinMinus88TrialityStage.coverEdge_acyclic,
    ⟨hRefl.1, hRefl.2.1, hRefl.2.2.2.2.2.1, hRefl.2.2.2.2.2.2.1,
     hBraid.2.2.2.2.1, hBraid.2.2.2.2.2.1, h48.2.2.2.2.1, hUnit.1, hUnit.2.1, hOrth.2, hAdj.2.2.2.2.2⟩,
    ⟨hPT.2.2.2.2.1, hPT.2.2.2.2.2.1, hPT.2.2.2.2.2.2.1, hPT.2.2.2.2.2.2.2.2,
     hCl3.2.2.1, hSt8.1, hSt8.2.2.2.2.2.1, hIdx8.2.2.2⟩,
    ⟨hCyc.1, hCyc.2.1, hCyc.2.2.1, hCyc.2.2.2.1, hCyc.2.2.2.2,
     hCRT.2.2.2.2.2.2.1, hCRT.2.2.2.2.2.2.2⟩⟩

end PinMinusTrialityAdamsBridge

end PinMinus88TrialityPoset
