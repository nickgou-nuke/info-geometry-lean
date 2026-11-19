/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
import InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Categorical.SequentialRingColimit
import InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Categorical Colimit Algebra for the Cantor Double Cylinder Fractal

This module integrates the Cantor double cylinder colimit operator ring with
Felix Klein Erlangen 2.0 symmetry invariants, Krein doubled spaces, and the
Bernoulli fractal measure into a canonical `Erlangen20Datum`.

## Mathematical Architecture

1. **Double Cylinder Matrix Stages**:
   - `DoubleCylinderWord n := BitWord n × BitWord n`
   - `doubleCylinderOp B n u v := doubleCylinderUnit B n u v`
   - Matrix unit calculus: $E_{u, v} E_{w, z} = \delta_{v, w} E_{u, z}$.
   - Single cylinder diagonal projections: $P_u = E_{u, u}$ are idempotent.
   - Non-commutativity: $[E_{u, v}, E_{v, u}] \ne 0$ for $u \ne v$.

2. **Sequential RingColimit Integration**:
   - Sequential diagram `doubleCylinderDiagram B` in `RingCat`.
   - Colimit carrier `CantorDoubleCylinderColimitRing B := DoubleCylinderColimit B`.
   - Universal property `doubleCylinderIsColimit B : IsColimit (doubleCylinderCocone B)`.
   - Certified non-commutativity persisting in the colimit.

3. **Krein Two-Sheet Doubled Space & Cl(1,1) Clifford Relations**:
   - Real doubled Hilbert space `DoubledSpace E` equipped with modular swap $J$
     and fundamental symmetry $\varepsilon$.
   - Descent of Clifford relations: $J^2 = \mathrm{id}$, $\varepsilon^2 = \mathrm{id}$,
     $J \varepsilon = - \varepsilon J$.
   - Filtered colimit compatibility via `TwoSheetKreinFilteredColimit`.

4. **Bernoulli Fractal Measure on Cylinder Projectors**:
   - State evaluation $\varphi_n(E_{u, v}) = \delta_{u, v} 2^{-|u|}$.
   - Exact Bernoulli measure on diagonal cylinder projections: $\varphi_n(P_w) = 2^{-|w|}$.

5. **Erlangen 2.0 Geometry Datum**:
   - Packaging of the double cylinder colimit, Krein $\mathrm{Cl}(1,1)$ symmetries,
     and invariant data into `Erlangen20Datum`.
   - Non-degeneracy model witness structure satisfying OpenGauss T17.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Canonical.ConcreteHilbertCuntzO2
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Topology
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
open InfoGeometry.Krein
open Matrix
open InfoGeometry.MetaCompiler

universe u

variable (B : Type u) [Ring B]

/-! ## 1. Double Cylinder Carriers and Matrix Stages -/

/-- A double cylinder of length `n` is an ordered pair of equal-length binary words `(u, v)`. -/
abbrev DoubleCylinderWord (n : ℕ) : Type := BitWord n × BitWord n

/-- The double cylinder operator $E_{u, v}$ as a matrix unit in stage `n`. -/
def doubleCylinderOp (n : ℕ) (u v : BitWord n) : DoubleCylinderStage B n :=
  doubleCylinderUnit B n u v

/-- Double cylinder multiplication law: $E_{u, v} E_{w, z} = \delta_{v, w} E_{u, z}$. -/
theorem doubleCylinderOp_mul (n : ℕ) (u v w z : BitWord n) :
    doubleCylinderOp B n u v * doubleCylinderOp B n w z =
      if v = w then doubleCylinderOp B n u z else 0 :=
  doubleCylinderUnit_mul B n u v w z

/-- Diagonal double cylinders are idempotent projections: $P_u^2 = P_u$. -/
theorem doubleCylinderOp_proj (n : ℕ) (u : BitWord n) :
    doubleCylinderOp B n u u * doubleCylinderOp B n u u = doubleCylinderOp B n u u := by
  have h := doubleCylinderUnit_mul B n u u u u
  simp only [ite_true] at h
  exact h

/-- Distinct double cylinder operators do not commute (Strict Noncommutative Operator Discipline). -/
theorem doubleCylinderOp_noncommutative [Nontrivial B] (n : ℕ) {u v : BitWord n} (huv : u ≠ v) :
    doubleCylinderOp B n u v * doubleCylinderOp B n v u ≠
      doubleCylinderOp B n v u * doubleCylinderOp B n u v := by
  intro h
  have h_comm : ⁅doubleCylinderUnit B n u v, doubleCylinderUnit B n v u⁆ = 0 := by
    rw [Ring.lie_def, sub_eq_zero]
    exact h
  exact doubleCylinderUnit_commutator_ne_zero B n huv h_comm

/-! ## 2. Sequential Colimit of Double Cylinder Stages in RingCat -/

/-- The inductive colimit ring of the Cantor double cylinder fractal. -/
abbrev CantorDoubleCylinderColimitRing : Type u :=
  DoubleCylinderColimit B

/-- Canonical stage inclusion of stage `n` into the colimit ring. -/
abbrev colimitInclusion (n : ℕ) : DoubleCylinderStage B n →+* CantorDoubleCylinderColimitRing B :=
  doubleCylinderInclusion B n

/-- Canonical colimit cocone in `RingCat`. -/
def doubleCylinderCocone : Cocone (doubleCylinderDiagram B) :=
  SequentialRingColimit.cocone (doubleCylinderBond B)

/-- Universal property: `doubleCylinderCocone` is a categorical colimit in `RingCat`. -/
def doubleCylinderIsColimit : IsColimit (doubleCylinderCocone B) :=
  doubleCylinderColimitWitness B

/-- Each stage inclusion into the colimit ring is injective. -/
theorem colimitInclusion_injective (n : ℕ) :
    Function.Injective (colimitInclusion B n) :=
  doubleCylinderInclusion_injective B n

/-- Strict Noncommutative Operator Discipline: The colimit ring is certified non-commutative. -/
theorem colimitRing_noncommutative [Nontrivial B] :
    ∃ a b : CantorDoubleCylinderColimitRing B, a * b ≠ b * a :=
  doubleCylinderColimit_noncommutative B

/-! ## 3. Krein Two-Sheet Doubled Space & Cl(1,1) Clifford Relations -/

/-- Two-sheet swap operator $J$ on `DoubledSpace E`. -/
def doubleCylinderModularJ (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Module.End ℝ (DoubledSpace E) :=
  (modular_j (E := E)).toLinearMap

/-- Fundamental symmetry $\varepsilon$ on `DoubledSpace E`. -/
def doubleCylinderSpectralEpsilon (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Module.End ℝ (DoubledSpace E) :=
  (spectral_epsilon (E := E)).toLinearMap

/-- Modular swap operator $J$ is an involution: $J^2 = \mathrm{id}$. -/
theorem doubleCylinderModularJ_sq (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    doubleCylinderModularJ E * doubleCylinderModularJ E = LinearMap.id := by
  apply LinearMap.ext
  intro u
  have h := congrArg (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f u)
    (doubledCarrier (E := E)).J_sq
  exact h

/-- Fundamental symmetry $\varepsilon$ is an involution: $\varepsilon^2 = \mathrm{id}$. -/
theorem doubleCylinderSpectralEpsilon_sq (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    doubleCylinderSpectralEpsilon E * doubleCylinderSpectralEpsilon E = LinearMap.id := by
  apply LinearMap.ext
  intro u
  have h := congrArg (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f u)
    (doubledCarrier (E := E)).ε_sq
  exact h

/-- Anticommutation of modular swap $J$ and fundamental symmetry $\varepsilon$: $J \varepsilon = - \varepsilon J$. -/
theorem doubleCylinderModularJ_spectralEpsilon_anticomm (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    doubleCylinderModularJ E * doubleCylinderSpectralEpsilon E =
      -(doubleCylinderSpectralEpsilon E * doubleCylinderModularJ E) := by
  apply LinearMap.ext
  intro u
  have h := congrArg (fun f : DoubledSpace E →L[ℝ] DoubledSpace E => f u)
    (doubledCarrier (E := E)).J_ε_anticomm
  exact h

/-- The two-sheet Krein symmetries satisfy full $\mathrm{Cl}(1,1)$ Clifford algebra relations. -/
theorem doubleCylinderKrein_cl11_relations (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    doubleCylinderModularJ E * doubleCylinderModularJ E = LinearMap.id ∧
    doubleCylinderSpectralEpsilon E * doubleCylinderSpectralEpsilon E = LinearMap.id ∧
    doubleCylinderModularJ E * doubleCylinderSpectralEpsilon E =
      -(doubleCylinderSpectralEpsilon E * doubleCylinderModularJ E) :=
  ⟨doubleCylinderModularJ_sq E,
   doubleCylinderSpectralEpsilon_sq E,
   doubleCylinderModularJ_spectralEpsilon_anticomm E⟩

/-- Descent of Krein involution to filtered colimits via `TwoSheetKreinFilteredColimit`. -/
theorem colimitEnd_krein_involutive (F : ℕ ⥤ ModuleCat ℝ) [HasColimit F]
    (eta : F ⟶ F) (hη : eta ≫ eta = 𝟙 F) :
    colimitEnd eta * colimitEnd eta = LinearMap.id :=
  TwoSheetKreinFilteredColimit.colimitEnd_involutive eta hη

/-- Descent of sheet exchange law to filtered colimits via `TwoSheetKreinFilteredColimit`. -/
theorem colimitEnd_krein_exchange (F : ℕ ⥤ ModuleCat ℝ) [HasColimit F]
    (eta fplus fminus : F ⟶ F) (hex : eta ≫ fplus ≫ eta = fminus) :
    colimitEnd eta * colimitEnd fplus * colimitEnd eta = colimitEnd fminus :=
  TwoSheetKreinFilteredColimit.colimitEnd_exchange eta fplus fminus hex

/-! ## 4. Bernoulli Fractal Measure on Cylinder Projectors -/

/-- Cardinality of binary word cylinder space at depth `n` is $2^n$. -/
lemma card_bitWord (n : ℕ) : Fintype.card (BitWord n) = 2 ^ n := by
  change Fintype.card (Fin n → Bool) = 2 ^ n
  simp [Fintype.card_fin, Fintype.card_bool]

/-- The normalized trace state on diagonal cylinder projectors evaluates to the exact
    Bernoulli fractal measure $\mu([w]) = 2^{-|w|}$. -/
theorem bitWordMatrixTraceFunctional_diagonal_bernoulli
    (n : ℕ) (w : BitWord n) :
    bitWordMatrixTraceFunctional n (doubleCylinderUnit ℂ n w w) = (1 / 2 : ℂ) ^ n := by
  have h_single := bitWordMatrixTraceFunctional_single n w w
  simp only [ite_true] at h_single
  change bitWordMatrixTraceFunctional n (Matrix.single w w 1) = (1 / 2 : ℂ) ^ n
  rw [h_single]
  have hcard : Fintype.card (BitWord n) = 2 ^ n := card_bitWord n
  rw [hcard]
  push_cast
  rw [← _root_.one_div_pow]

/-- Off-diagonal cylinder transition operators vanish under the trace state. -/
theorem bitWordMatrixTraceFunctional_off_diagonal
    (n : ℕ) {u v : BitWord n} (huv : u ≠ v) :
    bitWordMatrixTraceFunctional n (doubleCylinderUnit ℂ n u v) = 0 := by
  have h_single := bitWordMatrixTraceFunctional_single n u v
  simp only [huv, ite_false] at h_single
  exact h_single

/-! ## 4.5. Concrete Hilbert Operator Representation on `H_lp ℝ` -/

/-- Cuntz branch continuous linear map for bit `b : Bool` on `H_lp ℝ`.
    `false ↦ S_left_lp_clm`, `true ↦ S_right_lp_clm`. -/
def cuntzBranchCLM (b : Bool) : H_lp ℝ →L[ℝ] H_lp ℝ :=
  if b then S_right_lp_clm else S_left_lp_clm

/-- Pullback (adjoint coisometry) for bit `b : Bool` on `H_lp ℝ`. -/
def cuntzPullbackCLM (b : Bool) : H_lp ℝ →L[ℝ] H_lp ℝ :=
  (cuntzBranchCLM b).adjoint

/-- Cuntz $O_2$ partition-of-unity on `H_lp ℝ`:
    `S_{false} S_{false}^* + S_{true} S_{true}^* = id`. -/
theorem cuntz_o2_partition_of_unity :
    (cuntzBranchCLM false).comp (cuntzPullbackCLM false) +
    (cuntzBranchCLM true).comp (cuntzPullbackCLM true) =
      ContinuousLinearMap.id ℝ (H_lp ℝ) := by
  dsimp [cuntzBranchCLM, cuntzPullbackCLM]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  obtain ⟨φ₁, φ₂, hy⟩ := cuntz_o2_lp_decomposition (E := ℝ) y
  rw [hy]
  simp only [ContinuousLinearMap.id_apply, inner_add_right, _root_.add_apply, ContinuousLinearMap.comp_apply, inner_add_left]
  have hL (u v : H_lp ℝ) : inner ℝ (S_left_lp_clm (E := ℝ) u) (S_left_lp_clm (E := ℝ) v) = inner ℝ u v :=
    (LinearIsometry.mk (S_left_lp_linear (E := ℝ)) S_left_lp_norm_eq).inner_map_map u v
  have hR (u v : H_lp ℝ) : inner ℝ (S_right_lp_clm (E := ℝ) u) (S_right_lp_clm (E := ℝ) v) = inner ℝ u v :=
    (LinearIsometry.mk (S_right_lp_linear (E := ℝ)) S_right_lp_norm_eq).inner_map_map u v
  have hRL (u v : H_lp ℝ) : inner ℝ (S_right_lp_clm (E := ℝ) u) (S_left_lp_clm (E := ℝ) v) = 0 := by
    rw [lp.inner_eq_tsum]
    have h_zero (k : BinaryCantorBoundary) :
        inner ℝ (S_right_lp_clm (E := ℝ) u k) (S_left_lp_clm (E := ℝ) v k) = 0 := by
      rw [S_right_lp_clm_apply, S_left_lp_clm_apply]
      split_ifs with h1 h2
      · exfalso; rw [h1] at h2; cases h2
      · rw [inner_zero_right]
      · rw [inner_zero_left]
      · rw [inner_zero_left]
    simp_rw [h_zero, tsum_zero]
  have hLR (u v : H_lp ℝ) : inner ℝ (S_left_lp_clm (E := ℝ) u) (S_right_lp_clm (E := ℝ) v) = 0 := by
    rw [real_inner_comm]
    exact hRL v u
  rw [hL, hRL, hLR, hR]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  rw [add_zero, zero_add]

/-- Word operator on `H_lp ℝ` for a binary word of depth `n`. -/
def wordCLM : (n : ℕ) → BitWord n → (H_lp ℝ →L[ℝ] H_lp ℝ)
  | 0, _ => ContinuousLinearMap.id ℝ (H_lp ℝ)
  | n + 1, w => (wordCLM n (prefixSucc n w)).comp (cuntzBranchCLM (w ⟨n, Nat.lt_succ_self n⟩))

/-- Word pullback (adjoint coisometry) on `H_lp ℝ` for a binary word of depth `n`. -/
def wordPullbackCLM : (n : ℕ) → BitWord n → (H_lp ℝ →L[ℝ] H_lp ℝ)
  | 0, _ => ContinuousLinearMap.id ℝ (H_lp ℝ)
  | n + 1, w => (cuntzPullbackCLM (w ⟨n, Nat.lt_succ_self n⟩)).comp (wordPullbackCLM n (prefixSucc n w))

/-- Cylinder partial isometry `E_{u, v} = S_u S_v^*` on `H_lp ℝ`. -/
def bitWordUnitCLM (n : ℕ) (u v : BitWord n) : H_lp ℝ →L[ℝ] H_lp ℝ :=
  (wordCLM n u).comp (wordPullbackCLM n v)

@[simp]
theorem wordCLM_extendSucc (n : ℕ) (u : BitWord n) (b : Bool) :
    wordCLM (n + 1) (extendSucc n u b) =
      (wordCLM n u).comp (cuntzBranchCLM b) := by
  dsimp [wordCLM]
  have hpref : prefixSucc n (extendSucc n u b) = u := by
    funext i; exact congrFun (prefixSucc_extendSucc n u b) i
  have hlast : (extendSucc n u b) ⟨n, Nat.lt_succ_self n⟩ = b := by
    dsimp [extendSucc]; split_ifs with h <;> first | omega | rfl
  rw [hpref, hlast]

@[simp]
theorem wordPullbackCLM_extendSucc (n : ℕ) (v : BitWord n) (b : Bool) :
    wordPullbackCLM (n + 1) (extendSucc n v b) =
      (cuntzPullbackCLM b).comp (wordPullbackCLM n v) := by
  dsimp [wordPullbackCLM]
  have hpref : prefixSucc n (extendSucc n v b) = v := by
    funext i; exact congrFun (prefixSucc_extendSucc n v b) i
  have hlast : (extendSucc n v b) ⟨n, Nat.lt_succ_self n⟩ = b := by
    dsimp [extendSucc]; split_ifs with h <;> first | omega | rfl
  rw [hpref, hlast]

/-- Dyadic subdivision decomposition of cylinder partial isometries:
    `S_u S_v^* = S_{u0} S_{v0}^* + S_{u1} S_{v1}^*`. -/
theorem bitWordUnitCLM_decomp (n : ℕ) (u v : BitWord n) :
    bitWordUnitCLM (n + 1) (extendSucc n u false) (extendSucc n v false) +
    bitWordUnitCLM (n + 1) (extendSucc n u true) (extendSucc n v true) =
      bitWordUnitCLM n u v := by
  dsimp [bitWordUnitCLM]
  rw [wordCLM_extendSucc, wordPullbackCLM_extendSucc]
  rw [wordCLM_extendSucc, wordPullbackCLM_extendSucc]
  have h1 : (wordCLM n u).comp (cuntzBranchCLM false) ∘L (cuntzPullbackCLM false).comp (wordPullbackCLM n v) =
            (wordCLM n u).comp (((cuntzBranchCLM false).comp (cuntzPullbackCLM false)).comp (wordPullbackCLM n v)) := by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (cuntzBranchCLM false)]
  have h2 : (wordCLM n u).comp (cuntzBranchCLM true) ∘L (cuntzPullbackCLM true).comp (wordPullbackCLM n v) =
            (wordCLM n u).comp (((cuntzBranchCLM true).comp (cuntzPullbackCLM true)).comp (wordPullbackCLM n v)) := by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (cuntzBranchCLM true)]
  rw [h1, h2]
  rw [← ContinuousLinearMap.comp_add]
  rw [← ContinuousLinearMap.add_comp]
  rw [cuntz_o2_partition_of_unity]
  rw [ContinuousLinearMap.id_comp]

theorem cuntzBranchCLM_inner (b c : Bool) (u v : H_lp ℝ) :
    inner ℝ (cuntzBranchCLM b u) (cuntzBranchCLM c v) =
      if b = c then inner ℝ u v else 0 := by
  have hL (x y : H_lp ℝ) :
      inner ℝ (S_left_lp_clm (E := ℝ) x) (S_left_lp_clm (E := ℝ) y) = inner ℝ x y :=
    (LinearIsometry.mk (S_left_lp_linear (E := ℝ)) S_left_lp_norm_eq).inner_map_map x y
  have hR (x y : H_lp ℝ) :
      inner ℝ (S_right_lp_clm (E := ℝ) x) (S_right_lp_clm (E := ℝ) y) = inner ℝ x y :=
    (LinearIsometry.mk (S_right_lp_linear (E := ℝ)) S_right_lp_norm_eq).inner_map_map x y
  have hRL (x y : H_lp ℝ) :
      inner ℝ (S_right_lp_clm (E := ℝ) x) (S_left_lp_clm (E := ℝ) y) = 0 := by
    rw [lp.inner_eq_tsum]
    have h_zero (k : BinaryCantorBoundary) :
        inner ℝ (S_right_lp_clm (E := ℝ) x k) (S_left_lp_clm (E := ℝ) y k) = 0 := by
      rw [S_right_lp_clm_apply, S_left_lp_clm_apply]
      split_ifs with h1 h2
      · exfalso; rw [h1] at h2; cases h2
      · rw [inner_zero_right]
      · rw [inner_zero_left]
      · rw [inner_zero_left]
    simp_rw [h_zero, tsum_zero]
  have hLR (x y : H_lp ℝ) :
      inner ℝ (S_left_lp_clm (E := ℝ) x) (S_right_lp_clm (E := ℝ) y) = 0 := by
    rw [real_inner_comm]
    exact hRL y x
  cases b <;> cases c
  · simpa [cuntzBranchCLM] using hL u v
  · simpa [cuntzBranchCLM] using hLR u v
  · simpa [cuntzBranchCLM] using hRL u v
  · simpa [cuntzBranchCLM] using hR u v

/-- Cuntz $O_2$ branch pullback orthogonality: $S_b^* S_c = \delta_{b, c} \mathrm{id}$. -/
theorem cuntzPullbackCLM_comp_cuntzBranchCLM (b c : Bool) :
    (cuntzPullbackCLM b).comp (cuntzBranchCLM c) =
      if b = c then ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.comp_apply]
  dsimp [cuntzPullbackCLM]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [cuntzBranchCLM_inner c b x y]
  by_cases hbc : b = c
  · subst hbc
    simp only [ite_true, ContinuousLinearMap.id_apply]
  · have hcb : c ≠ b := Ne.symm hbc
    simp only [hbc, hcb, ite_false, _root_.zero_apply, inner_zero_left]

/-- Word pullback orthogonality at depth `n`: $S_v^* S_w = \delta_{v, w} \mathrm{id}$. -/
theorem wordPullbackCLM_comp_wordCLM (n : ℕ) (v w : BitWord n) :
    (wordPullbackCLM n v).comp (wordCLM n w) =
      if v = w then ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
  induction n with
  | zero =>
      have hvw : v = w := by
        funext i
        exact Fin.elim0 i
      subst hvw
      simp [wordPullbackCLM, wordCLM]
  | succ n ih =>
      dsimp [wordPullbackCLM, wordCLM]
      rw [ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc (wordPullbackCLM n (prefixSucc n v))]
      rw [ih (prefixSucc n v) (prefixSucc n w)]
      by_cases hpref : prefixSucc n v = prefixSucc n w
      · simp only [hpref, ite_true, ContinuousLinearMap.id_comp]
        rw [cuntzPullbackCLM_comp_cuntzBranchCLM]
        have hiff : (v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩) ↔ (v = w) := by
          constructor
          · intro hlast
            apply (bitWordSuccEquiv n).injective
            exact Prod.ext hpref hlast
          · intro hvw
            rw [hvw]
        by_cases hlast : v ⟨n, Nat.lt_succ_self n⟩ = w ⟨n, Nat.lt_succ_self n⟩
        · simp [hiff.mp hlast]
        · have hne : v ≠ w := mt hiff.mpr hlast
          simp [hlast, hne]
      · simp only [hpref, ite_false, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
        have hne : v ≠ w := by
          intro hvw
          apply hpref
          rw [hvw]
        simp [hne]

/-- Matrix unit composition law: $(S_u S_v^*) \circ (S_w S_z^*) = \delta_{v, w} S_u S_z^*$. -/
theorem bitWordUnitCLM_comp (n : ℕ) (u v w z : BitWord n) :
    (bitWordUnitCLM n u v).comp (bitWordUnitCLM n w z) =
      if v = w then bitWordUnitCLM n u z else 0 := by
  dsimp [bitWordUnitCLM]
  rw [ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (wordPullbackCLM n v)]
  rw [wordPullbackCLM_comp_wordCLM n v w]
  by_cases hvw : v = w
  · simp [hvw, ContinuousLinearMap.id_comp]
  · simp [hvw, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- Matrix unit multiplication law: $(S_u S_v^*)(S_w S_z^*) = \delta_{v, w} S_u S_z^*$. -/
theorem bitWordUnitCLM_mul (n : ℕ) (u v w z : BitWord n) :
    bitWordUnitCLM n u v * bitWordUnitCLM n w z =
      if v = w then bitWordUnitCLM n u z else 0 :=
  bitWordUnitCLM_comp n u v w z

theorem bitWordUnitCLM_decomp_smul (n : ℕ) (c : ℝ) (u v : BitWord n) :
    c • bitWordUnitCLM (n + 1) (extendSucc n u true) (extendSucc n v true) +
    c • bitWordUnitCLM (n + 1) (extendSucc n u false) (extendSucc n v false) =
      c • bitWordUnitCLM n u v := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [_root_.add_apply, _root_.smul_apply]
  rw [add_comm, ← smul_add]
  have h := congrArg (fun T : H_lp ℝ →L[ℝ] H_lp ℝ => T x) (bitWordUnitCLM_decomp n u v)
  simp only [_root_.add_apply] at h
  rw [h]

theorem cuntzBranchCLM_commutes_J_lp_clm (b : Bool) :
    (cuntzBranchCLM b).comp (J_lp_clm (E := ℝ)) =
      (J_lp_clm (E := ℝ)).comp (cuntzBranchCLM b) := by
  cases b
  · dsimp [cuntzBranchCLM]
    exact S_left_lp_clm_commutes_J_lp_clm
  · dsimp [cuntzBranchCLM]
    exact S_right_lp_clm_commutes_J_lp_clm

theorem wordCLM_commutes_J_lp_clm (n : ℕ) (w : BitWord n) :
    (wordCLM n w).comp (J_lp_clm (E := ℝ)) =
      (J_lp_clm (E := ℝ)).comp (wordCLM n w) := by
  induction n with
  | zero =>
      dsimp [wordCLM]
      rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  | succ n ih =>
      dsimp [wordCLM]
      rw [ContinuousLinearMap.comp_assoc]
      rw [cuntzBranchCLM_commutes_J_lp_clm]
      rw [← ContinuousLinearMap.comp_assoc]
      rw [ih (prefixSucc n w)]
      rw [ContinuousLinearMap.comp_assoc]

theorem J_lp_clm_selfAdjoint :
    (J_lp_clm (E := ℝ)).adjoint = J_lp_clm (E := ℝ) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (inner_J_lp_clm_selfAdjoint (E := ℝ) x y).symm

theorem wordPullbackCLM_commutes_J_lp_clm (n : ℕ) (w : BitWord n) :
    (wordPullbackCLM n w).comp (J_lp_clm (E := ℝ)) =
      (J_lp_clm (E := ℝ)).comp (wordPullbackCLM n w) := by
  induction n with
  | zero =>
      dsimp [wordPullbackCLM]
      rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  | succ n ih =>
      dsimp [wordPullbackCLM]
      have hadj : (cuntzPullbackCLM (w ⟨n, Nat.lt_succ_self n⟩)).comp (J_lp_clm (E := ℝ)) =
                  (J_lp_clm (E := ℝ)).comp (cuntzPullbackCLM (w ⟨n, Nat.lt_succ_self n⟩)) := by
        dsimp [cuntzPullbackCLM]
        have hcomm := cuntzBranchCLM_commutes_J_lp_clm (w ⟨n, Nat.lt_succ_self n⟩)
        have h := congrArg ContinuousLinearMap.adjoint hcomm
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, J_lp_clm_selfAdjoint] at h
        exact h.symm
      rw [ContinuousLinearMap.comp_assoc]
      rw [ih (prefixSucc n w)]
      rw [← ContinuousLinearMap.comp_assoc]
      rw [hadj]
      rw [ContinuousLinearMap.comp_assoc]

theorem bitWordUnitCLM_commutes_J_lp_clm (n : ℕ) (u v : BitWord n) :
    (bitWordUnitCLM n u v).comp (J_lp_clm (E := ℝ)) =
      (J_lp_clm (E := ℝ)).comp (bitWordUnitCLM n u v) := by
  dsimp [bitWordUnitCLM]
  rw [ContinuousLinearMap.comp_assoc]
  rw [wordPullbackCLM_commutes_J_lp_clm]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [wordCLM_commutes_J_lp_clm]
  rw [ContinuousLinearMap.comp_assoc]

/-- Sewing invariance of cylinder partial isometries under the Krein involution $J_{lp}$:
    $J_{lp} E_{u, v} J_{lp} = E_{u, v}$. -/
theorem bitWordUnitCLM_sewn_invariant (n : ℕ) (u v : BitWord n) :
    (J_lp_clm (E := ℝ)).comp ((bitWordUnitCLM n u v).comp (J_lp_clm (E := ℝ))) =
      bitWordUnitCLM n u v := by
  rw [bitWordUnitCLM_commutes_J_lp_clm]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [J_lp_clm_comp_self, ContinuousLinearMap.id_comp]

def sewnConjugateLM : (H_lp ℝ →L[ℝ] H_lp ℝ) →ₗ[ℝ] (H_lp ℝ →L[ℝ] H_lp ℝ) where
  toFun T := (J_lp_clm (E := ℝ)).comp (T.comp (J_lp_clm (E := ℝ)))
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, map_add]
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, ContinuousLinearMap.map_smul, RingHom.id_apply]

/-- Concrete finite-stage representation of double cylinder operators on `H_lp ℝ`. -/
def stageRepresentationCLM (n : ℕ) (M : DoubleCylinderStage ℝ n) : H_lp ℝ →L[ℝ] H_lp ℝ :=
  ∑ u : BitWord n, ∑ v : BitWord n, (M u v • bitWordUnitCLM n u v)

/-- Krein $J_{lp}$ sewing invariance of finite-stage double cylinder operators. -/
theorem stageRepresentationCLM_sewn_invariant (n : ℕ) (M : DoubleCylinderStage ℝ n) :
    (J_lp_clm (E := ℝ)).comp ((stageRepresentationCLM n M).comp (J_lp_clm (E := ℝ))) =
      stageRepresentationCLM n M := by
  change sewnConjugateLM (stageRepresentationCLM n M) = stageRepresentationCLM n M
  dsimp [stageRepresentationCLM]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul]
  change (M u v) • sewnConjugateLM (bitWordUnitCLM n u v) = (M u v) • bitWordUnitCLM n u v
  rw [show sewnConjugateLM (bitWordUnitCLM n u v) = bitWordUnitCLM n u v from bitWordUnitCLM_sewn_invariant n u v]

/-- Sewn chiral anomaly cancellation on finite-stage double cylinder operators. -/
theorem stageRepresentationCLM_chiral_zero (n : ℕ) (M : DoubleCylinderStage ℝ n) :
    inner ℝ canonicalCantorSewnState
      (((epsilon_lp_clm (E := ℝ)).comp (stageRepresentationCLM n M)) canonicalCantorSewnState) = 0 :=
  canonicalCantorSewnState_chiral_zero (stageRepresentationCLM n M)
    (stageRepresentationCLM_sewn_invariant n M)

/-- Compatibility of the stage representation with the dyadic bonding homomorphism. -/
theorem stageRepresentationCLM_bond (n : ℕ) (M : DoubleCylinderStage ℝ n) :
    stageRepresentationCLM (n + 1) (doubleCylinderBond ℝ n M) =
      stageRepresentationCLM n M := by
  change (∑ u : BitWord (n + 1), ∑ v : BitWord (n + 1),
    doubleCylinderBond ℝ n M u v • bitWordUnitCLM (n + 1) u v) =
    (∑ u' : BitWord n, ∑ v' : BitWord n,
      M u' v' • bitWordUnitCLM n u' v')
  rw [bitword_sum_last_split n]
  have h_v_true (u' : BitWord n) :
      (∑ v : BitWord (n + 1), doubleCylinderBond ℝ n M (extendSucc n u' true) v • bitWordUnitCLM (n + 1) (extendSucc n u' true) v) =
      ∑ v' : BitWord n, M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' true) := by
    rw [bitword_sum_last_split n]
    apply Finset.sum_congr rfl
    intro v' _
    have h1 : doubleCylinderBond ℝ n M (extendSucc n u' true) (extendSucc n v' true) = M u' v' := by
      change doubleCylinderBondFun ℝ n M (extendSucc n u' true) (extendSucc n v' true) = M u' v'
      rw [doubleCylinderBondFun_extendSucc]
      simp only [ite_true]
    have h2 : doubleCylinderBond ℝ n M (extendSucc n u' true) (extendSucc n v' false) = 0 := by
      change doubleCylinderBondFun ℝ n M (extendSucc n u' true) (extendSucc n v' false) = 0
      rw [doubleCylinderBondFun_extendSucc]
      simp only [Bool.true_eq_false, ite_false]
    have hstep1 := congr (congrArg (· + ·)
      (congrArg (· • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' true)) h1))
      (congrArg (· • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' false)) h2)
    have hz : (0 : ℝ) • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' false) = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [_root_.smul_apply, _root_.zero_apply, zero_smul]
    have hstep2 :=
      congrArg (M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' true) + ·) hz
    have hstep3 :
      M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' true) + 0 =
      M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' true) (extendSucc n v' true) :=
      add_zero _
    exact hstep1.trans (hstep2.trans hstep3)
  have h_v_false (u' : BitWord n) :
      (∑ v : BitWord (n + 1), doubleCylinderBond ℝ n M (extendSucc n u' false) v • bitWordUnitCLM (n + 1) (extendSucc n u' false) v) =
      ∑ v' : BitWord n, M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' false) := by
    rw [bitword_sum_last_split n]
    apply Finset.sum_congr rfl
    intro v' _
    have h1 : doubleCylinderBond ℝ n M (extendSucc n u' false) (extendSucc n v' true) = 0 := by
      change doubleCylinderBondFun ℝ n M (extendSucc n u' false) (extendSucc n v' true) = 0
      rw [doubleCylinderBondFun_extendSucc]
      simp only [Bool.false_eq_true, ite_false]
    have h2 : doubleCylinderBond ℝ n M (extendSucc n u' false) (extendSucc n v' false) = M u' v' := by
      change doubleCylinderBondFun ℝ n M (extendSucc n u' false) (extendSucc n v' false) = M u' v'
      rw [doubleCylinderBondFun_extendSucc]
      simp only [ite_true]
    have hstep1 := congr (congrArg (· + ·)
      (congrArg (· • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' true)) h1))
      (congrArg (· • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' false)) h2)
    have hz : (0 : ℝ) • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' true) = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [_root_.smul_apply, _root_.zero_apply, zero_smul]
    have hstep2 :=
      congrArg (· + M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' false)) hz
    have hstep3 :
      0 + M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' false) =
      M u' v' • bitWordUnitCLM (n + 1) (extendSucc n u' false) (extendSucc n v' false) :=
      zero_add _
    exact hstep1.trans (hstep2.trans hstep3)
  apply Finset.sum_congr rfl
  intro u' _
  rw [h_v_true u', h_v_false u', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v' _
  exact bitWordUnitCLM_decomp_smul n (M u' v') u' v'

theorem stageRepresentationCLM_bondMap (m n : ℕ) (h : m ≤ n) (M : DoubleCylinderStage ℝ m) :
    stageRepresentationCLM n (bondMap (doubleCylinderBond ℝ) m n h M) =
      stageRepresentationCLM m M := by
  induction h with
  | refl =>
      rw [bondMap_refl]
      rfl
  | @step k hk ih =>
      rw [bondMap_succ (doubleCylinderBond ℝ) m k hk]
      change stageRepresentationCLM (k + 1) ((doubleCylinderBond ℝ k) (bondMap (doubleCylinderBond ℝ) m k hk M)) =
             stageRepresentationCLM m M
      rw [stageRepresentationCLM_bond]
      exact ih

/-- Universal concrete representation of the Cantor double cylinder colimit on `H_lp ℝ`. -/
def colimitRepresentationCLM (X : DoubleCylinderColimit ℝ) : H_lp ℝ →L[ℝ] H_lp ℝ :=
  DirectLimit.lift
    (fun m n h => bondMap (doubleCylinderBond ℝ) m n h)
    (fun n => stageRepresentationCLM n)
    (fun m n h M => (stageRepresentationCLM_bondMap m n h M).symm)
    X

@[simp]
theorem colimitRepresentationCLM_inclusion (n : ℕ) (M : DoubleCylinderStage ℝ n) :
    colimitRepresentationCLM (doubleCylinderInclusion ℝ n M) = stageRepresentationCLM n M :=
  rfl

private lemma clm_zero_smul (A : H_lp ℝ →L[ℝ] H_lp ℝ) :
    (0 : ℝ) • A = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [_root_.smul_apply, _root_.zero_apply, zero_smul]

private lemma clm_smul_zero (c : ℝ) :
    c • (0 : H_lp ℝ →L[ℝ] H_lp ℝ) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [_root_.smul_apply, _root_.zero_apply, smul_zero]

private lemma clm_smul_mul_smul (a b : ℝ) (A B : H_lp ℝ →L[ℝ] H_lp ℝ) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  apply ContinuousLinearMap.ext
  intro x
  change (a • A) ((b • B) x) = (a * b) • A (B x)
  simp only [_root_.smul_apply, map_smul, smul_smul, mul_comm]

theorem stageRepresentationCLM_zero (n : ℕ) :
    stageRepresentationCLM n 0 = 0 := by
  dsimp [stageRepresentationCLM]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  exact clm_zero_smul (bitWordUnitCLM n u v)

theorem stageRepresentationCLM_add (n : ℕ) (M N : DoubleCylinderStage ℝ n) :
    stageRepresentationCLM n (M + N) =
      stageRepresentationCLM n M + stageRepresentationCLM n N := by
  dsimp [stageRepresentationCLM]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  exact add_smul (M u v) (N u v) (bitWordUnitCLM n u v)

theorem stageRepresentationCLM_smul (n : ℕ) (c : ℝ) (M : DoubleCylinderStage ℝ n) :
    stageRepresentationCLM n (c • M) = c • stageRepresentationCLM n M := by
  dsimp [stageRepresentationCLM]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_smul c (M u v) (bitWordUnitCLM n u v)

theorem stageRepresentationCLM_one (n : ℕ) :
    stageRepresentationCLM n 1 = 1 := by
  induction n with
  | zero =>
      dsimp [stageRepresentationCLM]
      have huniq : ∀ x : BitWord 0, x = default := fun x => funext fun i => Fin.elim0 i
      have : Unique (BitWord 0) := ⟨⟨default⟩, huniq⟩
      simp [bitWordUnitCLM, wordCLM, wordPullbackCLM, ContinuousLinearMap.one_def]
  | succ n ih =>
      rw [← (doubleCylinderBond ℝ n).map_one]
      rw [stageRepresentationCLM_bond n 1]
      exact ih

private lemma stageSum_mul_aux (n : ℕ) (f g : BitWord n → BitWord n → ℝ) :
    (∑ u : BitWord n, ∑ v : BitWord n, f u v • bitWordUnitCLM n u v) *
      (∑ w : BitWord n, ∑ z : BitWord n, g w z • bitWordUnitCLM n w z) =
    ∑ u : BitWord n, ∑ z : BitWord n,
      (∑ v : BitWord n, f u v * g v z) • bitWordUnitCLM n u z := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_mul]
  have h1 :
      (∑ v : BitWord n,
        (f u v • bitWordUnitCLM n u v) *
          (∑ w : BitWord n, ∑ z : BitWord n, g w z • bitWordUnitCLM n w z)) =
      ∑ v : BitWord n, ∑ z : BitWord n, (f u v * g v z) • bitWordUnitCLM n u z := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.mul_sum]
    have hpush :
        (∑ w : BitWord n, (f u v • bitWordUnitCLM n u v) * (∑ z : BitWord n, g w z • bitWordUnitCLM n w z)) =
        ∑ w : BitWord n, ∑ z : BitWord n, (f u v • bitWordUnitCLM n u v) * (g w z • bitWordUnitCLM n w z) := by
      apply Finset.sum_congr rfl
      intro w _
      exact Finset.mul_sum _ _ _
    rw [hpush, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    have h_ite : ∀ w : BitWord n,
        (f u v • bitWordUnitCLM n u v) * (g w z • bitWordUnitCLM n w z) =
          if w = v then (f u v * g v z) • bitWordUnitCLM n u z else 0 := by
      intro w
      rw [clm_smul_mul_smul, bitWordUnitCLM_mul]
      by_cases hwv : w = v
      · subst hwv
        simp only [ite_true]
      · have hvw : v ≠ w := Ne.symm hwv
        simp only [hwv, hvw, ite_false, clm_smul_zero]
    calc
      (∑ w : BitWord n, (f u v • bitWordUnitCLM n u v) * (g w z • bitWordUnitCLM n w z))
          = ∑ w : BitWord n, if w = v then (f u v * g v z) • bitWordUnitCLM n u z else 0 :=
            Finset.sum_congr rfl fun w _ => h_ite w
      _ = (f u v * g v z) • bitWordUnitCLM n u z := by
            simp
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_smul]

/-- Multiplicativity of the finite-stage operator representation on `H_lp ℝ`. -/
theorem stageRepresentationCLM_mul (n : ℕ) (M N : DoubleCylinderStage ℝ n) :
    stageRepresentationCLM n (M * N) =
      stageRepresentationCLM n M * stageRepresentationCLM n N := by
  let f : BitWord n → BitWord n → ℝ := fun u v => M u v
  let g : BitWord n → BitWord n → ℝ := fun w z => N w z
  have h := (stageSum_mul_aux n f g).symm
  change stageRepresentationCLM n (M * N) =
    (∑ u : BitWord n, ∑ v : BitWord n, f u v • bitWordUnitCLM n u v) *
      (∑ w : BitWord n, ∑ z : BitWord n, g w z • bitWordUnitCLM n w z)
  rw [← h]
  rfl

/-- Finite-stage representation packaged as a unital ring homomorphism. -/
def stageRepresentationRingHom (n : ℕ) :
    DoubleCylinderStage ℝ n →+* (H_lp ℝ →L[ℝ] H_lp ℝ) where
  toFun := stageRepresentationCLM n
  map_one' := stageRepresentationCLM_one n
  map_mul' := stageRepresentationCLM_mul n
  map_zero' := stageRepresentationCLM_zero n
  map_add' := stageRepresentationCLM_add n

/-- Finite-stage representation packaged as a unital `ℝ`-algebra homomorphism. -/
def stageRepresentationAlgHom (n : ℕ) :
    DoubleCylinderStage ℝ n →ₐ[ℝ] (H_lp ℝ →L[ℝ] H_lp ℝ) where
  toRingHom := stageRepresentationRingHom n
  commutes' r := by
    change stageRepresentationCLM n (algebraMap ℝ (DoubleCylinderStage ℝ n) r) =
      algebraMap ℝ (H_lp ℝ →L[ℝ] H_lp ℝ) r
    rw [Algebra.algebraMap_eq_smul_one, stageRepresentationCLM_smul,
        stageRepresentationCLM_one, Algebra.algebraMap_eq_smul_one]

private theorem doubleCylinderBond_smul (n : ℕ) (c : ℝ) (M : DoubleCylinderStage ℝ n) :
    doubleCylinderBond ℝ n (c • M) = c • doubleCylinderBond ℝ n M := by
  ext v w
  dsimp [doubleCylinderBond, doubleCylinderBondFun]
  split_ifs with h
  · rfl
  · simp

private theorem doubleCylinderBond_algebraMap (n : ℕ) (c : ℝ) :
    doubleCylinderBond ℝ n (algebraMap ℝ (DoubleCylinderStage ℝ n) c) =
      algebraMap ℝ (DoubleCylinderStage ℝ (n + 1)) c := by
  rw [Algebra.algebraMap_eq_smul_one, doubleCylinderBond_smul, map_one,
    ← Algebra.algebraMap_eq_smul_one]

private theorem doubleCylinderInclusion_algebraMap (n : ℕ) (c : ℝ) :
    doubleCylinderInclusion ℝ n (algebraMap ℝ (DoubleCylinderStage ℝ n) c) =
      doubleCylinderInclusion ℝ 0 (algebraMap ℝ (DoubleCylinderStage ℝ 0) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← doubleCylinderBond_algebraMap n c, doubleCylinderInclusion_bond, ih]

private def doubleCylinderColimitAlgebraMap : ℝ →+* DoubleCylinderColimit ℝ :=
  (doubleCylinderInclusion ℝ 0).comp (algebraMap ℝ (DoubleCylinderStage ℝ 0))

private theorem doubleCylinderColimitAlgebraMap_commutes (c : ℝ) (X : DoubleCylinderColimit ℝ) :
    doubleCylinderColimitAlgebraMap c * X = X * doubleCylinderColimitAlgebraMap c := by
  induction X using DirectLimit.induction with
  | ih n M =>
      change doubleCylinderInclusion ℝ 0 (algebraMap ℝ (DoubleCylinderStage ℝ 0) c) *
          doubleCylinderInclusion ℝ n M =
        doubleCylinderInclusion ℝ n M *
          doubleCylinderInclusion ℝ 0 (algebraMap ℝ (DoubleCylinderStage ℝ 0) c)
      rw [← doubleCylinderInclusion_algebraMap n c]
      rw [← (doubleCylinderInclusion ℝ n).map_mul, ← (doubleCylinderInclusion ℝ n).map_mul]
      rw [Algebra.commutes]

/-- Canonical `ℝ`-algebra structure on `DoubleCylinderColimit ℝ`. -/
instance instAlgebraRealDoubleCylinderColimit : Algebra ℝ (DoubleCylinderColimit ℝ) :=
  RingHom.toAlgebra' doubleCylinderColimitAlgebraMap doubleCylinderColimitAlgebraMap_commutes

/-- Canonical Lie ring structure on `DoubleCylinderColimit ℝ` from its associative multiplication. -/
instance instLieRingDoubleCylinderColimitReal : LieRing (DoubleCylinderColimit ℝ) :=
  LieRing.ofAssociativeRing

/-- Canonical real Lie algebra structure on `DoubleCylinderColimit ℝ`. -/
instance instLieAlgebraRealDoubleCylinderColimit : LieAlgebra ℝ (DoubleCylinderColimit ℝ) :=
  LieAlgebra.ofAssociativeAlgebra

private theorem stageRepresentationRingHom_compatible :
    CompatibleCone (doubleCylinderBond ℝ) stageRepresentationRingHom :=
  fun n M => stageRepresentationCLM_bond n M

/-- Colimit representation packaged as a unital ring homomorphism out of `DoubleCylinderColimit ℝ`. -/
def colimitRepresentationRingHom :
    DoubleCylinderColimit ℝ →+* (H_lp ℝ →L[ℝ] H_lp ℝ) :=
  directLimitLift (doubleCylinderBond ℝ) stageRepresentationRingHom
    stageRepresentationRingHom_compatible

@[simp]
theorem colimitRepresentationRingHom_apply (X : DoubleCylinderColimit ℝ) :
    colimitRepresentationRingHom X = colimitRepresentationCLM X :=
  rfl

theorem colimitRepresentationCLM_zero :
    colimitRepresentationCLM 0 = 0 :=
  colimitRepresentationRingHom.map_zero

theorem colimitRepresentationCLM_one :
    colimitRepresentationCLM 1 = 1 :=
  colimitRepresentationRingHom.map_one

theorem colimitRepresentationCLM_add (X Y : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM (X + Y) =
      colimitRepresentationCLM X + colimitRepresentationCLM Y :=
  colimitRepresentationRingHom.map_add X Y

theorem colimitRepresentationCLM_sub (X Y : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM (X - Y) =
      colimitRepresentationCLM X - colimitRepresentationCLM Y :=
  colimitRepresentationRingHom.map_sub X Y

theorem colimitRepresentationCLM_neg (X : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM (-X) = -colimitRepresentationCLM X :=
  colimitRepresentationRingHom.map_neg X

/-- Multiplicativity of the universal colimit representation on `H_lp ℝ`. -/
theorem colimitRepresentationCLM_mul (X Y : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM (X * Y) =
      colimitRepresentationCLM X * colimitRepresentationCLM Y :=
  colimitRepresentationRingHom.map_mul X Y

theorem colimitRepresentationCLM_comp (X Y : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM (X * Y) =
      (colimitRepresentationCLM X).comp (colimitRepresentationCLM Y) :=
  colimitRepresentationCLM_mul X Y

section LieCompatibility

local instance : LieRing (H_lp ℝ →L[ℝ] H_lp ℝ) :=
  LieRing.ofAssociativeRing

theorem colimitRepresentationCLM_lie (X Y : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM ⁅X, Y⁆ =
      ⁅colimitRepresentationCLM X, colimitRepresentationCLM Y⁆ := by
  rw [Ring.lie_def, Ring.lie_def, colimitRepresentationCLM_sub,
      colimitRepresentationCLM_mul, colimitRepresentationCLM_mul]

end LieCompatibility

/-- Colimit representation packaged as a unital `ℝ`-algebra homomorphism into `H_lp ℝ →L[ℝ] H_lp ℝ`. -/
def colimitRepresentationAlgHom :
    DoubleCylinderColimit ℝ →ₐ[ℝ] (H_lp ℝ →L[ℝ] H_lp ℝ) where
  __ := colimitRepresentationRingHom
  commutes' r := by
    change colimitRepresentationRingHom
      (directLimitOf (doubleCylinderBond ℝ) 0 (algebraMap ℝ (DoubleCylinderStage ℝ 0) r)) =
        algebraMap ℝ (H_lp ℝ →L[ℝ] H_lp ℝ) r
    unfold colimitRepresentationRingHom
    rw [directLimitLift_of]
    change stageRepresentationCLM 0 (algebraMap ℝ (DoubleCylinderStage ℝ 0) r) =
      algebraMap ℝ (H_lp ℝ →L[ℝ] H_lp ℝ) r
    rw [Algebra.algebraMap_eq_smul_one, stageRepresentationCLM_smul, stageRepresentationCLM_one,
      ← Algebra.algebraMap_eq_smul_one]

/-- Colimit representation packaged as an `ℝ`-algebra homomorphism into `Module.End ℝ (H_lp ℝ)`. -/
def colimitRepresentationEndAlgHom :
    DoubleCylinderColimit ℝ →ₐ[ℝ] Module.End ℝ (H_lp ℝ) where
  __ := ContinuousLinearMap.toLinearMapRingHom.comp colimitRepresentationAlgHom.toRingHom
  commutes' r := by
    apply LinearMap.ext
    intro x
    change (colimitRepresentationAlgHom (algebraMap ℝ (DoubleCylinderColimit ℝ) r)) x =
      (algebraMap ℝ (Module.End ℝ (H_lp ℝ)) r) x
    rw [colimitRepresentationAlgHom.commutes r, ContinuousLinearMap.algebraMap_apply,
      Module.algebraMap_end_apply]

private lemma wordPullbackCLM_comp_bitWordUnitCLM_comp_wordCLM
    (n : ℕ) (u₀ v₀ u v : BitWord n) :
    (wordPullbackCLM n u₀).comp ((bitWordUnitCLM n u v).comp (wordCLM n v₀)) =
      if u = u₀ ∧ v = v₀ then ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
  dsimp [bitWordUnitCLM]
  rw [ContinuousLinearMap.comp_assoc (wordCLM n u),
      wordPullbackCLM_comp_wordCLM n v v₀,
      ← ContinuousLinearMap.comp_assoc (wordPullbackCLM n u₀),
      wordPullbackCLM_comp_wordCLM n u₀ u]
  by_cases hu : u = u₀ <;> by_cases hv : v = v₀
  · subst hu; subst hv
    simp
  · subst hu
    simp [hv]
  · have hu' : u₀ ≠ u := Ne.symm hu
    simp [hu, hu']
  · have hu' : u₀ ≠ u := Ne.symm hu
    simp [hu, hu']

private lemma wordPullbackCLM_comp_stageSum_comp_wordCLM
    (n : ℕ) (f : BitWord n → BitWord n → ℝ) (u₀ v₀ : BitWord n) :
    (wordPullbackCLM n u₀).comp
      ((∑ u : BitWord n, ∑ v : BitWord n, f u v • bitWordUnitCLM n u v).comp (wordCLM n v₀)) =
      f u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) := by
  have hmul :
      (wordPullbackCLM n u₀).comp
        ((∑ u : BitWord n, ∑ v : BitWord n, f u v • bitWordUnitCLM n u v).comp (wordCLM n v₀)) =
        wordPullbackCLM n u₀ *
          (∑ u : BitWord n, ∑ v : BitWord n, f u v • bitWordUnitCLM n u v) *
          wordCLM n v₀ := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [hmul, Finset.mul_sum, Finset.sum_mul]
  have houter : ∀ u : BitWord n,
      (wordPullbackCLM n u₀ * (∑ v : BitWord n, f u v • bitWordUnitCLM n u v)) * wordCLM n v₀ =
        if u = u₀ then f u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
    intro u
    rw [Finset.mul_sum, Finset.sum_mul]
    have hterm : ∀ v : BitWord n,
        (wordPullbackCLM n u₀ * (f u v • bitWordUnitCLM n u v)) * wordCLM n v₀ =
          if u = u₀ ∧ v = v₀ then f u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
      intro v
      have hsmul :
          (wordPullbackCLM n u₀ * (f u v • bitWordUnitCLM n u v)) * wordCLM n v₀ =
            f u v • ((wordPullbackCLM n u₀).comp ((bitWordUnitCLM n u v).comp (wordCLM n v₀))) := by
        apply ContinuousLinearMap.ext
        intro x
        change wordPullbackCLM n u₀ ((f u v • bitWordUnitCLM n u v) (wordCLM n v₀ x)) =
          f u v • wordPullbackCLM n u₀ (bitWordUnitCLM n u v (wordCLM n v₀ x))
        simp only [_root_.smul_apply, map_smul]
      rw [hsmul, wordPullbackCLM_comp_bitWordUnitCLM_comp_wordCLM]
      by_cases hu : u = u₀ <;> by_cases hv : v = v₀
      · subst hu; subst hv
        simp
      · subst hu
        simp [hv, clm_smul_zero]
      · simp [hu, clm_smul_zero]
      · simp [hu, clm_smul_zero]
    by_cases hu : u = u₀
    · subst hu
      calc
        (∑ v : BitWord n, (wordPullbackCLM n u * (f u v • bitWordUnitCLM n u v)) * wordCLM n v₀)
            = ∑ v : BitWord n, if v = v₀ then f u v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro v _
              rw [hterm v]
              by_cases hv : v = v₀ <;> simp [hv]
        _ = if u = u then f u v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
              simp
    · calc
        (∑ v : BitWord n, (wordPullbackCLM n u₀ * (f u v • bitWordUnitCLM n u v)) * wordCLM n v₀)
            = ∑ _v : BitWord n, (0 : H_lp ℝ →L[ℝ] H_lp ℝ) := by
              apply Finset.sum_congr rfl
              intro v _
              rw [hterm v]
              simp [hu]
        _ = if u = u₀ then f u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 := by
              simp [hu]
  calc
    (∑ u : BitWord n,
      (wordPullbackCLM n u₀ * (∑ v : BitWord n, f u v • bitWordUnitCLM n u v)) * wordCLM n v₀)
        = ∑ u : BitWord n,
            if u = u₀ then f u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) else 0 :=
          Finset.sum_congr rfl fun u _ => houter u
    _ = f u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) := by
          simp

theorem wordPullbackCLM_comp_stageRepresentation_comp_wordCLM
    (n : ℕ) (M : DoubleCylinderStage ℝ n) (u₀ v₀ : BitWord n) :
    (wordPullbackCLM n u₀).comp ((stageRepresentationCLM n M).comp (wordCLM n v₀)) =
      M u₀ v₀ • ContinuousLinearMap.id ℝ (H_lp ℝ) :=
  wordPullbackCLM_comp_stageSum_comp_wordCLM n (fun u v => M u v) u₀ v₀

theorem stageRepresentationCLM_eq_zero_iff (n : ℕ) (M : DoubleCylinderStage ℝ n) :
    stageRepresentationCLM n M = 0 ↔ M = 0 := by
  constructor
  · intro hM
    ext u₀ v₀
    have hcomp := wordPullbackCLM_comp_stageRepresentation_comp_wordCLM n M u₀ v₀
    rw [hM, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] at hcomp
    have hvec := congrArg (fun T : H_lp ℝ →L[ℝ] H_lp ℝ => T canonicalCantorSewnState) hcomp.symm
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, _root_.zero_apply] at hvec
    rcases smul_eq_zero.mp hvec with hscalar | hstate
    · exact hscalar
    · exact absurd hstate canonicalCantorSewnState_ne_zero
  · intro hM
    subst hM
    exact stageRepresentationCLM_zero n

/-- Faithfulness (injectivity) of the finite-stage operator representation. -/
theorem stageRepresentationCLM_injective (n : ℕ) :
    Function.Injective (stageRepresentationCLM n) := by
  intro M N hMN
  rw [← sub_eq_zero, ← stageRepresentationCLM_eq_zero_iff n (M - N)]
  change (stageRepresentationRingHom n) (M - N) = 0
  rw [map_sub, sub_eq_zero]
  exact hMN

theorem colimitRepresentationCLM_eq_zero_iff (X : DoubleCylinderColimit ℝ) :
    colimitRepresentationCLM X = 0 ↔ X = 0 := by
  constructor
  · intro hX
    induction X using DirectLimit.induction with
    | ih n M =>
        change colimitRepresentationCLM (doubleCylinderInclusion ℝ n M) = 0 at hX
        rw [colimitRepresentationCLM_inclusion, stageRepresentationCLM_eq_zero_iff] at hX
        subst hX
        exact map_zero (doubleCylinderInclusion ℝ n)
  · intro hX
    subst hX
    exact colimitRepresentationCLM_zero

/-- Faithfulness (injectivity) of the universal colimit operator representation. -/
theorem colimitRepresentationCLM_injective :
    Function.Injective colimitRepresentationCLM := by
  intro X Y hXY
  rw [← sub_eq_zero, ← colimitRepresentationCLM_eq_zero_iff (X - Y),
      colimitRepresentationCLM_sub, hXY, sub_self]

theorem colimitRepresentationEndAlgHom_injective :
    Function.Injective colimitRepresentationEndAlgHom := by
  intro X Y hXY
  apply colimitRepresentationCLM_injective
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun hXY v

/-- Krein $J_{lp}$ sewing invariance of the colimit representation on `H_lp ℝ`:
    $J_{lp} \circ \rho_\infty(X) \circ J_{lp} = \rho_\infty(X)$. -/
theorem colimitRepresentation_sewn_invariant (X : DoubleCylinderColimit ℝ) :
    (J_lp_clm (E := ℝ)).comp ((colimitRepresentationCLM X).comp (J_lp_clm (E := ℝ))) =
      colimitRepresentationCLM X := by
  induction X using DirectLimit.induction with
  | ih n M =>
      change (J_lp_clm (E := ℝ)).comp ((colimitRepresentationCLM (doubleCylinderInclusion ℝ n M)).comp (J_lp_clm (E := ℝ))) =
        colimitRepresentationCLM (doubleCylinderInclusion ℝ n M)
      rw [colimitRepresentationCLM_inclusion]
      exact stageRepresentationCLM_sewn_invariant n M

/-- Sewn chiral anomaly cancellation for double cylinder colimit operators:
    $\langle \Omega_{\mathrm{sewn}}, \varepsilon_{lp} (\rho_\infty(X) \Omega_{\mathrm{sewn}}) \rangle = 0$. -/
theorem doubleCylinderColimit_canonicalVacuum_chiral_zero (X : DoubleCylinderColimit ℝ) :
    inner ℝ canonicalCantorSewnState
      (((epsilon_lp_clm (E := ℝ)).comp (colimitRepresentationCLM X)) canonicalCantorSewnState) = 0 :=
  canonicalCantorSewnState_chiral_zero (colimitRepresentationCLM X)
    (colimitRepresentation_sewn_invariant X)

/-! ## 5. Erlangen 2.0 Geometry Datum -/

/-- Symmetry data bundling Krein $\\mathrm{Cl}(1,1)$ generators and Erlangen $G_{\\mathrm{swap}}$ symmetry action. -/
structure CantorDoubleCylinderSymmetryData where
  modularJ : Module.End ℝ (DoubledSpace ℝ)
  spectralEpsilon : Module.End ℝ (DoubledSpace ℝ)
  modularJ_sq : modularJ * modularJ = LinearMap.id
  spectralEpsilon_sq : spectralEpsilon * spectralEpsilon = LinearMap.id
  anticommutes : modularJ * spectralEpsilon = -(spectralEpsilon * modularJ)
  gSwapAction : SymmetryAction G_swap (DoubleCylinderColimit ℝ)

/-- Invariant data bundling invariant subrings, Bernoulli measure evaluations, and noncommutativity. -/
structure CantorDoubleCylinderInvariantData where
  invariantSubring : Subring (DoubleCylinderColimit ℝ)
  bernoulliMeasure : ∀ (n : ℕ) (w : BitWord n),
    bitWordMatrixTraceFunctional n (doubleCylinderUnit ℂ n w w) = (1 / 2 : ℂ) ^ n
  noncommutative : ∃ a b : erlangenDoubleCylinderInvariantSubring ℤ, a * b ≠ b * a

/-- Canonical symmetry data instance for the Cantor double cylinder colimit. -/
def cantorDoubleCylinderSymmetryData : CantorDoubleCylinderSymmetryData where
  modularJ := doubleCylinderModularJ ℝ
  spectralEpsilon := doubleCylinderSpectralEpsilon ℝ
  modularJ_sq := doubleCylinderModularJ_sq ℝ
  spectralEpsilon_sq := doubleCylinderSpectralEpsilon_sq ℝ
  anticommutes := doubleCylinderModularJ_spectralEpsilon_anticomm ℝ
  gSwapAction := erlangenDoubleCylinderSymmetryAction ℝ

/-- Canonical invariant data instance for the Cantor double cylinder colimit. -/
def cantorDoubleCylinderInvariantData : CantorDoubleCylinderInvariantData where
  invariantSubring := erlangenDoubleCylinderInvariantSubring ℝ
  bernoulliMeasure := bitWordMatrixTraceFunctional_diagonal_bernoulli
  noncommutative := erlangenDoubleCylinderInvariantSubring_noncommutative ℤ

local instance : LieRing (Module.End ℝ (H_lp ℝ)) :=
  LieRing.ofAssociativeRing

local instance : LieAlgebra ℝ (Module.End ℝ (H_lp ℝ)) :=
  LieAlgebra.ofAssociativeAlgebra

/-- Associative operator subalgebra of `Module.End ℝ (H_lp ℝ)` generated by the concrete
    representation of `DoubleCylinderColimit ℝ` on `H_lp ℝ`. -/
def doubleCylinderOperatorSubalgebra : Subalgebra ℝ (Module.End ℝ (H_lp ℝ)) :=
  colimitRepresentationEndAlgHom.range

/-- Lie algebra representation of `DoubleCylinderColimit ℝ` on `H_lp ℝ` induced by
    `colimitRepresentationEndAlgHom`. -/
def colimitRepresentationLieHom :
    DoubleCylinderColimit ℝ →ₗ⁅ℝ⁆ Module.End ℝ (H_lp ℝ) :=
  colimitRepresentationEndAlgHom.toLieHom

@[simp]
theorem colimitRepresentationLieHom_apply (X : DoubleCylinderColimit ℝ) :
    colimitRepresentationLieHom X = (colimitRepresentationCLM X).toLinearMap :=
  rfl

/-- Concrete Erlangen 2.0 Geometry Datum for the Cantor double cylinder colimit on `H_lp ℝ`. -/
def cantorDoubleCylinderErlangen20Datum :
    Erlangen20Datum ℝ (H_lp ℝ) (DoubleCylinderColimit ℝ)
      CantorDoubleCylinderSymmetryData CantorDoubleCylinderInvariantData where
  operatorAlgebra := doubleCylinderOperatorSubalgebra
  representation := colimitRepresentationLieHom
  representation_mem := colimitRepresentationEndAlgHom.mem_range_self
  symmetryData := cantorDoubleCylinderSymmetryData
  invariantData := cantorDoubleCylinderInvariantData

theorem cantorDoubleCylinderErlangen20Datum_representation_injective :
    Function.Injective cantorDoubleCylinderErlangen20Datum.representation :=
  colimitRepresentationEndAlgHom_injective

/-! ## 6. Model Witness Structure & Non-Degeneracy Certification -/

/-- Closed witness packet for the Cantor double cylinder colimit algebra and Erlangen 2.0 datum (satisfies T17). -/
structure CantorDoubleCylinderWitnessPacket where
  datum : Erlangen20Datum ℝ (H_lp ℝ) (DoubleCylinderColimit ℝ)
    CantorDoubleCylinderSymmetryData CantorDoubleCylinderInvariantData
  noncommutative : ∃ a b : erlangenDoubleCylinderInvariantSubring ℤ, a * b ≠ b * a
  bernoulli_base : bitWordMatrixTraceFunctional 0 (doubleCylinderUnit ℂ 0 default default) = 1
  cl11_j_sq : doubleCylinderModularJ ℝ * doubleCylinderModularJ ℝ = LinearMap.id

/-- Constructive closed model witness for `CantorDoubleCylinderWitnessPacket`. -/
def cantorDoubleCylinderWitnessPacketModel : CantorDoubleCylinderWitnessPacket where
  datum := cantorDoubleCylinderErlangen20Datum
  noncommutative := erlangenDoubleCylinderInvariantSubring_noncommutative ℤ
  bernoulli_base := by
    have h := bitWordMatrixTraceFunctional_diagonal_bernoulli 0 default
    rw [h]
    exact pow_zero (1 / 2 : ℂ)
  cl11_j_sq := doubleCylinderModularJ_sq ℝ

instance : Inhabited CantorDoubleCylinderWitnessPacket :=
  ⟨cantorDoubleCylinderWitnessPacketModel⟩

/-! ## 7. Epistemic TypedArchetype Registration -/

/-- Certified epistemic `TypedArchetype Unit .proved` unifying intrinsic swap-invariant noncommutativity,
concrete Cuntz dyadic decomposition on `H_lp ℝ`, Krein $J_{lp}$ sewing invariance, and chiral anomaly cancellation. -/
@[rep_depth thermo, capstone]
def cantorDoubleCylinderErlangenArchetype : TypedArchetype Unit .proved where
  name := `cantorDoubleCylinderErlangenArchetype
  phase := 3
  claim := fun _ =>
    (∀ (B : Type) [Ring B] [Nontrivial B],
      ∃ a b : erlangenDoubleCylinderInvariantSubring B, a * b ≠ b * a) ∧
    (∀ (n : ℕ) (u v : BitWord n),
      bitWordUnitCLM (n + 1) (extendSucc n u false) (extendSucc n v false) +
      bitWordUnitCLM (n + 1) (extendSucc n u true) (extendSucc n v true) =
        bitWordUnitCLM n u v) ∧
    (∀ (X : DoubleCylinderColimit ℝ),
      (J_lp_clm (E := ℝ)).comp ((colimitRepresentationCLM X).comp (J_lp_clm (E := ℝ))) =
        colimitRepresentationCLM X) ∧
    (∀ (X : DoubleCylinderColimit ℝ),
      inner ℝ canonicalCantorSewnState
        (((epsilon_lp_clm (E := ℝ)).comp (colimitRepresentationCLM X)) canonicalCantorSewnState) = 0) ∧
    (∀ (X Y : DoubleCylinderColimit ℝ),
      colimitRepresentationCLM (X * Y) =
        colimitRepresentationCLM X * colimitRepresentationCLM Y) ∧
    Function.Injective cantorDoubleCylinderErlangen20Datum.representation
  evidence := fun _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro B _ _
      exact erlangenDoubleCylinderInvariantSubring_noncommutative B
    · intro n u v
      exact bitWordUnitCLM_decomp n u v
    · intro X
      exact colimitRepresentation_sewn_invariant X
    · intro X
      exact doubleCylinderColimit_canonicalVacuum_chiral_zero X
    · intro X Y
      exact colimitRepresentationCLM_mul X Y
    · exact cantorDoubleCylinderErlangen20Datum_representation_injective

end InfoGeometry.Categorical.CantorDoubleCylinderColimitAlgebra
