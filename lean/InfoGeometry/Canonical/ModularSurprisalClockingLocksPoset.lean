/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import InfoGeometry.Canonical.OperatorSurprisalCFCCommute
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorBogoliubovCrossGradeClosure
import InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon

/-!
# The Modular Surprisal Binary Cut, Normal-Form Operator Surprisal, The Master $1 : (-2)$ Clocking Identity, 5-Graded Supercolor Kantor Sandwich, BKM Resolvent Factorization, and Conditional Metriplectic Cramér–Rao Bound (`S₁ → S₈`)

This module proves an algebraic operator-surprisal and clocking spine over an arbitrary associative
ring `[Ring B]` equipped with `[Algebra ℝ B]`. Abstract logarithmic functional calculus, the
Fréchet derivative of the volume logarithm, the traced BKM resolvent metric, and derivation of the
Robertson–Schrödinger inequality are outside this module's proved scope. The scalar improper
resolvent integral, its fixed-vector consequence, and its operator-algebra-valued Peirce
factorization under explicit normed-completeness hypotheses are proved below:

* **Phase I (The Fundamental Binary Cut `T ↔ S`)**:
  Equal sheet weights give the scalar reference state (`ρ_iso = p P + p (1 - P) = p • 1`,
  `Δs = 0`, `[K_sheet, X] = 0`). This condition is independent of the off-diagonal deformation:
  `Φ = 0` and `V = 0` are separate conditions on its generators, not consequences of equal sheet
  weights. The deformed supergraded color shadow has
  (`Φ = N₊ + N₋ ≠ 0`, `V = Φ² = {N₊, N₋}`, `W(β) = (1 + β • V)⁻¹`, `K_sheet = s̄ • 1 - (Δs / 2) • S_P`).
* **Phase II (The Fourfold Relational Anatomy)**:
  1. *Internal Consistency*: Orthogonal idempotent power law `ρ(p, q, P)^n = p^n • P + q^n • (1 - P)`
     for `n ≥ 1` and the exact normal form `K_sheet(p, q, P) = s̄ • 1 - (Δs / 2) • S_P` where
     `s̄ = -(log p + log q) / 2 = -log(p q) / 2` and `Δs = log p - log q = log(p / q) = -log(q / p)`.
  2. *Outward Projection*: Supergraded color deformation `Ψ = P + Φ` with `Ψ² - Ψ = V = {N₊, N₋}`,
     together with the Zorn color 3-vector realization `Φ_Zorn(u, v) = N₊(u) + N₋(v)`, diquark
     creation `N₊(u₁) N₊(u₂) = N₋(u₁ × u₂)`, and non-Abelian self-wedge `u × u`.
  3. *Inward Shadow-Intrusion*: Sheet modular precession `[K_sheet, Φ] = -Δs • J` and
     `[K_sheet, J] = -Δs • Φ`, endogenous spin-surprisal flow `[Σ, Φ] = 2 • (V * J)`, and relative
     algebraically specified resolvent force `F = (2 * β) • (W * Φ)` satisfying
     `(1 + β • V) * F = (2 * β) • Φ` when `W` is a two-sided inverse.
  4. *Autonomous Ground*: The Bogoliubov–Kubo–Mori (BKM) relative-volume metric evaluation
     `g_BKM(Φ, Φ) = bkmDividedDiffWeight(p,q) * Tr(V)`, with the continuous isotropic value
     `bkmDividedDiffWeight(p,p) = 1 / p`.
* **Phase III (The Transcendent Function & Clocking Lock)**:
  The **Master `1 : (-2)` Clocking Identity**
  `-[Φ, [Φ, J]] = -(2 : ℤ) • [Σ, Φ] = -(4 : ℤ) • (V * J)`
  and the **Thermal Harmonic Oscillator Equation**
  `[K_sheet, [K_sheet, Φ]] = (Δs²) • Φ`.
* **Phase IV (Socratic Aporia & The 5-Rung Tower of Meta-Cognition, Rung 0–Rung 4)**:
  From the frozen isotropic clock (Rung 0) through normal-form sheet surprisal (Rung 1), relative
  volume resolvent-force identity (Rung 2), `1 : (-2)` clocking lock (Rung 3), to the 5-graded Kantor
  sandwich `kantorG0²(X) - {kantorGp2, kantorGm2}(X) = Σ X Σ`, 4th-order harmonic
  `[Σ, [Σ, Φ]] = 4 • (V² * Φ)`, pointwise BKM resolvent factorization and divided-difference
  identity, and a Cramér–Rao consequence conditional on the Robertson–Schrödinger bound (Rung 4).
* **Phase V (The 8-Stage Acyclic Causal Poset `S₁ ≺ S₂ ≺ ⋯ ≺ S₈`, Axiom I, Deductions 1–3,
  Theorems 1–5, and Master Structural Synthesis)**.
-/

namespace InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Archetypes.TwistorAmplituhedronZornBaryon
open ZornMatrix
open Filter Set TopologicalSpace Topology

/-!
## 1. The 8-Stage Acyclic Causal Poset (`S₁ ≺ S₂ ≺ ⋯ ≺ S₈`)
-/

/-- The 8-stage causal poset of the Modular Surprisal Binary Cut, Normal-Form Operator Surprisal,
Relative Volume Resolvent Force, Master `1 : (-2)` Clocking Identity, 5-Graded Supercolor Kantor
Sandwich, BKM Resolvent Factorization, and Conditional Metriplectic Cramér–Rao Bound
(`S₁ → S₈`). -/
inductive ModularSurprisalClockingStage : Type
  | S1_supergraded_color_vacuum_deformation
  | S2_normal_form_sheet_operator_surprisal
  | S3_relative_volume_surprisal_resolvent
  | S4_modular_automorphism_precession_flow
  | S5_dissipative_surprisal_clocking_lock
  | S6_five_graded_supercolor_kantor_sandwich
  | S7_bkm_resolvent_factorization
  | S8_master_metriplectic_cramer_rao_closure
  deriving DecidableEq, Repr, Inhabited

namespace ModularSurprisalClockingStage

/-- Numerical topological rank of each stage `S₁..S₈`. -/
def rank : ModularSurprisalClockingStage → ℕ
  | S1_supergraded_color_vacuum_deformation => 1
  | S2_normal_form_sheet_operator_surprisal => 2
  | S3_relative_volume_surprisal_resolvent => 3
  | S4_modular_automorphism_precession_flow => 4
  | S5_dissipative_surprisal_clocking_lock => 5
  | S6_five_graded_supercolor_kantor_sandwich => 6
  | S7_bkm_resolvent_factorization => 7
  | S8_master_metriplectic_cramer_rao_closure => 8

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance instLinearOrderModularSurprisalClockingStage : LinearOrder ModularSurprisalClockingStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal dependency edges of the `S₁ → S₈` poset:
`S₁ ≺ S₂`, `S₁ ≺ S₃`, `S₂ ≺ S₄`, `S₃ ≺ S₄`, and `S₄ ≺ S₅ ≺ S₆ ≺ S₇ ≺ S₈`. -/
def causalEdge : ModularSurprisalClockingStage → ModularSurprisalClockingStage → Prop
  | S1_supergraded_color_vacuum_deformation, S2_normal_form_sheet_operator_surprisal => True
  | S1_supergraded_color_vacuum_deformation, S3_relative_volume_surprisal_resolvent => True
  | S2_normal_form_sheet_operator_surprisal, S4_modular_automorphism_precession_flow => True
  | S3_relative_volume_surprisal_resolvent, S4_modular_automorphism_precession_flow => True
  | S4_modular_automorphism_precession_flow, S5_dissipative_surprisal_clocking_lock => True
  | S5_dissipative_surprisal_clocking_lock, S6_five_graded_supercolor_kantor_sandwich => True
  | S6_five_graded_supercolor_kantor_sandwich, S7_bkm_resolvent_factorization => True
  | S7_bkm_resolvent_factorization, S8_master_metriplectic_cramer_rao_closure => True
  | _, _ => False

theorem causalEdge_strict_rank_mono {a b : ModularSurprisalClockingStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

theorem causalEdge_irrefl (a : ModularSurprisalClockingStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : ModularSurprisalClockingStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : ModularSurprisalClockingStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

end ModularSurprisalClockingStage

/-!
## 2. Core Operator Surprisal, Relative Volume, and BKM Primitives
-/

section CorePrimitives

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- Two-sheet reference state `ρ(p, q, P) = p • P + q • (1 - P)`. -/
def sheetRho (p q : ℝ) (P : B) : B :=
  p • P + q • (1 - P)

/-- Mean sheet surprisal `s̄(p, q) = -(log p + log q) / 2`. -/
noncomputable def sheetSurprisalMean (p q : ℝ) : ℝ :=
  -((Real.log p + Real.log q) / 2)

/-- Sheet surprisal gap (modular log-odds) `Δs(p, q) = log p - log q`. -/
noncomputable def sheetSurprisalGap (p q : ℝ) : ℝ :=
  Real.log p - Real.log q

/-- Diagonal sheet operator surprisal `K_sheet(p, q, P) = (-log p) • P + (-log q) • (1 - P)`. -/
noncomputable def sheetOperatorSurprisal (p q : ℝ) (P : B) : B :=
  (-Real.log p) • P + (-Real.log q) • (1 - P)

/-- Relative sheet surprisal against the scalar reference state `r • 1`.
Its two coefficients are the logarithmic density ratios, so this is the
idempotent normal form of `-log (ρ(p,q,P) * (r • 1)⁻¹)` whenever the two
sheet functional calculus is interpreted. The algebraic definition itself
does not assert existence of a logarithm in `B`. -/
noncomputable def relativeSheetSurprisalOp (p q r : ℝ) (P : B) : B :=
  (-Real.log (p / r)) • P + (-Real.log (q / r)) • (1 - P)

/-- Equal sheet and reference weights give zero *relative* surprisal. This
distinguishes the frozen relative clock from the generally nonzero absolute
state surprisal `-log (r • 1)`. -/
theorem relativeSheetSurprisalOp_equal_sheets (p r : ℝ) (P : B) :
    relativeSheetSurprisalOp p p r P = (-Real.log (p / r)) • (1 : B) := by
  unfold relativeSheetSurprisalOp
  have hcut : P + (1 - P) = (1 : B) := by abel
  calc
    (-Real.log (p / r)) • P + (-Real.log (p / r)) • (1 - P)
        = (-Real.log (p / r)) • (P + (1 - P)) := by rw [smul_add]
    _ = (-Real.log (p / r)) • (1 : B) := by rw [hcut]

/-- Equal sheet weights make the relative surprisal central, even when its common
weight differs from the reference weight. The relative surprisal itself is zero
only in the matched-reference case. -/
theorem relativeSheetSurprisalOp_isotropic (r : ℝ) (hr : 0 < r) (P : B) :
    relativeSheetSurprisalOp r r r P = 0 := by
  have hrr : r / r = 1 := div_self (ne_of_gt hr)
  rw [relativeSheetSurprisalOp_equal_sheets, hrr]
  simp

/-- Relative sheet surprisal is absolute sheet surprisal with the logarithm
of the scalar reference density removed. This identifies the log-ratio
definition with the normal form already used by the sheet-clock owner. -/
theorem relativeSheetSurprisalOp_eq_absolute_sub_reference
    (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (P : B) :
    relativeSheetSurprisalOp p q r P =
      sheetOperatorSurprisal p q P + Real.log r • (1 : B) := by
  unfold relativeSheetSurprisalOp sheetOperatorSurprisal
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hr),
    Real.log_div (ne_of_gt hq) (ne_of_gt hr)]
  simp only [neg_sub]
  have hcut : P + (1 - P) = (1 : B) := by abel
  calc
    (Real.log r - Real.log p) • P +
        (Real.log r - Real.log q) • (1 - P)
      = ((-Real.log p) • P + (-Real.log q) • (1 - P)) +
          Real.log r • (P + (1 - P)) := by
            rw [sub_smul, sub_smul, smul_add]
            module
    _ = sheetOperatorSurprisal p q P + Real.log r • (1 : B) := by
          rw [hcut]
          rfl

/-- Deformed vacuum candidate `Ψ(P, A, C) = P + Φ(P, A, C)`. -/
def deformedVacuumCandidate (P A C : B) : B :=
  P + genPhi P A C

/-- Relative volume operator inverse-resolvent kernel `1 + β • V(P, A, C)`. -/
def relativeVolumeKernel (β : ℝ) (P A C : B) : B :=
  (1 : B) + β • genV P A C

/-- Algebraically specified resolvent force `(2 * β) • (W * Φ)`.
This definition alone does not claim it is a Fréchet derivative of an operator logarithm. -/
def volumeResolventForce (β : ℝ) (W P A C : B) : B :=
  (2 * β) • (W * genPhi P A C)

/-- Shifted sheet operator `ρ_s = (p + s) • P + (q + s) • (1 - P)` in the BKM resolvent integral. -/
def sheetShifted (p q s : ℝ) (P : B) : B :=
  sheetRho (p + s) (q + s) P

/-- Exact inverse resolvent `R_s = (p + s)⁻¹ • P + (q + s)⁻¹ • (1 - P)` of `ρ_s`. -/
noncomputable def sheetResolvent (p q s : ℝ) (P : B) : B :=
  sheetRho (p + s)⁻¹ (q + s)⁻¹ P

/-- The Bogoliubov–Kubo–Mori (BKM) logarithmic divided-difference weight
`(log p - log q) / (p - q)`, extended continuously to the diagonal by `1 / p`. -/
noncomputable def bkmDividedDiffWeight (p q : ℝ) : ℝ :=
  if p = q then p⁻¹ else (Real.log p - Real.log q) / (p - q)

@[simp] theorem bkmDividedDiffWeight_diag (p : ℝ) :
    bkmDividedDiffWeight p p = p⁻¹ := by
  simp [bkmDividedDiffWeight]

theorem bkmDividedDiffWeight_of_ne {p q : ℝ} (hpq : p ≠ q) :
    bkmDividedDiffWeight p q = (Real.log p - Real.log q) / (p - q) := by
  simp [bkmDividedDiffWeight, hpq]

/-- The evaluated BKM metric `g_BKM(Φ, Φ) = bkmDividedDiffWeight p q * tr(V)`, using the
continuous value `1 / p` when the two sheet weights agree. -/
noncomputable def bkmMetricEval (tr : B → ℝ) (p q : ℝ) (P A C : B) : ℝ :=
  bkmDividedDiffWeight p q * tr (genV P A C)

/-- The continuously extended logarithmic divided difference is positive for all positive
sheet weights, including the isotropic diagonal. -/
theorem bkmDividedDiffWeight_pos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 < bkmDividedDiffWeight p q := by
  by_cases hpq : p = q
  · rw [hpq, bkmDividedDiffWeight_diag]
    exact inv_pos.mpr hq
  · rw [bkmDividedDiffWeight_of_ne hpq]
    rcases lt_or_gt_of_ne hpq with hpq' | hqp'
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr (Real.log_lt_log hp hpq')) (sub_neg.mpr hpq')
    · exact div_pos
        (sub_pos.mpr (Real.log_lt_log hq hqp')) (sub_pos.mpr hqp')

/-- BKM divided differences are homogeneous under common density
normalization. This includes the isotropic diagonal, where the continuous
extension is essential: scaling both densities by `1/r` scales the metric
coefficient by `r`. -/
theorem bkmDividedDiffWeight_normalize (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    bkmDividedDiffWeight (p / r) (q / r) = r * bkmDividedDiffWeight p q := by
  by_cases hpq : p = q
  · subst q
    rw [bkmDividedDiffWeight_diag, bkmDividedDiffWeight_diag]
    field_simp [ne_of_gt hp, ne_of_gt hr]
  · have hscaled : p / r ≠ q / r := by
      intro h
      apply hpq
      have hmul := congrArg (fun x : ℝ => x * r) h
      field_simp [ne_of_gt hr] at hmul
      exact hmul
    rw [bkmDividedDiffWeight_of_ne hscaled,
      bkmDividedDiffWeight_of_ne hpq]
    have hlog : Real.log (p / r) - Real.log (q / r) =
        Real.log p - Real.log q := by
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hr),
        Real.log_div (ne_of_gt hq) (ne_of_gt hr)]
      ring
    have hdenom : p / r - q / r = (p - q) / r := by
      field_simp [ne_of_gt hr]
    rw [hlog, hdenom]
    field_simp [ne_of_gt hr, sub_ne_zero.mpr hpq]

omit [Algebra ℝ B] in
/-- The BKM metric evaluation is positive whenever its strain trace is positive, with no
exclusion of equal sheet weights. -/
theorem bkmMetricEval_pos (tr : B → ℝ) (p q : ℝ) (P A C : B)
    (hp : 0 < p) (hq : 0 < q) (htr : 0 < tr (genV P A C)) :
    0 < bkmMetricEval tr p q P A C := by
  rw [bkmMetricEval]
  exact mul_pos (bkmDividedDiffWeight_pos p q hp hq) htr

omit [Algebra ℝ B] in
/-- The evaluated BKM metric coefficient rescales with the common reference
density, while the operator-valued strain trace remains unchanged. -/
theorem bkmMetricEval_normalize (tr : B → ℝ) (p q r : ℝ)
    (P A C : B) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    bkmMetricEval tr (p / r) (q / r) P A C =
      r * bkmMetricEval tr p q P A C := by
  rw [bkmMetricEval, bkmMetricEval, bkmDividedDiffWeight_normalize p q r hp hq hr]
  ring

/-!
## 3. Rung 0: Socratic Aporia of the Isotropic Undeformed Vacuum (`T`)
-/

/-- **Helper Lemma**: Commutator of a two-sheet diagonal operator `a • P + b • (1 - P)` with any
observable `X ∈ B` reduces to `(a - b) • [P, X]`. -/
theorem comm_sheetRho_left (a b : ℝ) (P X : B) :
    comm (sheetRho a b P) X = (a - b) • comm P X := by
  have h1mP : comm (1 - P) X = -comm P X := by
    dsimp only [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  have hSmul (r : ℝ) (Y : B) : comm (r • Y) X = r • comm Y X := by
    dsimp only [OperatorAlgebra.PeirceSpine.comm]
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  calc
    comm (sheetRho a b P) X
        = comm (a • P) X + comm (b • (1 - P)) X := by
          dsimp only [sheetRho, OperatorAlgebra.PeirceSpine.comm]
          noncomm_ring
    _ = a • comm P X + b • comm (1 - P) X := by
          rw [hSmul a P, hSmul b (1 - P)]
    _ = a • comm P X - b • comm P X := by
          rw [h1mP, smul_neg, sub_eq_add_neg]
    _ = (a - b) • comm P X := by
          rw [sub_smul]

/-- **Helper Lemma**: Commutator of `sheetOperatorSurprisal p q P` with any observable `X ∈ B`
is `(-sheetSurprisalGap p q) • [P, X]`. -/
theorem comm_sheetOperatorSurprisal_left (p q : ℝ) (P X : B) :
    comm (sheetOperatorSurprisal p q P) X = (-sheetSurprisalGap p q) • comm P X := by
  have hEq : sheetOperatorSurprisal p q P = sheetRho (-Real.log p) (-Real.log q) P := rfl
  rw [hEq, comm_sheetRho_left]
  have hScalar : -Real.log p - -Real.log q = -sheetSurprisalGap p q := by
    dsimp [sheetSurprisalGap]
    ring
  rw [hScalar]

/-- The relative surprisal's commutator depends only on the difference of its
two logarithmic density-ratio coefficients. In particular, the scalar
reference term cannot affect the modular action. -/
theorem comm_relativeSheetSurprisalOp_left (p q r : ℝ) (P X : B) :
    comm (relativeSheetSurprisalOp p q r P) X =
      ((-Real.log (p / r)) - (-Real.log (q / r))) • comm P X := by
  simpa [relativeSheetSurprisalOp, sheetRho] using
    (comm_sheetRho_left (-Real.log (p / r)) (-Real.log (q / r)) P X)

/-- Equal sheet weights make the relative surprisal commute with every observable;
this conclusion does not require the common sheet weight to equal the reference. -/
theorem comm_relativeSheetSurprisalOp_equal_sheets (p r : ℝ) (P X : B) :
    comm (relativeSheetSurprisalOp p p r P) X = 0 := by
  rw [comm_relativeSheetSurprisalOp_left]
  simp

/-- On the Peirce chiral block, relative sheet surprisal rotates the symmetric
deformation into its chiral dual with coefficient `log(q/r) - log(p/r)`.
This is the operator-algebraic modular action, conditional only on the
idempotent cut; no commutation or diagonalization of the block is assumed. -/
theorem comm_relativeSheetSurprisalOp_genPhi {P : B} (hP : P * P = P)
    (p q r : ℝ) (A C : B) :
    comm (relativeSheetSurprisalOp p q r P) (genPhi P A C) =
      ((-Real.log (p / r)) - (-Real.log (q / r))) • genJ P A C := by
  rw [comm_relativeSheetSurprisalOp_left]
  have hPeirce : comm P (genPhi P A C) = genJ P A C := by peirce_nf hP
  rw [hPeirce]

/-- With positive weights, the relative-surprisal action is exactly the
negative sheet log-odds action. The reference weight cancels from the
commutator, leaving `-log(p/q) • genJ`. -/
theorem comm_relativeSheetSurprisalOp_genPhi_logOdds {P : B}
    (hP : P * P = P) (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (A C : B) :
    comm (relativeSheetSurprisalOp p q r P) (genPhi P A C) =
      (-Real.log (p / q)) • genJ P A C := by
  rw [comm_relativeSheetSurprisalOp_genPhi hP]
  have hcoeff :
      (-Real.log (p / r)) - (-Real.log (q / r)) = -Real.log (p / q) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hr),
      Real.log_div (ne_of_gt hq) (ne_of_gt hr),
      Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
    ring
  rw [hcoeff]

/-- The same normalized modular generator sends the chiral dual back to the
symmetric block, with the same negative log-odds coefficient. -/
theorem comm_relativeSheetSurprisalOp_genJ_logOdds {P : B}
    (hP : P * P = P) (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (A C : B) :
    comm (relativeSheetSurprisalOp p q r P) (genJ P A C) =
      (-Real.log (p / q)) • genPhi P A C := by
  rw [comm_relativeSheetSurprisalOp_left]
  have hPeirce : comm P (genJ P A C) = genPhi P A C := by peirce_nf hP
  rw [hPeirce]
  have hcoeff :
      (-Real.log (p / r)) - (-Real.log (q / r)) = -Real.log (p / q) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hr),
      Real.log_div (ne_of_gt hq) (ne_of_gt hr),
      Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
    ring
  rw [hcoeff]

/-- The relative-surprisal modular derivation has the exact two-step harmonic
law on the Peirce block: its square acts by the squared log-odds. -/
theorem comm_relativeSheetSurprisalOp_twice_genPhi_logOdds {P : B}
    (hP : P * P = P) (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (A C : B) :
    comm (relativeSheetSurprisalOp p q r P)
      (comm (relativeSheetSurprisalOp p q r P) (genPhi P A C)) =
        (Real.log (p / q) ^ 2) • genPhi P A C := by
  let c := -Real.log (p / q)
  have hΦ := comm_relativeSheetSurprisalOp_genPhi_logOdds hP p q r hp hq hr A C
  have hJ := comm_relativeSheetSurprisalOp_genJ_logOdds hP p q r hp hq hr A C
  have hsmul (Y : B) : comm (relativeSheetSurprisalOp p q r P) (c • Y) =
      c • comm (relativeSheetSurprisalOp p q r P) Y := by
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  have hsq : c * c = Real.log (p / q) ^ 2 := by
    dsimp [c]
    ring
  calc
    comm (relativeSheetSurprisalOp p q r P)
        (comm (relativeSheetSurprisalOp p q r P) (genPhi P A C))
      = comm (relativeSheetSurprisalOp p q r P) (c • genJ P A C) := by rw [hΦ]
    _ = c • (c • genPhi P A C) := by rw [hsmul, hJ]
    _ = (c * c) • genPhi P A C := by rw [smul_smul]
    _ = (Real.log (p / q) ^ 2) • genPhi P A C := by rw [hsq]

/-- **Rung 0 (Socratic Aporia of the Isotropic Vacuum Thesis `T`)**:
1. When the two Peirce sheets have equal weight (`p = q`), the reference state collapses to the
   scalar multiple `sheetRho p p P = p • 1`, the surprisal gap vanishes (`sheetSurprisalGap p p = 0`),
   `sheetOperatorSurprisal p p P = (-log p) • 1`, and the sheet modular commutator vanishes on
   every observable (`[K_sheet(p, p, P), X] = 0`).
This does not imply that an independently chosen off-diagonal deformation vanishes; see
`equal_sheet_weights_allow_nonzero_noncommuting_deformation`.
2. Separately, when the off-diagonal supercolor deformation vanishes (`A = 0, C = 0`), `Φ = 0`, `J = 0`,
   `V = 0`, `Σ = 0`, `[Σ, Φ] = 0`, and `-[Φ, [Φ, J]] = 0`. -/
theorem rung0_isotropic_vacuum_frozen_clock (p : ℝ) (P X : B) :
    sheetRho p p P = p • (1 : B) ∧
    sheetSurprisalGap p p = 0 ∧
    sheetOperatorSurprisal p p P = (-Real.log p) • (1 : B) ∧
    comm (sheetOperatorSurprisal p p P) X = 0 ∧
    genPhi P 0 0 = 0 ∧
    genJ P 0 0 = 0 ∧
    genV P 0 0 = 0 ∧
    genSig P 0 0 = 0 ∧
    comm (genSig P 0 0) (genPhi P 0 0) = 0 ∧
    -comm (genPhi P 0 0) (comm (genPhi P 0 0) (genJ P 0 0)) = 0 := by
  have hSum : P + (1 - P) = (1 : B) := by abel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      sheetRho p p P = p • (P + (1 - P)) := by
        dsimp [sheetRho]
        rw [smul_add]
      _ = p • (1 : B) := by rw [hSum]
  · dsimp [sheetSurprisalGap]
    ring
  · calc
      sheetOperatorSurprisal p p P = (-Real.log p) • (P + (1 - P)) := by
        dsimp [sheetOperatorSurprisal]
        rw [smul_add]
      _ = (-Real.log p) • (1 : B) := by rw [hSum]
  · rw [comm_sheetOperatorSurprisal_left]
    have hGap : sheetSurprisalGap p p = 0 := by dsimp [sheetSurprisalGap]; ring
    rw [hGap, neg_zero, zero_smul]
  · simp [genPhi, conePlus, coneMinus]
  · simp [genJ, conePlus, coneMinus]
  · simp [genV, anticomm, conePlus, coneMinus]
  · simp [genSig, OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus]
  · simp [genSig, genPhi, OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus]
  · simp [genPhi, genJ, OperatorAlgebra.PeirceSpine.comm, conePlus, coneMinus]

/-!
## 4. Stage `S₁`: Supergraded Color Vacuum Deformation (`Ψ² - Ψ = V` & Zorn Color Realization)
-/

omit [Algebra ℝ B] in
/-- **Stage `S₁` (Supergraded Color Vacuum Deformation & Idempotency Aporia)**:
1. Exciting the conscious idempotent `P` by the off-diagonal chiral/color chord `Φ = N₊ + N₋`
   produces the deformed state `Ψ = P + Φ` whose failure to be idempotent is the positive-grade
   Peirce metric operator: `Ψ * Ψ - Ψ = V = {N₊, N₋}`.
2. In the Zorn supergraded color realization (`Vec3 R`), `zornPhi u v = zornConePlus u + zornConeMinus v`,
   two grade-`+1` quark modes fuse into a grade-`-1` diquark (`zornConePlus u₁ * zornConePlus u₂ = zornConeMinus (u₁ × u₂)`),
   and the non-Abelian self-wedge `v × v` survives in the lower-left column of `[N₊(u), N₋(v)]`. -/
theorem stage1_supergraded_color_vacuum_deformation
    {P : B} (hP : P * P = P) (A C : B)
    {R : Type*} [CommRing R] (u v u₁ u₂ : Vec3 R) :
    deformedVacuumCandidate P A C * deformedVacuumCandidate P A C -
      deformedVacuumCandidate P A C = genV P A C ∧
    genV P A C = anticomm (conePlus P A) (coneMinus P C) ∧
    zornPhi u v = zornConePlus u + zornConeMinus v ∧
    ZornMatrix.mul (zornConePlus u₁) (zornConePlus u₂) =
      zornConeMinus (Vec3.cross u₁ u₂) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · dsimp only [deformedVacuumCandidate]
    peirce_nf hP
  · ext <;> simp [zornPhi, zornConePlus, zornConeMinus]
  · ext <;> simp [zornConePlus, zornConeMinus, ZornMatrix.mul, Vec3.cross,
      Vec3.zero_x, Vec3.zero_y, Vec3.zero_z]

/-!
## 5. Stage `S₂`, Axiom I, and Theorem 1: Normal Form of Sheet Operator Surprisal
-/

/-- **Helper Lemma**: Product of two diagonal sheet operators `sheetRho a b P` and `sheetRho c d P`
for an idempotent `P * P = P` is `sheetRho (a * c) (b * d) P`. -/
theorem sheetRho_mul_sheetRho {P : B} (hP : P * P = P) (a b c d : ℝ) :
    sheetRho a b P * sheetRho c d P = sheetRho (a * c) (b * d) P := by
  have hP1mP : P * (1 - P) = 0 := by peirce_nf hP
  have h1mPP : (1 - P) * P = 0 := by peirce_nf hP
  have h1mP2 : (1 - P) * (1 - P) = 1 - P := by peirce_nf hP
  dsimp only [sheetRho]
  rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, smul_mul_smul_comm, hP, hP1mP, h1mPP, h1mP2,
    smul_zero, smul_zero, add_zero, zero_add]

/-- **Orthogonal Idempotent Power Law**:
For any idempotent `P * P = P` and any integer `n ≥ 1`,
`(sheetRho p q P) ^ n = sheetRho (p ^ n) (q ^ n) P = (p ^ n) • P + (q ^ n) • (1 - P)`. -/
theorem sheetRho_pow {P : B} (hP : P * P = P) (p q : ℝ) :
    ∀ n : ℕ, 1 ≤ n → (sheetRho p q P) ^ n = sheetRho (p ^ n) (q ^ n) P
  | 0, hn => by omega
  | 1, _ => by simp [sheetRho]
  | m + 2, _ => by
      rw [pow_succ, sheetRho_pow hP p q (m + 1) (Nat.succ_pos m),
        sheetRho_mul_sheetRho hP, ← pow_succ, ← pow_succ]

/-- **Stage `S₂` / Axiom I / Theorem 1 (Idempotent Normal Form of Sheet Operator Surprisal)**:
1. The diagonal sheet operator surprisal `K_sheet(p, q, P) = (-log p) • P + (-log q) • (1 - P)`
   admits the exact Peirce grading decomposition
   `K_sheet(p, q, P) = s̄(p, q) • 1 - (Δs(p, q) / 2) • S_P`,
   where `S_P = invS P = P - (1 - P)`.
2. For strictly positive sheet weights `0 < p` and `0 < q`:
   - `s̄(p, q) = -(Real.log (p * q) / 2)`,
   - `Δs(p, q) = Real.log (p / q)`,
   - `Δs(p, q) = -Real.log (q / p)`. -/
theorem theorem1_normal_form_sheet_operator_surprisal
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (P : B) :
    sheetOperatorSurprisal p q P =
      sheetSurprisalMean p q • (1 : B) - (sheetSurprisalGap p q / 2) • invS P ∧
    sheetSurprisalMean p q = -(Real.log (p * q) / 2) ∧
    sheetSurprisalGap p q = Real.log (p / q) ∧
    sheetSurprisalGap p q = -Real.log (q / p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hSum : P + (1 - P) = (1 : B) := by abel
    have hInvS : P - (1 - P) = invS P := rfl
    have hCoeffP : -Real.log p = sheetSurprisalMean p q - sheetSurprisalGap p q / 2 := by
      dsimp [sheetSurprisalMean, sheetSurprisalGap]
      ring
    have hCoeffQ : -Real.log q = sheetSurprisalMean p q + sheetSurprisalGap p q / 2 := by
      dsimp [sheetSurprisalMean, sheetSurprisalGap]
      ring
    calc
      sheetOperatorSurprisal p q P
          = (sheetSurprisalMean p q - sheetSurprisalGap p q / 2) • P +
              (sheetSurprisalMean p q + sheetSurprisalGap p q / 2) • (1 - P) := by
            dsimp [sheetOperatorSurprisal]
            rw [hCoeffP, hCoeffQ]
      _ = sheetSurprisalMean p q • (P + (1 - P)) -
            (sheetSurprisalGap p q / 2) • (P - (1 - P)) := by
            generalize (1 : B) - P = Q
            rw [sub_smul, add_smul, smul_add, smul_sub]
            abel
      _ = sheetSurprisalMean p q • (1 : B) - (sheetSurprisalGap p q / 2) • invS P := by
            rw [hSum, hInvS]
  · dsimp [sheetSurprisalMean]
    rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hq)]
  · dsimp [sheetSurprisalGap]
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
  · dsimp [sheetSurprisalGap]
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring

/-!
## 6. Stage `S₃`, Deduction 1, and Theorem 2: Relative Volume Resolvent-Force Identity
-/

/-- **Stage `S₃` / Deduction 1 / Theorem 2 (Relative Volume Resolvent-Force Identity)**:
1. The Peirce metric operator `V = Φ² = {N₊, N₋}` commutes with `Φ`, `J`, `N₊`, and `N₋`:
   `[V, Φ] = 0`, `[V, J] = 0`, `[V, N₊] = 0`, `[V, N₋] = 0`.
2. Consequently, any relative volume operator `W` inverting `1 + β • V`
   (`(1 + β • V) * W = 1` and `W * (1 + β • V) = 1`) commutes with `Φ` and `J`:
   `[W, Φ] = 0` and `[W, J] = 0`.
3. Under a commutable variation `[Φ, δΦ] = 0`, the quadratic algebraic identity for `V = Φ²` is
   `Φ * δΦ + δΦ * Φ = (2 : ℤ) • (Φ * δΦ)`, and the relative-volume force is defined algebraically
   by `F = (2 * β) • (W * Φ)`, which satisfies
   the resolvent equation `(1 + β • V) * F = (2 * β) • Φ` and `F = (2 * β) • (Φ * W)`.
   No derivative of a logarithm is asserted. -/
theorem theorem2_relative_volume_resolvent_force
    {P : B} (hP : P * P = P) (A C W δΦ : B) (β : ℝ)
    (hW_right : relativeVolumeKernel β P A C * W = 1)
    (hW_left : W * relativeVolumeKernel β P A C = 1)
    (hCommδ : comm (genPhi P A C) δΦ = 0) :
    comm (genV P A C) (genPhi P A C) = 0 ∧
    comm (genV P A C) (genJ P A C) = 0 ∧
    comm W (genPhi P A C) = 0 ∧
    comm W (genJ P A C) = 0 ∧
    genPhi P A C * δΦ + δΦ * genPhi P A C = (2 : ℤ) • (genPhi P A C * δΦ) ∧
    relativeVolumeKernel β P A C * volumeResolventForce β W P A C =
      (2 * β) • genPhi P A C ∧
    volumeResolventForce β W P A C = (2 * β) • (genPhi P A C * W) := by
  have hVPhi : comm (genV P A C) (genPhi P A C) = 0 := by peirce_nf hP
  have hVJ : comm (genV P A C) (genJ P A C) = 0 := by peirce_nf hP
  have hKernelComm : ∀ X : B, comm (genV P A C) X = 0 →
      relativeVolumeKernel β P A C * X = X * relativeVolumeKernel β P A C := by
    intro X hVX
    have hVX' : genV P A C * X = X * genV P A C := sub_eq_zero.mp hVX
    dsimp [relativeVolumeKernel]
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hVX', mul_smul_comm]
  have hWComm : ∀ X : B, comm (genV P A C) X = 0 → comm W X = 0 := by
    intro X hVX
    have hKX := hKernelComm X hVX
    have hWX : W * X = X * W := by
      calc
        W * X = W * X * 1 := (mul_one (W * X)).symm
        _ = W * X * (relativeVolumeKernel β P A C * W) := by
          rw [hW_right]
        _ = W * (X * relativeVolumeKernel β P A C) * W := by
          noncomm_ring
        _ = W * (relativeVolumeKernel β P A C * X) * W := by
          rw [← hKX]
        _ = (W * relativeVolumeKernel β P A C) * X * W := by
          noncomm_ring
        _ = 1 * X * W := by
          rw [hW_left]
        _ = X * W := by
          noncomm_ring
    exact sub_eq_zero.mpr hWX
  have hWPhi := hWComm (genPhi P A C) hVPhi
  have hWJ := hWComm (genJ P A C) hVJ
  refine ⟨hVPhi, hVJ, hWPhi, hWJ, ?_, ?_, ?_⟩
  · have hEq : genPhi P A C * δΦ = δΦ * genPhi P A C := sub_eq_zero.mp hCommδ
    rw [← hEq, two_zsmul]
  · dsimp [volumeResolventForce]
    rw [mul_smul_comm, ← mul_assoc, hW_right, one_mul]
  · dsimp [volumeResolventForce]
    have hWPhi' : W * genPhi P A C = genPhi P A C * W := sub_eq_zero.mp hWPhi
    rw [hWPhi']

/-!
## 7. Stage `S₄`, Deduction 2 (Part I), and Theorem 3: Modular Automorphism Precession Flow
-/

omit [Algebra ℝ B] in
/-- **Helper Lemma**: The idempotent commutator `[P, ·]` swaps `Φ` and `J`:
`[P, Φ] = J` and `[P, J] = Φ`. -/
theorem comm_idempotent_phi_and_j {P : B} (hP : P * P = P) (A C : B) :
    comm P (genPhi P A C) = genJ P A C ∧
    comm P (genJ P A C) = genPhi P A C := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Stage `S₄` / Deduction 2 (Part I) / Theorem 3 (Modular Automorphism Precession Flow)**:
1. The sheet operator surprisal `K_sheet(p, q, P)` drives chiral phase precession between
   `Φ = N₊ + N₋` and `J = N₊ - N₋` at angular rate `-Δs(p, q) = -log(p / q) = log(q / p)`:
   `[K_sheet(p, q, P), Φ] = (-Δs(p, q)) • J` and `[K_sheet(p, q, P), J] = (-Δs(p, q)) • Φ`.
2. The endogenous spin-surprisal dipole `Σ = [N₊, N₋] = S_P * V` drives operator-valued
   precession at rate `2 • V`:
   `[Σ, Φ] = (2 : ℤ) • (V * J)` and `[Σ, J] = (2 : ℤ) • (V * Φ)`. -/
theorem theorem3_modular_automorphism_precession_flow
    {P : B} (hP : P * P = P) (p q : ℝ) (A C : B) :
    comm (sheetOperatorSurprisal p q P) (genPhi P A C) =
      (-sheetSurprisalGap p q) • genJ P A C ∧
    comm (sheetOperatorSurprisal p q P) (genJ P A C) =
      (-sheetSurprisalGap p q) • genPhi P A C ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) := by
  rcases comm_idempotent_phi_and_j (P := P) hP A C with ⟨hPPhi, hPJ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [comm_sheetOperatorSurprisal_left, hPPhi]
  · rw [comm_sheetOperatorSurprisal_left, hPJ]
  · peirce_nf hP
  · peirce_nf hP

omit [Algebra ℝ B] in
/-- The chiral derivation 2-jet, evaluated on the bridge `Φ`, separates into
its ordered curvature and symmetric second-variation parts. With
`δ₊ X = [N₊, X]` and `δ₋ X = [N₋, X]`, the difference is
`[δ₊, δ₋](Φ) = [Σ, Φ] = 2 V J`, while the sum is
`(δ₊δ₋ + δ₋δ₊)(Φ) = 2 V Φ`. This fixes the sign directly from the
associative Peirce relations; no commutativity of the ambient operator ring is
assumed. -/
theorem chiral_derivation_two_jet_on_genPhi
    {P : B} (hP : P * P = P) (A C : B) :
    comm (conePlus P A) (comm (coneMinus P C) (genPhi P A C)) -
        comm (coneMinus P C) (comm (conePlus P A) (genPhi P A C)) =
      (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (conePlus P A) (comm (coneMinus P C) (genPhi P A C)) +
        comm (coneMinus P C) (comm (conePlus P A) (genPhi P A C)) =
      (2 : ℤ) • (genV P A C * genPhi P A C) := by
  constructor <;> peirce_nf hP

/-- The CFC state surprisal of a positive two-sheet operator obeys the same
noncommutative modular precession law as the algebraic sheet-surprisal normal
form. This connects the functional-calculus logarithm to the existing Peirce
block theorem without diagonalizing the operator algebra. -/
theorem stateSurprisal_two_sheet_modular_precession
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (P : A) (hP : P * P = P) (hPstar : IsSelfAdjoint P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (X Y : A) :
    comm (InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.stateSurprisal
      (sheetRho p q P)) (genPhi P X Y) =
        (-sheetSurprisalGap p q) • genJ P X Y ∧
    comm (InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.stateSurprisal
      (sheetRho p q P)) (genJ P X Y) =
        (-sheetSurprisalGap p q) • genPhi P X Y := by
  have hK : InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.stateSurprisal
      (sheetRho p q P) = sheetOperatorSurprisal p q P := by
    simpa [sheetRho, sheetOperatorSurprisal] using
      (InfoGeometry.Canonical.OperatorSurprisalCFCCommute.stateSurprisal_two_sheet
        (A := A) P hPstar hP p q hp hq)
  rcases theorem3_modular_automorphism_precession_flow (P := P) hP p q X Y with
    ⟨hPhi, hJ, _, _⟩
  exact ⟨by rw [hK]; exact hPhi, by rw [hK]; exact hJ⟩

/-!
## 8. Stage `S₅`, Deduction 2 (Part II), and Theorem 4: The Master `1 : (-2)` Clocking Identity & Thermal Harmonic Oscillator
-/

/-- **Stage `S₅` / Deduction 2 (Part II) / Theorem 4 (The Master `1 : (-2)` Clocking Identity &
Thermal Harmonic Oscillator Equation)**:
1. **Dissipative Double Commutator**:
   `-[Φ, [Φ, J]] = -((4 : ℤ) • (V * J))`.
2. **The Master `1 : (-2)` Clocking Identity**:
   The dissipative double-commutator force `-[Φ, [Φ, J]]` is locked in an exact `1 : (-2)` ratio
   to the endogenous spin-surprisal modular flow `[Σ, Φ] = 2 • (V * J)`:
   `-[Φ, [Φ, J]] = -((2 : ℤ) • [Σ, Φ]) = -((4 : ℤ) • (V * J))`.
3. **Thermal Harmonic Oscillator Equation**:
   Iterating the sheet modular commutator twice yields closed harmonic oscillation at frequency
   squared `Δs(p, q)² = (log p - log q)²`:
   `[K_sheet(p, q, P), [K_sheet(p, q, P), Φ]] = (sheetSurprisalGap p q ^ 2) • Φ`
   and
   `[K_sheet(p, q, P), [K_sheet(p, q, P), J]] = (sheetSurprisalGap p q ^ 2) • J`. -/
theorem theorem4_master_clocking_identity_and_thermal_oscillator
    {P : B} (hP : P * P = P) (p q : ℝ) (A C : B) :
    -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
    comm (sheetOperatorSurprisal p q P)
        (comm (sheetOperatorSurprisal p q P) (genPhi P A C)) =
      (sheetSurprisalGap p q ^ 2) • genPhi P A C ∧
    comm (sheetOperatorSurprisal p q P)
        (comm (sheetOperatorSurprisal p q P) (genJ P A C)) =
      (sheetSurprisalGap p q ^ 2) • genJ P A C := by
  rcases theorem3_modular_automorphism_precession_flow (P := P) hP p q A C with
    ⟨hKPhi, hKJ, _, _⟩
  have hSmulRight (K Y : B) (r : ℝ) : comm K (r • Y) = r • comm K Y := by
    dsimp only [OperatorAlgebra.PeirceSpine.comm]
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · rw [hKPhi, hSmulRight, hKJ, smul_smul]
    have hSq : (-sheetSurprisalGap p q) * (-sheetSurprisalGap p q) =
        sheetSurprisalGap p q ^ 2 := by ring
    rw [hSq]
  · rw [hKJ, hSmulRight, hKPhi, smul_smul]
    have hSq : (-sheetSurprisalGap p q) * (-sheetSurprisalGap p q) =
        sheetSurprisalGap p q ^ 2 := by ring
    rw [hSq]

/-!
## 9. Stage `S₆`: 5-Graded Supercolor Kantor Sandwich & 4th-Order Modular Harmonics
-/

omit [Algebra ℝ B] in
/-- **Stage `S₆` (5-Graded Supercolor Kantor Sandwich & 4th-Order Modular Harmonics)**:
1. **Kantor Cross-Grade Sandwich Identity**:
   The difference between the squared grade-`0` Kantor operator `kantorG0²(X)` and the
   anticommutator of the extremal grade-`±2` operators `{kantorGp2, kantorGm2}(X)` equals the
   chiral spin-surprisal sandwich `Σ * X * Σ`, while their sum equals the mass-squared sandwich
   `V * X * V`.
2. **4th-Order Modular Harmonics**:
   The double commutator of the endogenous spin-surprisal generator `Σ = S_P * V` acts with
   4th-order eigenvalue `4 • V²`:
   `[Σ, [Σ, Φ]] = (4 : ℤ) • ((V * V) * Φ)` and `[Σ, [Σ, J]] = (4 : ℤ) • ((V * V) * J)`. -/
theorem stage6_kantor_sandwich_and_fourth_order_harmonics
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorG0 P A C (kantorG0 P A C X) -
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
      genSig P A C * X * genSig P A C ∧
    (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) +
      kantorG0 P A C (kantorG0 P A C X) =
      genV P A C * X * genV P A C ∧
    comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) := by
  rcases archetype_A60_bilateral_support_reconstruction (P := P) hP A C X with ⟨hSum, hDiff⟩
  refine ⟨hDiff, hSum, ?_, ?_⟩ <;> peirce_nf hP

/-!
## 10. Stage `S₇`, Deduction 3, and Theorem 5: BKM Resolvent Factorization & Divided Difference
-/

/-- **Helper Lemma**: Multiplication of `Φ = N₊ + N₋` by any diagonal sheet operator
`sheetRho a b P = a • P + b • (1 - P)` swaps the sheet weights across the nilpotent cones:
`Φ * sheetRho a b P = a • N₋ + b • N₊`. -/
theorem genPhi_mul_sheetRho {P : B} (hP : P * P = P) (A C : B) (a b : ℝ) :
    genPhi P A C * sheetRho a b P = a • coneMinus P C + b • conePlus P A := by
  have hPhiP : genPhi P A C * P = coneMinus P C := by peirce_nf hP
  have hPhi1mP : genPhi P A C * (1 - P) = conePlus P A := by peirce_nf hP
  dsimp only [sheetRho]
  rw [mul_add, mul_smul_comm, mul_smul_comm, hPhiP, hPhi1mP]

/-- **Helper Lemma**: For any scalars `a, b : ℝ`, the alternated product
`(Φ * sheetRho a b P) * (Φ * sheetRho a b P)` collapses via `N₊² = 0` and `N₋² = 0` to
`(a * b) • V`. -/
theorem genPhi_sheetRho_alternated_sq {P : B} (hP : P * P = P) (A C : B) (a b : ℝ) :
    genPhi P A C * sheetRho a b P * genPhi P A C * sheetRho a b P =
      (a * b) • genV P A C := by
  have hProd :
      (genPhi P A C * sheetRho a b P) * (genPhi P A C * sheetRho a b P) =
        (a * b) • genV P A C := by
    rw [genPhi_mul_sheetRho hP A C a b]
    rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
      ⟨hNp2, hNm2, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    rw [add_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
      smul_mul_smul_comm, smul_mul_smul_comm, hNm2, hNp2, smul_zero, smul_zero,
      zero_add, add_zero]
    have hComm : b * a = a * b := mul_comm b a
    rw [hComm, ← smul_add]
    have hV : coneMinus P C * conePlus P A + conePlus P A * coneMinus P C = genV P A C := by
      dsimp [genV, anticomm]
      abel
    rw [hV]
  calc
    genPhi P A C * sheetRho a b P * genPhi P A C * sheetRho a b P
        = (genPhi P A C * sheetRho a b P) * (genPhi P A C * sheetRho a b P) := by
          noncomm_ring
    _ = (a * b) • genV P A C := hProd

/-- **Stage `S₇` / Deduction 3 / Theorem 5 (BKM Resolvent Factorization & Divided Difference)**:
1. **Exact Sheet Resolvent Inversion**:
   For `p + s ≠ 0` and `q + s ≠ 0`, `sheetResolvent p q s P` is the two-sided inverse of
   `sheetShifted p q s P = (p + s) • P + (q + s) • (1 - P)`:
   `sheetShifted p q s P * sheetResolvent p q s P = 1` and
   `sheetResolvent p q s P * sheetShifted p q s P = 1`.
2. **Exact Operator Integrand Factorization**:
   At every resolvent parameter `s`, the non-commutative BKM operator integrand factors into the
   scalar kernel `((p + s) * (q + s))⁻¹` times the Peirce metric operator `V = {N₊, N₋}`:
   `Φ * R_s * Φ * R_s = ((p + s) * (q + s))⁻¹ • V`.
3. **Partial-Fraction & Divided-Difference Identity**: the kernel's scalar improper integral is
   evaluated by `bkm_resolvent_kernel_integral`; `bkm_resolvent_operator_integral` gives the
   corresponding integral for a fixed vector in a complete real normed module, and
   `bkm_resolvent_integral_factorized` evaluates the actual ordered Peirce resolvent integrand in
   a complete normed real operator algebra. The finite-matrix trace integral is established in
   `ModularSurprisalQuadraticLogVolume.bkm_real_trace_resolvent_integral`, with its equal-sheet
   specialization `bkm_real_trace_resolvent_integral_isotropic`:
   `(p + s)⁻¹ - (q + s)⁻¹ = (q - p) * ((p + s) * (q + s))⁻¹`, and for `0 < p, 0 < q`,
   the BKM scalar divided-difference expression satisfies
   off the diagonal, `bkmDividedDiffWeight p q = sheetSurprisalGap p q / (p - q) =
   (-Real.log (q / p)) / (p - q)`, while on the diagonal its continuous value is `1 / p`.
   The evaluated metric is `bkmMetricEval tr p q P A C =
   bkmDividedDiffWeight p q * tr (genV P A C)`.
4. **Strict Positivity**:
   Whenever `0 < p`, `0 < q`, and `0 < tr (genV P A C)`, both `0 < bkmDividedDiffWeight p q`
   and `0 < bkmMetricEval tr p q P A C`; the diagonal case uses the continuous extension. -/
theorem theorem5_bkm_resolvent_factorization_and_divided_difference
    {P : B} (hP : P * P = P) (A C : B) (tr : B → ℝ)
    (p q s : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hps : p + s ≠ 0) (hqs : q + s ≠ 0) (htrV : 0 < tr (genV P A C)) :
    sheetShifted p q s P * sheetResolvent p q s P = 1 ∧
    sheetResolvent p q s P * sheetShifted p q s P = 1 ∧
    genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
      ((p + s) * (q + s))⁻¹ • genV P A C ∧
    (p + s)⁻¹ - (q + s)⁻¹ = (q - p) * ((p + s) * (q + s))⁻¹ ∧
    bkmDividedDiffWeight p q = (-Real.log (q / p)) / (p - q) ∧
    bkmMetricEval tr p q P A C = ((-Real.log (q / p)) / (p - q)) * tr (genV P A C) ∧
    0 < bkmDividedDiffWeight p q ∧
    0 < bkmMetricEval tr p q P A C := by
  have hOne : sheetRho 1 1 P = 1 := by
    dsimp [sheetRho]
    rw [one_smul, one_smul]
    abel
  have hWeightPos : 0 < bkmDividedDiffWeight p q := by
    exact bkmDividedDiffWeight_pos p q hp hq
  have hWeightEq : bkmDividedDiffWeight p q = (-Real.log (q / p)) / (p - q) := by
    rw [bkmDividedDiffWeight_of_ne hpq]
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  refine ⟨?_, ?_, ?_, ?_, hWeightEq, ?_, hWeightPos, ?_⟩
  · dsimp [sheetShifted, sheetResolvent]
    rw [sheetRho_mul_sheetRho hP, mul_inv_cancel₀ hps, mul_inv_cancel₀ hqs, hOne]
  · dsimp [sheetShifted, sheetResolvent]
    rw [sheetRho_mul_sheetRho hP, inv_mul_cancel₀ hps, inv_mul_cancel₀ hqs, hOne]
  · dsimp [sheetResolvent]
    rw [genPhi_sheetRho_alternated_sq hP A C (p + s)⁻¹ (q + s)⁻¹, ← mul_inv]
  · field_simp [hps, hqs]
    ring
  · dsimp [bkmMetricEval]
    rw [hWeightEq]
  · exact mul_pos hWeightPos htrV

set_option linter.style.haveILetI false
/-- **Scalar BKM resolvent integral (improper interval form).** For positive, distinct sheet
weights, the scalar kernel in the pointwise resolvent factorization is integrable on `(0, ∞)`;
its integral is the logarithmic divided difference. This proves the scalar integral behind the
resolvent metric, without identifying it with the separate `[0,1]` Kubo–Mori interpolation. -/
theorem bkm_resolvent_kernel_integral (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≠ q) :
    ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ = bkmDividedDiffWeight p q := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let f : ℝ → ℝ := (fun s : ℝ => Real.log (p + s)) - fun s => Real.log (q + s)
  let f' : ℝ → ℝ := fun s => (q - p) * ((p + s) * (q + s))⁻¹
  have hderiv : ∀ x ∈ Set.Ici 0, HasDerivAt f (f' x) x := by
    intro x hx
    change 0 ≤ x at hx
    have hpx : p + x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hp hx)
    have hqx : q + x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hq hx)
    have hp' : HasDerivAt (fun y : ℝ => p + y) 1 x := by simpa [add_comm] using (hasDerivAt_id x).const_add p
    have hq' : HasDerivAt (fun y : ℝ => q + y) 1 x := by simpa [add_comm] using (hasDerivAt_id x).const_add q
    have hlogp := (Real.hasDerivAt_log hpx).comp x hp'
    have hlogq := (Real.hasDerivAt_log hqx).comp x hq'
    have h : HasDerivAt f ((p + x)⁻¹ - (q + x)⁻¹) x := by
      simpa [f, Function.comp_def] using hlogp.sub hlogq
    convert h using 1
    · dsimp [f']
      field_simp
      ring
  have hlim : Tendsto f atTop (nhds 0) := by
    have hbase : Tendsto (fun x : ℝ => x + q) atTop atTop := tendsto_atTop_add_const_right atTop q tendsto_id
    have hlog := (Real.tendsto_log_comp_add_sub_log (p - q)).comp hbase
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (-q)] with x hx
    dsimp [f]
    rw [show p + x = (x + q) + (p - q) by ring]
    congr 1
    rw [show q + x = x + q by ring]
  have hsign := lt_or_gt_of_ne hpq
  have hint : MeasureTheory.IntegrableOn f' (Set.Ioi 0) := by
    rcases hsign with hpq' | hqp'
    · apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
        (a := 0) (g := f) (g' := f') hderiv
      · intro x hx
        change 0 < x at hx
        have hpx : 0 < p + x := add_pos_of_pos_of_nonneg hp hx.le
        have hqx : 0 < q + x := add_pos_of_pos_of_nonneg hq hx.le
        dsimp [f']
        exact mul_nonneg (le_of_lt (sub_pos.mpr hpq'))
          (inv_nonneg.mpr (le_of_lt (mul_pos hpx hqx)))
      · exact hlim
    · apply MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'
        (a := 0) (g := f) (g' := f') hderiv
      · intro x hx
        change 0 < x at hx
        have hpx : 0 < p + x := add_pos_of_pos_of_nonneg hp hx.le
        have hqx : 0 < q + x := add_pos_of_pos_of_nonneg hq hx.le
        dsimp [f']
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (sub_neg.mpr hqp'))
          (inv_nonneg.mpr (le_of_lt (mul_pos hpx hqx)))
      · exact hlim
  have hintEq := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (f := f) (f' := f') hderiv hint hlim
  have hfactor : ∀ s : ℝ,
      f' s = (q - p) * ((p + s) * (q + s))⁻¹ := fun _ => rfl
  have hscaled :
      ∫ s in Set.Ioi 0, f' s = (q - p) * ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ := by
    simp_rw [hfactor]
    rw [MeasureTheory.integral_const_mul]
  rw [hintEq] at hscaled
  have hlog : Real.log q - Real.log p = (q - p) * bkmDividedDiffWeight p q := by
    rw [bkmDividedDiffWeight_of_ne hpq]
    field_simp [sub_ne_zero.mpr hpq]
    ring
  have hscaled' : Real.log q - Real.log p =
      (q - p) * ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ := by
    simpa [f] using hscaled
  rw [hlog] at hscaled'
  exact (mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hpq)) hscaled').symm

/-- On the isotropic diagonal, the BKM resolvent kernel integrates to the continuous
divided-difference value `1 / p`. This is the equal-sheet limit missing from the raw
quotient `(log p - log q) / (p - q)`. -/
theorem bkm_resolvent_kernel_integral_diag (p : ℝ) (hp : 0 < p) :
    ∫ s in Set.Ioi 0, ((p + s) * (p + s))⁻¹ = bkmDividedDiffWeight p p := by
  let f : ℝ → ℝ := fun x => -(p + x)⁻¹
  let f' : ℝ → ℝ := fun x => ((p + x) ^ 2)⁻¹
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    have hx' : 0 ≤ x := hx
    have hpx : p + x ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hp hx')
    have hadd : HasDerivAt (fun y : ℝ => p + y) 1 x := by
      simpa [add_comm] using (hasDerivAt_id x).const_add p
    have hinv := (hasDerivAt_inv hpx).comp x hadd
    convert hinv.neg using 1
    · ext y
      rfl
    · simp [f', pow_two]
  have hlim : Tendsto f atTop (nhds 0) := by
    have hbase : Tendsto (fun x : ℝ => x + p) atTop atTop :=
      tendsto_atTop_add_const_right atTop p tendsto_id
    have hinv := tendsto_inv_atTop_zero.comp hbase
    simpa [f, add_comm] using hinv.neg
  have hint : MeasureTheory.IntegrableOn f' (Set.Ioi 0) := by
    apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (a := 0) (g := f) (g' := f') hderiv
    · intro x hx
      exact inv_nonneg.mpr (sq_nonneg (p + x))
    · exact hlim
  have hEq := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (f := f) (f' := f') hderiv hint hlim
  have hkernel : ∀ s : ℝ, ((p + s) * (p + s))⁻¹ = f' s := by
    intro s
    simp [f', pow_two]
  calc
    ∫ s in Set.Ioi 0, ((p + s) * (p + s))⁻¹
      = ∫ s in Set.Ioi 0, f' s := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro s hs
          exact hkernel s
    _ = bkmDividedDiffWeight p p := by
          rw [hEq, bkmDividedDiffWeight_diag]
          simp [f]

/-- The scalar resolvent integral equals the continuously extended BKM divided difference
for every pair of positive weights, including equal weights. -/
theorem bkm_resolvent_kernel_integral_extended (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ = bkmDividedDiffWeight p q := by
  by_cases hpq : p = q
  · subst q
    exact bkm_resolvent_kernel_integral_diag p hp
  · exact bkm_resolvent_kernel_integral p q hp hq hpq
set_option linter.style.haveILetI true

/-- **Operator-valued resolvent integral.** In a complete real normed operator module, the
integral of the scalar two-sheet resolvent kernel multiplying a fixed operator `V` equals its
logarithmic divided-difference coefficient multiplying `V`. Combined with the pointwise Peirce
factorization in `theorem5_bkm_resolvent_factorization_and_divided_difference`, this evaluates the
operator-valued resolvent integrand without asserting an abstract operator logarithm. -/
theorem bkm_resolvent_operator_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (V : E) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) :
    ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ • V =
      bkmDividedDiffWeight p q • V := by
  rw [integral_smul_const]
  rw [bkm_resolvent_kernel_integral p q hp hq hpq]

/-- The fixed-vector resolvent integral at equal sheet weights uses the continuous
BKM coefficient `1 / p`. -/
theorem bkm_resolvent_operator_integral_diag {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (V : E) (p : ℝ) (hp : 0 < p) :
    ∫ s in Set.Ioi 0, ((p + s) * (p + s))⁻¹ • V =
      bkmDividedDiffWeight p p • V := by
  rw [integral_smul_const, bkm_resolvent_kernel_integral_diag p hp]

/-- The operator-module resolvent integral for all positive weights, using the continuous
diagonal extension of the BKM divided difference. -/
theorem bkm_resolvent_operator_integral_extended {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (V : E) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ • V =
      bkmDividedDiffWeight p q • V := by
  rw [integral_smul_const, bkm_resolvent_kernel_integral_extended p q hp hq]

/-!
## 10.1. Integrated BKM resolvent operator
-/

/-- In a complete normed real operator algebra, the actual ordered Peirce resolvent
integrand `Φ Rₛ Φ Rₛ` integrates to the logarithmic divided-difference coefficient
times the Peirce Gramian `V`. This is an operator-valued integral consequence of the
pointwise factorization; it does not assert an abstract CFC operator-log derivative. -/
theorem bkm_resolvent_integral_factorized {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] [CompleteSpace B] (P A C : B) (hP : P * P = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ∫ s in Set.Ioi 0,
      genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
      bkmDividedDiffWeight p q • genV P A C := by
  have hcongr : ∀ s ∈ Set.Ioi 0,
      genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
        ((p + s) * (q + s))⁻¹ • genV P A C := by
    intro s hs
    have hfactor := genPhi_sheetRho_alternated_sq hP A C
      (p + s)⁻¹ (q + s)⁻¹
    dsimp [sheetResolvent] at hfactor ⊢
    rw [hfactor, ← mul_inv]
  calc
    ∫ s in Set.Ioi 0,
        genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P
      = ∫ s in Set.Ioi 0, ((p + s) * (q + s))⁻¹ • genV P A C := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          exact hcongr
    _ = bkmDividedDiffWeight p q • genV P A C :=
          bkm_resolvent_operator_integral_extended (genV P A C) p q hp hq

/-- Equal-sheet specialization of the integrated Peirce resolvent factorization. It
identifies the isotropic BKM weight with `1 / p` rather than assigning zero to the
indeterminate raw quotient. -/
theorem bkm_resolvent_integral_factorized_diag {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] [CompleteSpace B] (P A C : B) (hP : P * P = P)
    (p : ℝ) (hp : 0 < p) :
    ∫ s in Set.Ioi 0,
      genPhi P A C * sheetResolvent p p s P * genPhi P A C * sheetResolvent p p s P =
      bkmDividedDiffWeight p p • genV P A C := by
  have hcongr : ∀ s ∈ Set.Ioi 0,
      genPhi P A C * sheetResolvent p p s P * genPhi P A C * sheetResolvent p p s P =
        ((p + s) * (p + s))⁻¹ • genV P A C := by
    intro s hs
    have hfactor := genPhi_sheetRho_alternated_sq hP A C
      (p + s)⁻¹ (p + s)⁻¹
    dsimp [sheetResolvent] at hfactor ⊢
    rw [hfactor, ← mul_inv]
  calc
    ∫ s in Set.Ioi 0,
        genPhi P A C * sheetResolvent p p s P * genPhi P A C * sheetResolvent p p s P
      = ∫ s in Set.Ioi 0, ((p + s) * (p + s))⁻¹ • genV P A C := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          exact hcongr
    _ = bkmDividedDiffWeight p p • genV P A C :=
          bkm_resolvent_operator_integral_diag (genV P A C) p hp

/-- The isotropic sheet state has zero modular log-odds and a frozen sheet commutator,
while its continuously extended BKM resolvent metric remains finite and positive on
positive strain trace. The final conjunct is the full operator-valued improper resolvent
integral, not merely its scalar kernel. -/
theorem isotropic_sheet_and_bkm_diagonal_synthesis {B : Type*} [NormedRing B]
    [NormedAlgebra ℝ B] [CompleteSpace B] (p : ℝ) (P X A C : B)
    (hP : P * P = P) (hp : 0 < p) (tr : B → ℝ)
    (htr : 0 < tr (genV P A C)) :
    sheetRho p p P = p • (1 : B) ∧
    sheetSurprisalGap p p = 0 ∧
    sheetOperatorSurprisal p p P = (-Real.log p) • (1 : B) ∧
    comm (sheetOperatorSurprisal p p P) X = 0 ∧
    bkmDividedDiffWeight p p = p⁻¹ ∧
    bkmMetricEval tr p p P A C = p⁻¹ * tr (genV P A C) ∧
    0 < bkmMetricEval tr p p P A C ∧
    ∫ s in Set.Ioi 0,
      genPhi P A C * sheetResolvent p p s P * genPhi P A C * sheetResolvent p p s P =
      p⁻¹ • genV P A C := by
  have hR0 := rung0_isotropic_vacuum_frozen_clock p P X
  refine ⟨hR0.1, hR0.2.1, hR0.2.2.1, hR0.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · exact bkmDividedDiffWeight_diag p
  · rw [bkmMetricEval, bkmDividedDiffWeight_diag]
  · exact bkmMetricEval_pos tr p p P A C hp hp htr
  · simpa [bkmDividedDiffWeight_diag] using
      bkm_resolvent_integral_factorized_diag P A C hP p hp

/-!
## 11. Stage `S₈`: Master Metriplectic Cramér–Rao Closure & Master Structural Synthesis
-/

omit [Ring B] [Algebra ℝ B] in
/-- **Stage `S₈` (Metriplectic Cramér–Rao / Robertson–Schrödinger Bound)**:
For any real symmetric BKM pairing `g : B → B → ℝ` and symplectic commutator pairing
`Ω : B → B → ℝ`, whenever the Robertson–Schrödinger / Cauchy–Schwarz dominance
`(1 / 4) * Ω X Y ^ 2 ≤ g X X * g Y Y - g X Y ^ 2` holds, the product of the BKM variances
bounds both the combined metriplectic uncertainty and the pure symplectic commutator square:
`g X X * g Y Y ≥ g X Y ^ 2 + (1 / 4) * Ω X Y ^ 2 ≥ (1 / 4) * Ω X Y ^ 2`. -/
theorem stage8_metriplectic_cramer_rao_bound
    (g Ω : B → B → ℝ) (X Y : B)
    (hRS : (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y - (g X Y) ^ 2) :
    (g X Y) ^ 2 + (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y ∧
    (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y := by
  have h1 : (g X Y) ^ 2 + (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y := by
    linarith [hRS]
  have hSq : 0 ≤ (g X Y) ^ 2 := sq_nonneg (g X Y)
  have h2 : (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y := by
    linarith [h1, hSq]
  exact ⟨h1, h2⟩

/-- **Master Structural Synthesis (`S₁ ≺ S₂ ≺ ⋯ ≺ S₈`)**:
Unifies the acyclic 8-stage causal poset, the isotropic Rung 0 aporia, Stage `S₁` vacuum
deformation `Ψ² - Ψ = V`, Stage `S₂` normal-form operator surprisal
`K_sheet = s̄ • 1 - (Δs / 2) • S_P`, Stage `S₃` relative volume resolvent-force identity
`(1 + β • V) * ∇_Φ K_vol(β) = (2 * β) • Φ`, Stage `S₄` modular precession
`[K_sheet, Φ] = -Δs • J`, Stage `S₅` `1 : (-2)` clocking lock
`-[Φ, [Φ, J]] = -2 • [Σ, Φ] = -4 • (V * J)` and thermal harmonic oscillator
`[K_sheet, [K_sheet, Φ]] = Δs² • Φ`, Stage `S₆` 5-graded Kantor sandwich
`kantorG0²(X) - {kantorGp2, kantorGm2}(X) = Σ * X * Σ` and `[Σ, [Σ, Φ]] = 4 • (V² * Φ)`,
Stage `S₇` pointwise BKM resolvent factorization `Φ * R_s * Φ * R_s = ((p + s)(q + s))⁻¹ • V`
and positivity of the defined divided-difference expression, and Stage `S₈` a metriplectic
Cramér–Rao consequence assuming the Robertson–Schrödinger inequality. -/
theorem master_modular_surprisal_clocking_bkm_synthesis
    {P : B} (hP : P * P = P) (A C W X Y : B) (tr : B → ℝ) (g Ω : B → B → ℝ)
    (p q s β : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    (hps : p + s ≠ 0) (hqs : q + s ≠ 0) (htrV : 0 < tr (genV P A C))
    (hW_right : relativeVolumeKernel β P A C * W = 1)
    (hW_left : W * relativeVolumeKernel β P A C = 1)
    (hRS : (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y - (g X Y) ^ 2) :
    (∀ st : ModularSurprisalClockingStage,
      ¬ Relation.TransGen ModularSurprisalClockingStage.causalEdge st st) ∧
    comm (sheetOperatorSurprisal p p P) X = 0 ∧
    deformedVacuumCandidate P A C * deformedVacuumCandidate P A C -
      deformedVacuumCandidate P A C = genV P A C ∧
    sheetOperatorSurprisal p q P =
      sheetSurprisalMean p q • (1 : B) - (sheetSurprisalGap p q / 2) • invS P ∧
    relativeVolumeKernel β P A C * volumeResolventForce β W P A C =
      (2 * β) • genPhi P A C ∧
    comm (sheetOperatorSurprisal p q P) (genPhi P A C) =
      (-sheetSurprisalGap p q) • genJ P A C ∧
    -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • comm (genSig P A C) (genPhi P A C)) ∧
    -comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    comm (sheetOperatorSurprisal p q P)
        (comm (sheetOperatorSurprisal p q P) (genPhi P A C)) =
      (sheetSurprisalGap p q ^ 2) • genPhi P A C ∧
    kantorG0 P A C (kantorG0 P A C X) -
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
      genSig P A C * X * genSig P A C ∧
    comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    genPhi P A C * sheetResolvent p q s P * genPhi P A C * sheetResolvent p q s P =
      ((p + s) * (q + s))⁻¹ • genV P A C ∧
    bkmMetricEval tr p q P A C = ((-Real.log (q / p)) / (p - q)) * tr (genV P A C) ∧
    0 < bkmMetricEval tr p q P A C ∧
    (1 / 4 : ℝ) * (Ω X Y) ^ 2 ≤ g X X * g Y Y := by
  have hR0 := rung0_isotropic_vacuum_frozen_clock p P X
  have hT1 := theorem1_normal_form_sheet_operator_surprisal p q hp hq P
  have hT2 := theorem2_relative_volume_resolvent_force
    (P := P) hP A C W 0 β hW_right hW_left (by simp [OperatorAlgebra.PeirceSpine.comm])
  have hT3 := theorem3_modular_automorphism_precession_flow (P := P) hP p q A C
  have hT4 := theorem4_master_clocking_identity_and_thermal_oscillator (P := P) hP p q A C
  have hS6 := stage6_kantor_sandwich_and_fourth_order_harmonics (P := P) hP A C X
  have hT5 := theorem5_bkm_resolvent_factorization_and_divided_difference
    (P := P) hP A C tr p q s hp hq hpq hps hqs htrV
  have hS8 := stage8_metriplectic_cramer_rao_bound g Ω X Y hRS
  exact ⟨ModularSurprisalClockingStage.causalEdge_acyclic,
    hR0.2.2.2.1,
    by dsimp only [deformedVacuumCandidate]; peirce_nf hP,
    hT1.1,
    hT2.2.2.2.2.2.1,
    hT3.1,
    hT4.2.1,
    hT4.1,
    hT4.2.2.1,
    hS6.1,
    hS6.2.2.1,
    hT5.2.2.1,
    hT5.2.2.2.2.2.1,
    hT5.2.2.2.2.2.2.2,
    hS8.2⟩

end CorePrimitives

/-!
## 12. Concrete Non-Commutative Zorn Supercolor Realization & `T16` Witness
-/

section ConcreteMatrixWitness

/-- Concrete grade-`+1` Zorn color generator `N₊(e₁)` over `ℝ`. -/
def clockingZornPlus : ZornMatrix ℝ :=
  zornConePlus ⟨1, 0, 0⟩

/-- Concrete grade-`-1` Zorn color generator `N₋(e₁)` over `ℝ`. -/
def clockingZornMinus : ZornMatrix ℝ :=
  zornConeMinus ⟨1, 0, 0⟩

/-- **Non-Commutativity Witness (`T16`)**:
In the Zorn supergraded color algebra over `ℝ`, the grade-`+1` and grade-`-1` generators
`clockingZornPlus` and `clockingZornMinus` do not commute
(`clockingZornPlus * clockingZornMinus ≠ clockingZornMinus * clockingZornPlus`),
certifying that the carrier algebra is genuinely non-commutative. -/
theorem clockingZorn_noncommutative :
    clockingZornPlus * clockingZornMinus ≠
      clockingZornMinus * clockingZornPlus :=
  zornConePlus_mul_zornConeMinus_ne_comm

/-- Rank-one Peirce cut in the concrete operator algebra `M₂(ℝ)`. -/
def clockingMatrixCut : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- An off-diagonal operator from the complementary sheet to the cut sheet. -/
def clockingMatrixMode : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Equal sheet weights freeze the relative sheet commutator but do not force an independently
chosen Peirce deformation to vanish. The witness is genuinely noncommutative: its mode fails to
commute with the cut, and its positive Peirce block is nonzero. -/
theorem equal_sheet_weights_allow_nonzero_noncommuting_deformation :
    sheetRho (1 : ℝ) 1 clockingMatrixCut = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    genPhi clockingMatrixCut clockingMatrixMode 0 ≠ 0 ∧
    comm clockingMatrixCut (genPhi clockingMatrixCut clockingMatrixMode 0) ≠ 0 ∧
    clockingMatrixCut * clockingMatrixMode ≠ clockingMatrixMode * clockingMatrixCut := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sheetRho, clockingMatrixCut]
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [genPhi, conePlus, coneMinus, clockingMatrixCut, clockingMatrixMode,
      Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Matrix.one_apply, Fin.sum_univ_two] at h01
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [OperatorAlgebra.PeirceSpine.comm, genPhi, conePlus, coneMinus,
      clockingMatrixCut, clockingMatrixMode, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecHead, Matrix.vecTail, Matrix.one_apply, Fin.sum_univ_two] at h01
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [clockingMatrixCut, clockingMatrixMode, Matrix.mul_apply,
      Fin.sum_univ_two] at h01

/-- A vanishing quadratic strain does not force the algebraic resolvent force to vanish.
For this nonzero nilpotent Peirce mode, `V = 0`, the resolvent kernel is `1`, and the
force at `β = 1`, `W = 1` is the nonzero operator `2 • Φ`. Thus a vanishing double
commutator is distinct from vanishing of the first variation force. -/
theorem zero_strain_can_have_nonzero_resolvent_force :
    genV clockingMatrixCut clockingMatrixMode 0 = 0 ∧
    relativeVolumeKernel 1 clockingMatrixCut clockingMatrixMode 0 = 1 ∧
    volumeResolventForce 1 1 clockingMatrixCut clockingMatrixMode 0 =
      (2 : ℝ) • genPhi clockingMatrixCut clockingMatrixMode 0 ∧
    volumeResolventForce 1 1 clockingMatrixCut clockingMatrixMode 0 ≠ 0 := by
  have hV : genV clockingMatrixCut clockingMatrixMode 0 = 0 := by
    simp [genV, anticomm, coneMinus]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hV
  · unfold relativeVolumeKernel
    rw [hV]
    simp
  · simp [volumeResolventForce]
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [volumeResolventForce, genPhi, conePlus, coneMinus,
      clockingMatrixCut, clockingMatrixMode, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecHead, Matrix.vecTail, Matrix.one_apply, Fin.sum_univ_two] at h01

end ConcreteMatrixWitness

end InfoGeometry.Canonical.ModularSurprisalClockingLocksPoset
