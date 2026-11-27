/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.NCG.NoncommutativeDifferentialCalculus
import InfoGeometry.Canonical.CoordinateFreeConnectionChannels
import InfoGeometry.Physics.SolderingSpinConnectionBogoliubov
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge

/-!
# Curved-Heisenberg Lie–Rinehart Geometry, Koszul Connection, and Schwarzschild Dirac Audit

This module formalizes and mathematically audits J. E. Johnson (2025),
*"Riemannian geometry reframed as a generalized lie algebra to integrate general relativity with the
standard model"* (*Gen. Relativ. Gravit.* 57:130), strictly reusing the repository's existing
noncommutative calculus, coordinate-free connection channels, soldering tetrads, and Majorana–Dirac
Clifford infrastructure.

## Audit & Formalization Summary (`Three-Bucket Map`)

### BUCKET 1: PROVED KERNEL THEOREMS
1. **Flat-Collapse Obstruction (`johnson_eq222_eq231_flat_collapse`, `johnson_curved_metric_obstruction_witness`)**:
   Assuming `[D_μ, X^ν] = b · g^{μν}` (Eq. 2.22) together with flat derivative action
   `[D_μ, X^ν] = b · δ_μ^ν` (implicitly used when replacing `∂_α` by `[D_α, ·]/b` in Eqs. 2.31–2.34)
   forces `g^{μν} = δ^{μν}`, excluding non-flat metrics such as Schwarzschild (`f = 1/2`).
2. **Curved First-Order Operator & Lie–Rinehart Bracket (`CurvedHeisenbergOperatorModel`)**:
   Realizing `D^μ(ψ) = b · ∑ α, g^{μα} • PA_α(ψ) + Φ^μ * ψ` via `NCDerivation` recovers exact
   coordinate commutation `[D^μ, L_{X^ν}] = (b · g^{μν}) • id`, annihilates arbitrary scalar/matrix
   connection terms `Φ^μ` in `[D^μ, L_f]`, and splits `[D^μ, D^ν]` cleanly into the 1st-order
   anchor bracket plus `CoordinateFreeConnectionChannels.twoSlotCurvature`.
3. **Repaired Koszul Christoffel & Riemann Curvature (`repaired_koszul_christoffel_from_commutators`)**:
   Using the inverse-metric relation `∂_β = ∑ ρ, g_{βρ} gradOp^ρ`, the genuine torsion-free,
   metric-compatible Levi-Civita connection is recovered from metric-gradient commutators, and
   `riemannCurvatureMatrix` inherits exact antisymmetry from `twoSlotCurvature_swap`.
4. **Schwarzschild Inverse Audit, Unimodular Uncertainty & Curved Dirac Clifford Algebra**:
   Refutes `g₀₀ = g⁰⁰` (`f ≠ f⁻¹` for `0 < f ≠ 1`), proves invariance of the Robertson product
   `(ΔX_r ΔD_r)(Δt ΔE) ≥ (ℏ/2)^2`, verifies `inducedMetric (schwarzschildTetradCov f) = schwarzschildMetricCov f`
   and `det = 1`, proves the covariant and contravariant curved Clifford anticommutators on
   `diracGamma0..3`, and exhibits the signature bug `(!![0, 1; 1, 0] ⊗ₖ σ1)^2 = +1 ≠ -1`.
5. **Orbital Angular Momentum Flat Heisenberg Closure (`orbitalL_flat_heisenberg_comm`)**:
   Under flat `[D_μ, X^ν] = b δ_{μν}`, `L_{μν} = X_μ D_ν - X_ν D_μ` closes into the Lorentz/orthogonal
   Lie bracket with structure factor `b`.

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Coordinate-frame commutativity (`[PC_μ, PC_ν] = 0`, `[PA_μ, PA_ν] = 0`), metric invertibility
  `gCov * gInv = 1`, and symmetry `gCov α β = gCov β α` are explicit hypotheses of
  `CurvedHeisenbergOperatorModel` and the Koszul theorems.

### BUCKET 3: OPEN CLOSURE DEBT
* Unbounded self-adjoint domain issues for position/momentum operators `X_μ, D_μ` on `L²(M, √|g| dⁿx)`,
  analytic power-series convergence of `exp(ds · η_μ D^μ / b)`, and curved spinor-connection covariant
  Bianchi contractions remain outside this finite/algebraic canonical bridge.
-/

noncomputable section

open scoped BigOperators Kronecker
open Matrix
open InfoGeometry.NCG.Calculus
open InfoGeometry.Canonical.CoordinateFreeConnectionChannels (twoSlotCurvature twoSlotCurvature_swap)
open InfoGeometry.Physics.SolderingSpinConnectionBogoliubov
open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge

namespace InfoGeometry.Canonical.JohnsonCurvedHeisenbergRiemannBridge

/-! ### Part 1: Flat-Collapse Obstruction (`Eq. 2.22` vs `Eqs. 2.31–2.34`) -/

section FlatCollapseObstruction

/-- If `D μ` simultaneously satisfies the curved commutator `[D μ, X ν] = b • g μ ν` (`Eq. 2.22`)
and the flat-space derivative rule `[D μ, X ν] = b • δ_{μν}` (assumed when replacing `∂` by
`[D, ·]/b` in `Eqs. 2.31–2.34`), then for nonzero scalar `b`, the metric collapses to `δ_{μν}`. -/
theorem johnson_eq222_eq231_flat_collapse
    {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {n : ℕ}
    (D X : Fin n → A) (g : Fin n → Fin n → A) (b : K) (hb : b ≠ 0)
    (hDX : ∀ μ ν : Fin n, CoordinateFreeConnectionChannels.commutator (D μ) (X ν) = b • g μ ν)
    (hFlat : ∀ μ ν : Fin n,
      CoordinateFreeConnectionChannels.commutator (D μ) (X ν) =
        b • (if μ = ν then (1 : A) else 0)) :
    ∀ μ ν : Fin n, g μ ν = if μ = ν then (1 : A) else 0 := by
  intro μ ν
  have hEq : b • g μ ν = b • (if μ = ν then (1 : A) else 0) := (hDX μ ν).symm.trans (hFlat μ ν)
  have hScaled := congrArg (fun z : A => b⁻¹ • z) hEq
  simpa [smul_smul, inv_mul_cancel₀ hb, one_smul] using hScaled

/-- Concrete Schwarzschild obstruction (`f = 1 / 2`): no pair `(D, X)` can realize both a
non-flat Schwarzschild component (`g⁰⁰ = 2`) and the flat Heisenberg value `δ⁰⁰ = 1`. -/
theorem johnson_curved_metric_obstruction_witness
    (D X : Fin 4 → ℝ) (b : ℝ) (hb : b ≠ 0)
    (hFlat : ∀ μ ν : Fin 4,
      CoordinateFreeConnectionChannels.commutator (D μ) (X ν) =
        b • (if μ = ν then (1 : ℝ) else 0)) :
    CoordinateFreeConnectionChannels.commutator (D 0) (X 0) ≠ b • (2 : ℝ) := by
  intro hCurved
  have h00 := hFlat 0 0
  rw [hCurved] at h00
  have hScaled := congrArg (fun z : ℝ => b⁻¹ * z) h00
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hb, one_mul] at hScaled
  norm_num at hScaled

end FlatCollapseObstruction

/-! ### Part 2: Curved First-Order Operator, Lie–Rinehart Bracket, and Repaired Koszul Connection -/

section CurvedOperatorModel

/-- Algebraic model of Eq. (2.29): a commutative coordinate algebra `C` with coordinate functions
`X μ : C` and commuting Leibniz derivations `PC μ : NCDerivation C` extended to an associative
`C`-algebra `A` (`PA μ : NCDerivation A`).  `algebraMap C A f` is automatically central in `A`,
modelling multiplication by functions of position `X`. -/
structure CurvedHeisenbergOperatorModel (C A : Type*) [CommRing C] [Ring A] [Algebra C A] (n : ℕ) where
  PC : Fin n → NCDerivation C
  PA : Fin n → NCDerivation A
  X : Fin n → C
  PC_comm : ∀ μ ν : Fin n, ∀ f : C, PC μ (PC ν f) = PC ν (PC μ f)
  PA_comm : ∀ μ ν : Fin n, ∀ ψ : A, PA μ (PA ν ψ) = PA ν (PA μ ψ)
  PC_X : ∀ μ ν : Fin n, PC μ (X ν) = if μ = ν then 1 else 0
  PA_alg : ∀ μ : Fin n, ∀ f : C, PA μ (algebraMap C A f) = algebraMap C A (PC μ f)

variable {C A : Type*} [CommRing C] [Ring A] [Algebra C A] {n : ℕ}

/-- Johnson's curved translation / momentum differential operator with vector/spin connection `Φ`:
`D^μ(ψ) = b • ∑ α, g^{μα} • PA_α(ψ) + Φ_μ * ψ` (`Eq. 2.29`). -/
def curvedDiffOp (M : CurvedHeisenbergOperatorModel C A n)
    (b : C) (g : Fin n → Fin n → C) (Φ : Fin n → A) (μ : Fin n) (ψ : A) : A :=
  b • (∑ α : Fin n, g μ α • M.PA α ψ) + Φ μ * ψ

/-- Exact commutator with left multiplication by any coordinate function `f : C`:
`[D^μ, L_f](ψ) = (b * ∑ α, g^{μα} ∂_α f) • ψ`.  Any vector/matrix potential `Φ` cancels! -/
theorem curvedDiffOp_comm_mulOp (M : CurvedHeisenbergOperatorModel C A n)
    (b : C) (g : Fin n → Fin n → C) (Φ : Fin n → A) (μ : Fin n) (f : C) (ψ : A) :
    curvedDiffOp M b g Φ μ (algebraMap C A f * ψ) -
        algebraMap C A f * curvedDiffOp M b g Φ μ ψ =
      (b * ∑ α : Fin n, g μ α * M.PC α f) • ψ := by
  have hLeib : ∀ α : Fin n,
      M.PA α (algebraMap C A f * ψ) =
        algebraMap C A (M.PC α f) * ψ + algebraMap C A f * M.PA α ψ := by
    intro α
    rw [(M.PA α).leibniz, M.PA_alg]
  have hComm : ∀ x : A, algebraMap C A f * x = x * algebraMap C A f := Algebra.commutes f
  have hPhi : Φ μ * (algebraMap C A f * ψ) - algebraMap C A f * (Φ μ * ψ) = 0 := by
    rw [hComm (Φ μ * ψ), mul_assoc, hComm ψ, sub_self]
  unfold curvedDiffOp
  simp_rw [hLeib, smul_add]
  rw [Finset.sum_add_distrib, smul_add, mul_add]
  have hMovePhi :
      b • (∑ α : Fin n, g μ α • (algebraMap C A (M.PC α f) * ψ)) +
        b • (∑ α : Fin n, g μ α • (algebraMap C A f * M.PA α ψ)) +
        Φ μ * (algebraMap C A f * ψ) -
      (algebraMap C A f * (b • (∑ α : Fin n, g μ α • M.PA α ψ)) +
        algebraMap C A f * (Φ μ * ψ)) =
      b • (∑ α : Fin n, g μ α • (algebraMap C A (M.PC α f) * ψ)) +
        (b • (∑ α : Fin n, g μ α • (algebraMap C A f * M.PA α ψ)) -
          algebraMap C A f * (b • (∑ α : Fin n, g μ α • M.PA α ψ))) +
        (Φ μ * (algebraMap C A f * ψ) - algebraMap C A f * (Φ μ * ψ)) := by
    abel
  rw [hMovePhi, hPhi, add_zero]
  have hSecond :
      b • (∑ α : Fin n, g μ α • (algebraMap C A f * M.PA α ψ)) -
        algebraMap C A f * (b • (∑ α : Fin n, g μ α • M.PA α ψ)) = 0 := by
    have hEq :
        b • (∑ α : Fin n, g μ α • (algebraMap C A f * M.PA α ψ)) =
          algebraMap C A f * (b • (∑ α : Fin n, g μ α • M.PA α ψ)) := by
      simp_rw [Algebra.smul_def, Finset.mul_sum, ← mul_assoc]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [← map_mul]
      rw [mul_comm (b * g μ α) f]
      simp only [map_mul, mul_assoc]
    rw [hEq, sub_self]
  rw [hSecond, add_zero]
  rw [Finset.smul_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [smul_smul, Algebra.smul_def, Algebra.smul_def]
  simp only [map_mul, mul_assoc]

/-- Exact `Eq. (2.22)` / `Eq. (2.29)` recovery:
`[D^μ, L_{X ν}](ψ) = (b * g^{μν}) • ψ`. -/
theorem curvedDiffOp_comm_coord (M : CurvedHeisenbergOperatorModel C A n)
    (b : C) (g : Fin n → Fin n → C) (Φ : Fin n → A) (μ ν : Fin n) (ψ : A) :
    curvedDiffOp M b g Φ μ (algebraMap C A (M.X ν) * ψ) -
        algebraMap C A (M.X ν) * curvedDiffOp M b g Φ μ ψ =
      (b * g μ ν) • ψ := by
  rw [curvedDiffOp_comm_mulOp]
  congr 1
  rw [show (∑ α : Fin n, g μ α * M.PC α (M.X ν)) = g μ ν by
    simp [M.PC_X]]

private lemma PA_const_smul (M : CurvedHeisenbergOperatorModel C A n)
    (c : C) (α : Fin n) (hc : M.PC α c = 0) (z : A) :
    M.PA α (c • z) = c • M.PA α z := by
  rw [Algebra.smul_def, (M.PA α).leibniz, M.PA_alg, hc, map_zero, zero_mul, zero_add,
    ← Algebra.smul_def]

private lemma PA_var_smul (M : CurvedHeisenbergOperatorModel C A n)
    (c : C) (α : Fin n) (z : A) :
    M.PA α (c • z) = M.PC α c • z + c • M.PA α z := by
  rw [Algebra.smul_def, (M.PA α).leibniz, M.PA_alg, ← Algebra.smul_def, ← Algebra.smul_def]

/-- Exact Lie–Rinehart / gauge-curvature identity for `[D^μ, D^ν](ψ)`:
when `b` is constant (`PC α b = 0`), the 2nd-order terms cancel via `[PA_α, PA_β] = 0`, leaving
the 1st-order metric-anchor bracket plus `twoSlotCurvature` of the potential `Φ`. -/
theorem curvedDiffOp_comm_curvedDiffOp (M : CurvedHeisenbergOperatorModel C A n)
    (b : C) (hb : ∀ α : Fin n, M.PC α b = 0)
    (g : Fin n → Fin n → C) (Φ : Fin n → A) (μ ν : Fin n) (ψ : A) :
    curvedDiffOp M b g Φ μ (curvedDiffOp M b g Φ ν ψ) -
        curvedDiffOp M b g Φ ν (curvedDiffOp M b g Φ μ ψ) =
      (b ^ 2) • (∑ β : Fin n,
          (∑ α : Fin n, (g μ α * M.PC α (g ν β) - g ν α * M.PC α (g μ β))) • M.PA β ψ) +
        twoSlotCurvature
          (b • ∑ α : Fin n, g μ α • M.PA α (Φ ν))
          (b • ∑ α : Fin n, g ν α • M.PA α (Φ μ))
          (Φ μ) (Φ ν) * ψ := by
  have hPAsum : ∀ (α : Fin n) (s : Finset (Fin n)) (fn : Fin n → A),
      M.PA α (∑ β ∈ s, fn β) = ∑ β ∈ s, M.PA α (fn β) :=
    fun α s fn => _root_.map_sum (M.PA α).toLinearMap fn s
  have hExpand : ∀ μ' ν' : Fin n,
      curvedDiffOp M b g Φ μ' (curvedDiffOp M b g Φ ν' ψ) =
        (b ^ 2) • (∑ α : Fin n, ∑ β : Fin n,
            (g μ' α * M.PC α (g ν' β)) • M.PA β ψ) +
          (b ^ 2) • (∑ α : Fin n, ∑ β : Fin n,
            (g μ' α * g ν' β) • M.PA α (M.PA β ψ)) +
          (b • ∑ α : Fin n, g μ' α • M.PA α (Φ ν')) * ψ +
          Φ ν' * (b • ∑ α : Fin n, g μ' α • M.PA α ψ) +
          Φ μ' * (b • ∑ β : Fin n, g ν' β • M.PA β ψ) +
          (Φ μ' * Φ ν') * ψ := by
    intro μ' ν'
    unfold curvedDiffOp
    simp_rw [NCDerivation.map_add, PA_const_smul M b _ (hb _), hPAsum, PA_var_smul M _ _ _]
    have hPhiTerm : ∀ α : Fin n, M.PA α (Φ ν' * ψ) = M.PA α (Φ ν') * ψ + Φ ν' * M.PA α ψ :=
      fun α => (M.PA α).leibniz (Φ ν') ψ
    simp_rw [hPhiTerm, smul_add, Finset.sum_add_distrib, smul_add, Finset.sum_add_distrib]
    have hS1 :
        b • ∑ α : Fin n, g μ' α • (b • ∑ β : Fin n, M.PC α (g ν' β) • M.PA β ψ) =
          (b ^ 2) • ∑ α : Fin n, ∑ β : Fin n, (g μ' α * M.PC α (g ν' β)) • M.PA β ψ := by
      simp_rw [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      congr 1; ring
    have hS2 :
        b • ∑ α : Fin n, g μ' α • (b • ∑ β : Fin n, g ν' β • M.PA α (M.PA β ψ)) =
          (b ^ 2) • ∑ α : Fin n, ∑ β : Fin n, (g μ' α * g ν' β) • M.PA α (M.PA β ψ) := by
      simp_rw [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      congr 1; ring
    have hS3 :
        b • ∑ α : Fin n, g μ' α • (M.PA α (Φ ν') * ψ) =
          (b • ∑ α : Fin n, g μ' α • M.PA α (Φ ν')) * ψ := by
      rw [Finset.smul_sum, smul_mul_assoc, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [smul_mul_assoc]
    have hS4 :
        b • ∑ α : Fin n, g μ' α • (Φ ν' * M.PA α ψ) =
          Φ ν' * (b • ∑ α : Fin n, g μ' α • M.PA α ψ) := by
      simp_rw [Algebra.smul_def, Finset.mul_sum, ← mul_assoc]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← map_mul, Algebra.commutes (b * g μ' α) (Φ ν')]
      simp only [map_mul, mul_assoc]
    rw [smul_add, hS1, hS2, hS3, hS4, mul_add]
    simp only [mul_assoc]
    abel
  have hSecondSym :
      (b ^ 2) • (∑ α : Fin n, ∑ β : Fin n, (g μ α * g ν β) • M.PA α (M.PA β ψ)) =
        (b ^ 2) • (∑ α : Fin n, ∑ β : Fin n, (g ν α * g μ β) • M.PA α (M.PA β ψ)) := by
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [M.PA_comm α β ψ, mul_comm (g μ α) (g ν β)]
  rw [hExpand μ ν, hExpand ν μ, hSecondSym]
  have hAnchor :
      (b ^ 2) • (∑ α : Fin n, ∑ β : Fin n, (g μ α * M.PC α (g ν β)) • M.PA β ψ) -
        (b ^ 2) • (∑ α : Fin n, ∑ β : Fin n, (g ν α * M.PC α (g μ β)) • M.PA β ψ) =
      (b ^ 2) • (∑ β : Fin n,
          (∑ α : Fin n, (g μ α * M.PC α (g ν β) - g ν α * M.PC α (g μ β))) • M.PA β ψ) := by
    rw [← smul_sub]
    congr 1
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun α β => (g ν α * M.PC α (g μ β)) • M.PA β ψ), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [Finset.sum_smul, ← sub_smul]
  unfold twoSlotCurvature CoordinateFreeConnectionChannels.commutator
  simp only [sub_mul, add_mul, mul_assoc]
  rw [← hAnchor]
  abel

end CurvedOperatorModel

/-! ### Part 3: Repaired Koszul Christoffel & Riemann Curvature from Metric-Gradient Commutators -/

section RepairedKoszul

variable {C : Type*} [CommRing C] {n : ℕ}

/-- The metric-raised gradient derivation `gradOp^μ(f) := ∑ α, g^{μα} ∂_α f`, equal to `(1/b)[D^μ, L_f]`. -/
def gradOp (gInv : Fin n → Fin n → C) (PC : Fin n → NCDerivation C) (μ : Fin n) (f : C) : C :=
  ∑ α : Fin n, gInv μ α * PC α f

/-- Recovering coordinate partial derivatives `∂_μ` from curved commutators `gradOp`:
`∂_μ f = ∑ ρ, g_{μρ} gradOp^ρ(f)`. -/
theorem coordDeriv_eq_metric_gradOp
    (gInv gCov : Fin n → Fin n → C) (PC : Fin n → NCDerivation C)
    (hgInv : ∀ μ ν : Fin n, ∑ ρ : Fin n, gCov μ ρ * gInv ρ ν = if μ = ν then 1 else 0)
    (μ : Fin n) (f : C) :
    PC μ f = ∑ ρ : Fin n, gCov μ ρ * gradOp gInv PC ρ f := by
  unfold gradOp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hCollapse : ∀ α : Fin n,
      ∑ ρ : Fin n, gCov μ ρ * (gInv ρ α * PC α f) = (if μ = α then (1 : C) else 0) * PC α f := by
    intro α
    simp_rw [← mul_assoc, ← Finset.sum_mul, hgInv μ α]
  simp_rw [hCollapse]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

variable [Algebra ℝ C]

/-- Genuine Levi-Civita Christoffel symbol `Γ^γ_{αβ}` defined from coordinate derivations `PC`. -/
def christoffel (gInv gCov : Fin n → Fin n → C) (PC : Fin n → NCDerivation C)
    (γ α β : Fin n) : C :=
  (1 / 2 : ℝ) • ∑ σ : Fin n,
    gInv γ σ * (PC β (gCov σ α) + PC α (gCov σ β) - PC σ (gCov α β))

/-- Repaired commutator formula for `Γ^γ_{αβ}` expressing `∂_β = ∑ ρ, g_{βρ} gradOp^ρ` so that
every derivative is written purely in terms of metric-gradient commutators `gradOp`. -/
def repairedCommutatorChristoffel (gInv gCov : Fin n → Fin n → C) (PC : Fin n → NCDerivation C)
    (γ α β : Fin n) : C :=
  (1 / 2 : ℝ) • (∑ σ : Fin n,
      gInv γ σ *
        (∑ ρ : Fin n, gCov β ρ * gradOp gInv PC ρ (gCov σ α) +
         ∑ ρ : Fin n, gCov α ρ * gradOp gInv PC ρ (gCov σ β)) -
      gradOp gInv PC γ (gCov α β))

/-- **Repaired Koszul Connection Theorem (`Eqs. 2.31–2.34` corrected)**:
when `gCov * gInv = 1`, `repairedCommutatorChristoffel` agrees identically with the genuine
Levi-Civita `christoffel` symbol, is torsion-free (`Γ^γ_{αβ} = Γ^γ_{βα}`), and is
metric-compatible (`∂_γ g_{αβ} = ∑ σ, Γ^σ_{γα} g_{σβ} + ∑ σ, Γ^σ_{γβ} g_{ασ}`). -/
theorem repaired_koszul_christoffel_from_commutators
    (gInv gCov : Fin n → Fin n → C) (PC : Fin n → NCDerivation C)
    (hgSym : ∀ α β : Fin n, gCov α β = gCov β α)
    (hgInv : ∀ μ ν : Fin n, ∑ ρ : Fin n, gCov μ ρ * gInv ρ ν = if μ = ν then 1 else 0) :
    (∀ γ α β : Fin n,
      repairedCommutatorChristoffel gInv gCov PC γ α β = christoffel gInv gCov PC γ α β) ∧
    (∀ γ α β : Fin n,
      christoffel gInv gCov PC γ α β = christoffel gInv gCov PC γ β α) ∧
    (∀ γ α β : Fin n,
      PC γ (gCov α β) =
        ∑ σ : Fin n, christoffel gInv gCov PC σ γ α * gCov σ β +
        ∑ σ : Fin n, christoffel gInv gCov PC σ γ β * gCov α σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ α β
    unfold repairedCommutatorChristoffel christoffel
    congr 1
    simp_rw [← coordDeriv_eq_metric_gradOp gInv gCov PC hgInv]
    unfold gradOp
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  · intro γ α β
    unfold christoffel
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hgSym α β, add_comm (PC β (gCov σ α))]
  · intro γ α β
    have hHalfSum : ∀ a b : Fin n,
        ∑ σ : Fin n, christoffel gInv gCov PC σ γ a * gCov σ b =
          (1 / 2 : ℝ) • (PC γ (gCov b a) + PC a (gCov b γ) - PC b (gCov γ a)) := by
      intro a b
      unfold christoffel
      simp_rw [smul_mul_assoc]
      rw [← Finset.smul_sum]
      congr 1
      have hSwap :
          ∑ σ : Fin n,
              (∑ τ : Fin n, gInv σ τ * (PC a (gCov τ γ) + PC γ (gCov τ a) - PC τ (gCov γ a))) *
                gCov σ b =
            ∑ τ : Fin n,
              (∑ σ : Fin n, gCov b σ * gInv σ τ) *
                (PC a (gCov τ γ) + PC γ (gCov τ a) - PC τ (gCov γ a)) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hgSym σ b]
        ring
      rw [hSwap]
      simp_rw [hgInv b _]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [add_comm (PC a (gCov b γ)) (PC γ (gCov b a))]
    have hSymSwap : ∀ σ : Fin n,
        christoffel gInv gCov PC σ γ β * gCov α σ =
          christoffel gInv gCov PC σ γ β * gCov σ α := fun σ => by rw [hgSym α σ]
    simp_rw [hSymSwap]
    rw [hHalfSum α β, hHalfSum β α, ← smul_add]
    have hInner :
        (PC γ (gCov β α) + PC α (gCov β γ) - PC β (gCov γ α)) +
          (PC γ (gCov α β) + PC β (gCov α γ) - PC α (gCov γ β)) =
        (2 : ℝ) • PC γ (gCov α β) := by
      rw [hgSym β α, hgSym β γ, hgSym α γ, hgSym γ α, hgSym γ β, two_smul]
      abel
    rw [hInner, smul_smul]
    norm_num

/-- Coordinate Riemann endomorphism matrix `(R_{βγ})^λ_α` assembled via `twoSlotCurvature`
applied to the Christoffel connection matrices `(Γ_β)^λ_α := christoffel gInv gCov PC λ β α`. -/
def riemannCurvatureMatrix (gInv gCov : Fin n → Fin n → C) (PC : Fin n → NCDerivation C)
    (β γ : Fin n) : Matrix (Fin n) (Fin n) C :=
  let Γ : Fin n → Matrix (Fin n) (Fin n) C := fun μ =>
    Matrix.of fun l α => christoffel gInv gCov PC l μ α
  twoSlotCurvature ((Γ γ).map (PC β)) ((Γ β).map (PC γ)) (Γ β) (Γ γ)

/-- Exact Riemann curvature antisymmetry `R_{γβ} = -R_{βγ}` inherited directly from
`CoordinateFreeConnectionChannels.twoSlotCurvature_swap`. -/
theorem riemannCurvatureMatrix_antisymm
    (gInv gCov : Fin n → Fin n → C) (PC : Fin n → NCDerivation C) (β γ : Fin n) :
    riemannCurvatureMatrix gInv gCov PC γ β = -riemannCurvatureMatrix gInv gCov PC β γ := by
  exact twoSlotCurvature_swap _ _ _ _

end RepairedKoszul

/-! ### Part 3: Schwarzschild Metric Inverse Audit & Unimodular Robertson Uncertainty Product -/

section SchwarzschildAudit

/-- Covariant Schwarzschild radial-time metric `diag(f, -f⁻¹, -1, -1)` (`Eq. 3.5`). -/
def schwarzschildMetricCov (f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![f, -f⁻¹, -1, -1]

/-- Contravariant Schwarzschild inverse metric `diag(f⁻¹, -f, -1, -1)`. -/
def schwarzschildMetricInv (f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![f⁻¹, -f, -1, -1]

theorem schwarzschildMetricCov_mul_inv {f : ℝ} (hf : f ≠ 0) :
    schwarzschildMetricCov f * schwarzschildMetricInv f = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [schwarzschildMetricCov, schwarzschildMetricInv, mul_inv_cancel₀ hf, inv_mul_cancel₀ hf]

/-- Audit of p. 11 (`g_{00} = g^{00}`, `g_{11} = g^{11}`): for every nontrivial Schwarzschild factor
`0 < f ≠ 1`, the covariant and contravariant `(0,0)` and `(1,1)` entries are strictly unequal. -/
theorem schwarzschild_cov_ne_inv_audit {f : ℝ} (hf0 : 0 < f) (hf1 : f ≠ 1) :
    schwarzschildMetricCov f 0 0 ≠ schwarzschildMetricInv f 0 0 ∧
    schwarzschildMetricCov f 1 1 ≠ schwarzschildMetricInv f 1 1 := by
  have hff : f ≠ f⁻¹ := by
    intro h
    have hsq : f ^ 2 = 1 := by
      calc f ^ 2 = f * f := by ring
        _ = f * f⁻¹ := by conv_rhs => rw [← h]
        _ = 1 := mul_inv_cancel₀ hf0.ne'
    have hCases : f = 1 ∨ f = -1 := sq_eq_one_iff.mp hsq
    rcases hCases with rfl | hneg
    · exact hf1 rfl
    · linarith
  constructor
  · simpa [schwarzschildMetricCov, schwarzschildMetricInv] using hff
  · intro h
    simp [schwarzschildMetricCov, schwarzschildMetricInv] at h
    exact hff h.symm

/-- **Unimodular Radial-Time Uncertainty Theorem (`Eqs. 3.6–3.7`)**:
because `|g₀₀ · g₁₁| = |g⁰⁰ · g¹¹| = 1`, the multiplied Schwarzschild uncertainty bound
`(ΔX_r ΔD_r)(Δt ΔE) ≥ (ℏ/2)^2` holds identically under either covariant or contravariant
normalization for any `f > 0`. -/
theorem schwarzschild_unimodular_uncertainty_product
    {f ℏ ΔXr ΔDr Δt ΔE : ℝ} (hf : 0 < f) (hℏ : 0 ≤ ℏ)
    (hXr : (ℏ / 2) * |schwarzschildMetricCov f 1 1| ≤ ΔXr * ΔDr)
    (ht : (ℏ / 2) * |schwarzschildMetricCov f 0 0| ≤ Δt * ΔE) :
    |schwarzschildMetricCov f 0 0 * schwarzschildMetricCov f 1 1| = 1 ∧
    |schwarzschildMetricInv f 0 0 * schwarzschildMetricInv f 1 1| = 1 ∧
    (ℏ / 2) ^ 2 ≤ (ΔXr * ΔDr) * (Δt * ΔE) := by
  have h1 : |schwarzschildMetricCov f 0 0 * schwarzschildMetricCov f 1 1| = 1 := by
    simp [schwarzschildMetricCov, mul_inv_cancel₀ hf.ne']
  have h2 : |schwarzschildMetricInv f 0 0 * schwarzschildMetricInv f 1 1| = 1 := by
    simp [schwarzschildMetricInv, inv_mul_cancel₀ hf.ne']
  have hNonneg1 : 0 ≤ (ℏ / 2) * |schwarzschildMetricCov f 1 1| :=
    mul_nonneg (by positivity) (abs_nonneg _)
  have hNonneg2 : 0 ≤ (ℏ / 2) * |schwarzschildMetricCov f 0 0| :=
    mul_nonneg (by positivity) (abs_nonneg _)
  have hProd : ((ℏ / 2) * |schwarzschildMetricCov f 1 1|) *
      ((ℏ / 2) * |schwarzschildMetricCov f 0 0|) ≤ (ΔXr * ΔDr) * (Δt * ΔE) :=
    mul_le_mul hXr ht hNonneg2 (le_trans hNonneg1 hXr)
  have hEq : ((ℏ / 2) * |schwarzschildMetricCov f 1 1|) *
      ((ℏ / 2) * |schwarzschildMetricCov f 0 0|) = (ℏ / 2) ^ 2 := by
    calc ((ℏ / 2) * |schwarzschildMetricCov f 1 1|) * ((ℏ / 2) * |schwarzschildMetricCov f 0 0|)
        = (ℏ / 2) ^ 2 * |schwarzschildMetricCov f 0 0 * schwarzschildMetricCov f 1 1| := by
          rw [abs_mul]; ring
      _ = (ℏ / 2) ^ 2 := by rw [h1, mul_one]
  exact ⟨h1, h2, hEq ▸ hProd⟩

end SchwarzschildAudit

/-! ### Part 4: Schwarzschild Unimodular Tetrad & Curved Dirac Clifford Relations (`Eq. 3.8`) -/

section SchwarzschildTetradDirac

/-- Unimodular Schwarzschild covariant diagonal tetrad `diag(√f, (√f)⁻¹, 1, 1)` reusing `tetradDiag`. -/
def schwarzschildTetradCov (f : ℝ) : M4R :=
  tetradDiag (Real.sqrt f) (Real.sqrt f)⁻¹ 1 1

/-- Unimodular Schwarzschild contravariant inverse tetrad `diag((√f)⁻¹, √f, 1, 1)`. -/
def schwarzschildTetradInv (f : ℝ) : M4R :=
  tetradDiag (Real.sqrt f)⁻¹ (Real.sqrt f) 1 1

/-- Reusing `SolderingSpinConnectionBogoliubov.inducedMetric_diag`, `schwarzschildTetradCov f`
has `det = 1`, is inverse to `schwarzschildTetradInv f`, and induces `schwarzschildMetricCov f`. -/
theorem schwarzschild_tetrad_inducedMetric {f : ℝ} (hf : 0 < f) :
    inducedMetric (schwarzschildTetradCov f) = schwarzschildMetricCov f ∧
    inducedMetric (schwarzschildTetradInv f) = schwarzschildMetricInv f ∧
    (schwarzschildTetradCov f).det = 1 ∧
    schwarzschildTetradCov f * schwarzschildTetradInv f = 1 := by
  have hSqrt : Real.sqrt f ^ 2 = f := Real.sq_sqrt hf.le
  have hSqrtInv : (Real.sqrt f)⁻¹ ^ 2 = f⁻¹ := by rw [inv_pow, hSqrt]
  have hSqrtNe : Real.sqrt f ≠ 0 := (Real.sqrt_pos.mpr hf).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold schwarzschildTetradCov schwarzschildMetricCov
    rw [inducedMetric_diag, hSqrt, hSqrtInv]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · unfold schwarzschildTetradInv schwarzschildMetricInv
    rw [inducedMetric_diag, hSqrt, hSqrtInv]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · unfold schwarzschildTetradCov tetradDiag
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_four, mul_inv_cancel₀ hSqrtNe]
  · unfold schwarzschildTetradCov schwarzschildTetradInv tetradDiag
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_inv_cancel₀ hSqrtNe, inv_mul_cancel₀ hSqrtNe]

/-- Curved real Majorana–Dirac matrices `Γ_μ(f)` in `M₄(ℝ)` built on `diracGamma0..3` with
tetrad weights `(√f, (√f)⁻¹, 1, 1)`. -/
def schwarzschildRealGammaCov (f : ℝ) : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ
  | 0 => Real.sqrt f • diracGamma0
  | 1 => (Real.sqrt f)⁻¹ • diracGamma1
  | 2 => diracGamma2
  | 3 => diracGamma3

/-- Contravariant curved real Majorana–Dirac matrices `Γ^μ(f)` with inverse weights `((√f)⁻¹, √f, 1, 1)`. -/
def schwarzschildRealGammaInv (f : ℝ) : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ
  | 0 => (Real.sqrt f)⁻¹ • diracGamma0
  | 1 => Real.sqrt f • diracGamma1
  | 2 => diracGamma2
  | 3 => diracGamma3

/-- Curved complex Dirac matrices `γ_μ(f) = i · Γ_μ(f)` with Lorentzian `(+, -, -, -)` metric. -/
def schwarzschildComplexGammaCov (f : ℝ) (μ : Fin 4) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Complex.I • (schwarzschildRealGammaCov f μ).map Complex.ofReal

/-- Contravariant curved complex Dirac matrices `γ^μ(f) = i · Γ^μ(f)`. -/
def schwarzschildComplexGammaInv (f : ℝ) (μ : Fin 4) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Complex.I • (schwarzschildRealGammaInv f μ).map Complex.ofReal

/-- **Repaired Eq. (3.8) — Covariant & Contravariant Curved Clifford Anticommutators**:
for every `0 < f` and all `μ ν : Fin 4`:
- real Majorana–Dirac: `Γ_μ Γ_ν + Γ_ν Γ_μ = (-2 g_{μν}) • 1` (and `Inv` with `g^{μν}`);
- complex Dirac `(+, -, -, -)`: `γ_μ γ_ν + γ_ν γ_μ = (2 g_{μν}) • 1` (and `Inv` with `g^{μν}`). -/
theorem schwarzschild_dirac_clifford_relations {f : ℝ} (hf : 0 < f) :
    (∀ μ ν : Fin 4,
      schwarzschildRealGammaCov f μ * schwarzschildRealGammaCov f ν +
        schwarzschildRealGammaCov f ν * schwarzschildRealGammaCov f μ =
      (-2 * schwarzschildMetricCov f μ ν) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (∀ μ ν : Fin 4,
      schwarzschildRealGammaInv f μ * schwarzschildRealGammaInv f ν +
        schwarzschildRealGammaInv f ν * schwarzschildRealGammaInv f μ =
      (-2 * schwarzschildMetricInv f μ ν) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (∀ μ ν : Fin 4,
      schwarzschildComplexGammaCov f μ * schwarzschildComplexGammaCov f ν +
        schwarzschildComplexGammaCov f ν * schwarzschildComplexGammaCov f μ =
      ((2 * schwarzschildMetricCov f μ ν : ℝ) : ℂ) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) ∧
    (∀ μ ν : Fin 4,
      schwarzschildComplexGammaInv f μ * schwarzschildComplexGammaInv f ν +
        schwarzschildComplexGammaInv f ν * schwarzschildComplexGammaInv f μ =
      ((2 * schwarzschildMetricInv f μ ν : ℝ) : ℂ) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by
  have hC := diracGamma_clifford_relations
  have hSqrt : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf.le
  have hSqrtInv : (Real.sqrt f)⁻¹ * (Real.sqrt f)⁻¹ = f⁻¹ := by
    rw [← mul_inv, hSqrt]
  have hSqrtNe : Real.sqrt f ≠ 0 := (Real.sqrt_pos.mpr hf).ne'
  have h10 : diracGamma1 * diracGamma0 + diracGamma0 * diracGamma1 = 0 := by
    rw [add_comm]; exact hC.2.2.2.2.1
  have h20 : diracGamma2 * diracGamma0 + diracGamma0 * diracGamma2 = 0 := by
    rw [add_comm]; exact hC.2.2.2.2.2.1
  have h30 : diracGamma3 * diracGamma0 + diracGamma0 * diracGamma3 = 0 := by
    rw [add_comm]; exact hC.2.2.2.2.2.2.1
  have h21 : diracGamma2 * diracGamma1 + diracGamma1 * diracGamma2 = 0 := by
    rw [add_comm]; exact hC.2.2.2.2.2.2.2.1
  have h31 : diracGamma3 * diracGamma1 + diracGamma1 * diracGamma3 = 0 := by
    rw [add_comm]; exact hC.2.2.2.2.2.2.2.2.1
  have h32 : diracGamma3 * diracGamma2 + diracGamma2 * diracGamma3 = 0 := by
    rw [add_comm]; exact hC.2.2.2.2.2.2.2.2.2
  have hRealCov : ∀ μ ν : Fin 4,
      schwarzschildRealGammaCov f μ * schwarzschildRealGammaCov f ν +
        schwarzschildRealGammaCov f ν * schwarzschildRealGammaCov f μ =
      (-2 * schwarzschildMetricCov f μ ν) • 1 := by
    intro μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [schwarzschildRealGammaCov, schwarzschildMetricCov,
        smul_smul, mul_inv_cancel₀ hSqrtNe, inv_mul_cancel₀ hSqrtNe, one_smul,
        hSqrt, hSqrtInv, ← smul_add, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1,
        hC.2.2.2.2.1, hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1,
        hC.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2,
        h10, h20, h30, h21, h31, h32, ← two_smul ℝ]
  have hRealInv : ∀ μ ν : Fin 4,
      schwarzschildRealGammaInv f μ * schwarzschildRealGammaInv f ν +
        schwarzschildRealGammaInv f ν * schwarzschildRealGammaInv f μ =
      (-2 * schwarzschildMetricInv f μ ν) • 1 := by
    intro μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [schwarzschildRealGammaInv, schwarzschildMetricInv,
        smul_smul, mul_inv_cancel₀ hSqrtNe, inv_mul_cancel₀ hSqrtNe, one_smul,
        hSqrt, hSqrtInv, ← smul_add, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1,
        hC.2.2.2.2.1, hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1,
        hC.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2,
        h10, h20, h30, h21, h31, h32, ← two_smul ℝ]
  have hLift : ∀ (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (c : ℝ),
      A * B + B * A = (-2 * c) • 1 →
      (Complex.I • A.map Complex.ofReal) * (Complex.I • B.map Complex.ofReal) +
        (Complex.I • B.map Complex.ofReal) * (Complex.I • A.map Complex.ofReal) =
      ((2 * c : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    intro A B c hAB
    have hMap : (A.map Complex.ofReal) * (B.map Complex.ofReal) +
        (B.map Complex.ofReal) * (A.map Complex.ofReal) =
        (((-2 * c : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) := by
      have hM := congrArg (fun M => M.map Complex.ofReal) hAB
      ext i j
      have hij := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M i j) hM
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul] at hij ⊢
      push_cast at hij ⊢
      simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero] at hij
      exact hij
    rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_smul, ← smul_add, hMap, smul_smul, Complex.I_mul_I]
    congr 1
    push_cast
    ring
  refine ⟨hRealCov, hRealInv, ?_, ?_⟩
  · intro μ ν
    exact hLift _ _ _ (hRealCov μ ν)
  · intro μ ν
    exact hLift _ _ _ (hRealInv μ ν)

/-- **Signature Audit of p. 11 `γ¹`**: Johnson writes `γ¹ = !![0, σ₁; σ₁, 0]` (`!![0, 1; 1, 0] ⊗ₖ σ1`),
which squares to `+1 ≠ -1` (turning signature `(+, -, -, -)` into `(+, +, -, -)`).  Replacing the
outer symmetric block by `!![0, 1; -1, 0]` restores `γ₁² = -1`. -/
theorem johnson_printed_gamma1_signature_bug :
    let gamma1Printed : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := !![0, 1; 1, 0] ⊗ₖ σ1
    let gamma1Fixed : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := !![0, 1; -1, 0] ⊗ₖ σ1
    gamma1Printed * gamma1Printed = (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
    gamma1Printed * gamma1Printed ≠ -(1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
    gamma1Fixed * gamma1Fixed = -(1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  have hSwap2 : (!![(0 : ℂ), 1; 1, 0] * !![(0 : ℂ), 1; 1, 0]) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hSkew2 : (!![(0 : ℂ), 1; -1, 0] * !![(0 : ℂ), 1; -1, 0]) = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hSig1 : σ1 * σ1 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]
  have hPrint : (!![(0 : ℂ), 1; 1, 0] ⊗ₖ σ1) * (!![(0 : ℂ), 1; 1, 0] ⊗ₖ σ1) =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    rw [← Matrix.mul_kronecker_mul, hSwap2, hSig1, Matrix.one_kronecker_one]
  refine ⟨hPrint, ?_, ?_⟩
  · intro hNeg
    rw [hNeg] at hPrint
    have h00 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M (0, 0) (0, 0)) hPrint
    simp at h00
    norm_num at h00
  · rw [← Matrix.mul_kronecker_mul, hSkew2, hSig1]
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases j₁ <;> fin_cases i₂ <;> fin_cases j₂ <;>
      simp [Matrix.kroneckerMap_apply]

end SchwarzschildTetradDirac

/-! ### Part 5: Orbital Angular Momentum `L_{μν}` (`Eq. 2.41`) -/

section OrbitalAngularMomentum

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A] {n : ℕ}

/-- Corrected antisymmetric orbital generator `L_{μν} = X_μ D_ν - X_ν D_μ` (fixing `Eq. 2.41`
typo `X_μ D_ν - X_ν D_ν`). -/
def orbitalL (X D : Fin n → A) (μ ν : Fin n) : A :=
  X μ * D ν - X ν * D μ

theorem orbitalL_skew (X D : Fin n → A) (μ ν : Fin n) :
    orbitalL X D ν μ = -orbitalL X D μ ν := by
  unfold orbitalL
  noncomm_ring

private lemma assoc_comm_prod_sub (a b c : A) :
    CoordinateFreeConnectionChannels.commutator (a * b) c =
      a * CoordinateFreeConnectionChannels.commutator b c +
        CoordinateFreeConnectionChannels.commutator a c * b := by
  unfold CoordinateFreeConnectionChannels.commutator
  noncomm_ring

/-- In the flat Heisenberg limit `[X_μ, X_ν] = 0`, `[D_μ, D_ν] = 0`, `[D_μ, X_ν] = b • δ_{μν}`,
the corrected orbital generators `L_{μν}` form the closed Lie algebra of infinitesimal rotations
with structure constant `b`. -/
theorem orbitalL_flat_heisenberg_comm (X D : Fin n → A) (b : R)
    (hXX : ∀ μ ν : Fin n, CoordinateFreeConnectionChannels.commutator (X μ) (X ν) = 0)
    (hDD : ∀ μ ν : Fin n, CoordinateFreeConnectionChannels.commutator (D μ) (D ν) = 0)
    (hDX : ∀ μ ν : Fin n,
      CoordinateFreeConnectionChannels.commutator (D μ) (X ν) =
        b • (if μ = ν then (1 : A) else 0))
    (μ ν ρ σ : Fin n) :
    CoordinateFreeConnectionChannels.commutator (orbitalL X D μ ν) (orbitalL X D ρ σ) =
      b • ((if ν = ρ then orbitalL X D μ σ else 0) -
           (if μ = ρ then orbitalL X D ν σ else 0) -
           (if ν = σ then orbitalL X D μ ρ else 0) +
           (if μ = σ then orbitalL X D ν ρ else 0)) := by
  have hXD : ∀ i j : Fin n,
      CoordinateFreeConnectionChannels.commutator (X i) (D j) =
        -(b • (if j = i then (1 : A) else 0)) := by
    intro i j
    calc CoordinateFreeConnectionChannels.commutator (X i) (D j)
        = -CoordinateFreeConnectionChannels.commutator (D j) (X i) := by
          unfold CoordinateFreeConnectionChannels.commutator; noncomm_ring
      _ = -(b • (if j = i then (1 : A) else 0)) := by rw [hDX j i]
  have hTerm : ∀ a c d e : Fin n,
      CoordinateFreeConnectionChannels.commutator (X a * D c) (X d * D e) =
        b • ((if c = d then X a * D e else 0) - (if e = a then X d * D c else 0)) := by
    intro a c d e
    have hXac : X a * X d = X d * X a := sub_eq_zero.mp (hXX a d)
    have hDce : D c * D e = D e * D c := sub_eq_zero.mp (hDD c e)
    calc CoordinateFreeConnectionChannels.commutator (X a * D c) (X d * D e)
        = (X a * D c) * (X d * D e) - (X d * D e) * (X a * D c) := rfl
      _ = X a * (CoordinateFreeConnectionChannels.commutator (D c) (X d)) * D e +
            X d * (CoordinateFreeConnectionChannels.commutator (X a) (D e)) * D c +
            (X a * X d) * (D c * D e) - (X d * X a) * (D e * D c) := by
          unfold CoordinateFreeConnectionChannels.commutator; noncomm_ring
      _ = X a * (b • (if c = d then (1 : A) else 0)) * D e +
            X d * (-(b • (if e = a then (1 : A) else 0))) * D c := by
          rw [hDX c d, hXD a e, hXac, hDce]; noncomm_ring
      _ = b • ((if c = d then X a * D e else 0) - (if e = a then X d * D c else 0)) := by
          split_ifs <;> simp [sub_eq_add_neg, smul_add, smul_neg]
  unfold orbitalL
  have hBilin :
      CoordinateFreeConnectionChannels.commutator (X μ * D ν - X ν * D μ) (X ρ * D σ - X σ * D ρ) =
        CoordinateFreeConnectionChannels.commutator (X μ * D ν) (X ρ * D σ) -
          CoordinateFreeConnectionChannels.commutator (X μ * D ν) (X σ * D ρ) -
          CoordinateFreeConnectionChannels.commutator (X ν * D μ) (X ρ * D σ) +
          CoordinateFreeConnectionChannels.commutator (X ν * D μ) (X σ * D ρ) := by
    unfold CoordinateFreeConnectionChannels.commutator; noncomm_ring
  rw [hBilin, hTerm μ ν ρ σ, hTerm μ ν σ ρ, hTerm ν μ ρ σ, hTerm ν μ σ ρ]
  simp only [← smul_sub, ← smul_add]
  congr 1
  by_cases h1 : ν = ρ <;> by_cases h2 : μ = ρ <;> by_cases h3 : ν = σ <;>
    by_cases h4 : μ = σ <;> by_cases h5 : ρ = σ <;>
    simp [h1, h2, h3, h4, h5, eq_comm] <;> (try abel)

end OrbitalAngularMomentum

/-- Closed `4 × 4` real matrix non-commutativity witness complementing `schwarzschildMetricCov`. -/
theorem johnson_mat4r_noncomm :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 0 1, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne] at h00

end InfoGeometry.Canonical.JohnsonCurvedHeisenbergRiemannBridge
