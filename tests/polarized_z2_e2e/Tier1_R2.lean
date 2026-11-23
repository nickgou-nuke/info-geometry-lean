/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lean.Util.CollectAxioms
import Lean.Elab.Command
import InfoGeometry.Canonical.CurvedZ2GradedDGA
import InfoGeometry.Canonical.PeirceBoundaryComplex
import InfoGeometry.Algebra.GradedNullconeAlgebra

set_option autoImplicit false

/-!
# E2E Tier 1 (R2): Curved Z/2-Graded Differential Algebra (Features F6–F8)

Opaque-box feature verification for Requirement R2 across Features F6–F8:
* F6: `CurvedZ2GradedDGA` structure, graded Leibniz rule, `∂_F² = [h, ·]`, Bianchi
  `∂_F(h) = 0`, parity switching, `ofPeirce` / `ofParityConj` / `toCochainComplex` bridges.
* F7: Exhaustive `CurvatureRegime` trichotomy and concrete witnesses across all three regimes
  (`flatMat2DGA`, `centralMat2DGA`, `centralDoubledDGA`, `nonCentralBlockDGA`, `nonCentralMat4DGA`).
* F8: Algebraic separation of `∂_F` from ungraded inner commutator derivations
  `commutatorDeriv G` (and `PR #426` scope), plus `nilpotent_commutatorDeriv_sq_ne_zero`.
-/

namespace PolarizedZ2E2E.Tier1R2

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory
open InfoGeometry.Canonical.CurvedZ2GradedDGA
open InfoGeometry.Canonical.PeirceBoundaryComplex
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

/-! ## Feature F6: Curved Z/2-Graded DGA Core Laws & Bridges -/

theorem t1_f6_curved_dga_core_identities
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : CurvedZ2GradedDGA R A) (x y : A) :
    D.diff (x * y) = D.diff x * y + D.parity x * D.diff y ∧
    D.diff ^ 2 = LieAlgebra.ad R A D.curvature ∧
    D.diff D.curvature = 0 ∧
    D.IsEven D.curvature :=
  ⟨D.diff_mul x y, D.diff_sq, D.bianchi, D.curvature_isEven⟩

theorem t1_f6_parity_flip_and_center_iff
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : CurvedZ2GradedDGA R A) (x : A) :
    D.parity (D.diff x) = -D.diff (D.parity x) ∧
    (D.IsEven x → D.IsOdd (D.diff x)) ∧
    (D.IsOdd x → D.IsEven (D.diff x)) ∧
    (D.diff ^ 2 = 0 ↔ D.curvature ∈ Subalgebra.center R A) :=
  ⟨D.parity_diff x, fun hx => D.diff_isOdd_of_isEven hx,
    fun hx => D.diff_isEven_of_isOdd hx, D.diff_sq_eq_zero_iff_mem_center⟩

theorem t1_f6_ofPeirce_matches_boundary_complex
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ LinearMap.range (odd p)) :
    (CurvedZ2GradedDGA.ofPeirce (R := R) hp hu).diff =
      differential (R := R) p u ∧
    (CurvedZ2GradedDGA.ofPeirce (R := R) hp hu).curvature = u * u ∧
    (∀ x : A, (CurvedZ2GradedDGA.ofPeirce (R := R) hp hu).parity x =
      parityConj (reflection p) x) := by
  have hbridge := CurvedZ2GradedDGA.ofPeirce_eq_ofParityConj_reflection (R := R) hp hu
  refine ⟨CurvedZ2GradedDGA.ofPeirce_diff_eq (R := R) hp hu, rfl, ?_⟩
  intro x
  exact hbridge.2.1 x

theorem t1_f6_flat_toCochainComplex_matches_cornerComplex
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {p u : A} (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) (i : ℕ) :
    ((ofPeirce10 (R := R) hp hu).toCochainComplex (ofPeirce10_isFlat hp hu)).d i (i + 1) =
      (cornerComplex (R := R) hp hu).d i (i + 1) ∧
    ((ofPeirce10 (R := R) hp hu).toCochainComplex (ofPeirce10_isFlat hp hu)).X i =
      ModuleCat.of R A :=
  ⟨ofPeirce10_toCochainComplex_d_eq_cornerComplex_d hp hu i, rfl⟩

theorem t1_f6_diff_anticommutator_shared_parity
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D₁ D₂ : CurvedZ2GradedDGA R A) (hα : D₁.parity = D₂.parity) (x : A) :
    (D₁.diff * D₂.diff + D₂.diff * D₁.diff) x =
      (D₁.oddGen * D₂.oddGen + D₂.oddGen * D₁.oddGen) * x -
        x * (D₁.oddGen * D₂.oddGen + D₂.oddGen * D₁.oddGen) := by
  have hanti := CurvedZ2GradedDGA.diff_anticommutator D₁ D₂ hα
  exact congrArg (fun f : Module.End R A => f x) hanti

/-! ## Feature F7: Three Curvature Regimes & Concrete Witnesses -/

theorem t1_f7_regime_trichotomy_exhaustive {A : Type*} [Ring A] (h : A) :
    (IsFlatRegime h ∨ IsCentralNonzeroRegime h ∨ IsNonCentralRegime h) ∧
    (classifyRegime h = .flat ↔ IsFlatRegime h) ∧
    (classifyRegime h = .centralNonzero ↔ IsCentralNonzeroRegime h) ∧
    (classifyRegime h = .nonCentral ↔ IsNonCentralRegime h) :=
  ⟨(curvatureRegime_trichotomy h).1,
    classifyRegime_eq_flat_iff h,
    classifyRegime_eq_centralNonzero_iff h,
    classifyRegime_eq_nonCentral_iff h⟩

theorem t1_f7_flat_regime_witness_mat2 :
    flatMat2DGA.curvature = 0 ∧
    classifyRegime flatMat2DGA.curvature = .flat ∧
    flatMat2DGA.diff ^ 2 = 0 ∧
    flatMat2DGA.diff ≠ 0 ∧
    flatMat2DGA.diff atomPos2 = 1 :=
  ⟨flatMat2DGA_curvature_eq_zero,
    flatMat2DGA_classifyRegime,
    flatMat2DGA_diff_sq,
    flatMat2DGA_diff_ne_zero,
    flatMat2DGA_diff_atomPos2⟩

theorem t1_f7_central_nonzero_witness_mat2 :
    centralMat2DGA.curvature = 1 ∧
    IsCentralNonzeroRegime centralMat2DGA.curvature ∧
    classifyRegime centralMat2DGA.curvature = .centralNonzero ∧
    centralMat2DGA.diff ^ 2 = 0 ∧
    centralMat2DGA.diff ≠ 0 :=
  ⟨centralMat2DGA_curvature_eq_one,
    centralMat2DGA_isCentralNonzero,
    centralMat2DGA_classifyRegime,
    centralMat2DGA_diff_sq,
    centralMat2DGA_diff_ne_zero⟩

theorem t1_f7_central_nonzero_witness_doubled :
    let E := EuclideanSpace ℝ (Fin 2)
    (centralDoubledDGA E).curvature = 1 ∧
    IsCentralNonzeroRegime (centralDoubledDGA E).curvature ∧
    classifyRegime (centralDoubledDGA E).curvature = .centralNonzero ∧
    (centralDoubledDGA E).diff ^ 2 = 0 ∧
    (centralDoubledDGA E).diff ≠ 0 := by
  dsimp only
  refine ⟨centralDoubledDGA_curvature_eq_one,
    centralDoubledDGA_isCentralNonzero,
    centralDoubledDGA_classifyRegime,
    centralDoubledDGA_diff_sq,
    centralDoubledDGA_diff_ne_zero⟩

theorem t1_f7_noncentral_witness_mat4_and_block :
    (IsNonCentralRegime nonCentralBlockDGA.curvature ∧
      classifyRegime nonCentralBlockDGA.curvature = .nonCentral ∧
      nonCentralBlockDGA.diff ^ 2 ≠ 0 ∧
      nonCentralBlockDGA.diff nonCentralBlockDGA.curvature = 0) ∧
    (IsNonCentralRegime nonCentralMat4DGA.curvature ∧
      classifyRegime nonCentralMat4DGA.curvature = .nonCentral ∧
      nonCentralMat4DGA.diff ^ 2 ≠ 0 ∧
      nonCentralMat4DGA.diff nonCentralMat4DGA.curvature = 0) :=
  ⟨⟨nonCentralBlockDGA_isNonCentral,
      nonCentralBlockDGA_classifyRegime,
      nonCentralBlockDGA_diff_sq_ne_zero,
      nonCentralBlockDGA_bianchi⟩,
    ⟨nonCentralMat4DGA_isNonCentral,
      nonCentralMat4DGA_classifyRegime,
      nonCentralMat4DGA_diff_sq_ne_zero,
      nonCentralMat4DGA_bianchi⟩⟩

/-! ## Feature F8: Separation from Commutator Derivations & PR #426 -/

theorem t1_f8_commutator_vs_curved_leibniz
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : CurvedZ2GradedDGA R A) :
    (∀ x y : A, commutatorDeriv (R := R) D.oddGen (x * y) =
      commutatorDeriv (R := R) D.oddGen x * y + x * commutatorDeriv (R := R) D.oddGen y) ∧
    (∀ x y : A, D.diff (x * y) = D.diff x * y + D.parity x * D.diff y) ∧
    (∀ G : A, D.diff = commutatorDeriv (R := R) G →
      ∀ x y : A, (x - D.parity x) * D.diff y = 0) ∧
    ((∃ x : A, D.parity x ≠ x) → (∃ y : A, IsUnit (D.diff y)) →
      ∀ G : A, D.diff ≠ commutatorDeriv (R := R) G) :=
  commutatorDeriv_vs_curvedDiff D

theorem t1_f8_pointwise_discrepancy_even_vs_odd
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : CurvedZ2GradedDGA R A) (x : A) :
    (D.IsEven x → D.diff x = commutatorDeriv (R := R) D.oddGen x) ∧
    (D.IsOdd x → D.diff x - commutatorDeriv (R := R) D.oddGen x = (2 : R) • (x * D.oddGen)) :=
  ⟨fun hx => curvedDiff_eq_commutatorDeriv_of_even D hx,
    fun hx => curvedDiff_sub_commutatorDeriv_of_odd D hx⟩

theorem t1_f8_flat_and_central_mat2_ne_all_commutators
    (H : Matrix (Fin 2) (Fin 2) ℝ) :
    flatMat2DGA.diff ≠ commutatorDeriv (R := ℝ) H ∧
    centralMat2DGA.diff ≠ commutatorDeriv (R := ℝ) H :=
  ⟨flatMat2DGA_diff_ne_commutatorDeriv H, centralMat2DGA_diff_ne_commutatorDeriv H⟩

theorem t1_f8_doubled_ne_all_commutators
    (H : EndH₂ (E := EuclideanSpace ℝ (Fin 2))) :
    (centralDoubledDGA (EuclideanSpace ℝ (Fin 2))).diff ≠ commutatorDeriv (R := ℝ) H :=
  centralDoubledDGA_diff_ne_commutatorDeriv H

theorem t1_f8_nilpotent_commutator_sq_ne_zero :
    atomNeg2 * atomNeg2 = 0 ∧
    (commutatorDeriv (R := ℝ) atomNeg2) ^ 2 ≠ 0 ∧
    flatMat2DGA.diff ^ 2 = 0 ∧
    flatMat2DGA.diff (atomPos2 * !![1, 0; 0, 0]) ≠
      commutatorDeriv (R := ℝ) atomNeg2 (atomPos2 * !![1, 0; 0, 0]) := by
  have h := nilpotent_commutatorDeriv_sq_ne_zero
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end PolarizedZ2E2E.Tier1R2

section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
