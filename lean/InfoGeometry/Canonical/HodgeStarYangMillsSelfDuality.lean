/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HodgeStarSignatureFour
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge
import InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
import InfoGeometry.Canonical.GradedConnectionBianchiBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeStarYangMillsSelfDuality

open ExteriorAlgebra
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
open InfoGeometry.Canonical.GradedConnectionBianchiBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Algebra.HodgeStarSignatureFour
open InfoGeometry.MetaCompiler
open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Fintype V] {n : ℕ}

/- **Hodge star axioms stated explicitly as premises.**
- `star_sq_law`: `star.comp star = s • id` where `s * s = 1`
  (square/sign law; `s = 1` Euclidean, `s = -1` Lorentzian).
- `star_degree_reversal`: `star` maps homogeneous `k`-forms to homogeneous
  `(card V - k)`-forms.
These are premises, not derived facts; no concrete metric/orientation is
asserted.
-/
structure HodgeStarAxioms where
  star : Module.End R (ExteriorAlgebra R V)
  s : R
  hs_sq : s * s = 1
  star_sq_law : star.comp star = (s : R) • LinearMap.id
  star_degree_reversal :
    ∀ {k : ℕ} {x : ExteriorAlgebra R V},
      IsHomogeneousExteriorDegree k x →
      IsHomogeneousExteriorDegree (Fintype.card V - k) (star x)

/-- Self-dual instanton solves vacuum Yang–Mills `D_A (★ F_A) = 0` from Bianchi
`D_A F_A = 0`, assuming only the Hodge star endomorphism and the explicit
self-duality condition `★ F = F`. No product-rule premise is bundled. -/
theorem self_dual_instanton_from_bianchi
    (H : HodgeStarAxioms)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_self_dual : isSelfDualCurvature H.star F)
    (h_bianchi : covariantDerivative A d F = 0) :
    covariantDerivative A d (matrixHodgeStar H.star F) = 0 := by
  exact self_dual_solves_yang_mills H.star A d F h_self_dual h_bianchi

/-- Anti-self-dual instanton solves vacuum Yang–Mills `D_A (★ F_A) = 0` from
Bianchi `D_A F_A = 0`, assuming only the Hodge star endomorphism and the explicit
anti-self-duality condition `★ F = -F`. -/
theorem anti_self_dual_instanton_from_bianchi
    (H : HodgeStarAxioms)
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (d : Module.End R (ExteriorAlgebra R V))
    (F : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (h_anti_self_dual : isAntiSelfDualCurvature H.star F)
    (h_bianchi : covariantDerivative A d F = 0) :
    covariantDerivative A d (matrixHodgeStar H.star F) = 0 := by
  have h_cov_neg : covariantDerivative A d (-F) = - covariantDerivative A d F := by
    dsimp [covariantDerivative, matrixCommutator]
    ext i j
    dsimp [matrixExteriorDerivative, Matrix.mul_apply]
    rw [LinearMap.map_neg]
    simp_rw [mul_neg, neg_mul, Finset.sum_neg_distrib]
    noncomm_ring
  exact anti_self_dual_solves_yang_mills H.star A d F h_anti_self_dual h_cov_neg h_bianchi

/-! ### Phase 1 & 2 Synthesis: Unconditional Instanton Solutions from Graded Bianchi -/

/-- Unconditional Self-Dual Yang-Mills Field Equation Solution `D_A (★ F_A) = 0`
from structural Bianchi `D_A F_A = 0` (derived strictly from `D.sq_zero`, graded 1-form
Leibniz rule, and `|A|=1`) without primitive Bianchi or product-rule assumptions. -/
theorem self_dual_connection_curvature_solves_graded_yang_mills
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V] [Fintype V] {n : ℕ}
    (D : ExteriorDifferentialData R V)
    (H : HodgeStarAxioms (R := R) (V := V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A)
    (h_self_dual : isSelfDualCurvature H.star (curvatureFromConnection D.d A)) :
    covariantDerivative A D.d (matrixHodgeStar H.star (curvatureFromConnection D.d A)) = 0 := by
  have h_bianchi := graded_connection_curvature_bianchi D A hA
  exact self_dual_instanton_from_bianchi H A D.d (curvatureFromConnection D.d A) h_self_dual h_bianchi

/-- Unconditional Anti-Self-Dual Yang-Mills Field Equation Solution `D_A (★ F_A) = 0`
from structural Bianchi `D_A F_A = 0` without primitive Bianchi or product-rule assumptions. -/
theorem anti_self_dual_connection_curvature_solves_graded_yang_mills
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V] [Fintype V] {n : ℕ}
    (D : ExteriorDifferentialData R V)
    (H : HodgeStarAxioms (R := R) (V := V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A)
    (h_anti_self_dual : isAntiSelfDualCurvature H.star (curvatureFromConnection D.d A)) :
    covariantDerivative A D.d (matrixHodgeStar H.star (curvatureFromConnection D.d A)) = 0 := by
  have h_bianchi := graded_connection_curvature_bianchi D A hA
  exact anti_self_dual_instanton_from_bianchi H A D.d (curvatureFromConnection D.d A) h_anti_self_dual h_bianchi

/-! ### Phase 1 & 2 Synthesis: Unconditional Instanton Solutions from Graded Bianchi -/

/-- Master Graded Connection Curvature & Hodge Duality Synthesis.
Unifies:
1. Structural Bianchi `D_A F_A = 0` from `D.sq_zero` and graded Leibniz;
2. Unconditional self-dual instanton implication `D_A (★ F_A) = 0`;
3. Unconditional anti-self-dual instanton implication `D_A (★ F_A) = 0`. -/
theorem master_graded_connection_hodge_duality_synthesis
    {R V : Type*} [Field R] [AddCommGroup V] [Module R V] [Fintype V] {n : ℕ}
    (D : ExteriorDifferentialData R V)
    (H : HodgeStarAxioms (R := R) (V := V))
    (A : Matrix (Fin n) (Fin n) (ExteriorAlgebra R V))
    (hA : InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge.MatrixIsHomogeneous 1 A) :
    (covariantDerivative A D.d (curvatureFromConnection D.d A) = 0) ∧
    (isSelfDualCurvature H.star (curvatureFromConnection D.d A) →
      covariantDerivative A D.d (matrixHodgeStar H.star (curvatureFromConnection D.d A)) = 0) ∧
    (isAntiSelfDualCurvature H.star (curvatureFromConnection D.d A) →
      covariantDerivative A D.d (matrixHodgeStar H.star (curvatureFromConnection D.d A)) = 0) := ⟨
  graded_connection_curvature_bianchi D A hA,
  self_dual_connection_curvature_solves_graded_yang_mills D H A hA,
  anti_self_dual_connection_curvature_solves_graded_yang_mills D H A hA
⟩

/-! ### Duality Order: Peirce Parity vs Spacetime Hodge Duality -/

/-- Theorem: Spacetime Hodge star on 2-forms produces an idempotent Peirce decomposition
on Euclidean 4-space, while on Lorentzian 4-space its square is `-1`. -/
theorem euclidean_vs_lorentzian_hodge_square_duality
    {k : Type*} [CommRing k] [Invertible (2 : k)] :
    (projSelfDual (R := k) * projSelfDual (R := k) = projSelfDual) ∧
    (projAntiSelfDual (R := k) * projAntiSelfDual (R := k) = projAntiSelfDual) ∧
    (projSelfDual (R := k) + projAntiSelfDual (R := k) = 1) ∧
    (hodgeLorentz (R := k) * hodgeLorentz (R := k) = -(1 : Matrix (Fin 6) (Fin 6) k)) := ⟨
  projSelfDual_sq,
  projAntiSelfDual_sq,
  projSelfDual_add_projAntiSelfDual,
  hodgeLorentz_sq
⟩

end InfoGeometry.Canonical.HodgeStarYangMillsSelfDuality
