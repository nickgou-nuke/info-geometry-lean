/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral
import InfoGeometry.Thermo.OnsagerOperatorClosure

/-!
# Unified Onsager Formalism on Operator Differential Forms

This synthesis module formalizes the unified framework connecting:
1. Operator-Valued 1-Forms and 2-Forms (`Op1Form`, `Op2Form`) via `OperatorExteriorAlgebra`.
2. The Noncommutative Wedge Product and Gauge Curvature: `(α ∧ α)(u, v) = [α(u), α(v)]`.
3. Derivations acting on Forms via the Graded Leibniz Rule: `D(α ∧ β) = (D α) ∧ β + α ∧ (D β)`.
4. The Onsager–Metriplectic Decomposition: `W = L + Ω` where `L` is symmetric (dissipative)
   and `Ω` is an alternating 2-form (reversible/Hamiltonian).
5. Exact Dissipation Isolation: `W(u, u) = L(u, u)`.
6. Onsager–Casimir Reciprocity under Time-Reversal Involutions.

Compatibility status: `TransportTensor` and `TimeReversal` here are retained as
deprecated compatibility wrappers for downstream callers and bridged losslessly to
the canonical owners `InfoGeometry.OperatorAlgebra.General.TransportTensor` and
`InfoGeometry.Thermo.OnsagerClosure.TimeReversal` / `OnsagerCasimirSystem`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.OnsagerNCG

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

section Part1

variable {R V A : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [Ring A] [Algebra R A]

/-!
=============================================================================
PART 1: Onsager–Metriplectic Operator Decomposition on Forms
=============================================================================
-/

/-- Deprecated compatibility wrapper for `InfoGeometry.OperatorAlgebra.General.TransportTensor`:
an `R`-bilinear transport tensor on `V` with values in `A`: `W(u, v)`.
Prefer `InfoGeometry.OperatorAlgebra.General.TransportTensor` for new code;
convert losslessly via `TransportTensor.equivGeneral`. -/
structure TransportTensor (R V A : Type*) [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] where
  toBilin : V →ₗ[R] V →ₗ[R] A

instance : CoeFun (TransportTensor R V A) (fun _ => V → V → A) where
  coe W u v := W.toBilin u v

namespace TransportTensor

variable (W : TransportTensor R V A)

@[simp]
theorem map_zero_left (v : V) : W 0 v = 0 := by
  have h := W.toBilin.map_zero
  exact congr_fun (congr_arg DFunLike.coe h) v

@[simp]
theorem map_zero_right (u : V) : W u 0 = 0 :=
  (W.toBilin u).map_zero

@[simp]
theorem map_add_left (u₁ u₂ v : V) : W (u₁ + u₂) v = W u₁ v + W u₂ v := by
  have h := W.toBilin.map_add u₁ u₂
  exact congr_fun (congr_arg DFunLike.coe h) v

@[simp]
theorem map_add_right (u v₁ v₂ : V) : W u (v₁ + v₂) = W u v₁ + W u v₂ :=
  (W.toBilin u).map_add v₁ v₂

@[simp]
theorem map_smul_left (c : R) (u v : V) : W (c • u) v = c • W u v := by
  have h := W.toBilin.map_smul c u
  exact congr_fun (congr_arg DFunLike.coe h) v

@[simp]
theorem map_smul_right (c : R) (u v : V) : W u (c • v) = c • W u v :=
  (W.toBilin u).map_smul c v

/-- The Symmetric Dissipative Tensor: L(u, v) = (1/2) • (W(u, v) + W(v, u)). -/
def symmPart (half : R) (W : TransportTensor R V A) : V → V → A :=
  fun u v => half • (W u v + W v u)

/-- The Alternating Reversible 2-Form: Ω(u, v) = (1/2) • (W(u, v) - W(v, u)). -/
def altPart (half : R) (W : TransportTensor R V A) : Op2Form R V A where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => half • (W.toBilin u v - W.toBilin v u)
      map_add' := by
        intro v₁ v₂
        rw [(W.toBilin u).map_add v₁ v₂]
        rw [W.toBilin.map_add v₁ v₂, LinearMap.add_apply]
        have h_alg : ((W.toBilin u) v₁ + (W.toBilin u) v₂) - ((W.toBilin v₁) u + (W.toBilin v₂) u) =
          ((W.toBilin u) v₁ - (W.toBilin v₁) u) + ((W.toBilin u) v₂ - (W.toBilin v₂) u) := by abel
        rw [h_alg, smul_add]
      map_smul' := by
        intro c v
        rw [(W.toBilin u).map_smul c v]
        rw [W.toBilin.map_smul c v, LinearMap.smul_apply]
        rw [← smul_sub, smul_comm, RingHom.id_apply]
    }
    map_add' := by
      intro u₁ u₂
      ext v
      dsimp
      rw [W.toBilin.map_add u₁ u₂, LinearMap.add_apply]
      rw [(W.toBilin v).map_add u₁ u₂]
      have h_alg : ((W.toBilin u₁) v + (W.toBilin u₂) v) - ((W.toBilin v) u₁ + (W.toBilin v) u₂) =
        ((W.toBilin u₁) v - (W.toBilin v) u₁) + ((W.toBilin u₂) v - (W.toBilin v) u₂) := by abel
      rw [h_alg, smul_add]
    map_smul' := by
      intro c u
      ext v
      dsimp
      rw [W.toBilin.map_smul c u, LinearMap.smul_apply]
      rw [(W.toBilin v).map_smul c u]
      rw [← smul_sub, smul_comm]
  }
  alt' := by
    intro v
    dsimp
    rw [sub_self, smul_zero]

@[simp]
theorem symmPart_apply (half : R) (u v : V) :
    W.symmPart half u v = half • (W u v + W v u) := rfl

@[simp]
theorem altPart_apply (half : R) (u v : V) :
    (W.altPart half) u v = half • (W u v - W v u) := rfl

/-- 
  THEOREM 1 (Exact Metriplectic / Onsager Decomposition):
  W(u, v) = L(u, v) + Ω(u, v)
  Splits transport into symmetric dissipative and 2-form Hamiltonian dynamics.
-/
theorem onsager_metriplectic_decomposition
    (half : R) (h_half : (2 : R) * half = 1)
    (W : TransportTensor R V A) (u v : V) :
    W u v = W.symmPart half u v + (W.altPart half) u v := by
  simp only [symmPart_apply, altPart_apply]
  rw [← smul_add]
  have h_add : (W u v + W v u) + (W u v - W v u) = (2 : R) • (W u v) := by
    calc
      (W u v + W v u) + (W u v - W v u) = (W u v + W u v) + (W v u - W v u) := by abel
      _ = (2 : R) • (W u v) + 0 := by rw [two_smul, sub_self]
      _ = (2 : R) • (W u v) := by rw [add_zero]
  rw [h_add, smul_smul]
  have h_norm : half * 2 = 1 := by rw [mul_comm, h_half]
  rw [h_norm, one_smul]

/-- 
  THEOREM 2 (Exact Dissipation Isolation / Diagonal Degeneracy):
  W(u, u) = L(u, u)
  The alternating 2-form drops out identically on the diagonal, proving that
  entropy production is governed purely by the symmetric dissipative metric.
-/
theorem dissipation_eq_symmetric
    (half : R) (h_half : (2 : R) * half = 1)
    (W : TransportTensor R V A) (u : V) :
    W u u = W.symmPart half u u := by
  have h_decomp := W.onsager_metriplectic_decomposition half h_half u u
  rw [(W.altPart half).alt u, add_zero] at h_decomp
  exact h_decomp

section TransportTensorBridge

/-- Lossless conversion from the compatibility wrapper `OnsagerNCG.TransportTensor`
to the canonical `InfoGeometry.OperatorAlgebra.General.TransportTensor`. -/
def toGeneral (W : TransportTensor R V A) :
    InfoGeometry.OperatorAlgebra.General.TransportTensor R V A where
  toFun u v := W.toBilin u v
  map_add_left' u₁ u₂ v := W.map_add_left u₁ u₂ v
  map_add_right' u v₁ v₂ := W.map_add_right u v₁ v₂
  map_smul_left' c u v := W.map_smul_left c u v
  map_smul_right' c u v := W.map_smul_right c u v

/-- Lossless conversion from the canonical `InfoGeometry.OperatorAlgebra.General.TransportTensor`
to the compatibility wrapper `OnsagerNCG.TransportTensor`. -/
def ofGeneral (W : InfoGeometry.OperatorAlgebra.General.TransportTensor R V A) :
    TransportTensor R V A where
  toBilin :=
    { toFun := fun u =>
        { toFun := fun v => W.toFun u v
          map_add' := W.map_add_right' u
          map_smul' := fun c v => W.map_smul_right' c u v }
      map_add' := fun u₁ u₂ => by
        ext v
        exact W.map_add_left' u₁ u₂ v
      map_smul' := fun c u => by
        ext v
        exact W.map_smul_left' c u v }

@[simp]
theorem toGeneral_apply (W : TransportTensor R V A) (u v : V) :
    W.toGeneral u v = W u v :=
  rfl

@[simp]
theorem ofGeneral_apply (W : InfoGeometry.OperatorAlgebra.General.TransportTensor R V A) (u v : V) :
    (ofGeneral W) u v = W u v :=
  rfl

/-- Canonical equivalence between `OnsagerNCG.TransportTensor` and
`InfoGeometry.OperatorAlgebra.General.TransportTensor`. -/
def equivGeneral :
    TransportTensor R V A ≃ InfoGeometry.OperatorAlgebra.General.TransportTensor R V A where
  toFun := toGeneral
  invFun := ofGeneral
  left_inv W := by
    cases W
    rfl
  right_inv W := by
    cases W
    rfl

theorem toGeneral_symmPart (half : R) (W : TransportTensor R V A) (u v : V) :
    W.toGeneral.symmPart half u v = W.symmPart half u v :=
  rfl

theorem toGeneral_altPart (half : R) (W : TransportTensor R V A) (u v : V) :
    W.toGeneral.altPart half u v = (W.altPart half) u v :=
  rfl

theorem ofGeneral_symmPart (half : R)
    (W : InfoGeometry.OperatorAlgebra.General.TransportTensor R V A) (u v : V) :
    (ofGeneral W).symmPart half u v = W.symmPart half u v :=
  rfl

theorem ofGeneral_altPart (half : R)
    (W : InfoGeometry.OperatorAlgebra.General.TransportTensor R V A) (u v : V) :
    ((ofGeneral W).altPart half) u v = W.altPart half u v :=
  rfl

end TransportTensorBridge

end TransportTensor

end Part1

/-!
=============================================================================
PART 2: Onsager–Casimir Reciprocity under Time-Reversal Involutions
=============================================================================
-/

/-- Deprecated compatibility wrapper for `InfoGeometry.Thermo.OnsagerClosure.TimeReversal`
(generalized to an arbitrary ring `R` with `CoeFun`): a linear involution `T² = id`.
When `R = ℝ`, prefer `InfoGeometry.Thermo.OnsagerClosure.TimeReversal`;
convert losslessly via `TimeReversal.equivClosure`. -/
structure TimeReversal (R V : Type*) [Ring R] [AddCommGroup V] [Module R V] where
  toLinearMap : V →ₗ[R] V
  involutive' : toLinearMap.comp toLinearMap = LinearMap.id

instance {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] :
    CoeFun (TimeReversal R V) (fun _ => V → V) where
  coe T := T.toLinearMap

namespace TimeReversal

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable (T : TimeReversal R V)

@[simp]
theorem involutive (v : V) : T (T v) = v := by
  have h := congr_fun (congr_arg DFunLike.coe T.involutive') v
  exact h

end TimeReversal

/-- 
  THEOREM 3 (Onsager–Casimir Reciprocal Relations):
  For a time-even transport tensor where L(Tu, Tv) = L(v, u) and Ω(Tu, Tv) = - Ω(v, u),
  the full tensor satisfies time-reversal transpose reciprocity:
    W(Tu, Tv) = L(v, u) - Ω(v, u).
-/
theorem onsager_casimir_reciprocity
    {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A]
    (half : R) (h_half : (2 : R) * half = 1)
    (W : TransportTensor R V A)
    (T : TimeReversal R V)
    (u v : V)
    (hL : W.symmPart half (T u) (T v) = W.symmPart half v u)
    (hOmega : (W.altPart half) (T u) (T v) = - (W.altPart half) v u) :
    W (T u) (T v) = W.symmPart half v u + - (W.altPart half) v u := by
  have h_decomp := W.onsager_metriplectic_decomposition half h_half (T u) (T v)
  rw [hL, hOmega] at h_decomp
  exact h_decomp

section TimeReversalAndClosureBridge

theorem onsager_casimir_reciprocity_via_general
    {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A]
    (half : R) (h_half : (2 : R) * half = 1)
    (W : TransportTensor R V A) (T : TimeReversal R V) (u v : V)
    (hL : W.symmPart half (T u) (T v) = W.symmPart half u v)
    (hOmega : (W.altPart half) (T u) (T v) = - (W.altPart half) u v) :
    W (T u) (T v) = W v u :=
  W.toGeneral.onsager_casimir_reciprocity_exact half h_half T.toLinearMap u v hL hOmega

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Lossless conversion from `OnsagerNCG.TimeReversal ℝ V` to canonical
`InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V`. -/
def TimeReversal.toClosure (T : TimeReversal ℝ V) :
    InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V where
  op := T.toLinearMap
  involutive := T.involutive

/-- Lossless conversion from canonical
`InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V`
to `OnsagerNCG.TimeReversal ℝ V`. -/
def TimeReversal.ofClosure
    (T : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V) :
    TimeReversal ℝ V where
  toLinearMap := T.op
  involutive' := LinearMap.ext T.involutive

@[simp]
theorem TimeReversal.toClosure_op (T : TimeReversal ℝ V) (v : V) :
    T.toClosure.op v = T v :=
  rfl

@[simp]
theorem TimeReversal.ofClosure_apply
    (T : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V) (v : V) :
    (TimeReversal.ofClosure T) v = T.op v :=
  rfl

/-- Canonical equivalence between `OnsagerNCG.TimeReversal ℝ V` and
`InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V`. -/
def TimeReversal.equivClosure :
    TimeReversal ℝ V ≃ InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal V where
  toFun := TimeReversal.toClosure
  invFun := TimeReversal.ofClosure
  left_inv T := by cases T; rfl
  right_inv T := by cases T; rfl

/-- Embed any canonical `OnsagerClosure.OnsagerCasimirSystem V` into the
compatibility wrapper `OnsagerNCG.TransportTensor ℝ V ℝ`. -/
def ofOnsagerCasimirSystem (S : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem V) :
    TransportTensor ℝ V ℝ where
  toBilin := S.totalGenerator

@[simp]
theorem ofOnsagerCasimirSystem_apply
    (S : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem V) (u v : V) :
    ofOnsagerCasimirSystem S u v = S.totalGenerator u v :=
  rfl

theorem ofOnsagerCasimirSystem_symmPart
    (S : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem V) (u v : V) :
    (ofOnsagerCasimirSystem S).symmPart (1 / 2 : ℝ) u v = S.dissipative u v :=
  S.totalGenerator_symm_part u v

theorem ofOnsagerCasimirSystem_altPart
    (S : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem V) (u v : V) :
    ((ofOnsagerCasimirSystem S).altPart (1 / 2 : ℝ)) u v = S.reversible u v :=
  S.totalGenerator_skew_part u v

theorem ofParityOnsagerSystem_reciprocity
    (PS : InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.ParityOnsagerSystem V)
    (u v : V) :
    ofOnsagerCasimirSystem PS.toOnsagerCasimirSystem
        (TimeReversal.ofClosure PS.T u) (TimeReversal.ofClosure PS.T v) =
      ofOnsagerCasimirSystem PS.toOnsagerCasimirSystem v u :=
  PS.onsager_casimir_master_reciprocity u v

end TimeReversalAndClosureBridge

end InfoGeometry.Synthesis.OnsagerNCG

end noncomputable section
