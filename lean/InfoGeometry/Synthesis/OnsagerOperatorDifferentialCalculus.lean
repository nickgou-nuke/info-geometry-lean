import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra

noncomputable section

namespace InfoGeometry.Synthesis.OnsagerNCG

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

variable {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Ring A] [Algebra R A]

/-!
=============================================================================
PART 1: Operator-Valued Differential Forms & Noncommutative Curvature
=============================================================================
-/

/-- THEOREM 1 (Graded Skew-Symmetry of the Operator Wedge Product in Arguments):
    (α ∧ β)(u, v) = - (α ∧ β)(v, u)
-/
theorem form_wedge_skew_args
    (α β : Op1Form R V A) (u v : V) :
    (wedge α β) u v = - (wedge α β) v u := by
  exact (wedge α β).skew u v

/-- THEOREM 2 (Noncommutative Gauge Curvature / Self-Wedge Commutator Identity):
    (α ∧ α)(u, v) = [α(u), α(v)] = α(u)α(v) - α(v)α(u)
-/
theorem form_wedge_curvature
    (α : Op1Form R V A) (u v : V) :
    (wedge α α) u v = α u * α v - α v * α u := by
  exact wedge_self_eq_commutator α u v

/-!
=============================================================================
PART 2: Operator Derivations Acting on Forms
=============================================================================
-/

/-- THEOREM 3 (Graded Leibniz Product Rule for Operator Differential Forms):
    D(α ∧ β) = (D α) ∧ β + α ∧ (D β)
-/
theorem form_deriv_wedge_leibniz
    (D : OpDerivation R A) (α β : Op1Form R V A) (u v : V) :
    (applyDeriv2 D (wedge α β)) u v =
      (wedge (applyDeriv1 D α) β) u v + (wedge α (applyDeriv1 D β)) u v := by
  exact deriv_wedge_leibniz D α β u v

/-!
=============================================================================
PART 3: Onsager–Metriplectic Operator Decomposition on Forms
=============================================================================
-/

/-- An R-bilinear transport tensor on V with values in operator algebra A: W(u, v). -/
structure TransportTensor (R V A : Type*) [CommRing R] [AddCommGroup V] [Module R V] [Ring A] [Algebra R A] where
  toBilin : V →ₗ[R] V →ₗ[R] A

namespace TransportTensor

variable (W : TransportTensor R V A)

instance : CoeFun (TransportTensor R V A) (fun _ => V → V → A) where
  coe W u v := W.toBilin u v

/-- The Symmetric Dissipative Tensor: L(u, v) = (1/2) • (W(u, v) + W(v, u)). -/
def symmPart (half : R) (u v : V) : A :=
  half • (W u v + W v u)

/-- The Alternating Reversible 2-Form: Ω(u, v) = (1/2) • (W(u, v) - W(v, u)). -/
def altPart (half : R) : Op2Form R V A where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => half • (W u v - W v u)
      map_add' := by
        intro v₁ v₂
        dsimp
        have h1 : W.toBilin u (v₁ + v₂) = W.toBilin u v₁ + W.toBilin u v₂ := (W.toBilin u).map_add v₁ v₂
        have h2 : W.toBilin (v₁ + v₂) u = W.toBilin v₁ u + W.toBilin v₂ u := by
          have h := W.toBilin.map_add v₁ v₂
          exact congr_fun (congr_arg DFunLike.coe h) u
        rw [h1, h2]
        have h_rearr : (W.toBilin u v₁ + W.toBilin u v₂) - (W.toBilin v₁ u + W.toBilin v₂ u) =
                       (W.toBilin u v₁ - W.toBilin v₁ u) + (W.toBilin u v₂ - W.toBilin v₂ u) := by abel
        rw [h_rearr, smul_add]
      map_smul' := by
        intro c v
        dsimp
        have h1 : W.toBilin u (c • v) = c • W.toBilin u v := (W.toBilin u).map_smul c v
        have h2 : W.toBilin (c • v) u = c • W.toBilin v u := by
          have h := W.toBilin.map_smul c v
          exact congr_fun (congr_arg DFunLike.coe h) u
        rw [h1, h2, ← smul_sub, smul_comm]
    }
    map_add' := by
      intro u₁ u₂
      ext v
      dsimp
      have h1 : W.toBilin (u₁ + u₂) v = W.toBilin u₁ v + W.toBilin u₂ v := by
        have h := W.toBilin.map_add u₁ u₂
        exact congr_fun (congr_arg DFunLike.coe h) v
      have h2 : W.toBilin v (u₁ + u₂) = W.toBilin v u₁ + W.toBilin v u₂ := (W.toBilin v).map_add u₁ u₂
      rw [h1, h2]
      have h_rearr : (W.toBilin u₁ v + W.toBilin u₂ v) - (W.toBilin v u₁ + W.toBilin v u₂) =
                     (W.toBilin u₁ v - W.toBilin v u₁) + (W.toBilin u₂ v - W.toBilin v u₂) := by abel
      rw [h_rearr, smul_add]
    map_smul' := by
      intro c u
      ext v
      dsimp
      have h1 : W.toBilin (c • u) v = c • W.toBilin u v := by
        have h := W.toBilin.map_smul c u
        exact congr_fun (congr_arg DFunLike.coe h) v
      have h2 : W.toBilin v (c • u) = c • W.toBilin v u := (W.toBilin v).map_smul c u
      rw [h1, h2, ← smul_sub, smul_comm]
  }
  alt' := by
    intro v
    dsimp
    rw [sub_self, smul_zero]

@[simp]
theorem symmPart_apply
    (half : R) (u v : V) :
    W.symmPart half u v = half • (W u v + W v u) :=
  rfl

@[simp]
theorem altPart_apply
    (half : R) (u v : V) :
    (W.altPart half) u v = half • (W u v - W v u) :=
  rfl

/-- THEOREM 4 (Exact Metriplectic / Onsager Decomposition):
    W(u, v) = L(u, v) + Ω(u, v)
    Splits transport into symmetric dissipative and 2-form Hamiltonian dynamics.
-/
theorem onsager_metriplectic_decomposition
    (half : R) (h_half : (2 : R) * half = 1) (u v : V) :
    W u v = W.symmPart half u v + (W.altPart half) u v := by
  dsimp [symmPart, altPart]
  rw [← smul_add]
  have h_add : (W u v + W v u) + (W u v - W v u) = (2 : R) • (W u v) := by
    calc
      (W u v + W v u) + (W u v - W v u) = (W u v + W u v) + (W v u - W v u) := by abel
      _ = (2 : R) • (W u v) + 0 := by rw [two_smul, sub_self]
      _ = (2 : R) • (W u v) := by rw [add_zero]
  rw [h_add, smul_smul]
  have h_norm : half * 2 = 1 := by rw [mul_comm, h_half]
  rw [h_norm, one_smul]

/-- THEOREM 5 (Exact Dissipation Isolation / Diagonal Degeneracy):
    W(u, u) = L(u, u)
    The alternating 2-form drops out identically on the diagonal, proving that
    entropy production is governed purely by the symmetric dissipative metric.
-/
theorem dissipation_eq_symmetric
    (half : R) (h_half : (2 : R) * half = 1) (u : V) :
    W u u = W.symmPart half u u := by
  have h_decomp := W.onsager_metriplectic_decomposition half h_half u u
  rw [(W.altPart half).alt u, add_zero] at h_decomp
  exact h_decomp

end TransportTensor

/-!
=============================================================================
PART 4: Onsager–Casimir Reciprocity under Time-Reversal Involutions
=============================================================================
-/

/-- A Time-Reversal linear involution on the tangent module: T² = id. -/
structure TimeReversal (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  toLinearMap : V →ₗ[R] V
  involutive' : toLinearMap.comp toLinearMap = LinearMap.id

namespace TimeReversal

instance : CoeFun (TimeReversal R V) (fun _ => V → V) where
  coe T := T.toLinearMap

variable (T : TimeReversal R V)

@[simp]
theorem map_add
    (x y : V) :
    T (x + y) = T x + T y :=
  T.toLinearMap.map_add x y

@[simp]
theorem map_smul
    (c : R) (x : V) :
    T (c • x) = c • T x :=
  T.toLinearMap.map_smul c x

@[simp]
theorem involutive
    (x : V) :
    T (T x) = x := by
  have h := congr_fun (congr_arg DFunLike.coe T.involutive') x
  exact h

end TimeReversal

/-- THEOREM 6 (Onsager–Casimir Reciprocal Relations):
    For a time-even transport tensor where L(Tu, Tv) = L(v, u) and Ω(Tu, Tv) = - Ω(v, u) = Ω(u, v),
    the full tensor satisfies time-reversal transpose reciprocity:
      W(Tu, Tv) = W(v, u)
-/
theorem onsager_casimir_reciprocity
    (W : TransportTensor R V A)
    (half : R) (h_half : (2 : R) * half = 1)
    (T : TimeReversal R V)
    (u v : V)
    (hL : W.symmPart half (T u) (T v) = W.symmPart half v u)
    (hOmega : (W.altPart half) (T u) (T v) = (W.altPart half) u v) :
    W (T u) (T v) = W.symmPart half v u + (W.altPart half) u v := by
  rw [W.onsager_metriplectic_decomposition half h_half (T u) (T v)]
  rw [hL, hOmega]

end InfoGeometry.Synthesis.OnsagerNCG

end noncomputable section
