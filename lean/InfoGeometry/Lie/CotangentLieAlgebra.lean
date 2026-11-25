/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Cotangent Lie algebra and its hemi-semidirect companion

The existing real phase-space carrier `g × Module.Dual ℝ g` carries the
cotangent semidirect Lie bracket. Its dual action is Mathlib's native
coadjoint action. The neutral bilinear form is the existing evaluation
pairing from `NeutralPhaseSpaceCore`.

The one-sided hemi-semidirect operation is separately named: it satisfies
the left Leibniz identity and preserves the pairing under its left action,
but its symmetric part need not vanish. It is therefore not, in general,
a Courant bracket over a point. The cotangent Lie bracket is the double
associated with a zero Lie cobracket; this file does not construct a
general Lie bialgebra or a Courant algebroid on a manifold.

The Lie ring and Lie algebra structures are explicit named definitions,
not global instances competing with the native product Lie bracket.
-/

noncomputable section

namespace InfoGeometry.Lie.CotangentLieAlgebra

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The cotangent semidirect bracket, with the dual given its zero internal bracket. -/
def cotangentBracket (e f : PhaseSpaceCarrier g) : PhaseSpaceCarrier g :=
  (⁅e.1, f.1⁆, ⁅e.1, f.2⁆ - ⁅f.1, e.2⁆)

/-- The coadjoint hemi-semidirect operation. This is a left Leibniz operation. -/
def hemiSemidirectBracket (e f : PhaseSpaceCarrier g) : PhaseSpaceCarrier g :=
  (⁅e.1, f.1⁆, ⁅e.1, f.2⁆)

theorem cotangentBracket_add_left (e f h : PhaseSpaceCarrier g) :
    cotangentBracket (e + f) h = cotangentBracket e h + cotangentBracket f h := by
  apply Prod.ext
  · simp [cotangentBracket]
  · simp only [cotangentBracket, Prod.fst_add, Prod.snd_add, add_lie, lie_add]
    abel

theorem cotangentBracket_add_right (e f h : PhaseSpaceCarrier g) :
    cotangentBracket e (f + h) = cotangentBracket e f + cotangentBracket e h := by
  apply Prod.ext
  · simp [cotangentBracket]
  · simp only [cotangentBracket, Prod.fst_add, Prod.snd_add, add_lie, lie_add]
    abel

theorem cotangentBracket_smul_left (r : ℝ) (e f : PhaseSpaceCarrier g) :
    cotangentBracket (r • e) f = r • cotangentBracket e f := by
  apply Prod.ext
  · exact LieModule.smul_lie r e.1 f.1
  · change ⁅r • e.1, f.2⁆ - ⁅f.1, r • e.2⁆ =
      r • (⁅e.1, f.2⁆ - ⁅f.1, e.2⁆)
    rw [LieModule.smul_lie r e.1 f.2, LieModule.lie_smul r f.1 e.2, smul_sub]

theorem cotangentBracket_smul_right (r : ℝ) (e f : PhaseSpaceCarrier g) :
    cotangentBracket e (r • f) = r • cotangentBracket e f := by
  apply Prod.ext
  · exact LieModule.lie_smul r e.1 f.1
  · change ⁅e.1, r • f.2⁆ - ⁅r • f.1, e.2⁆ =
      r • (⁅e.1, f.2⁆ - ⁅f.1, e.2⁆)
    rw [LieModule.lie_smul r e.1 f.2, LieModule.smul_lie r f.1 e.2, smul_sub]

@[simp] theorem cotangentBracket_self (e : PhaseSpaceCarrier g) :
    cotangentBracket e e = 0 := by
  simp [cotangentBracket]

theorem cotangentBracket_skew (e f : PhaseSpaceCarrier g) :
    cotangentBracket e f = -cotangentBracket f e := by
  apply Prod.ext
  · exact (lie_skew e.1 f.1).symm
  · simp only [cotangentBracket, Prod.snd_neg]
    abel

/-- Jacobi follows from the native Lie-module identities for the coadjoint action. -/
theorem cotangentBracket_leibniz (e f h : PhaseSpaceCarrier g) :
    cotangentBracket e (cotangentBracket f h) =
      cotangentBracket (cotangentBracket e f) h +
        cotangentBracket f (cotangentBracket e h) := by
  apply Prod.ext
  · exact leibniz_lie e.1 f.1 h.1
  · simp only [cotangentBracket, Prod.snd_add, lie_sub]
    rw [leibniz_lie e.1 f.1 h.2, leibniz_lie e.1 h.1 f.2,
      leibniz_lie f.1 h.1 e.2]
    abel

/-- A genuine native Lie ring structure on the existing phase-space carrier. -/
@[instance_reducible] def cotangentLieRing : LieRing (PhaseSpaceCarrier g) where
  __ := (inferInstance : AddCommGroup (PhaseSpaceCarrier g))
  bracket := cotangentBracket
  add_lie := cotangentBracket_add_left
  lie_add := cotangentBracket_add_right
  lie_self := cotangentBracket_self
  leibniz_lie := cotangentBracket_leibniz

/-- The cotangent Lie ring is a real Lie algebra with its existing scalar multiplication. -/
@[instance_reducible] def cotangentLieAlgebra :
    @LieAlgebra ℝ (PhaseSpaceCarrier g) inferInstance (cotangentLieRing (g := g)) := by
  letI : LieRing (PhaseSpaceCarrier g) := cotangentLieRing (g := g)
  exact
    { (inferInstance : Module ℝ (PhaseSpaceCarrier g)) with
      lie_smul := cotangentBracket_smul_right }

/-- The neutral evaluation form is invariant under the cotangent Lie bracket. -/
theorem cotangentBracket_neutral_invariant (e f h : PhaseSpaceCarrier g) :
    canonicalNeutralBilin (cotangentBracket e f) h +
      canonicalNeutralBilin f (cotangentBracket e h) = 0 := by
  simp only [canonicalNeutralBilin_apply, cotangentBracket,
    LinearMap.sub_apply, Module.Dual.lie_apply]
  have hskew : e.2 ⁅h.1, f.1⁆ = -e.2 ⁅f.1, h.1⁆ := by
    simpa only [map_neg] using congrArg e.2 (lie_skew h.1 f.1).symm
  rw [hskew]
  ring

/-- The original Lie algebra embeds as the first summand at the level of brackets. -/
@[simp] theorem cotangentBracket_primal (X Y : g) :
    cotangentBracket (X, 0) (Y, 0) = (⁅X, Y⁆, 0) := by
  simp [cotangentBracket]

/-- The dual summand is abelian for the cotangent semidirect bracket. -/
@[simp] theorem cotangentBracket_dual (α β : Module.Dual ℝ g) :
    cotangentBracket (0, α) (0, β) = 0 := by
  simp [cotangentBracket]

/-- The mixed bracket is exactly the native coadjoint action. -/
@[simp] theorem cotangentBracket_mixed (X : g) (α : Module.Dual ℝ g) :
    cotangentBracket (X, 0) (0, α) = (0, ⁅X, α⁆) := by
  simp [cotangentBracket]

/-- The left Leibniz identity holds without imposing skew-symmetry. -/
theorem hemiSemidirectBracket_leibniz (e f h : PhaseSpaceCarrier g) :
    hemiSemidirectBracket e (hemiSemidirectBracket f h) =
      hemiSemidirectBracket (hemiSemidirectBracket e f) h +
        hemiSemidirectBracket f (hemiSemidirectBracket e h) := by
  apply Prod.ext
  · exact leibniz_lie e.1 f.1 h.1
  · exact leibniz_lie e.1 f.1 h.2

/-- The symmetric part is a generally nonzero dual vector. -/
theorem hemiSemidirectBracket_symmetric_sum (e f : PhaseSpaceCarrier g) :
    hemiSemidirectBracket e f + hemiSemidirectBracket f e =
      (0, ⁅e.1, f.2⁆ + ⁅f.1, e.2⁆) := by
  apply Prod.ext
  · change ⁅e.1, f.1⁆ + ⁅f.1, e.1⁆ = 0
    rw [← lie_skew e.1 f.1]
    exact neg_add_cancel _
  · rfl

/-- Evaluation gives the precise signs of the hemi-semidirect symmetric part. -/
theorem hemiSemidirectBracket_symmetric_sum_apply
    (e f : PhaseSpaceCarrier g) (Z : g) :
    (hemiSemidirectBracket e f + hemiSemidirectBracket f e).2 Z =
      -(f.2 ⁅e.1, Z⁆ + e.2 ⁅f.1, Z⁆) := by
  rw [hemiSemidirectBracket_symmetric_sum]
  simp only [LinearMap.add_apply, Module.Dual.lie_apply]
  ring

/-- The diagonal adjoint/coadjoint action preserves the neutral pairing.
Consequently its infinitesimal derivative of that scalar pairing is zero. -/
theorem hemiSemidirectBracket_neutral_invariant (e f h : PhaseSpaceCarrier g) :
    canonicalNeutralBilin (hemiSemidirectBracket e f) h +
      canonicalNeutralBilin f (hemiSemidirectBracket e h) = 0 := by
  simp only [canonicalNeutralBilin_apply, hemiSemidirectBracket, Module.Dual.lie_apply]
  ring

/-- Any nonzero coadjoint readout witnesses failure of a zero symmetric part. -/
theorem hemiSemidirectBracket_symmetric_sum_ne_zero
    (X Z : g) (α : Module.Dual ℝ g) (h : α ⁅X, Z⁆ ≠ 0) :
    hemiSemidirectBracket (X, 0) (0, α) +
      hemiSemidirectBracket (0, α) (X, 0) ≠ 0 := by
  intro heq
  have hz := congrArg (fun e : PhaseSpaceCarrier g => e.2 Z) heq
  have hneg : -α ⁅X, Z⁆ = 0 := by
    simpa [hemiSemidirectBracket] using hz
  exact h (neg_eq_zero.mp hneg)

/-- A nonzero coadjoint readout also witnesses failure of alternation. -/
theorem hemiSemidirectBracket_self_ne_zero
    (X Z : g) (α : Module.Dual ℝ g) (h : α ⁅X, Z⁆ ≠ 0) :
    hemiSemidirectBracket (X, α) (X, α) ≠ 0 := by
  intro heq
  have hz := congrArg (fun e : PhaseSpaceCarrier g => e.2 Z) heq
  have hneg : -α ⁅X, Z⁆ = 0 := by
    simpa [hemiSemidirectBracket] using hz
  exact h (neg_eq_zero.mp hneg)

/-- Over a dual-separating real module, the hemi-semidirect operation is alternating
exactly when the original Lie algebra is abelian. -/
theorem hemiSemidirectBracket_alternating_iff [Module.Projective ℝ g] :
    (∀ e : PhaseSpaceCarrier g, hemiSemidirectBracket e e = 0) ↔
      ∀ X Y : g, ⁅X, Y⁆ = 0 := by
  constructor
  · intro h X Y
    apply (Module.forall_dual_apply_eq_zero_iff ℝ ⁅X, Y⁆).mp
    intro α
    have hy := congrArg (fun e : PhaseSpaceCarrier g => e.2 Y) (h (X, α))
    have hneg : -α ⁅X, Y⁆ = 0 := by
      simpa [hemiSemidirectBracket] using hy
    exact neg_eq_zero.mp hneg
  · intro h e
    apply Prod.ext
    · exact h e.1 e.1
    · apply LinearMap.ext
      intro Y
      simp [hemiSemidirectBracket, h]

open InfoGeometry.Algebra.FiniteSpin (Mat2R)

section MatrixObstruction

local instance : LieRing Mat2R := LieRing.ofAssociativeRing

/-- The first matrix unit on the diagonal. -/
def hemiObstructionH : Mat2R := Matrix.single 0 0 1

/-- The upper off-diagonal matrix unit. -/
def hemiObstructionE : Mat2R := Matrix.single 0 1 1

/-- The actual algebraic covector reading the upper off-diagonal entry. -/
def hemiObstructionReadout : Module.Dual ℝ Mat2R :=
  ((LinearMap.proj (1 : Fin 2)) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).comp
    ((LinearMap.proj (0 : Fin 2)) : Mat2R →ₗ[ℝ] (Fin 2 → ℝ))

@[simp] theorem hemiObstructionReadout_apply (A : Mat2R) :
    hemiObstructionReadout A = A 0 1 := rfl

/-- The selected matrices exhibit a nonzero native commutator. -/
theorem hemiObstruction_lie :
    ⁅hemiObstructionH, hemiObstructionE⁆ = hemiObstructionE := by
  rw [LieRing.of_associative_ring_bracket]
  simp [hemiObstructionH, hemiObstructionE, Matrix.single_mul_single_of_ne]

@[simp] theorem hemiObstructionReadout_lie :
    hemiObstructionReadout ⁅hemiObstructionH, hemiObstructionE⁆ = 1 := by
  rw [hemiObstruction_lie, hemiObstructionReadout_apply]
  simp [hemiObstructionE]

/-- The symmetric part evaluates to minus one, rather than zero. -/
theorem matrix_hemi_symmetric_sum_eq_neg_one :
    (hemiSemidirectBracket (hemiObstructionH, 0) (0, hemiObstructionReadout) +
      hemiSemidirectBracket (0, hemiObstructionReadout) (hemiObstructionH, 0)).2
        hemiObstructionE = -1 := by
  rw [hemiSemidirectBracket_symmetric_sum_apply]
  simp only [hemiObstructionReadout_lie, LinearMap.zero_apply, add_zero]

/-- A concrete refutation of the proposed identification of the hemi-semidirect
symmetric part with the diagonal derivative of the invariant neutral pairing. -/
theorem matrix_hemi_pairing_derivative_identity_fails :
    (hemiSemidirectBracket (hemiObstructionH, 0) (0, hemiObstructionReadout) +
      hemiSemidirectBracket (0, hemiObstructionReadout) (hemiObstructionH, 0)).2
        hemiObstructionE ≠
      -canonicalNeutralBilin
        (hemiSemidirectBracket (hemiObstructionE, 0) (hemiObstructionH, 0))
        (0, hemiObstructionReadout) -
      canonicalNeutralBilin (hemiObstructionH, 0)
        (hemiSemidirectBracket (hemiObstructionE, 0) (0, hemiObstructionReadout)) := by
  have hzero := hemiSemidirectBracket_neutral_invariant
    (hemiObstructionE, 0) (hemiObstructionH, 0) (0, hemiObstructionReadout)
  have hright :
      -canonicalNeutralBilin
        (hemiSemidirectBracket (hemiObstructionE, 0) (hemiObstructionH, 0))
        (0, hemiObstructionReadout) -
      canonicalNeutralBilin (hemiObstructionH, 0)
        (hemiSemidirectBracket (hemiObstructionE, 0) (0, hemiObstructionReadout)) = 0 := by
    simpa only [neg_add, neg_zero, sub_eq_add_neg] using congrArg (fun r : ℝ => -r) hzero
  rw [matrix_hemi_symmetric_sum_eq_neg_one, hright]
  norm_num

end MatrixObstruction

end InfoGeometry.Lie.CotangentLieAlgebra
