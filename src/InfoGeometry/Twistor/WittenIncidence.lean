/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WittenSpinorHelicity
import InfoGeometry.Twistor.PluckerPenroseIncidence
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Witten's line equation in the native Penrose convention

The paper writes a twistor as `(λ, μ)` and uses `μ + xᵀ λ = 0`.
The repository writes `(ω, π)` and uses `ω = i X π`.  Exchanging the
two blocks therefore identifies Witten's graph at `x` with the existing
Penrose incidence plane at `X = i xᵀ`.  The transpose, block order and
factor of `i` are all explicit.

The resulting family lies in a genuine two-dimensional linear subspace
and hence projectivizes to a projective line.  The exterior-three-vector
vanishing theorem is a rank consequence.  It does not assert that distinct
points on this line are proportional vectors.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.WittenIncidence

open InfoGeometry.Twistor.PenroseIncidence

/-- Exchange Witten's `(λ, μ)` and the native `(ω, π)` block order. -/
def wittenBlockSwap : Twistor4 ≃ₗ[ℂ] Twistor4 :=
  LinearEquiv.prodComm ℂ Spinor2 Spinor2

@[simp] theorem wittenBlockSwap_apply (Z : Twistor4) :
    wittenBlockSwap Z = (Z.2, Z.1) := rfl

/-- Witten's equation (3.7), with the matrix indices displayed by a transpose. -/
def wittenIncidence (x : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Twistor4 where
  toFun lambda := (lambda, -(omegaLinearMap x.transpose lambda))
  map_add' lambda ρ := by
    apply Prod.ext
    · rfl
    · change -(omegaLinearMap x.transpose (lambda + ρ)) =
        -(omegaLinearMap x.transpose lambda) + -(omegaLinearMap x.transpose ρ)
      rw [map_add, neg_add]
  map_smul' c lambda := by simp

@[simp] theorem wittenIncidence_apply (x : ComplexSpacetime) (lambda : Spinor2) :
    wittenIncidence x lambda = (lambda, -(x.transpose.mulVec lambda)) := rfl

theorem wittenIncidence_injective (x : ComplexSpacetime) :
    Function.Injective (wittenIncidence x) := by
  intro lambda ρ h
  exact congrArg Prod.fst h

theorem wittenIncidence_ne_zero (x : ComplexSpacetime) (lambda : Spinor2)
    (hLambda : lambda ≠ 0) : wittenIncidence x lambda ≠ 0 := by
  intro h
  exact hLambda (congrArg Prod.fst h)

/-- This is the exact adapter, including the native imaginary unit. -/
theorem blockSwap_wittenIncidence (x : ComplexSpacetime) (lambda : Spinor2) :
    wittenBlockSwap (wittenIncidence x lambda) =
      incidenceLinearMap (Complex.I • x.transpose) lambda := by
  simp [wittenIncidence_apply, incidenceLinearMap_apply,
    omegaLinearMap_apply, Matrix.smul_mulVec, smul_smul]

/-- The literal linear plane underlying the Witten projective line. -/
def wittenPlane (x : ComplexSpacetime) : Submodule ℂ Twistor4 :=
  LinearMap.range (wittenIncidence x)

@[simp] theorem mem_wittenPlane_iff (x : ComplexSpacetime) (Z : Twistor4) :
    Z ∈ wittenPlane x ↔ Z.2 = -(x.transpose.mulVec Z.1) := by
  constructor
  · rintro ⟨lambda, rfl⟩
    rfl
  · intro h
    exact ⟨Z.1, Prod.ext rfl h.symm⟩

theorem wittenPlane_finrank (x : ComplexSpacetime) :
    Module.finrank ℂ (wittenPlane x) = 2 := by
  rw [wittenPlane, LinearMap.finrank_range_of_inj (wittenIncidence_injective x)]
  simp [Spinor2, InfoGeometry.Algebra.FiniteSpin.Vec2C, Module.finrank_pi]

/-- Transport acts on actual submodules, not only on coordinates. -/
theorem map_wittenPlane (x : ComplexSpacetime) :
    (wittenPlane x).map wittenBlockSwap.toLinearMap =
      incidencePlane (Complex.I • x.transpose) := by
  apply le_antisymm
  · rintro Z ⟨W, ⟨lambda, rfl⟩, rfl⟩
    exact ⟨lambda, (blockSwap_wittenIncidence x lambda).symm⟩
  · rintro Z ⟨lambda, rfl⟩
    exact ⟨wittenIncidence x lambda, ⟨lambda, rfl⟩, blockSwap_wittenIncidence x lambda⟩

/-- A homogeneous family is on one projective line when all representatives
are nonzero and lie in a common two-dimensional linear subspace. -/
def OnCommonProjectiveLine {ι : Type*} (Z : ι → Twistor4) : Prop :=
  (∀ i, Z i ≠ 0) ∧ ∃ L : Submodule ℂ Twistor4,
    Module.finrank ℂ L = 2 ∧ ∀ i, Z i ∈ L

theorem wittenIncidence_commonLine {ι : Type*}
    (x : ComplexSpacetime) (lambda : ι → Spinor2) (hLambda : ∀ i, lambda i ≠ 0) :
    OnCommonProjectiveLine (fun i => wittenIncidence x (lambda i)) := by
  refine ⟨fun i => wittenIncidence_ne_zero x (lambda i) (hLambda i),
    wittenPlane x, wittenPlane_finrank x, ?_⟩
  intro i
  exact ⟨lambda i, rfl⟩

theorem wittenIncidence_span_finrank_le_two {ι : Type*}
    (x : ComplexSpacetime) (lambda : ι → Spinor2) :
    Module.finrank ℂ
      (Submodule.span ℂ (Set.range (fun i => wittenIncidence x (lambda i)))) ≤ 2 := by
  calc
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range (fun i => wittenIncidence x (lambda i)))) ≤
        Module.finrank ℂ (wittenPlane x) := by
      apply Submodule.finrank_mono
      apply Submodule.span_le.mpr
      rintro Z ⟨i, rfl⟩
      exact ⟨lambda i, rfl⟩
    _ = 2 := wittenPlane_finrank x

/-- Witten's equation (3.36) on a native exterior cube. -/
theorem wittenIncidence_exteriorThree_zero
    (x : ComplexSpacetime) (lambda : Fin 3 → Spinor2) :
    exteriorPower.ιMulti ℂ 3 (fun i => wittenIncidence x (lambda i)) = 0 := by
  apply (exteriorPower.ιMulti ℂ 3).map_linearDependent
  intro h
  have hLambda : LinearIndependent ℂ lambda :=
    LinearIndependent.of_comp (wittenIncidence x) h
  have hdim := hLambda.fintype_card_le_finrank
  norm_num [Spinor2, InfoGeometry.Algebra.FiniteSpin.Vec2C,
    Module.finrank_pi] at hdim

/-- The actual quotient-level projective line map. -/
def wittenProjectiveIncidenceMap (x : ComplexSpacetime) :
    ProjectiveSpinorLine → ProjectiveTwistor3 :=
  Projectivization.map (wittenIncidence x) (wittenIncidence_injective x)

theorem wittenProjectiveIncidenceMap_injective (x : ComplexSpacetime) :
    Function.Injective (wittenProjectiveIncidenceMap x) :=
  Projectivization.map_injective (wittenIncidence x) (wittenIncidence_injective x)

/-- The convention adapter also commutes with the native projective quotient. -/
theorem projective_blockSwap_wittenIncidence
    (x : ComplexSpacetime) (lambda : Spinor2) (hLambda : lambda ≠ 0) :
    Projectivization.map wittenBlockSwap.toLinearMap wittenBlockSwap.injective
      (wittenProjectiveIncidenceMap x (Projectivization.mk ℂ lambda hLambda)) =
      projectiveIncidenceMap (Complex.I • x.transpose)
        (Projectivization.mk ℂ lambda hLambda) := by
  change Projectivization.mk ℂ (wittenBlockSwap (wittenIncidence x lambda)) _ =
    Projectivization.mk ℂ (incidenceLinearMap (Complex.I • x.transpose) lambda) _
  congr 1
  exact blockSwap_wittenIncidence x lambda

end InfoGeometry.Twistor.WittenIncidence
