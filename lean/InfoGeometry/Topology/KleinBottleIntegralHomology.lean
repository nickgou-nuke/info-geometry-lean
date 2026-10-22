/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinBottleCWChain
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral first homology of the Klein-bottle polygon chain model

The boundary map is obtained from the exponent-sum vector of the actual
relator owned by `KleinPresentedGroup`. The resulting algebraic chain model
has first homology `ℤ × ZMod 2`, retaining the torsion that disappears after
extension of scalars to `ℝ`. This file computes the homology of that chain
model; it does not identify it with the homology of the orbit quotient.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinBottleIntegralHomology

open InfoGeometry.Topology.KleinBottleCWChain

abbrev C0 := Fin 1 → ℤ
abbrev C1 := Fin 2 → ℤ

/-- Integral degree-two boundary from the relator exponent sums. -/
def boundary₂ : ℤ →ₗ[ℤ] C1 where
  toFun n i := relatorExponentSum i * n
  map_add' n m := by
    funext i
    simp [mul_add]
  map_smul' a n := by
    funext i
    change relatorExponentSum i * (a * n) = a * (relatorExponentSum i * n)
    ring

private theorem exponentSum_zero : relatorExponentSum 0 = 0 := by
  have h := congrFun relator_exponent_sum (0 : Fin 2)
  simpa using h

private theorem exponentSum_one : relatorExponentSum 1 = 2 := by
  have h := congrFun relator_exponent_sum (1 : Fin 2)
  simpa using h

/-- Coordinate form of the integral boundary, grounded in the presentation
relator rather than a separately chosen coefficient vector. -/
theorem boundary₂_apply (n : ℤ) :
    boundary₂ n = ![0, 2 * n] := by
  funext i
  change relatorExponentSum i * n = (![0, 2 * n] : Fin 2 → ℤ) i
  rw [relator_exponent_sum]
  fin_cases i <;> simp

/-- Degree-one boundary of the one-vertex integral polygon model. -/
def boundary₁ : C1 →ₗ[ℤ] C0 := 0

/-- The two boundary maps satisfy the chain condition. -/
theorem boundary₁_comp_boundary₂ : boundary₁.comp boundary₂ = 0 := by
  ext n
  simp [boundary₁]

/-- The degree-two boundary, with codomain restricted to the cycle space. -/
def boundary₂IntoCycles : ℤ →ₗ[ℤ] LinearMap.ker boundary₁ where
  toFun n := ⟨boundary₂ n, by simp [boundary₁]⟩
  map_add' n m := by
    apply Subtype.ext
    exact map_add boundary₂ n m
  map_smul' a n := by
    apply Subtype.ext
    exact map_smul boundary₂ a n

/-- First homology of the integral algebraic chain model, cycles modulo
boundaries. -/
abbrev H1 := LinearMap.ker boundary₁ ⧸ LinearMap.range boundary₂IntoCycles

/-- The two coordinates read the free generator and the parity class. -/
def h1Readout : C1 →ₗ[ℤ] ℤ × ZMod 2 where
  toFun x := (x 0, x 1)
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' a x := by
    apply Prod.ext <;> simp

theorem h1Readout_surjective : Function.Surjective h1Readout := by
  rintro ⟨a, b⟩
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective b
  refine ⟨![a, n], ?_⟩
  apply Prod.ext
  · rfl
  · simpa [h1Readout] using hn

/-- The kernel of the free-coordinate/parity readout is exactly the image of
the relator boundary. -/
theorem h1Readout_ker_eq_boundary_range :
    LinearMap.ker h1Readout = LinearMap.range boundary₂ := by
  ext x
  change h1Readout x = 0 ↔ x ∈ LinearMap.range boundary₂
  constructor
  · intro hx
    have hx₀ : x 0 = 0 := by
      have := congrArg Prod.fst hx
      simpa [h1Readout] using this
    have hx₁ : (x 1 : ZMod 2) = 0 := by
      have := congrArg Prod.snd hx
      simpa [h1Readout] using this
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_zero_iff_even).mp hx₁
    refine ⟨k, ?_⟩
    funext i
    fin_cases i
    · simpa [boundary₂, exponentSum_zero] using hx₀.symm
    · change relatorExponentSum 1 * k = x 1
      rw [exponentSum_one]
      calc
        (2 : ℤ) * k = k + k := by ring
        _ = x 1 := hk.symm
  · rintro ⟨n, rfl⟩
    apply Prod.ext
    · simp [h1Readout, boundary₂, exponentSum_zero]
    · change ((relatorExponentSum 1 * n : ℤ) : ZMod 2) = 0
      rw [exponentSum_one]
      exact ZMod.intCast_eq_zero_iff_even.mpr ⟨n, by ring⟩

/-- The readout restricted to cycles remains surjective because the modeled
degree-one boundary is zero. -/
def h1ReadoutCycles : LinearMap.ker boundary₁ →ₗ[ℤ] ℤ × ZMod 2 :=
  h1Readout.comp (LinearMap.ker boundary₁).subtype

theorem h1ReadoutCycles_surjective : Function.Surjective h1ReadoutCycles := by
  rintro y
  obtain ⟨x, hx⟩ := h1Readout_surjective y
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change boundary₁ x = 0
    simp [boundary₁]
  · exact hx

/-- The restricted readout has exactly the image of the degree-two boundary
as its kernel. -/
theorem h1ReadoutCycles_ker_eq_boundary_range :
    LinearMap.ker h1ReadoutCycles = LinearMap.range boundary₂IntoCycles := by
  ext x
  change h1Readout x.1 = 0 ↔ x ∈ LinearMap.range boundary₂IntoCycles
  constructor
  · intro hx
    have hxker : x.1 ∈ LinearMap.ker h1Readout :=
      LinearMap.mem_ker.mpr hx
    have hx' : x.1 ∈ LinearMap.range boundary₂ :=
      h1Readout_ker_eq_boundary_range ▸ hxker
    rcases hx' with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  · rintro ⟨n, hn⟩
    have hval : boundary₂ n = x.1 := congrArg Subtype.val hn
    have hxrange : x.1 ∈ LinearMap.range boundary₂ := ⟨n, hval⟩
    have hxker : x.1 ∈ LinearMap.ker h1Readout :=
      h1Readout_ker_eq_boundary_range.symm ▸ hxrange
    exact LinearMap.mem_ker.mp hxker

/-- Integral first homology of the algebraic Klein polygon chain model is the
free generator together with a parity class. -/
noncomputable def h1EquivFreeTimesParity : H1 ≃ₗ[ℤ] ℤ × ZMod 2 :=
  (Submodule.quotEquivOfEq (LinearMap.range boundary₂IntoCycles)
      (LinearMap.ker h1ReadoutCycles)
      h1ReadoutCycles_ker_eq_boundary_range.symm).trans
    (h1ReadoutCycles.quotKerEquivOfSurjective h1ReadoutCycles_surjective)

theorem h1EquivFreeTimesParity_mk (x : LinearMap.ker boundary₁) :
    h1EquivFreeTimesParity (Submodule.Quotient.mk x) =
      (x.1 0, (x.1 1 : ZMod 2)) := by
  change h1ReadoutCycles.quotKerEquivOfSurjective h1ReadoutCycles_surjective
    ((Submodule.quotEquivOfEq (LinearMap.range boundary₂IntoCycles)
      (LinearMap.ker h1ReadoutCycles)
      h1ReadoutCycles_ker_eq_boundary_range.symm)
      (Submodule.Quotient.mk x)) = h1Readout x
  rw [Submodule.quotEquivOfEq_mk]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end InfoGeometry.Topology.KleinBottleIntegralHomology

end noncomputable section
