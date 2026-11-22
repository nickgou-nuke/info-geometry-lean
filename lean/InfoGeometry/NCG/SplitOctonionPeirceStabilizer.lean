/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section

/-!
# Peirce-idempotent stabilizer predicate for the transported Zorn derivations

This module defines a predicate on the repository's concrete 14-parameter
family of split-octonion derivations and proves only consequences supported by
the owner declarations. It does not identify the parameter subset as a Lie
subalgebra isomorphic to `SU(3)`, prove its dimension, or establish triplet and
antitriplet representation laws. Those classification statements require
additional kernel and representation theorems. -/

namespace InfoGeometry.NCG.SplitOctonionPeirceStabilizer

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering

/- The existing lower-right Peirce idempotent. It has trace one, so it is not
   an imaginary split-octonion (the imaginary subspace is trace zero). -/
def selectedPeirceIdempotent : ZornSplitOctonion ℝ := zornE1

/-- The selected lower-right Peirce idempotent has trace one. -/
theorem selectedPeirceIdempotent_trace_eq_one :
    selectedPeirceIdempotent.a + selectedPeirceIdempotent.b = 1 := by
  simp [selectedPeirceIdempotent, zornE1]

/-- The selected element is an idempotent in the existing Zorn product. -/
theorem selectedPeirceIdempotent_mul_self :
    zornMul selectedPeirceIdempotent selectedPeirceIdempotent =
      selectedPeirceIdempotent := by
  simpa [selectedPeirceIdempotent] using zornE1_sq

/-- Predicate saying that one member of the existing parameterized derivation
   family fixes the selected Zorn element. No group or dimension structure is
   included in this predicate. -/
def FixesSelectedPeirceIdempotent (p : Params) : Prop :=
  zornG2Derivation p selectedPeirceIdempotent = zornZero

/-- Exact parameter criterion for fixing the selected Peirce idempotent. In the
repository's existing fourteen-parameter derivation coordinates, the six
parameters which move `zornE1` must vanish; the other eight remain
unconstrained by this stabilizer equation.  This is a coordinate
classification of the predicate, not by itself a proof of a Lie-subalgebra
isomorphism. -/
theorem fixesSelectedPeirceIdempotent_iff_parameters (p : Params) :
    FixesSelectedPeirceIdempotent p ↔
      p 0 = 0 ∧ p 3 = 0 ∧ p 4 = 0 ∧ p 8 = 0 ∧ p 9 = 0 ∧ p 10 = 0 := by
  simp [FixesSelectedPeirceIdempotent, selectedPeirceIdempotent, zornG2Derivation,
    parameterAction, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
    splitOctonionToZornVectorMatrix, zornE1, zornZero]
  constructor
  · rintro ⟨hw, hv⟩
    have hp10 := congrFun hw 0
    have hp9 := congrFun hw 1
    have hp4 := congrFun hw 2
    have hp0 := congrFun hv 0
    have hp3 := congrFun hv 1
    have hp8 := congrFun hv 2
    simp at hp10 hp9 hp4 hp0 hp3 hp8
    exact ⟨hp0, hp3, hp4, hp8, hp9, hp10⟩
  · rintro ⟨hp0, hp3, hp4, hp8, hp9, hp10⟩
    constructor
    · funext i
      fin_cases i <;> simp [hp4, hp8, hp9, hp10]
    · funext i
      fin_cases i <;> simp [hp0, hp3, hp8]

/-- The parameterized map satisfies the derivation rule; this follows from the
   owner theorem for every parameter, independently of the stabilizer proof. -/
theorem parameterizedMap_is_G2Derivation {p : Params} :
    ∀ (x y : ZornSplitOctonion ℝ),
    zornG2Derivation p (zornMul x y) =
      zornAdd (zornMul (zornG2Derivation p x) y)
              (zornMul x (zornG2Derivation p y)) := by
  intro x y
  exact zornG2Derivation_leibniz p x y

/-- Every parameterized derivation annihilates the identity. -/
theorem parameterizedMap_annihilates_one {p : Params} :
    zornG2Derivation p zornOne = zornZero := by
  exact zornG2Derivation_zornOne p

/-- Every parameterized derivation commutes with the split-octonion conjugation. -/
theorem parameterizedMap_commutes_conj {p : Params} (x : ZornSplitOctonion ℝ) :
    zornG2Derivation p (zornConj x) = zornConj (zornG2Derivation p x) := by
  exact zornG2Derivation_conj p x

/-- The stabilizer equation forces the two scalar Peirce coordinates of its
   value on the selected element to vanish. This is only a coordinate
   consequence; it is not a dimension calculation. -/
theorem stabilizer_scalar_coordinates {p : Params}
    (h : FixesSelectedPeirceIdempotent p) :
    (zornG2Derivation p selectedPeirceIdempotent).a = 0 ∧
    (zornG2Derivation p selectedPeirceIdempotent).b = 0 := by
  have h₁ : zornG2Derivation p selectedPeirceIdempotent = zornZero := h
  have h₂ : (zornG2Derivation p selectedPeirceIdempotent).a = 0 := by
    rw [h₁]
    simp [zornZero]
  have h₃ : (zornG2Derivation p selectedPeirceIdempotent).b = 0 := by
    rw [h₁]
    simp [zornZero]
  exact ⟨h₂, h₃⟩

/-- For every parameter, the scalar Peirce coordinates of the derivation's
   value on `zornE0` vanish. The off-diagonal coordinates are not asserted to
   vanish, so this is not pointwise fixation of the element. -/
theorem zornE0_scalar_coordinates {p : Params} :
    (zornG2Derivation p zornE0).a = 0 ∧
    (zornG2Derivation p zornE0).b = 0 := by
  have h₁ : (zornG2Derivation p zornE0).a = 0 := by
    simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornE0]
    <;>
    (try ext k <;> fin_cases k <;> ring) <;>
    (try funext i <;> fin_cases i <;> ring)
    <;>
    (try simp_all [ZornVec3.basis])
    <;>
    (try norm_num)
  have h₂ : (zornG2Derivation p zornE0).b = 0 := by
    simp [zornG2Derivation, zornVectorMatrixEquiv, zornVectorMatrixToSplitOctonion,
      splitOctonionToZornVectorMatrix, parameterAction, zornE0]
    <;>
    (try ext k <;> fin_cases k <;> ring) <;>
    (try funext i <;> fin_cases i <;> ring)
    <;>
    (try simp_all [ZornVec3.basis])
    <;>
    (try norm_num)
  exact ⟨h₁, h₂⟩

end InfoGeometry.NCG.SplitOctonionPeirceStabilizer
