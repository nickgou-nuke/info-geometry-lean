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
# Imaginary-unit stabilizer predicate for the transported Zorn derivations

This module defines a predicate on the repository's concrete 14-parameter
family of split-octonion derivations and proves only consequences supported by
the owner declarations. It does not identify the parameter subset as a Lie
subalgebra isomorphic to `SU(3)`, prove its dimension, or establish triplet and
antitriplet representation laws. Those classification statements require
additional kernel and representation theorems. -/

namespace InfoGeometry.NCG.GunaydinGurseySU3Stabilizer

open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering

/- The chosen imaginary unit `e₇` as the top-state Peirce component
   `zornE1` (lower-right scalar `b = 1`, all other components zero). -/
def imaginaryUnit : ZornSplitOctonion ℝ := zornE1

/-- Predicate saying that one member of the existing parameterized derivation
   family fixes the selected Zorn element. No group or dimension structure is
   included in this predicate. -/
def FixesChosenImaginaryUnit (p : Params) : Prop :=
  zornG2Derivation p imaginaryUnit = zornZero

/-- The parameterized map satisfies the derivation rule; this follows from the
   owner theorem for every parameter, independently of the stabilizer proof. -/
theorem fixedImaginary_is_G2Derivation {p : Params} :
    ∀ (x y : ZornSplitOctonion ℝ),
    zornG2Derivation p (zornMul x y) =
      zornAdd (zornMul (zornG2Derivation p x) y)
              (zornMul x (zornG2Derivation p y)) := by
  intro x y
  exact zornG2Derivation_leibniz p x y

/-- Every parameterized derivation annihilates the identity. -/
theorem fixedImaginary_annihilates_one {p : Params} :
    zornG2Derivation p zornOne = zornZero := by
  exact zornG2Derivation_zornOne p

/-- Every parameterized derivation commutes with the split-octonion conjugation. -/
theorem fixedImaginary_commutes_conj {p : Params} (x : ZornSplitOctonion ℝ) :
    zornG2Derivation p (zornConj x) = zornConj (zornG2Derivation p x) := by
  exact zornG2Derivation_conj p x

/-- The stabilizer equation forces the two scalar Peirce coordinates of its
   value on the selected element to vanish. This is only a coordinate
   consequence; it is not a dimension calculation. -/
theorem stabilizer_scalar_coordinates {p : Params}
    (h : FixesChosenImaginaryUnit p) :
    (zornG2Derivation p imaginaryUnit).a = 0 ∧
    (zornG2Derivation p imaginaryUnit).b = 0 := by
  have h₁ : zornG2Derivation p imaginaryUnit = zornZero := h
  have h₂ : (zornG2Derivation p imaginaryUnit).a = 0 := by
    rw [h₁]
    simp [zornZero]
  have h₃ : (zornG2Derivation p imaginaryUnit).b = 0 := by
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

end InfoGeometry.NCG.GunaydinGurseySU3Stabilizer
