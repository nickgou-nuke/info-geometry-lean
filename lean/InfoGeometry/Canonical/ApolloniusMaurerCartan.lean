/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-
# Apollonius global Maurer--Cartan connection

The intrinsic connection is written from the single-valued rational
Maurer--Cartan form q⁻¹ dq of the Cayley coordinate
q(s) = s / (1-s). No global logarithm is introduced.

The period/holonomy statements are kept cycle-indexed. The source and sink
generator holonomies are supplied by the existing finite winding owner; their
composite is proved separately. This file does not identify a contour
integral at the second puncture without an additional orientation theorem.
-/

import Mathlib.Tactic
import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import InfoGeometry.Canonical.ApolloniusPauliConnectionBridge

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusMaurerCartan

open InfoGeometry.Apollonius
open InfoGeometry.Canonical.ApolloniusPauliConnectionBridge
open InfoGeometry.Canonical.ApolloniusWindingFluxBridge

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- The differential of q(s) = s / (1-s) applied to a complex tangent. -/
def cayleyDerivative (s : PuncturedPlane) (v : ℂ) : ℂ :=
  v / (1 - s.1) ^ 2

/-- The rational global Maurer--Cartan form q⁻¹ dq. -/
def qInvDq (s : PuncturedPlane) (v : ℂ) : ℂ :=
  (crossRatio s)⁻¹ * cayleyDerivative s v

/-- Rational expression for q⁻¹dq; it has no logarithmic branch. -/
theorem qInvDq_eq_rational (s : PuncturedPlane) (v : ℂ) :
    qInvDq s v = v / (s.1 * (1 - s.1)) := by
  unfold qInvDq cayleyDerivative crossRatio
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.cayleyToFugacity
  field_simp [s.property.1, sub_ne_zero.mpr (Ne.symm s.property.2)]

@[simp]
theorem qInvDq_add (s : PuncturedPlane) (v w : ℂ) :
    qInvDq s (v + w) = qInvDq s v + qInvDq s w := by
  rw [qInvDq_eq_rational, qInvDq_eq_rational, qInvDq_eq_rational, add_div]

@[simp]
theorem qInvDq_smul (s : PuncturedPlane) (a v : ℂ) :
    qInvDq s (a • v) = a • qInvDq s v := by
  rw [qInvDq_eq_rational, qInvDq_eq_rational]
  change (a * v) / _ = a * (v / _)
  exact mul_div_assoc a v _

/-- The global Cartan connection A = (1/2) sigma3 q⁻¹dq. -/
def globalConnection (s : PuncturedPlane) (v : ℂ) : Mat2C :=
  cartanConnectionValue (qInvDq s v)

/-- Exact coefficient form of the global connection. -/
theorem globalConnection_eq_half_sigma3_qInvDq
    (s : PuncturedPlane) (v : ℂ) :
    globalConnection s v =
      (qInvDq s v / 2) •
        InfoGeometry.Canonical.PauliBraidB3.sigma3 := by
  rfl

/-- All values lie on the same Cartan axis, hence the algebraic
Maurer--Cartan commutator term vanishes. -/
theorem globalConnection_commutator_zero
    (s : PuncturedPlane) (v w : ℂ) :
    commutator (globalConnection s v) (globalConnection s w) = 0 := by
  rw [globalConnection, globalConnection, cartanConnectionValue_commutator]

/-- The finite algebraic curvature readout of the global connection. -/
def curvatureReadout (dA : Mat2C) (s : PuncturedPlane) (v w : ℂ) : Mat2C :=
  dA + commutator (globalConnection s v) (globalConnection s w)

/-- Closedness of the coefficient form reduces curvature to zero in the
one-axis Cartan realization. -/
theorem curvatureReadout_eq_zero_of_closed
    (dA : Mat2C) (hdA : dA = 0)
    (s : PuncturedPlane) (v w : ℂ) :
    curvatureReadout dA s v w = 0 := by
  rw [curvatureReadout, globalConnection_commutator_zero, hdA]
  simp

/-- The two fundamental puncture-cycle labels. -/
inductive FundamentalCycle
  | source
  | sink
deriving DecidableEq

/-- The existing finite winding realization assigns one unit logarithmic
period to each generator cycle. -/
def cyclePeriod (R : ℝ) : FundamentalCycle → ℂ
  | .source => quantizedWindingFlux R 1
  | .sink => quantizedWindingFlux R 1

/-- Half-weight spin holonomy attached to a fundamental cycle. -/
def cycleHolonomy (R : ℝ) : FundamentalCycle → Mat2C
  | .source => spinHolonomyMatrix R
  | .sink => spinHolonomyMatrix R

/-- Both fundamental cycles have the explicitly proved 2 pi i period. -/
theorem cyclePeriod_eq_two_pi_mul_I
    (R : ℝ) (hR : 0 < R) (c : FundamentalCycle) :
    cyclePeriod R c = (2 * Real.pi * Complex.I : ℂ) := by
  cases c <;> simp [cyclePeriod, quantizedWindingFlux_eq_two_pi_mul_I R hR 1]

/-- Source-cycle holonomy is -I₂. -/
theorem holonomy_gamma0_eq_neg_identity
    (R : ℝ) (hR : 0 < R) :
    cycleHolonomy R .source = -(1 : Mat2C) :=
  spinHolonomyMatrix_eq_neg_identity R hR

/-- Sink-cycle holonomy is represented by the same local half-weight
winding owner. Equality with a geometric sink contour is intentionally not
asserted here. -/
theorem holonomy_gamma1_eq_neg_identity
    (R : ℝ) (hR : 0 < R) :
    cycleHolonomy R .sink = -(1 : Mat2C) :=
  spinHolonomyMatrix_eq_neg_identity R hR

/-- The composite of the two fundamental cycle holonomies is trivial. -/
theorem holonomy_gamma0_add_gamma1_eq_identity
    (R : ℝ) (hR : 0 < R) :
    cycleHolonomy R .source * cycleHolonomy R .sink = (1 : Mat2C) := by
  rw [holonomy_gamma0_eq_neg_identity R hR,
    holonomy_gamma1_eq_neg_identity R hR]
  simp

end InfoGeometry.Canonical.ApolloniusMaurerCartan
