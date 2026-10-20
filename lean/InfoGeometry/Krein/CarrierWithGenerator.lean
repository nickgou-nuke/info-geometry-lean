/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.CarrierTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Carrier With Generator

This module defines the operatorial generators attached to the carrier 
and its transport flow.
-/

namespace InfoGeometry.Krein

/-- A carrier equipped with a static operatorial generator. -/
abbrev CarrierWithGenerator (X : InvolutiveSelfDualCarrier) :=
  X.H →L[ℝ] X.H

namespace CarrierWithGenerator

abbrev generator (G : CarrierWithGenerator X) : X.H →L[ℝ] X.H := G

def mk (generator : X.H →L[ℝ] X.H) : CarrierWithGenerator X :=
  generator

end CarrierWithGenerator

/-- A transport flow equipped with its infinitesimal generator. -/
abbrev CarrierTransportWithGenerator
    (X : InvolutiveSelfDualCarrier)
    (T : CarrierTransport X) :=
  X.H →L[ℝ] X.H

namespace CarrierTransportWithGenerator

abbrev infinitesimalGenerator
    (G : CarrierTransportWithGenerator X T) : X.H →L[ℝ] X.H := G

def mk (infinitesimalGenerator : X.H →L[ℝ] X.H) :
    CarrierTransportWithGenerator X T :=
  infinitesimalGenerator

end CarrierTransportWithGenerator

namespace CarrierWithGenerator

variable {X : InvolutiveSelfDualCarrier} (G : CarrierWithGenerator X)

/-- The generator is 'odd' (Fermionic) relative to the J-grading. -/
def IsOdd : Prop := X.J.comp G.generator = -(G.generator.comp X.J)

/-- The generator is 'even' (Bosonic) relative to the J-grading. -/
def IsEven : Prop := X.J.comp G.generator = G.generator.comp X.J

theorem odd_square_isEven (hG : G.IsOdd) :
    (CarrierWithGenerator.mk (G.generator.comp G.generator)).IsEven := by
  change X.J.comp G.generator = -(G.generator.comp X.J) at hG
  change X.J.comp (G.generator.comp G.generator) =
    (G.generator.comp G.generator).comp X.J
  calc
    X.J.comp (G.generator.comp G.generator) =
        (X.J.comp G.generator).comp G.generator := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (-(G.generator.comp X.J)).comp G.generator := by rw [hG]
    _ = -(G.generator.comp (X.J.comp G.generator)) := by
          rw [ContinuousLinearMap.neg_comp, ← ContinuousLinearMap.comp_assoc]
    _ = -(G.generator.comp (-(G.generator.comp X.J))) := by rw [hG]
    _ = (G.generator.comp G.generator).comp X.J := by
          rw [ContinuousLinearMap.comp_neg]
          simp only [neg_neg]
          rw [ContinuousLinearMap.comp_assoc]

end CarrierWithGenerator

end InfoGeometry.Krein
