/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.NumberField.DedekindZeta
import InfoGeometry.Arithmetic.NumberFieldHeckeLFunction

/-!
# Generalized Riemann hypothesis contracts

This file records the exact generalized zero-location propositions used by the
Riemann--Masullo project, on this repository's actual Dedekind-zeta and Hecke
`L`-series carriers.  They are contracts, not proofs of GRH.

The formulations are adapted from `Statements.lean` in
`mccorvie/riemann-masullo`, revision `be5d4cb0356d48406eae83233d73c99085b9a038`
(Apache-2.0).  The external project's `Main.lean` still leaves these headline
claims unproved, so these definitions deliberately expose the missing analytic
continuation and zero-location obligations rather than hiding them behind an
axiom or placeholder theorem.
-/

noncomputable section

open NumberField

namespace InfoGeometry.Arithmetic.GeneralizedRiemannHypothesisContracts

/-- GRH for Dedekind zeta: every zero of any meromorphic continuation in the
critical strip has real part `1/2`. -/
def DedekindZetaZerosOnLine : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ),
    MeromorphicOn f Set.univ →
      (∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) →
        ∀ s : ℂ, 0 < s.re → s.re < 1 →
          0 < meromorphicOrderAt f s → s.re = 1 / 2

/-- GRH for Hecke `L`-series: every zero of any meromorphic continuation of a
unitary character's series in the critical strip lies on the critical line. -/
def HeckeLZerosOnLine : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (χ : HeckeCharacter (𝓞 K) K),
    (∀ x, ‖χ x‖ = 1) →
      ∀ f : ℂ → ℂ, MeromorphicOn f Set.univ →
        (∀ s : ℂ, 1 < s.re → f s = χ.LSeries s) →
          ∀ s : ℂ, 0 < s.re → s.re < 1 →
            0 < meromorphicOrderAt f s → s.re = 1 / 2

end InfoGeometry.Arithmetic.GeneralizedRiemannHypothesisContracts
