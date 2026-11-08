/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorProjectiveLimitTopCat
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Finite-prefix readouts on the projective limit

Finite prefix words carry finite readout observables.  This owner packages
those observables as `TopCat` maps and composes them with the coherent-prefix
projections.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitFiniteReadoutTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat

def finitePrefixReadoutTopCatHom (n : ℕ) :
    TopCat.of (BitWord n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun w => finitePrefixReadout (List.ofFn w)
      continuous_toFun := by fun_prop }

def projectiveFinitePrefixReadoutTopCatHom (n : ℕ) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of ℝ :=
  projectiveProjectionTopCatHom n ≫ finitePrefixReadoutTopCatHom n

@[simp] theorem finitePrefixReadoutTopCatHom_apply
    (n : ℕ) (w : BitWord n) :
    finitePrefixReadoutTopCatHom n w = finitePrefixReadout (List.ofFn w) := rfl

@[simp] theorem projectiveFinitePrefixReadoutTopCatHom_apply
    (n : ℕ) (p : PrefixProjectiveLimit) :
    projectiveFinitePrefixReadoutTopCatHom n p =
      finitePrefixReadout (List.ofFn (π n p)) := by
  rfl

theorem projectiveFinitePrefixReadout_cantor_compatibility
    (n : ℕ) (x : CantorBoundary) :
    projectiveFinitePrefixReadoutTopCatHom n
        (cantorProjectiveLimitTopCatIso.hom x) =
      finitePrefixReadout (List.ofFn (boundaryPrefix n x)) := by
  change (projectiveProjectionTopCatHom n ≫
      finitePrefixReadoutTopCatHom n)
      (cantorProjectiveLimitTopCatIso.hom x) = _
  rw [TopCat.comp_app]
  change finitePrefixReadout
      (List.ofFn (π n (cantorProjectiveLimitTopCatIso.hom x))) = _
  have h := cantorProjectiveLimit_projection_readout n x
  exact congrArg (fun w => finitePrefixReadout (List.ofFn w)) h

/-! The finite-cylinder carrier and the projective-limit observable are the
same readout after the canonical reconstruction of a Cantor stream. -/

theorem cylinder_toCantor_eq_projective_projection
    (n : ℕ) (f : DiagAlg n) (p : PrefixProjectiveLimit) :
    cylinder n f (toCantor p) = f (π n p) := by
  rw [cylinder_apply, boundaryPrefix_toCantor_eq_word, π_apply]

end InfoGeometry.Canonical.CantorProjectiveLimitFiniteReadoutTopCat
