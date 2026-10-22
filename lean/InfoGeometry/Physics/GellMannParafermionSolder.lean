/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain

/-!
# Gell-Mann parafermion solder — theorem-honest carrier

This file keeps only the finite linear-algebraic readout used by downstream
Cantor-boundary examples.  It does not assert an `SU(3)` soldering theorem, a
Bogoliubov theorem, or a parafermion/Cuntz universal-property theorem without
explicit hypotheses.
-/

noncomputable section

namespace InfoGeometry.Physics.GellMannParafermionSolder

/-- Minimal realization data: three color components and a singlet component in
an arbitrary target carrier. -/
structure ParafermionRealization (V : Type*) where
  color : Fin 3 → V
  singlet : V

/-- Read out the spinor carried by a realization. -/
def realizedParafermionColorSpinor4 {V : Type*} (R : ParafermionRealization V) :
    InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ColorSpinor4 V :=
  (R.color, R.singlet)

/-- Matrix action on the color lane; the singlet lane is sent to zero. -/
def colorLieAction4 {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (A : InfoGeometry.Algebra.FiniteSpin.Mat3C)
    (ψ : InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ColorSpinor4 V) :
      InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ColorSpinor4 V :=
  (fun i => ∑ j : Fin 3, A i j • ψ.1 j, 0)

/-- The solder readout is the coefficient-matrix action on realized color data. -/
def gellMannParafermionSolder {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : ParafermionRealization V) (A : InfoGeometry.Algebra.FiniteSpin.Mat3C) :
      InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain.ColorSpinor4 V :=
  colorLieAction4 A (realizedParafermionColorSpinor4 R)

/-- The matrix color action leaves the singlet output at zero by definition. -/
theorem gellMannParafermionSolder_singlet_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (R : ParafermionRealization V) (A : InfoGeometry.Algebra.FiniteSpin.Mat3C) :
    (gellMannParafermionSolder R A).2 = 0 := by
  rfl

end InfoGeometry.Physics.GellMannParafermionSolder

end noncomputable section
