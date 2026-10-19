/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
import InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimitBlocks

/-!
# Concrete chiral Dirac blocks on the Hestenes colimit

The finite Hestenes phase commutes with the concrete chirality operator.  The
generic colimit block theorem therefore applies without a basis identification
or an analytic completion hypothesis.
-/

namespace InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimitBlocks

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimit
open InfoGeometry.Canonical.ChiralHodgeDiracFilteredColimitBlocks
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

theorem phaseColimit_commutes_chiralDiracPlus
    (v : V3) (φ : Module.Dual ℝ V3) :
    colimitPhaseEnd (concreteHestenesDatum v φ) *
        colimitChiralDiracPlus (concreteHestenesDatum v φ).toDatum =
      colimitChiralDiracPlus (concreteHestenesDatum v φ).toDatum *
        colimitPhaseEnd (concreteHestenesDatum v φ) := by
  let D := concreteHestenesDatum v φ
  let C : ChiralHestenesDatum (F := constantDoubledExterior3Functor) :=
    { toHestenesDatum := D
      phase_chirality := by
        ext j x
        simpa [D, concreteHestenesDatum, constantEndNatTrans,
          ModuleCat.comp_apply] using
          (congrArg (fun T => T x) concreteHestenesPhase_chirality_commutes).symm }
  have h := colimitPhaseEnd_commutes_chiralDiracPlus C
  simpa [D, C, colimitPhaseEnd, colimitChiralDiracPlus] using h

theorem phaseColimit_commutes_chiralDiracMinus
    (v : V3) (φ : Module.Dual ℝ V3) :
    colimitPhaseEnd (concreteHestenesDatum v φ) *
        colimitChiralDiracMinus (concreteHestenesDatum v φ).toDatum =
      colimitChiralDiracMinus (concreteHestenesDatum v φ).toDatum *
        colimitPhaseEnd (concreteHestenesDatum v φ) := by
  let D := concreteHestenesDatum v φ
  let C : ChiralHestenesDatum (F := constantDoubledExterior3Functor) :=
    { toHestenesDatum := D
      phase_chirality := by
        ext j x
        simpa [D, concreteHestenesDatum, constantEndNatTrans,
          ModuleCat.comp_apply] using
          (congrArg (fun T => T x) concreteHestenesPhase_chirality_commutes).symm }
  have h := colimitPhaseEnd_commutes_chiralDiracMinus C
  simpa [D, C, colimitPhaseEnd, colimitChiralDiracMinus] using h

end InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimitBlocks
