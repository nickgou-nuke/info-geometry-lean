import InfoGeometry.Canonical.RelativeSurprisalOperatorLift

/-!
# Finite relative surprisal as an operator

The relative surprisal is not represented here by a scalar density ratio.
The maintained finite owner is the matrix-valued relative modular-potential
operator from `RelativeSurprisalOperatorLift`.  Its diagonal entries are the
negative logarithmic readout of the finite relative modular operator, while
its cocycle laws are inherited from the projective relative-state owner.

This file is only a namespace bridge.  It does not claim a general measure
Radon--Nikodym theorem, an unbounded modular operator, or a scalar KL identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.RelativeSurprisalRadonNikodym

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

variable {n : ℕ} [Nonempty (Fin n)]

abbrev FiniteRelativeSurprisalOperator (n : ℕ) :=
  InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal.FinMat n

noncomputable abbrev relativeSurprisalOperator
    (q q0 : PositiveRay (Fin n)) : FiniteRelativeSurprisalOperator n :=
  relativeModularPotentialOperator (n := n) q q0

theorem relativeSurprisalOperator_diag
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeSurprisalOperator (n := n) q q0 i i =
      -Real.log (relativeModularOperator (n := n) q q0 i i) :=
  relativeModularPotentialOperator_diag_eq_neg_log_relativeModularOperator_diag q q0 i

theorem relativeSurprisalOperator_readout
    (q q0 : PositiveRay (Fin n)) :
    relativeSurprisalOperator (n := n) q q0 =
      relativeModularPotentialOperator (n := n) q q0 :=
  rfl

end InfoGeometry.Canonical.RelativeSurprisalRadonNikodym
