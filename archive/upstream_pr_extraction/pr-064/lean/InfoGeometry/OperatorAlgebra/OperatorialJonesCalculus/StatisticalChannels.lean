import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus.PolarizationProjectors

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## 4. Statistical channel layer -/

/--
A statistical polarization channel.

This is the Jones-to-Mueller upgrade: one no longer has a single coherent
operator, but a family of scattering operators.
-/
structure PolarizationChannel
    (Op : Type*) [Ring Op] where
  /-- Index of scattering/Jones branches. -/
  Branch : Type*

  /-- Branch operator. -/
  branchOp : Branch → Op

  /-- Abstract adjoint. -/
  adj : Op → Op

  /-- Channel action. -/
  channel : Op → Op


/-- Rough reflection is represented by the native statistical channel carrier. -/
abbrev RoughReflectionChannel
    (Op : Type*) [Ring Op] := PolarizationChannel Op

abbrev RoughReflectionChannel.toPolarizationChannel
    {Op : Type*} [Ring Op]
    (R : RoughReflectionChannel Op) : PolarizationChannel Op := R

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
