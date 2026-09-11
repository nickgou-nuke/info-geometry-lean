import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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


/--
Rough reflection belongs to the channel/Mueller layer, not the pure Jones
single-operator layer.
-/
structure RoughReflectionChannel
    (Op : Type*) [Ring Op]
    extends PolarizationChannel Op where

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
