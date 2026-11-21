/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

/-!
# InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue

Explicit commutator coordinates of the two ordered Weyl curvature blocks.

The parent owner proves that an operator-valued Weyl odd square has diagonal
blocks `σ(A) \barσ(A)` and `\barσ(A) σ(A)`.  This file expands those blocks
without assigning a geometric self-duality label.  Every departure from the
scalar Minkowski quadratic channel is written as an actual commutator of
operator coefficients.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue

open Matrix
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Canonical.OperatorWeylChiralCurvatureBlocks

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW (W : Type*) [AddCommGroup W] [Module ℂ W] := Module.End ℂ W
abbrev OperatorMat2 (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (EndW W)

/-- Ring commutator of operator coefficients. -/
def opComm (x y : EndW W) : EndW W := x * y - y * x

/-- Symmetric Minkowski quadratic channel of an operator-valued four-vector. -/
def operatorMinkowskiQuadratic (v : OperatorFourVector W) : EndW W :=
  v 0 * v 0 - v 1 * v 1 - v 2 * v 2 - v 3 * v 3

/-- Scalar `2×2` operator block. -/
def scalarOperatorBlock (q : EndW W) : OperatorMat2 W :=
  !![q, 0; 0, q]

end InfoGeometry.Canonical.OperatorWeylChiralCurvatureResidue
