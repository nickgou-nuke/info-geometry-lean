import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.FractalFockEquivalenceBridge

Infinite Celik--Kocak fractal lane:

`L²(K) -> Cl∞ -> Fock representation`.

This module keeps the equivalence with the classical Fock representation as an
explicit witness.  It does not reconstruct the analytic `L²(K)` model or prove
unitary equivalence internally.
-/

noncomputable section

namespace InfoGeometry.Canonical.FractalFockEquivalenceBridge

open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

/-- The verified algebraic content of the fractal/Fock bridge.

The carrier records the infinite Cantor--Clifford representation.  An analytic
equivalence with an `L²` Fock model is deliberately not part of this owner,
because no such equivalence is available in the present formal development.
-/
structure FractalFockEquivalenceBridge
    (Op : Type*) [Ring Op] where
  clifford : CantorCliffordRepresentation Op

abbrev FractalFockBridge (Op : Type*) [Ring Op] :=
  FractalFockEquivalenceBridge Op

namespace FractalFockBridge

variable {Op : Type*} [Ring Op]
variable (B : FractalFockBridge Op)

/-- Re-export: the infinite bridge is carried by a Cantor Clifford representation. -/
@[rep_depth operator]
def cliffordRepresentation : CantorCliffordRepresentation Op :=
  B.clifford

/-- Re-export: infinite Clifford generators square to one. -/
@[rep_depth operator]
theorem gamma_sq (i : ℕ) :
    B.clifford.gamma i * B.clifford.gamma i = 1 :=
  B.clifford.gamma_sq i

/-- Re-export: distinct infinite Clifford generators anticommute. -/
@[rep_depth operator]
theorem gamma_anticomm {i j : ℕ} (hij : i ≠ j) :
    B.clifford.gamma i * B.clifford.gamma j +
      B.clifford.gamma j * B.clifford.gamma i = 0 := by
  rw [B.clifford.gamma_anticomm i j hij]
  simp

end FractalFockBridge

end InfoGeometry.Canonical.FractalFockEquivalenceBridge
