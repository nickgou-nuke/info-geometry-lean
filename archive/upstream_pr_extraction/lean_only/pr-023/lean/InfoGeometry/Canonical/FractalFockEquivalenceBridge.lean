import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

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

/-- Public infinite fractal/Fock bridge alias. -/
abbrev FractalFockBridge
    (Op : Type*) [Ring Op] :=
  FractalFockEquivalenceBridge Op

namespace FractalFockBridge

variable {Op : Type*} [Ring Op]
variable (B : FractalFockBridge Op)

/-- Re-export: the infinite bridge is carried by a Cantor Clifford representation. -/
@[rep_depth operator]
def cliffordRepresentation : CantorCliffordRepresentation Op :=
  B.clifford

/-- The fractal/Fock equivalence proposition carried by this owner lane. -/
@[rep_depth operator]
def equivalence_witness_statement : Prop :=
  B.equivalenceWitness

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
