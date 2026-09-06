import InfoGeometry.Canonical.ThreeColorOperatorSuperBracketClosure

/-!
# The concrete sheet flip on the operator-valued Zorn carrier

This owner records only the algebraic involution that is available for the
native noncommutative carrier.  The carrier has no norm, topology, or
associative Lie structure, so no `C*` or modular-flow statement is made here.
-/

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A]

/-- Exchange the two diagonal and two chiral Zorn sheets. -/
def zornFlipOperator (Z : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨Z.n_minus, Z.n_plus, Z.sigma_minus, Z.sigma_plus⟩

@[simp] theorem zornFlipOperator_involutive
    (Z : OperatorZornMatrix A) :
    zornFlipOperator (zornFlipOperator Z) = Z := by
  cases Z
  rfl

@[simp] theorem zornFlipOperator_nPlus (a : A) :
    zornFlipOperator (nPlus a) = nMinus a := by
  rfl

@[simp] theorem zornFlipOperator_nMinus (a : A) :
    zornFlipOperator (nMinus a) = nPlus a := by
  rfl

@[simp] theorem zornFlipOperator_sigmaPlus (U : OperatorVector A) :
    zornFlipOperator (sigmaPlus U) = sigmaMinus U := by
  rfl

@[simp] theorem zornFlipOperator_sigmaMinus (U : OperatorVector A) :
    zornFlipOperator (sigmaMinus U) = sigmaPlus U := by
  rfl

@[simp] theorem zornFlipOperator_coordinates
    (a b : A) (u v : OperatorVector A) :
    zornFlipOperator (operatorZornCoordinates a b u v) =
      operatorZornCoordinates b a v u := by
  rfl

@[simp] theorem zornFlipOperator_chiralOperatorZorn
    (u v : OperatorVector A) :
    zornFlipOperator (chiralOperatorZorn u v) =
      operatorZornCoordinates 0 0 v u := by
  rfl

theorem zornFlipOperator_operatorAdd (X Y : OperatorZornMatrix A) :
    zornFlipOperator (operatorAdd X Y) =
      operatorAdd (zornFlipOperator X) (zornFlipOperator Y) := by
  cases X
  cases Y
  rfl

end InfoGeometry.Canonical
