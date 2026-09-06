import InfoGeometry.Optics.OperatorCausalFramework
import InfoGeometry.Physics.BogoliubovPauliSolderedFrame

/-!
# Real-to-complex Bogoliubov/Pauli operator bridge

The Bogoliubov/Pauli owner is real-valued.  The operator-valued causal owner
is complex-valued.  This file supplies the explicit scalar-extension map from
the former to `M₂(End ℂ W)` and proves its carrier action.  It does not assert
that an arbitrary real frame is a spin connection.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorBogoliubovPauliBridge

open InfoGeometry.Clifford
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Physics.BogoliubovPauliSolderedFrame

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev EndW (W : Type*) [AddCommGroup W] [Module ℂ W] := Module.End ℂ W
abbrev OperatorMatrix (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (EndW W)
abbrev RealPauliVector := InfoGeometry.Clifford.Soldering.Vec22
abbrev RealPauliMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- Scalar extension of a real `2 × 2` matrix to operator coefficients. -/
def complexifyMatrix {W : Type*} [AddCommGroup W] [Module ℂ W]
    (M : RealPauliMatrix) : OperatorMatrix W :=
  fun i j => algebraMap ℝ (EndW W) (M i j)

@[simp] theorem complexifyMatrix_apply
    (M : RealPauliMatrix) (i j : Fin 2) :
    complexifyMatrix (W := W) M i j = algebraMap ℝ (EndW W) (M i j) :=
  rfl

/-- The complexified Pauli frame attached to the existing real soldering owner. -/
def complexifiedPauliFrame (v : RealPauliVector) : OperatorMatrix W :=
  complexifyMatrix (W := W) (pauliTetradSoldering v)

@[simp] theorem complexifiedPauliFrame_apply
    (v : RealPauliVector) (i j : Fin 2) :
    complexifiedPauliFrame (W := W) v i j =
      algebraMap ℝ (EndW W) (pauliTetradSoldering v i j) :=
  rfl

/-- The scalar-extended frame acts on the doubled internal carrier by matrix action. -/
def complexifiedPauliFrameAction (v : RealPauliVector) :
    Module.End ℂ (Fin 2 → W) :=
  matrixAction (complexifiedPauliFrame (W := W) v)

@[simp] theorem complexifiedPauliFrameAction_apply
    (v : RealPauliVector) (ψ : Fin 2 → W) (i : Fin 2) :
    complexifiedPauliFrameAction (W := W) v ψ i =
      ∑ j : Fin 2,
        algebraMap ℝ (EndW W) (pauliTetradSoldering v i j) (ψ j) := by
  rw [complexifiedPauliFrameAction, matrixAction_apply]
  rfl

@[simp] theorem complexifiedPauliFrame_zero :
    complexifiedPauliFrame (W := W) 0 = 0 := by
  ext i j
  simp [complexifiedPauliFrame, complexifyMatrix]

end InfoGeometry.Optics.OperatorBogoliubovPauliBridge
