import InfoGeometry.Canonical.RealTomitaCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ModularSpectralWedge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Abstract spectral wedge decomposition for a modular generator on the owned
doubled carrier.
-/
@[rep_depth transport]
structure HasModularSpectralWedge
    (E : Type 0)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  PiPlus : DoubledSpace E →L[ℝ] DoubledSpace E
  PiMinus : DoubledSpace E →L[ℝ] DoubledSpace E
  PZero : DoubledSpace E →L[ℝ] DoubledSpace E

  PiPlus_idem : PiPlus * PiPlus = PiPlus
  PiMinus_idem : PiMinus * PiMinus = PiMinus
  PZero_idem : PZero * PZero = PZero

  PiPlus_PiMinus : PiPlus * PiMinus = 0
  PiMinus_PiPlus : PiMinus * PiPlus = 0

  PiPlus_PZero : PiPlus * PZero = 0
  PZero_PiPlus : PZero * PiPlus = 0

  PiMinus_PZero : PiMinus * PZero = 0
  PZero_PiMinus : PZero * PiMinus = 0

  resolution :
    PiPlus + PiMinus + PZero = (1 : DoubledSpace E →L[ℝ] DoubledSpace E)

namespace HasModularSpectralWedge

variable (W : HasModularSpectralWedge E)

/-- Spectral sign operator on the active hyperbolic wedge sector. -/
@[rep_depth transport]
noncomputable def wedgeSign : EndH :=
  W.PiPlus - W.PiMinus

/-- Active projector on the hyperbolic sector. -/
@[rep_depth transport]
noncomputable def activeProjector : EndH :=
  W.PiPlus + W.PiMinus

/--
The wedge sign squares to the identity on the active sector:
`wedgeSign^2 = 1 - PZero`.
-/
@[rep_depth transport]
theorem wedgeSign_sq :
    W.wedgeSign * W.wedgeSign = (1 : EndH) - W.PZero := by
  have hExpand :
      W.wedgeSign * W.wedgeSign
        =
      W.PiPlus * W.PiPlus
        - W.PiPlus * W.PiMinus
        - W.PiMinus * W.PiPlus
        + W.PiMinus * W.PiMinus := by
    unfold wedgeSign
    simp [sub_eq_add_neg, add_mul, mul_add]
    abel
  have hRes :
      W.PiPlus + W.PiMinus = (1 : EndH) - W.PZero := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_assoc] using W.resolution
  calc
    W.wedgeSign * W.wedgeSign
        =
      W.PiPlus * W.PiPlus
        - W.PiPlus * W.PiMinus
        - W.PiMinus * W.PiPlus
        + W.PiMinus * W.PiMinus := hExpand
    _ = W.PiPlus - 0 - 0 + W.PiMinus := by
          rw [W.PiPlus_idem, W.PiMinus_idem, W.PiPlus_PiMinus, W.PiMinus_PiPlus]
    _ = W.PiPlus + W.PiMinus := by abel
    _ = (1 : EndH) - W.PZero := hRes

/-- Equivalent form: the square is the active projector. -/
@[rep_depth transport]
theorem wedgeSign_sq_eq_activeProjector :
    W.wedgeSign * W.wedgeSign = W.activeProjector := by
  unfold activeProjector
  have hRes :
      W.PiPlus + W.PiMinus = (1 : EndH) - W.PZero := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_assoc] using W.resolution
  calc
    W.wedgeSign * W.wedgeSign = (1 : EndH) - W.PZero := W.wedgeSign_sq
    _ = W.PiPlus + W.PiMinus := hRes.symm

end HasModularSpectralWedge

end Core

end InfoGeometry.Canonical.ModularSpectralWedge
