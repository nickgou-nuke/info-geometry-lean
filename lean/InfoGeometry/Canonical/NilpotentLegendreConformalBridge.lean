import Mathlib
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Canonical.PrimeCl11ModularAtom
import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Convex.Legendre
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.NilpotentLegendreConformalBridge

Nilpotent translation, Legendre duality, conformal chart, and doubled-real
`Cl(1,1)` boosting on the same owner packet.

This bridge is intentionally theorem-safe:

* the nilpotent translation is an explicit square-zero operator field;
* the conformal chart is an explicit Legendre-potential readout;
* the dual-flat affine chart is its derivative coordinate readout;
* the doubled Majorana lift and `Cl(1,1)` atom are carried by existing root
  owners;
* the boost action is the existing `Cl11LorentzAction` modular flow.

The file does not claim any new analytic theorem about nilpotent exponentials
or affine geometry beyond the supplied compatibility data.
-/

noncomputable section

namespace NilpotentLegendreConformalBridge

open InfoGeometry.Core
open InfoGeometry.Convex
open InfoGeometry.Canonical.PrimeCl11ModularAtom
open InfoGeometry.Canonical.Cl11LorentzAction
open InfoGeometry.Krein

set_option linter.dupNamespace false

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance

/--
Nilpotent/Legendre conformal bridge packet.

The doubled-real Majorana lift and the split `Cl(1,1)` atom are carried as
data.  The nilpotent translation and the conformal/dual-flat charts are the
bridge's explicit operatorial and convex readouts.
-/
structure NilpotentLegendreConformalBridge where
  /-- Doubled-real Majorana lift. -/
  majorana : MajoranaLiftPacket (E := E)

  /-- Local `Cl(1,1)` atom on the doubled-real carrier. -/
  atom : Cl11Atom EndH

  /-- Square-zero translation operator on the doubled carrier. -/
  nilpotentTranslation : EndH

  /-- Nilpotent translation squares to zero. -/
  nilpotentTranslation_sq_zero :
    nilpotentTranslation * nilpotentTranslation = 0

  /-- Legendre potential used as the conformal chart. -/
  legendrePotential : LegendrePotential

  /-- Conformal chart readout. -/
  conformalChart : ℝ → ℝ

  /-- Dual-flat affine chart readout. -/
  dualFlatChart : ℝ → ℝ

  /-- The conformal chart is the Legendre transform of the chosen potential. -/
  conformalChart_eq_legendre :
    conformalChart = LegendrePotential.legendreTransform legendrePotential

  /-- The dual-flat chart is the derivative coordinate of the chosen potential. -/
  dualFlatChart_eq_deriv :
    ∀ θ : ℝ, dualFlatChart θ = deriv legendrePotential.f θ

  /-- Split `Cl(1,1)` boost action on the doubled carrier. -/
  boost : InfoGeometry.Quantum.RealSplitCl11Action H₂

  /--
  Boost transport of the nilpotent translation.

  This keeps the boost action and the square-zero translation on the same
  carrier without asserting a new nilpotent-flow theorem.
  -/
  boostedNilpotentTranslation : ℝ → EndH

  /-- The boosted translation is the conjugate of the nilpotent generator. -/
  boostedNilpotentTranslation_eq :
    ∀ t : ℝ,
      boostedNilpotentTranslation t =
        modularFlow boost t * nilpotentTranslation * modularFlow boost (-t)

namespace NilpotentLegendreConformalBridge

variable (B : NilpotentLegendreConformalBridge (E := E))

/-- The nilpotent translation is square-zero. -/
@[simp]
theorem nilpotentTranslation_sq_zero_readback :
    B.nilpotentTranslation * B.nilpotentTranslation = 0 :=
  B.nilpotentTranslation_sq_zero

/-- The conformal chart is the Legendre transform of the chosen potential. -/
theorem conformalChart_eq_legendreTransform_readback :
    B.conformalChart =
      LegendrePotential.legendreTransform B.legendrePotential :=
  B.conformalChart_eq_legendre

/-- The dual-flat chart is the derivative coordinate of the chosen potential. -/
theorem dualFlatChart_eq_deriv_readback (θ : ℝ) :
    B.dualFlatChart θ = deriv B.legendrePotential.f θ :=
  B.dualFlatChart_eq_deriv θ

/-- The boosted nilpotent translation is the stated conjugate transport. -/
theorem boostedNilpotentTranslation_eq_readback (t : ℝ) :
    B.boostedNilpotentTranslation t =
      modularFlow B.boost t * B.nilpotentTranslation * modularFlow B.boost (-t) :=
  B.boostedNilpotentTranslation_eq t

/-- The local `Cl(1,1)` atom carries the doubled-real Majorana square law. -/
theorem atom_mobiusParity_sq_eq_one_readback :
    (Cl11Atom.mobiusParity B.atom) * (Cl11Atom.mobiusParity B.atom) = 1 :=
  Cl11Atom.mobiusParity_sq_eq_one B.atom

end NilpotentLegendreConformalBridge

end Core

end NilpotentLegendreConformalBridge
