import Mathlib.Tactic.Ring
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Thermo.SplitChiralPolarizationBasis

Proof-only chiral polarization basis on the split-complex temperature plane.

This module is the split-signature analogue of
`ComplexCircularPolarizationBasis`.  It installs only the finite algebraic
content:

* a split rapidity coordinate `(sigma, tau)`,
* light-cone coordinates `u = sigma + tau` and `v = sigma - tau`,
* reconstruction of `(sigma, tau)` from `(u, v)`,
* componentwise Boltzmann exponents on the two chiral idempotent lanes,
* re-export of the `Cl(1,1)` idempotent projector laws.

No analytic continuation, no zero theorem, and no CFT central-charge theorem is
claimed here.
-/

noncomputable section

namespace InfoGeometry.Thermo.SplitChiralPolarizationBasis

open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors

/-- Split-complex rapidity coordinate `sigma + j tau`, stored as real data. -/
@[rep_depth thermo]
structure SplitRapidity where
  sigma : ℝ
  tau : ℝ

namespace SplitRapidity

/-- Left-moving light-cone coordinate `u = sigma + tau`. -/
@[rep_depth thermo]
def leftCoord (s : SplitRapidity) : ℝ :=
  s.sigma + s.tau

/-- Right-moving light-cone coordinate `v = sigma - tau`. -/
@[rep_depth thermo]
def rightCoord (s : SplitRapidity) : ℝ :=
  s.sigma - s.tau

/-- Recover `sigma` from the two light-cone coordinates. -/
@[bridge_target_tag, rep_depth thermo]
theorem sigma_eq_half_left_add_right (s : SplitRapidity) :
    s.sigma = (leftCoord s + rightCoord s) / 2 := by
  unfold leftCoord rightCoord
  ring

/-- Recover `tau` from the two light-cone coordinates. -/
@[bridge_target_tag, rep_depth thermo]
theorem tau_eq_half_left_sub_right (s : SplitRapidity) :
    s.tau = (leftCoord s - rightCoord s) / 2 := by
  unfold leftCoord rightCoord
  ring

end SplitRapidity

/-- A split-complex scalar represented in the idempotent basis. -/
@[rep_depth thermo]
abbrev ChiralScalar := ℝ × ℝ

/-- Left idempotent coordinate of a chiral scalar. -/
@[rep_depth thermo]
def leftPart (x : ChiralScalar) : ℝ :=
  x.1

/-- Right idempotent coordinate of a chiral scalar. -/
@[rep_depth thermo]
def rightPart (x : ChiralScalar) : ℝ :=
  x.2

/-- Componentwise multiplication in the idempotent basis. -/
@[rep_depth thermo]
def chiralMul (x y : ChiralScalar) : ChiralScalar :=
  (x.1 * y.1, x.2 * y.2)

@[simp, rep_depth thermo]
theorem leftPart_chiralMul (x y : ChiralScalar) :
    leftPart (chiralMul x y) = leftPart x * leftPart y :=
  rfl

@[simp, rep_depth thermo]
theorem rightPart_chiralMul (x y : ChiralScalar) :
    rightPart (chiralMul x y) = rightPart x * rightPart y :=
  rfl

/-- Left-moving thermal exponent. -/
@[rep_depth thermo]
def leftThermalExponent (E : ℝ) (s : SplitRapidity) : ℝ :=
  -(SplitRapidity.leftCoord s * E)

/-- Right-moving thermal exponent. -/
@[rep_depth thermo]
def rightThermalExponent (E : ℝ) (s : SplitRapidity) : ℝ :=
  -(SplitRapidity.rightCoord s * E)

/-- Elementary split-complex thermal exponent in the chiral idempotent basis. -/
@[rep_depth thermo]
def splitChiralThermalExponent (E : ℝ) (s : SplitRapidity) : ChiralScalar :=
  (leftThermalExponent E s, rightThermalExponent E s)

/-- Left-moving thermal exponent component. -/
@[bridge_target_tag, rep_depth thermo]
theorem leftPart_splitChiralThermalExponent (E : ℝ) (s : SplitRapidity) :
    leftPart (splitChiralThermalExponent E s) = leftThermalExponent E s :=
  rfl

/-- Right-moving thermal exponent component. -/
@[bridge_target_tag, rep_depth thermo]
theorem rightPart_splitChiralThermalExponent (E : ℝ) (s : SplitRapidity) :
    rightPart (splitChiralThermalExponent E s) = rightThermalExponent E s :=
  rfl

/-! ## Clifford projector readout -/

/-- The positive `Cl(1,1)` chiral idempotent is idempotent. -/
@[bridge_target_tag, rep_depth thermo]
theorem epsPlusProjector_is_idempotent :
    epsPlusProjector * epsPlusProjector = epsPlusProjector :=
  epsPlusProjector_idempotent

/-- The negative `Cl(1,1)` chiral idempotent is idempotent. -/
@[bridge_target_tag, rep_depth thermo]
theorem epsMinusProjector_is_idempotent :
    epsMinusProjector * epsMinusProjector = epsMinusProjector :=
  epsMinusProjector_idempotent

/-- The two `Cl(1,1)` chiral idempotents are orthogonal in the `-+` order. -/
@[bridge_target_tag, rep_depth thermo]
theorem epsMinusProjector_mul_epsPlusProjector_eq_zero :
    epsMinusProjector * epsPlusProjector = 0 :=
  epsMinusProjector_mul_epsPlusProjector

/-- The two `Cl(1,1)` chiral idempotents are orthogonal in the `+-` order. -/
@[bridge_target_tag, rep_depth thermo]
theorem epsPlusProjector_mul_epsMinusProjector_eq_zero :
    epsPlusProjector * epsMinusProjector = 0 :=
  epsPlusProjector_mul_epsMinusProjector

/-- The two `Cl(1,1)` chiral idempotents resolve the identity. -/
@[bridge_target_tag, rep_depth thermo]
theorem epsProjectors_add_eq_one :
    epsMinusProjector + epsPlusProjector = 1 :=
  epsMinusProjector_add_epsPlusProjector

/-- The split phase flip swaps the two chiral idempotents. -/
@[bridge_target_tag, rep_depth thermo]
theorem phaseFlip_swaps_epsPlusProjector :
    phaseFlipAlg epsPlusProjector = epsMinusProjector :=
  phaseFlip_apply_epsPlusProjector

/-- The split phase flip swaps the two chiral idempotents in the opposite direction. -/
@[bridge_target_tag, rep_depth thermo]
theorem phaseFlip_swaps_epsMinusProjector :
    phaseFlipAlg epsMinusProjector = epsPlusProjector :=
  phaseFlip_apply_epsMinusProjector

/-- Owner target for the split chiral polarization basis. -/
@[owner_target_tag]
def SplitChiralPolarizationBasisOwnerTarget : Prop :=
  (epsPlusProjector * epsPlusProjector = epsPlusProjector) ∧
    (epsMinusProjector * epsMinusProjector = epsMinusProjector) ∧
    (epsPlusProjector * epsMinusProjector = 0) ∧
    (epsMinusProjector * epsPlusProjector = 0) ∧
    (epsMinusProjector + epsPlusProjector = 1) ∧
    (∀ s : SplitRapidity,
      s.sigma = (SplitRapidity.leftCoord s + SplitRapidity.rightCoord s) / 2 ∧
        s.tau = (SplitRapidity.leftCoord s - SplitRapidity.rightCoord s) / 2)

/-- The split chiral polarization owner target is proved. -/
theorem splitChiralPolarizationBasisOwnerTarget :
    SplitChiralPolarizationBasisOwnerTarget := by
  refine ⟨epsPlusProjector_is_idempotent, epsMinusProjector_is_idempotent,
    epsPlusProjector_mul_epsMinusProjector_eq_zero,
    epsMinusProjector_mul_epsPlusProjector_eq_zero, epsProjectors_add_eq_one, ?_⟩
  intro s
  exact ⟨SplitRapidity.sigma_eq_half_left_add_right s,
    SplitRapidity.tau_eq_half_left_sub_right s⟩

end InfoGeometry.Thermo.SplitChiralPolarizationBasis
