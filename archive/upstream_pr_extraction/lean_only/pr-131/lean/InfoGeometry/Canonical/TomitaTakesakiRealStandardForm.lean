import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TomitaTakesakiRealStandardForm

Real-doubled standard-form interface and orientation-contract lemmas.

This file freezes the sign conventions behind the modular lane in the owned
carrier language `(H₂, J, ε, K)` and proves explicit gauge-equivalence facts:

- flipping the phase-axis orientation `K ↦ -K`,
- flipping the modular conjugation axis `J ↦ -J`,
- swapping left/right sector labels via the grading flip `ε ↦ -ε`,
- reversing modular time `t ↦ -t`.
-/

namespace InfoGeometry.Canonical.TomitaTakesakiRealStandardForm

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ProjectorEquivariance

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

/-- Linearity predicate relative to a chosen phase axis. -/
@[rep_depth krein]
def IsLinearWrt (K A : EndH) : Prop := A.comp K = K.comp A

/-- Antilinearity predicate relative to a chosen phase axis. -/
@[rep_depth krein]
def IsAntilinearWrt (K A : EndH) : Prop := A.comp K = -(K.comp A)

/-- Flipping `K ↦ -K` preserves linearity class. -/
@[rep_depth krein]
theorem isLinearWrt_negAxis_iff (K A : EndH) :
    IsLinearWrt (-K) A ↔ IsLinearWrt K A := by
  let _ : CompleteSpace E := inferInstance
  unfold IsLinearWrt
  constructor <;> intro h <;> simpa using h

/-- Flipping `K ↦ -K` preserves antilinearity class. -/
@[rep_depth krein]
theorem isAntilinearWrt_negAxis_iff (K A : EndH) :
    IsAntilinearWrt (-K) A ↔ IsAntilinearWrt K A := by
  let _ : CompleteSpace E := inferInstance
  unfold IsAntilinearWrt
  constructor
  · intro h
    have h1 : -(A.comp K) = K.comp A := by
      simpa using h
    have h2 : A.comp K = -(K.comp A) := by
      simpa using congrArg (fun X => -X) h1
    exact h2
  · intro h
    have h1 : -(A.comp K) = K.comp A := by
      simpa using congrArg (fun X => -X) h
    simpa using h1

/-- Conjugation by a doubled-carrier involution axis. -/
@[rep_depth krein]
def jConjugate (J A : EndH) : EndH := J * A * J

/-- Flipping `J ↦ -J` leaves conjugation action unchanged. -/
@[rep_depth krein]
theorem jConjugate_negJ (J A : EndH) :
    jConjugate (-J) A = jConjugate J A := by
  let _ : CompleteSpace E := inferInstance
  unfold jConjugate
  noncomm_ring

/--
Real standard-form interface on the doubled carrier:
`J` implements a left/right algebra transport map by conjugation.
-/
@[rep_depth krein]
structure RealStandardForm where
  leftAlgebra : Set EndH
  rightAlgebra : Set EndH
  J : EndH
  J_sq : J * J = 1
  J_left_to_right : ∀ {A : EndH}, A ∈ leftAlgebra → jConjugate J A ∈ rightAlgebra
  J_right_to_left : ∀ {A : EndH}, A ∈ rightAlgebra → jConjugate J A ∈ leftAlgebra

namespace RealStandardForm

variable (S : RealStandardForm (E := E))

/-- Orientation gauge: `J ↦ -J` preserves the standard-form transport laws. -/
@[rep_depth krein]
def flipJ : RealStandardForm (E := E) where
  leftAlgebra := S.leftAlgebra
  rightAlgebra := S.rightAlgebra
  J := -S.J
  J_sq := by
    calc
      (-S.J) * (-S.J) = S.J * S.J := by
        noncomm_ring
      _ = 1 := S.J_sq
  J_left_to_right := by
    intro A hA
    have hA' : jConjugate S.J A ∈ S.rightAlgebra := S.J_left_to_right hA
    simpa [jConjugate_negJ] using hA'
  J_right_to_left := by
    intro A hA
    have hA' : jConjugate S.J A ∈ S.leftAlgebra := S.J_right_to_left hA
    simpa [jConjugate_negJ] using hA'

/-- Label gauge: swap left/right algebras while keeping the same involution axis. -/
@[rep_depth krein]
def swapLeftRight : RealStandardForm (E := E) where
  leftAlgebra := S.rightAlgebra
  rightAlgebra := S.leftAlgebra
  J := S.J
  J_sq := S.J_sq
  J_left_to_right := by
    intro A hA
    exact S.J_right_to_left hA
  J_right_to_left := by
    intro A hA
    exact S.J_left_to_right hA

/-- Swapping left/right twice returns the original standard-form package. -/
@[rep_depth krein]
theorem swapLeftRight_involutive :
    (S.swapLeftRight).swapLeftRight = S := by
  let _ : CompleteSpace E := inferInstance
  cases S
  rfl

/-- Flipping `J ↦ -J` twice returns the original standard-form package. -/
@[rep_depth krein]
theorem flipJ_involutive :
    (S.flipJ).flipJ = S := by
  cases S
  simp [RealStandardForm.flipJ]

/-- `M ↔ M'` label swap: left-membership is right-membership of the original frame. -/
@[rep_depth krein]
theorem mem_leftAlgebra_swapLeftRight_iff (A : EndH) :
    A ∈ S.swapLeftRight.leftAlgebra ↔ A ∈ S.rightAlgebra := by
  let _ : CompleteSpace E := inferInstance
  exact Iff.rfl

/-- `M ↔ M'` label swap: right-membership is left-membership of the original frame. -/
@[rep_depth krein]
theorem mem_rightAlgebra_swapLeftRight_iff (A : EndH) :
    A ∈ S.swapLeftRight.rightAlgebra ↔ A ∈ S.leftAlgebra := by
  let _ : CompleteSpace E := inferInstance
  exact Iff.rfl

end RealStandardForm

/-- Wedge normalization map from modular time `t` to boost parameter `τ = 2π t`. -/
@[rep_depth transport]
noncomputable def wedgeBoostParameter (t : ℝ) : ℝ := (2 * Real.pi) * t

/-- Inverse wedge normalization map `t = τ / (2π)`. -/
@[rep_depth transport]
noncomputable def modularTimeOfWedgeBoost (τ : ℝ) : ℝ := ((2 * Real.pi)⁻¹) * τ

/-- The wedge normalization maps are inverse. -/
@[rep_depth transport]
theorem modularTimeOfWedgeBoost_wedgeBoostParameter (t : ℝ) :
    modularTimeOfWedgeBoost (wedgeBoostParameter t) = t := by
  unfold modularTimeOfWedgeBoost wedgeBoostParameter
  have hpi : (2 * Real.pi) ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 Real.pi_ne_zero
  field_simp [hpi]

/-- The wedge normalization inverse also holds in the opposite direction. -/
@[rep_depth transport]
theorem wedgeBoostParameter_modularTimeOfWedgeBoost (τ : ℝ) :
    wedgeBoostParameter (modularTimeOfWedgeBoost τ) = τ := by
  unfold modularTimeOfWedgeBoost wedgeBoostParameter
  have hpi : (2 * Real.pi) ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 Real.pi_ne_zero
  field_simp [hpi]

/-- The modular transport flow at negative time is the inverse branch. -/
@[rep_depth transport]
theorem modularTransportFlow_neg_mul (hMod : EndH) (t : ℝ) :
    modularTransportFlow (E := E) hMod (-t) * modularTransportFlow (E := E) hMod t = 1 := by
  have hAdd := modularTransportFlow_add (E := E) hMod (-t) t
  have hZero : modularTransportFlow (E := E) hMod 0 = 1 :=
    modularTransportFlow_zero (E := E) hMod
  calc
    modularTransportFlow (E := E) hMod (-t) * modularTransportFlow (E := E) hMod t
        = modularTransportFlow (E := E) hMod ((-t) + t) := by
            symm
            simpa using hAdd
    _ = modularTransportFlow (E := E) hMod 0 := by simp
    _ = 1 := hZero

/-- The modular transport flow at positive time is the inverse branch of `-t`. -/
@[rep_depth transport]
theorem modularTransportFlow_mul_neg (hMod : EndH) (t : ℝ) :
    modularTransportFlow (E := E) hMod t * modularTransportFlow (E := E) hMod (-t) = 1 := by
  have hAdd := modularTransportFlow_add (E := E) hMod t (-t)
  have hZero : modularTransportFlow (E := E) hMod 0 = 1 :=
    modularTransportFlow_zero (E := E) hMod
  calc
    modularTransportFlow (E := E) hMod t * modularTransportFlow (E := E) hMod (-t)
        = modularTransportFlow (E := E) hMod (t + (-t)) := by
            symm
            simpa using hAdd
    _ = modularTransportFlow (E := E) hMod 0 := by simp
    _ = 1 := hZero

/--
Concrete left/right grading-label swap packet induced by `ε ↦ -ε` in the fixed frame.
-/
@[rep_depth transport]
theorem gradingFlip_swaps_plus_minus_projectors :
    plusProjectorAfterPhaseFlip (E := E) = minusProjector (E := E)
      ∧ minusProjectorAfterPhaseFlip (E := E) = plusProjector (E := E) := by
  let _ : CompleteSpace E := inferInstance
  exact fixedGrading_projectorSwap (E := E)

/--
One-shot orientation-equivalence package in the real standard-form lane:
`K ↦ -K`, `J ↦ -J`, `ε ↦ -ε`, and `M ↔ M'`.
-/
@[rep_depth transport]
theorem orientation_equivalence_package
    (S : RealStandardForm (E := E)) (K A : EndH) :
    (IsLinearWrt (-K) A ↔ IsLinearWrt K A)
      ∧ (IsAntilinearWrt (-K) A ↔ IsAntilinearWrt K A)
      ∧ (jConjugate (-S.J) A = jConjugate S.J A)
      ∧ (A ∈ S.swapLeftRight.leftAlgebra ↔ A ∈ S.rightAlgebra)
      ∧ (A ∈ S.swapLeftRight.rightAlgebra ↔ A ∈ S.leftAlgebra)
      ∧ (plusProjectorAfterPhaseFlip (E := E) = minusProjector (E := E))
      ∧ (minusProjectorAfterPhaseFlip (E := E) = plusProjector (E := E)) := by
  have hGrading := gradingFlip_swaps_plus_minus_projectors (E := E)
  refine ⟨isLinearWrt_negAxis_iff K A, isAntilinearWrt_negAxis_iff K A,
    jConjugate_negJ S.J A, S.mem_leftAlgebra_swapLeftRight_iff A,
    S.mem_rightAlgebra_swapLeftRight_iff A, hGrading.1, hGrading.2⟩

end Core

end InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
