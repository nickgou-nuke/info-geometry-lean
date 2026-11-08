import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.HestenesPhaseSemilinear

Real doubled Hestenes replacement for semilinearity.

The owner language is the real doubled carrier with internal phase axis
`K = J ∘ ε`. In this file:

* linear phase transport means commuting with `K`;
* antilinear phase transport means anticommuting with `K`;
* semilinear composition is encoded by multiplication of phase-twist signs.

This module introduces no scalar-complex owner lane and no external conjugation
operation. It is only a real-operator calculus on the doubled carrier.
-/

namespace InfoGeometry.Canonical.HestenesPhaseSemilinear

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesRealStructures

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
@[rep_depth krein]
noncomputable abbrev phaseAxis : EndH := InfoGeometry.Krein.clockAxis (E := E)

/--
The two real Hestenes phase twists.

`linear` means commute with the internal phase axis `K`.
`antilinear` means anticommute with `K`.

This is the real doubled replacement for identity/conjugation scalar transport.
-/
@[rep_depth krein]
inductive PhaseTwist where
  | linear
  | antilinear
  deriving DecidableEq, Repr

namespace PhaseTwist

/-- Sign attached to a phase twist. -/
@[rep_depth krein]
def sign : PhaseTwist → ℝ
  | linear => 1
  | antilinear => -1

/-- Composition of phase twists. -/
@[rep_depth krein]
def comp : PhaseTwist → PhaseTwist → PhaseTwist
  | linear, linear => linear
  | linear, antilinear => antilinear
  | antilinear, linear => antilinear
  | antilinear, antilinear => linear

@[simp] theorem sign_linear : sign linear = 1 := rfl
@[simp] theorem sign_antilinear : sign antilinear = -1 := rfl

@[simp] theorem comp_linear_left (τ : PhaseTwist) :
    comp linear τ = τ := by
  cases τ <;> rfl

@[simp] theorem comp_linear_right (τ : PhaseTwist) :
    comp τ linear = τ := by
  cases τ <;> rfl

@[simp] theorem comp_antilinear_antilinear :
    comp antilinear antilinear = linear := rfl

/-- Phase-twist signs multiply under composition. -/
@[rep_depth krein]
theorem sign_comp (σ τ : PhaseTwist) :
    sign (comp σ τ) = sign σ * sign τ := by
  cases σ <;> cases τ <;> simp [sign, comp]

end PhaseTwist

/--
Hestenes-semilinearity of a real doubled operator.

Instead of scalar transport by conjugation, the operator transports the internal
phase axis `K` by a sign.

`τ = linear` means `A K = K A`.
`τ = antilinear` means `A K = -K A`.
-/
@[rep_depth krein]
def IsHestenesSemilinear (τ : PhaseTwist) (A : EndH) : Prop :=
  A.comp (phaseAxis (E := E)) = τ.sign • ((phaseAxis (E := E)).comp A)

/-- The `linear` case is exactly commutation with the internal phase axis. -/
@[rep_depth krein]
theorem isHestenesSemilinear_linear_iff (A : EndH) :
    IsHestenesSemilinear (E := E) PhaseTwist.linear A ↔ A.comp (phaseAxis (E := E)) = (phaseAxis (E := E)).comp A := by
  unfold IsHestenesSemilinear
  simp [PhaseTwist.sign]

/-- The `antilinear` case is exactly anticommutation with the internal phase axis. -/
@[rep_depth krein]
theorem isHestenesSemilinear_antilinear_iff (A : EndH) :
    IsHestenesSemilinear (E := E) PhaseTwist.antilinear A ↔ A.comp (phaseAxis (E := E)) = -((phaseAxis (E := E)).comp A) := by
  unfold IsHestenesSemilinear
  constructor
  · intro h
    rw [PhaseTwist.sign_antilinear] at h
    rw [h]
    exact neg_one_smul ℝ ((phaseAxis (E := E)).comp A)
  · intro h
    rw [PhaseTwist.sign_antilinear]
    rw [h]
    exact (neg_one_smul ℝ ((phaseAxis (E := E)).comp A)).symm

/-- Readback: Hestenes-semilinear with trivial phase twist is exactly `KLinear`. -/
@[rep_depth krein]
theorem isHestenesSemilinear_linear_iff_KLinear (A : EndH) :
    IsHestenesSemilinear (E := E) PhaseTwist.linear A
      ↔ KLinear (E := E) A := by
  rw [isHestenesSemilinear_linear_iff]
  simpa [KLinear, InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear, phaseAxis]

/--
Readback: Hestenes-semilinear with conjugating phase twist is exactly
`KAntilinear`.
-/
@[rep_depth krein]
theorem isHestenesSemilinear_antilinear_iff_KAntilinear (A : EndH) :
    IsHestenesSemilinear (E := E) PhaseTwist.antilinear A
      ↔ KAntilinear (E := E) A := by
  rw [isHestenesSemilinear_antilinear_iff]
  simpa [KAntilinear, InfoGeometry.Canonical.BogoliubovTransport.IsPhaseAntilinear,
    phaseAxis]

/-- Identity is Hestenes-linear. -/
@[rep_depth krein]
theorem id_isHestenesSemilinear :
    IsHestenesSemilinear (E := E) PhaseTwist.linear (ContinuousLinearMap.id ℝ H₂) := by
  unfold IsHestenesSemilinear
  apply ContinuousLinearMap.ext
  intro u
  simp [phaseAxis, PhaseTwist.sign]

/-- The internal phase axis is Hestenes-linear; it commutes with itself. -/
@[rep_depth krein]
theorem clockAxis_isHestenesLinear :
    IsHestenesSemilinear (E := E) PhaseTwist.linear (phaseAxis (E := E)) := by
  unfold IsHestenesSemilinear
  apply ContinuousLinearMap.ext
  intro u
  simp [phaseAxis, PhaseTwist.sign]

/--
The modular doubled swap `J` is Hestenes-antilinear.

This is the repo-native replacement for saying that conjugation is
antilinear. It is a real theorem over `DoubledSpace`.
-/
@[rep_depth krein]
theorem modular_j_isHestenesAntilinear :
    IsHestenesSemilinear (E := E) PhaseTwist.antilinear (modular_j (E := E)) := by
  apply (isHestenesSemilinear_antilinear_iff (E := E) (A := modular_j (E := E))).2
  simpa [phaseAxis, InfoGeometry.Krein.clockAxis] using
    InfoGeometry.Krein.modular_j_complex_i_anticommute (E := E)

/--
Composition law for Hestenes-semilinear operators.

A `σ`-twisted operator followed by a `τ`-twisted operator is
`PhaseTwist.comp σ τ`-twisted. This is the real doubled analogue of
semilinear composition: scalar transport is replaced by phase-sign transport.
-/
@[rep_depth krein]
theorem comp_isHestenesSemilinear
    {σ τ : PhaseTwist}
    {A B : EndH}
    (hA : IsHestenesSemilinear (E := E) σ A)
    (hB : IsHestenesSemilinear (E := E) τ B) :
    IsHestenesSemilinear (E := E) (PhaseTwist.comp σ τ) (A.comp B) := by
  unfold IsHestenesSemilinear at hA hB ⊢
  apply ContinuousLinearMap.ext
  intro u
  have hB_u : B (phaseAxis (E := E) u) = τ.sign • (phaseAxis (E := E) (B u)) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndH => F u) hB
  have hA_Bu : A (phaseAxis (E := E) (B u)) = σ.sign • (phaseAxis (E := E) (A (B u))) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun F : EndH => F (B u)) hA
  calc
    (((A.comp B).comp (phaseAxis (E := E))) u)
        = A (B (phaseAxis (E := E) u)) := rfl
    _ = A (τ.sign • phaseAxis (E := E) (B u)) := by rw [hB_u]
    _ = τ.sign • A (phaseAxis (E := E) (B u)) := by
      exact A.map_smul τ.sign (phaseAxis (E := E) (B u))
    _ = τ.sign • (σ.sign • phaseAxis (E := E) (A (B u))) := by rw [hA_Bu]
    _ = ((PhaseTwist.comp σ τ).sign • ((phaseAxis (E := E)).comp (A.comp B))) u := by
      rw [PhaseTwist.sign_comp]
      simp [mul_comm, smul_smul]

/-- Composition of two Hestenes-antilinear operators is Hestenes-linear. -/
@[rep_depth krein]
theorem comp_antilinear_antilinear_isHestenesLinear
    {A B : EndH}
    (hA : IsHestenesSemilinear (E := E) PhaseTwist.antilinear A)
    (hB : IsHestenesSemilinear (E := E) PhaseTwist.antilinear B) :
    IsHestenesSemilinear (E := E) PhaseTwist.linear (A.comp B) := by
  simpa [PhaseTwist.comp] using
    comp_isHestenesSemilinear (E := E) (A := A) (B := B) hA hB

/-- Composition of a Hestenes-linear and Hestenes-antilinear operator is antilinear. -/
@[rep_depth krein]
theorem comp_linear_antilinear_isHestenesAntilinear
    {A B : EndH}
    (hA : IsHestenesSemilinear (E := E) PhaseTwist.linear A)
    (hB : IsHestenesSemilinear (E := E) PhaseTwist.antilinear B) :
    IsHestenesSemilinear (E := E) PhaseTwist.antilinear (A.comp B) := by
  simpa [PhaseTwist.comp] using
    comp_isHestenesSemilinear (E := E) (A := A) (B := B) hA hB

/-- Composition of a Hestenes-antilinear and Hestenes-linear operator is antilinear. -/
@[rep_depth krein]
theorem comp_antilinear_linear_isHestenesAntilinear
    {A B : EndH}
    (hA : IsHestenesSemilinear (E := E) PhaseTwist.antilinear A)
    (hB : IsHestenesSemilinear (E := E) PhaseTwist.linear B) :
    IsHestenesSemilinear (E := E) PhaseTwist.antilinear (A.comp B) := by
  simpa [PhaseTwist.comp] using
    comp_isHestenesSemilinear (E := E) (A := A) (B := B) hA hB

/-- Composition of two Hestenes-linear operators is linear. -/
@[rep_depth krein]
theorem comp_linear_linear_isHestenesLinear
    {A B : EndH}
    (hA : IsHestenesSemilinear (E := E) PhaseTwist.linear A)
    (hB : IsHestenesSemilinear (E := E) PhaseTwist.linear B) :
    IsHestenesSemilinear (E := E) PhaseTwist.linear (A.comp B) := by
  simpa [PhaseTwist.comp] using
    comp_isHestenesSemilinear (E := E) (A := A) (B := B) hA hB

end Core

end InfoGeometry.Canonical.HestenesPhaseSemilinear
