import InfoGeometry.Canonical.KKTCore
import InfoGeometry.Canonical.KKTLorentzOrbitBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.Cl11LorentzAction

Owner-level Lie-action surface for the doubled real `Cl(1,1)` grading lane.

This file states the Cartan-action facts in explicit algebraic form:
- commutator eigen-relations on `uPlus/uMinus`,
- grade-zero commutator fixedness,
- channel-boost scaling in exponential form.
-/

namespace Cl11LorentzAction

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.KKTLorentzOrbitBridge
open InfoGeometry.Quantum

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H
local notation "IdH" => ContinuousLinearMap.id ℝ H

/-- Cartan generator on the doubled real lane (grading involution axis). -/
@[rep_depth transport]
noncomputable def cartanGenerator (X : RealSplitCl11Action H) : EndH :=
  X.eps

/--
`K` respects the `g₊/g₀/g₋` grading decomposition when its commutator action is:
- weight `+2` on `uPlus`,
- weight `0` on `gZeroPart`,
- weight `-2` on `uMinus`.
-/
@[rep_depth transport]
def RespectsGradingDecomposition (X : RealSplitCl11Action H) (K : EndH) : Prop :=
  ∀ A : EndH,
    InfoGeometry.Canonical.KKTCore.commutator K (uPlus X A) = (2 : ℝ) • uPlus X A
      ∧ InfoGeometry.Canonical.KKTCore.commutator K (gZeroPart X A) = 0
      ∧ InfoGeometry.Canonical.KKTCore.commutator K (uMinus X A) = (-2 : ℝ) • uMinus X A

/--
Modular flow on the split `Cl(1,1)` lane, expressed on the doubled real carrier.

This is the owner-level alias for the `ε`-generated hyperbolic channel boost.
-/
@[rep_depth transport]
noncomputable def modularFlow (X : RealSplitCl11Action H) (t : ℝ) : EndH :=
  channelBoost X t

/-- Cartan commutator eigen-relation on the `uPlus` channel. -/
@[rep_depth transport]
theorem cartan_commutator_uPlus
    (X : RealSplitCl11Action H) (A : EndH) :
    InfoGeometry.Canonical.KKTCore.commutator (cartanGenerator X) (uPlus X A)
      = (2 : ℝ) • uPlus X A := by
  unfold cartanGenerator InfoGeometry.Canonical.KKTCore.commutator uPlus
  calc
    X.eps * gOnePart X A - gOnePart X A * X.eps
        = gOnePart X A - (-(gOnePart X A)) := by
            rw [eps_mul_gOnePart, gOnePart_mul_eps]
    _ = (2 : ℝ) • gOnePart X A := by
          simp [two_smul]

/-- Cartan commutator eigen-relation on the `uMinus` channel. -/
@[rep_depth transport]
theorem cartan_commutator_uMinus
    (X : RealSplitCl11Action H) (A : EndH) :
    InfoGeometry.Canonical.KKTCore.commutator (cartanGenerator X) (uMinus X A)
      = (-2 : ℝ) • uMinus X A := by
  unfold cartanGenerator InfoGeometry.Canonical.KKTCore.commutator uMinus
  calc
    X.eps * gNegOnePart X A - gNegOnePart X A * X.eps
        = -(gNegOnePart X A) + -(gNegOnePart X A) := by
            rw [eps_mul_gNegOnePart, gNegOnePart_mul_eps]
            simp [sub_eq_add_neg]
    _ = (-2 : ℝ) • gNegOnePart X A := by
          simp [two_smul]

/-- Cartan commutator is zero on the grade-zero channel. -/
@[rep_depth transport]
theorem cartan_commutator_gZeroPart_eq_zero
    (X : RealSplitCl11Action H) (A : EndH) :
    InfoGeometry.Canonical.KKTCore.commutator (cartanGenerator X) (gZeroPart X A) = 0 := by
  unfold cartanGenerator InfoGeometry.Canonical.KKTCore.commutator
  rw [eps_mul_gZeroPart_eq_gZeroPart_mul_eps]
  simp

/--
The grading involution axis `K = eps` is the Cartan generator for the split
`Cl(1,1)` channel decomposition.
-/
@[rep_depth transport]
theorem K_is_Cartan
    (X : RealSplitCl11Action H) :
    RespectsGradingDecomposition X (cartanGenerator X) := by
  intro A
  refine ⟨?_, ?_, ?_⟩
  · exact cartan_commutator_uPlus (X := X) (A := A)
  · exact cartan_commutator_gZeroPart_eq_zero (X := X) (A := A)
  · exact cartan_commutator_uMinus (X := X) (A := A)

/-- Channel boost in exponential form on `uPlus`. -/
@[rep_depth transport]
theorem cartan_flow_scales_uPlus_exp
    (X : RealSplitCl11Action H) (τ : ℝ) (A : EndH) :
    channelBoost X τ * uPlus X A = Real.exp τ • uPlus X A := by
  simpa using channelBoost_mul_uPlus (X := X) (τ := τ) (A := A)

/-- Channel boost in exponential form on `uMinus`. -/
@[rep_depth transport]
theorem cartan_flow_scales_uMinus_exp
    (X : RealSplitCl11Action H) (τ : ℝ) (A : EndH) :
    channelBoost X τ * uMinus X A = Real.exp (-τ) • uMinus X A := by
  simpa using channelBoost_mul_uMinus (X := X) (τ := τ) (A := A)

/--
Modular flow weighted action on the `uPlus` chiral channel.

`uPlus` is the positive-weight channel and scales by `exp t`.
-/
@[rep_depth transport]
theorem modular_flow_scales_uPlus
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    modularFlow X t * uPlus X A = Real.exp t • uPlus X A := by
  unfold modularFlow
  calc
    channelBoost X t * uPlus X A
        = (Real.cosh t + Real.sinh t) • uPlus X A := by
            simpa using channelBoost_mul_uPlus (X := X) (τ := t) (A := A)
    _ = Real.exp t • uPlus X A := by
          congr 1
          rw [Real.cosh_eq, Real.sinh_eq]
          ring

/--
Modular flow weighted action on the `uMinus` chiral channel.

`uMinus` is the negative-weight channel and scales by `exp (-t)`.
-/
@[rep_depth transport]
theorem modular_flow_scales_uMinus
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    modularFlow X t * uMinus X A = Real.exp (-t) • uMinus X A := by
  unfold modularFlow
  calc
    channelBoost X t * uMinus X A
        = (Real.cosh t - Real.sinh t) • uMinus X A := by
            simpa using channelBoost_mul_uMinus (X := X) (τ := t) (A := A)
    _ = Real.exp (-t) • uMinus X A := by
          congr 1
          rw [Real.cosh_eq, Real.sinh_eq]
          ring

/--
Inverse law for the modular flow family on the split `Cl(1,1)` lane.
-/
@[rep_depth transport]
theorem modularFlow_mul_modularFlow_neg
    (X : RealSplitCl11Action H) (t : ℝ) :
    modularFlow X t * modularFlow X (-t) = (1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro x
  unfold modularFlow channelBoost
  rw [Real.cosh_neg, Real.sinh_neg]
  have hdiag : Real.cosh t * Real.cosh t + -(Real.sinh t * Real.sinh t) = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hcross : -(Real.cosh t * Real.sinh t) + Real.sinh t * Real.cosh t = 0 := by
    ring
  calc
    ((Real.cosh t) • (1 : EndH) + (Real.sinh t) • X.eps)
        (((Real.cosh t) • (1 : EndH) + (-Real.sinh t) • X.eps) x)
        = (Real.cosh t * Real.cosh t + -(Real.sinh t * Real.sinh t)) • x
            + (-(Real.cosh t * Real.sinh t) + Real.sinh t * Real.cosh t) • X.eps x := by
            simp [smul_add, add_smul, smul_smul, add_assoc, add_left_comm, add_comm,
              X.eps_sq_apply]
    _ = (1 : ℝ) • x + 0 • X.eps x := by simp [hdiag, hcross]
    _ = x := by simp

/--
Symmetric inverse law for the modular flow family.
-/
@[rep_depth transport]
theorem modularFlow_neg_mul_modularFlow
    (X : RealSplitCl11Action H) (t : ℝ) :
    modularFlow X (-t) * modularFlow X t = (1 : EndH) := by
  apply ContinuousLinearMap.ext
  intro x
  unfold modularFlow channelBoost
  rw [Real.cosh_neg, Real.sinh_neg]
  have hdiag : Real.cosh t * Real.cosh t + -(Real.sinh t * Real.sinh t) = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hcross : Real.cosh t * Real.sinh t + -(Real.sinh t * Real.cosh t) = 0 := by
    ring
  calc
    ((Real.cosh t) • (1 : EndH) + (-Real.sinh t) • X.eps)
        (((Real.cosh t) • (1 : EndH) + (Real.sinh t) • X.eps) x)
        = (Real.cosh t * Real.cosh t + -(Real.sinh t * Real.sinh t)) • x
            + (Real.cosh t * Real.sinh t + -(Real.sinh t * Real.cosh t)) • X.eps x := by
            simp [smul_add, add_smul, smul_smul, add_assoc, add_left_comm, add_comm,
              X.eps_sq_apply]
    _ = (1 : ℝ) • x + 0 • X.eps x := by simp [hdiag, hcross]
    _ = x := by simp

/--
Additive/group law for the modular flow family.
-/
@[rep_depth transport]
theorem modularFlow_add
    (X : RealSplitCl11Action H) (s t : ℝ) :
    modularFlow X (s + t) = modularFlow X s * modularFlow X t := by
  apply ContinuousLinearMap.ext
  intro x
  unfold modularFlow channelBoost
  rw [Real.cosh_add, Real.sinh_add]
  simp [smul_add, add_smul, smul_smul, X.eps_sq_apply,
    add_assoc, add_left_comm, add_comm, mul_comm]

/--
Lie-exponential transport packet on the Bogoliubov frame channels.

This packages the minimal owner facts:
- `modularFlow` is a one-parameter Lie group (`0`, additive law),
- the `uPlus/uMinus` channels scale exponentially with weights `±1`.
-/
@[rep_depth transport]
theorem modularFlow_lieExponential_transport_packet
    (X : RealSplitCl11Action H) :
    modularFlow X 0 = (1 : EndH)
      ∧ (∀ s t : ℝ, modularFlow X (s + t) = modularFlow X s * modularFlow X t)
      ∧ (∀ t : ℝ, ∀ A : EndH, modularFlow X t * uPlus X A = Real.exp t • uPlus X A)
      ∧ (∀ t : ℝ, ∀ A : EndH, modularFlow X t * uMinus X A = Real.exp (-t) • uMinus X A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold modularFlow channelBoost
    apply ContinuousLinearMap.ext
    intro x
    simp
  · intro s t
    exact modularFlow_add (X := X) (s := s) (t := t)
  · intro t A
    exact modular_flow_scales_uPlus (X := X) (t := t) (A := A)
  · intro t A
    exact modular_flow_scales_uMinus (X := X) (t := t) (A := A)

/--
Right action of `modularFlow (-t)` on the `uPlus` channel.
-/
@[rep_depth transport]
theorem uPlus_mul_modularFlow_neg
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    uPlus X A * modularFlow X (-t) = Real.exp t • uPlus X A := by
  have hIdRight (T : EndH) : T * IdH = T := by
    change T * (1 : EndH) = T
    simp
  have hexp : Real.cosh t + Real.sinh t = Real.exp t := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  unfold modularFlow channelBoost
  rw [Real.cosh_neg, Real.sinh_neg]
  calc
    uPlus X A * ((Real.cosh t) • IdH + (-Real.sinh t) • X.eps)
        = (Real.cosh t) • (uPlus X A * IdH) + (-Real.sinh t) • (uPlus X A * X.eps) := by
            simp [mul_add]
    _ = (Real.cosh t) • uPlus X A + (-Real.sinh t) • (-(uPlus X A)) := by
          rw [hIdRight]
          simp [uPlus, gOnePart_mul_eps]
    _ = (Real.cosh t) • uPlus X A + (Real.sinh t) • uPlus X A := by
          simp [smul_neg]
    _ = Real.exp t • uPlus X A := by
          rw [← add_smul, hexp]

/--
Right action of `modularFlow (-t)` on the `uMinus` channel.
-/
@[rep_depth transport]
theorem uMinus_mul_modularFlow_neg
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    uMinus X A * modularFlow X (-t) = Real.exp (-t) • uMinus X A := by
  have hIdRight (T : EndH) : T * IdH = T := by
    change T * (1 : EndH) = T
    simp
  have hexp : Real.cosh t - Real.sinh t = Real.exp (-t) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  unfold modularFlow channelBoost
  rw [Real.cosh_neg, Real.sinh_neg]
  calc
    uMinus X A * ((Real.cosh t) • IdH + (-Real.sinh t) • X.eps)
        = (Real.cosh t) • (uMinus X A * IdH) + (-Real.sinh t) • (uMinus X A * X.eps) := by
            simp [mul_add]
    _ = (Real.cosh t) • uMinus X A + (-Real.sinh t) • (uMinus X A) := by
          rw [hIdRight]
          simp [uMinus, gNegOnePart_mul_eps]
    _ = (Real.cosh t - Real.sinh t) • uMinus X A := by
          simp [sub_eq_add_neg, add_smul]
    _ = Real.exp (-t) • uMinus X A := by
          rw [hexp]

/-- Adjoint/conjugation transport along the modular flow. -/
@[rep_depth transport]
noncomputable def modularAdjointFlow
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) : EndH :=
  modularFlow X t * A * modularFlow X (-t)

/--
Additive/group action law for adjoint transport:
`Ad_{s+t} = Ad_s ∘ Ad_t`.
-/
@[rep_depth transport]
theorem modularAdjointFlow_add
    (X : RealSplitCl11Action H) (s t : ℝ) (A : EndH) :
    modularAdjointFlow X (s + t) A
      = modularAdjointFlow X s (modularAdjointFlow X t A) := by
  unfold modularAdjointFlow
  calc
    modularFlow X (s + t) * A * modularFlow X (-(s + t))
        = (modularFlow X s * modularFlow X t) * A * modularFlow X ((-t) + (-s)) := by
            rw [modularFlow_add (X := X) (s := s) (t := t)]
            congr 1
            ring_nf
    _ = (modularFlow X s * modularFlow X t) * A * (modularFlow X (-t) * modularFlow X (-s)) := by
          rw [modularFlow_add (X := X) (s := -t) (t := -s)]
    _ = modularFlow X s * (modularFlow X t * A * modularFlow X (-t)) * modularFlow X (-s) := by
          simp [mul_assoc]

/--
Adjoint/conjugation scaling on `uPlus`: weight `exp (2*t)`.
-/
@[rep_depth transport]
theorem modularAdjointFlow_scales_uPlus
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    modularAdjointFlow X t (uPlus X A) = Real.exp (2 * t) • uPlus X A := by
  unfold modularAdjointFlow
  have hExp2 : Real.exp t * Real.exp t = Real.exp (2 * t) := by
    calc
      Real.exp t * Real.exp t = Real.exp (t + t) := by rw [← Real.exp_add]
      _ = Real.exp (2 * t) := by ring_nf
  calc
    modularFlow X t * uPlus X A * modularFlow X (-t)
        = (Real.exp t • uPlus X A) * modularFlow X (-t) := by
            rw [modular_flow_scales_uPlus (X := X) (t := t) (A := A)]
    _ = Real.exp t • (uPlus X A * modularFlow X (-t)) := by
          simp
    _ = Real.exp t • (Real.exp t • uPlus X A) := by
          rw [uPlus_mul_modularFlow_neg (X := X) (t := t) (A := A)]
    _ = Real.exp (2 * t) • uPlus X A := by
          simp [smul_smul, hExp2]

/--
Adjoint/conjugation scaling on `uMinus`: weight `exp (-2*t)`.
-/
@[rep_depth transport]
theorem modularAdjointFlow_scales_uMinus
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    modularAdjointFlow X t (uMinus X A) = Real.exp (-2 * t) • uMinus X A := by
  unfold modularAdjointFlow
  have hExp2 : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
    calc
      Real.exp (-t) * Real.exp (-t) = Real.exp ((-t) + (-t)) := by rw [← Real.exp_add]
      _ = Real.exp (-2 * t) := by ring_nf
  calc
    modularFlow X t * uMinus X A * modularFlow X (-t)
        = (Real.exp (-t) • uMinus X A) * modularFlow X (-t) := by
            rw [modular_flow_scales_uMinus (X := X) (t := t) (A := A)]
    _ = Real.exp (-t) • (uMinus X A * modularFlow X (-t)) := by
          simp
    _ = Real.exp (-t) • (Real.exp (-t) • uMinus X A) := by
          rw [uMinus_mul_modularFlow_neg (X := X) (t := t) (A := A)]
    _ = Real.exp (-2 * t) • uMinus X A := by
          simp [smul_smul, hExp2]

/--
Adjoint/conjugation action fixes the grade-zero channel.
-/
@[rep_depth transport]
theorem modularAdjointFlow_fixes_gZeroPart
    (X : RealSplitCl11Action H) (t : ℝ) (A : EndH) :
    modularAdjointFlow X t (gZeroPart X A) = gZeroPart X A := by
  unfold modularAdjointFlow
  calc
    modularFlow X t * gZeroPart X A * modularFlow X (-t)
        = gZeroPart X A * (modularFlow X t * modularFlow X (-t)) := by
            have hComm :
                modularFlow X t * gZeroPart X A
                  = gZeroPart X A * modularFlow X t := by
              simpa [modularFlow] using
                channelBoost_mul_gZeroPart_eq_gZeroPart_mul_channelBoost (X := X) (τ := t) (A := A)
            rw [hComm]
            simp [mul_assoc]
    _ = gZeroPart X A * 1 := by
          rw [modularFlow_mul_modularFlow_neg (X := X) (t := t)]
    _ = gZeroPart X A := by simp

end Core

end Cl11LorentzAction
