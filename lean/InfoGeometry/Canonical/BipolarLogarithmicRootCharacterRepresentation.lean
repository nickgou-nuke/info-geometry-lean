import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import Mathlib.Tactic

/-!
# Genuine root-character representation for the bipolar logarithmic Cartan line

The scalar exponential weights of the logarithmic adjoint flow are bundled here
as genuine Mathlib monoid homomorphisms

`Multiplicative ℂ →* ℂˣ`.

The multiplicative wrapper is the standard way to regard the additive complex
Cartan parameter as a multiplicative source group.  The two characters are the
opposite `sl₂` roots `w ↦ exp(w)` and `w ↦ exp(-w)`.  Their scalar readbacks are
exactly the `plusRootCharacter` and `minusRootCharacter` already used by the
operator adjoint flow.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarLogarithmicRootCharacterRepresentation

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Physics.ChiralCausalCone

/-- Positive `sl₂` root character of the additive complex Cartan line. -/
def plusRootCharacterHom : Multiplicative ℂ →* ℂˣ where
  toFun w := Units.mk0
    (Complex.exp (Multiplicative.toAdd w))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' w z := by
    ext
    change Complex.exp (Multiplicative.toAdd w + Multiplicative.toAdd z) =
      Complex.exp (Multiplicative.toAdd w) *
        Complex.exp (Multiplicative.toAdd z)
    rw [Complex.exp_add]

/-- Negative `sl₂` root character of the additive complex Cartan line. -/
def minusRootCharacterHom : Multiplicative ℂ →* ℂˣ where
  toFun w := Units.mk0
    (Complex.exp (-Multiplicative.toAdd w))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' w z := by
    ext
    change Complex.exp (-(Multiplicative.toAdd w + Multiplicative.toAdd z)) =
      Complex.exp (-Multiplicative.toAdd w) *
        Complex.exp (-Multiplicative.toAdd z)
    rw [show -(Multiplicative.toAdd w + Multiplicative.toAdd z) =
      -Multiplicative.toAdd w + -Multiplicative.toAdd z by ring,
      Complex.exp_add]

@[simp] theorem plusRootCharacterHom_apply (w : Multiplicative ℂ) :
    ((plusRootCharacterHom w : ℂˣ) : ℂ) =
      plusRootCharacter (Multiplicative.toAdd w) := by
  rfl

@[simp] theorem minusRootCharacterHom_apply (w : Multiplicative ℂ) :
    ((minusRootCharacterHom w : ℂˣ) : ℂ) =
      minusRootCharacter (Multiplicative.toAdd w) := by
  rfl

/-- The positive character law on additive coordinates is the monoid-hom law. -/
theorem plusRootCharacterHom_additive_readout (w z : ℂ) :
    ((plusRootCharacterHom (Multiplicative.ofAdd (w + z)) : ℂˣ) : ℂ) =
      ((plusRootCharacterHom (Multiplicative.ofAdd w) : ℂˣ) : ℂ) *
        ((plusRootCharacterHom (Multiplicative.ofAdd z) : ℂˣ) : ℂ) := by
  exact congrArg Units.val
    (plusRootCharacterHom.map_mul
      (Multiplicative.ofAdd w) (Multiplicative.ofAdd z))

/-- The negative character law on additive coordinates is the monoid-hom law. -/
theorem minusRootCharacterHom_additive_readout (w z : ℂ) :
    ((minusRootCharacterHom (Multiplicative.ofAdd (w + z)) : ℂˣ) : ℂ) =
      ((minusRootCharacterHom (Multiplicative.ofAdd w) : ℂˣ) : ℂ) *
        ((minusRootCharacterHom (Multiplicative.ofAdd z) : ℂˣ) : ℂ) := by
  exact congrArg Units.val
    (minusRootCharacterHom.map_mul
      (Multiplicative.ofAdd w) (Multiplicative.ofAdd z))

/-- On the punctured bipolar domain the positive bundled character evaluates to
exactly the Cayley coordinate `q(s)`. -/
theorem plusRootCharacterHom_bipolar
    {s : ℂ} (hs : s ∈ punctured01) :
    ((plusRootCharacterHom
      (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) = crossRatio01 s := by
  simpa using plusRootCharacter_bipolar hs

/-- On the punctured bipolar domain the negative bundled character evaluates to
exactly `q(s)⁻¹`. -/
theorem minusRootCharacterHom_bipolar
    {s : ℂ} (hs : s ∈ punctured01) :
    ((minusRootCharacterHom
      (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) =
        (crossRatio01 s)⁻¹ := by
  simpa using minusRootCharacter_bipolar hs

/-- The finite adjoint flow on the positive root space is the positive bundled
character representation. -/
theorem finiteAdjointFlow_sigmaPlus_eq_characterHom (s : ℂ) :
    torusAdjoint s σPlus =
      ((plusRootCharacterHom
        (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) • σPlus := by
  simpa using torusAdjoint_sigmaPlus_eq_plusRootCharacter s

/-- The finite adjoint flow on the negative root space is the negative bundled
character representation. -/
theorem finiteAdjointFlow_sigmaMinus_eq_characterHom (s : ℂ) :
    torusAdjoint s σMinus =
      ((minusRootCharacterHom
        (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) • σMinus := by
  simpa using torusAdjoint_sigmaMinus_eq_minusRootCharacter s

/-- Exact bundled-character packet: two opposite roots, finite adjoint action,
and the bipolar `q/q⁻¹` specialization. -/
theorem bipolar_root_character_representation_packet
    {s : ℂ} (hs : s ∈ punctured01) :
    torusAdjoint s σPlus =
        ((plusRootCharacterHom
          (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) • σPlus ∧
      torusAdjoint s σMinus =
        ((minusRootCharacterHom
          (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) • σMinus ∧
      ((plusRootCharacterHom
        (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) = crossRatio01 s ∧
      ((minusRootCharacterHom
        (Multiplicative.ofAdd (bipolarLog s)) : ℂˣ) : ℂ) =
          (crossRatio01 s)⁻¹ := by
  exact ⟨finiteAdjointFlow_sigmaPlus_eq_characterHom s,
    finiteAdjointFlow_sigmaMinus_eq_characterHom s,
    plusRootCharacterHom_bipolar hs,
    minusRootCharacterHom_bipolar hs⟩

end InfoGeometry.Canonical.BipolarLogarithmicRootCharacterRepresentation
