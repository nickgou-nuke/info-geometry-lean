import Mathlib
import InfoGeometry.Projective.Rays

/-!
# Operator/Fierz readout correspondence

This owner supplies the missing generic correspondence layer without claiming
that arbitrary operators are separated by Fierz coordinates. A supplied
readout determines its observational quotient; the quotient is then
canonically equivalent to the readout range. Modular, Krein, and projective
compatibility are explicit hypotheses on maps, not inferred from names.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorFierzReadoutCorrespondence

universe u v

section Quotient

variable {X : Type u} {Y : Type v}

/-- Equality of readouts is the observational kernel relation. -/
def readoutSetoid (ρ : X → Y) : Setoid X where
  r x y := ρ x = ρ y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The quotient carrier determined by a supplied observable readout. -/
abbrev ReadoutQuotient (ρ : X → Y) := Quotient (readoutSetoid ρ)

/-- Canonical projection to the observational quotient. -/
def quotientMap (ρ : X → Y) : X → ReadoutQuotient ρ :=
  Quotient.mk (readoutSetoid ρ)

/-- The readout descends through its observational quotient. -/
def quotientReadout (ρ : X → Y) : ReadoutQuotient ρ → Y :=
  Quotient.lift ρ (by
    intro x y h
    exact h)

@[simp] theorem quotientReadout_quotientMap
    (ρ : X → Y) (x : X) :
    quotientReadout ρ (quotientMap ρ x) = ρ x := by
  rfl

/-- The quotient map into the concrete readout range. -/
def quotientRangeMap (ρ : X → Y) :
    ReadoutQuotient ρ → Set.range ρ :=
  Quotient.lift (fun x => ⟨ρ x, ⟨x, rfl⟩⟩) (by
    intro x y h
    apply Subtype.ext
    exact h)

@[simp] theorem quotientRangeMap_quotientMap
    (ρ : X → Y) (x : X) :
    quotientRangeMap ρ (quotientMap ρ x) = ⟨ρ x, ⟨x, rfl⟩⟩ := by
  rfl

theorem quotientRangeMap_val
    (ρ : X → Y) (q : ReadoutQuotient ρ) :
    (quotientRangeMap ρ q).1 = quotientReadout ρ q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- First-isomorphism theorem for an arbitrary supplied readout. -/
noncomputable def quotientRangeEquiv (ρ : X → Y) :
    ReadoutQuotient ρ ≃ Set.range ρ :=
  Equiv.ofBijective (quotientRangeMap ρ) (by
    constructor
    · intro a b h
      revert b
      refine Quotient.inductionOn a ?_
      intro x b
      refine Quotient.inductionOn b ?_
      intro y h
      apply Quotient.sound
      change ρ x = ρ y
      exact congrArg Subtype.val h
    · intro y
      rcases y with ⟨z, ⟨x, hx⟩⟩
      refine ⟨quotientMap ρ x, ?_⟩
      apply Subtype.ext
      simpa [quotientRangeMap_quotientMap] using hx)

@[simp] theorem quotientRangeEquiv_quotientMap
    (ρ : X → Y) (x : X) :
    quotientRangeEquiv ρ (quotientMap ρ x) = ⟨ρ x, ⟨x, rfl⟩⟩ := by
  rfl

end Quotient

section Compatibility

variable {X : Type u} {Y : Type v}

/-- A modular readout intertwining contract. -/
def ModularReadoutCompatible
    (ρ : X → Y) (σ : X → X) (τ : Y → Y) : Prop :=
  ∀ x, ρ (σ x) = τ (ρ x)

/-- A Krein-adjoint/readout intertwining contract. -/
def KreinReadoutCompatible
    (ρ : X → Y) (κX : X → X) (κY : Y → Y) : Prop :=
  ∀ x, ρ (κX x) = κY (ρ x)

theorem modular_quotient_readout
    (ρ : X → Y) (σ : X → X) (τ : Y → Y)
    (hσ : ModularReadoutCompatible ρ σ τ) (x : X) :
    quotientReadout ρ (quotientMap ρ (σ x)) =
      τ (quotientReadout ρ (quotientMap ρ x)) := by
  change ρ (σ x) = τ (ρ x)
  exact hσ x

theorem krein_quotient_readout
    (ρ : X → Y) (κX : X → X) (κY : Y → Y)
    (hκ : KreinReadoutCompatible ρ κX κY) (x : X) :
    quotientReadout ρ (quotientMap ρ (κX x)) =
      κY (quotientReadout ρ (quotientMap ρ x)) := by
  change ρ (κX x) = κY (ρ x)
  exact hκ x

/-- A modular action descends to the observational quotient when it preserves
equality of readouts. -/
def quotientAction
    (ρ : X → Y) (σ : X → X)
    (hσ : ∀ {x y}, ρ x = ρ y → ρ (σ x) = ρ (σ y)) :
    ReadoutQuotient ρ → ReadoutQuotient ρ :=
  Quotient.map σ (fun _ _ h => hσ h)

@[simp] theorem quotientAction_quotientMap
    (ρ : X → Y) (σ : X → X)
    (hσ : ∀ {x y}, ρ x = ρ y → ρ (σ x) = ρ (σ y)) (x : X) :
    quotientAction ρ σ hσ (quotientMap ρ x) = quotientMap ρ (σ x) := by
  change Quotient.map σ (fun _ _ h => hσ h) (Quotient.mk _ x) = Quotient.mk _ (σ x)
  rfl

theorem quotientAction_readout_intertwines
    (ρ : X → Y) (σ : X → X) (τ : Y → Y)
    (hσ : ∀ {x y}, ρ x = ρ y → ρ (σ x) = ρ (σ y))
    (hτ : ModularReadoutCompatible ρ σ τ) (q : ReadoutQuotient ρ) :
    quotientReadout ρ (quotientAction ρ σ hσ q) =
      τ (quotientReadout ρ q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change ρ (σ x) = τ (ρ x)
  exact hτ x

end Compatibility

section ProjectiveDescent

variable {X : Type u} {Y : Type v} {Z : Type*}

/-- Any map from readouts to a projective base descends through the same
observational quotient. -/
def projectiveBaseDescent (ρ : X → Y) (π : Y → Z) :
    ReadoutQuotient ρ → Z :=
  Quotient.lift (π ∘ ρ) (by
    intro x y h
    exact congrArg π h)

@[simp] theorem projectiveBaseDescent_quotientMap
    (ρ : X → Y) (π : Y → Z) (x : X) :
    projectiveBaseDescent ρ π (quotientMap ρ x) = π (ρ x) := by
  rfl

end ProjectiveDescent

end InfoGeometry.Canonical.OperatorFierzReadoutCorrespondence
