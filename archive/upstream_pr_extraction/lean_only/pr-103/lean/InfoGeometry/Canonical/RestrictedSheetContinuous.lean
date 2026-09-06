import InfoGeometry.Canonical.MongeAmpereDualSheetBridge

namespace InfoGeometry.Canonical.RestrictedSheetContinuous

open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.PolarizedSector

/-- Continuous sheetwise automorphism data on the doubled carrier. -/
structure RestrictedSheetContinuousEquiv
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  plus : E ≃L[ℝ] E
  minus : E ≃L[ℝ] E

namespace RestrictedSheetContinuousEquiv

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

@[ext] theorem ext (g h : RestrictedSheetContinuousEquiv E)
    (hplus : g.plus = h.plus) (hminus : g.minus = h.minus) : g = h := by
  cases g
  cases h
  cases hplus
  cases hminus
  rfl

/-- Multiplication is chosen so that the doubled lift is a homomorphism into operator composition. -/
instance : Mul (RestrictedSheetContinuousEquiv E) where
  mul g₁ g₂ :=
    { plus := g₂.plus.trans g₁.plus
      minus := g₂.minus.trans g₁.minus }

instance : One (RestrictedSheetContinuousEquiv E) where
  one :=
    { plus := ContinuousLinearEquiv.refl ℝ E
      minus := ContinuousLinearEquiv.refl ℝ E }

instance : Inv (RestrictedSheetContinuousEquiv E) where
  inv g :=
    { plus := g.plus.symm
      minus := g.minus.symm }

instance : Group (RestrictedSheetContinuousEquiv E) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc a b c := by
    cases a
    cases b
    cases c
    rfl
  one_mul a := by
    cases a
    rfl
  mul_one a := by
    cases a
    rfl
  inv_mul_cancel a := by
    cases a with
    | mk plus minus =>
        ext x
        · change plus.symm (plus x) = x
          exact plus.symm_apply_apply x
        · change minus.symm (minus x) = x
          exact minus.symm_apply_apply x

@[simp] theorem plus_mul (g h : RestrictedSheetContinuousEquiv E) :
    (g * h).plus = h.plus.trans g.plus := rfl

@[simp] theorem minus_mul (g h : RestrictedSheetContinuousEquiv E) :
    (g * h).minus = h.minus.trans g.minus := rfl

@[simp] theorem plus_one :
    (1 : RestrictedSheetContinuousEquiv E).plus = ContinuousLinearEquiv.refl ℝ E := rfl

@[simp] theorem minus_one :
    (1 : RestrictedSheetContinuousEquiv E).minus = ContinuousLinearEquiv.refl ℝ E := rfl

@[simp] theorem plus_inv (g : RestrictedSheetContinuousEquiv E) :
    (g⁻¹).plus = g.plus.symm := rfl

@[simp] theorem minus_inv (g : RestrictedSheetContinuousEquiv E) :
    (g⁻¹).minus = g.minus.symm := rfl

/-- Operator-valued doubled lift of the continuous sheet transport. -/
noncomputable def liftedOperator (g : RestrictedSheetContinuousEquiv E) : EndH :=
  (plusPointL (E := E)).comp (g.plus.toContinuousLinearMap.comp (fst_L (E := E))) +
    (minusPointL (E := E)).comp (g.minus.toContinuousLinearMap.comp (snd_L (E := E)))

@[simp] theorem liftedOperator_apply_to_doubled (g : RestrictedSheetContinuousEquiv E)
    (x xi : E) :
    liftedOperator g (to_doubled x xi : H₂) = to_doubled (g.plus x) (g.minus xi) := by
  apply DoubledSpace.ext <;>
    simp [liftedOperator, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      ContinuousLinearMap.comp_apply]

@[simp] theorem plusBlockMap_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    plusBlockMap (E := E) (liftedOperator g) = g.plus.toContinuousLinearMap := by
  ext x
  simp [plusBlockMap, liftedOperator]

@[simp] theorem minusBlockMap_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    minusBlockMap (E := E) (liftedOperator g) = g.minus.toContinuousLinearMap := by
  ext x
  simp [minusBlockMap, liftedOperator]

@[simp] theorem plusToMinusBlockMap_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    plusToMinusBlockMap (E := E) (liftedOperator g) = 0 := by
  ext x
  simp [plusToMinusBlockMap, liftedOperator]

@[simp] theorem minusToPlusBlockMap_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    minusToPlusBlockMap (E := E) (liftedOperator g) = 0 := by
  ext x
  simp [minusToPlusBlockMap, liftedOperator]

theorem spectralPlusProj_comp_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    (spectralPlusProj (E := E)).comp (liftedOperator g)
      = (liftedOperator g).comp (spectralPlusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, liftedOperator, spectralPlusProj_apply_eq_plusPoint]

theorem spectralMinusProj_comp_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    (spectralMinusProj (E := E)).comp (liftedOperator g)
      = (liftedOperator g).comp (spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, liftedOperator, spectralMinusProj_apply_eq_minusPoint]

@[simp] theorem plusProjectorFlux_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    plusProjectorFlux (E := E) (liftedOperator g) = 0 := by
  unfold plusProjectorFlux
  rw [spectralPlusProj_comp_liftedOperator]
  simp

@[simp] theorem minusProjectorFlux_liftedOperator (g : RestrictedSheetContinuousEquiv E) :
    minusProjectorFlux (E := E) (liftedOperator g) = 0 := by
  unfold minusProjectorFlux
  rw [spectralMinusProj_comp_liftedOperator]
  simp

theorem liftedOperator_mul (g h : RestrictedSheetContinuousEquiv E) :
    liftedOperator (g * h) = (liftedOperator g).comp (liftedOperator h) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext <;>
    simp [liftedOperator, ContinuousLinearMap.comp_apply]

/-- Common-mode Weyl balance means both sheet automorphisms agree. -/
def IsGaugeBalanced (g : RestrictedSheetContinuousEquiv E) : Prop :=
  g.plus = g.minus

@[simp] theorem isGaugeBalanced_one :
    IsGaugeBalanced (1 : RestrictedSheetContinuousEquiv E) := rfl

theorem IsGaugeBalanced.mul {g h : RestrictedSheetContinuousEquiv E}
    (hg : IsGaugeBalanced g) (hh : IsGaugeBalanced h) :
    IsGaugeBalanced (g * h) := by
  unfold IsGaugeBalanced at hg hh ⊢
  change h.plus.trans g.plus = h.minus.trans g.minus
  rw [hg, hh]

theorem IsGaugeBalanced.inv {g : RestrictedSheetContinuousEquiv E}
    (hg : IsGaugeBalanced g) :
    IsGaugeBalanced g⁻¹ := by
  unfold IsGaugeBalanced at hg ⊢
  change g.plus.symm = g.minus.symm
  rw [hg]

theorem liftedOperator_eq_dualSheetLift_of_isGaugeBalanced
    {g : RestrictedSheetContinuousEquiv E} (hg : IsGaugeBalanced g) :
    liftedOperator g = dualSheetLift (E := E) g.plus.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext
  · simp [liftedOperator, dualSheetLift, ContinuousLinearMap.comp_apply]
  · simp [liftedOperator, dualSheetLift, ContinuousLinearMap.comp_apply]
    rw [hg]

end Basic

end RestrictedSheetContinuousEquiv

/-- Abstract closure-stable restriction on continuous sheet transports. -/
class SheetRestriction (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  Holds : RestrictedSheetContinuousEquiv E → Prop
  one_mem : Holds 1
  mul_mem :
    ∀ {g h : RestrictedSheetContinuousEquiv E},
      Holds g → Holds h → Holds (g * h)
  inv_mem :
    ∀ {g : RestrictedSheetContinuousEquiv E},
      Holds g → Holds g⁻¹

/-- Restricted continuous shell with an abstract Shale-Stinespring-type condition. -/
abbrev ShaleStinespringEquiv
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SheetRestriction E] :=
  { g : RestrictedSheetContinuousEquiv E // SheetRestriction.Holds g }

namespace ShaleStinespringEquiv

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [SheetRestriction E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

instance : Coe (ShaleStinespringEquiv E) (RestrictedSheetContinuousEquiv E) where
  coe g := g.1

instance : Mul (ShaleStinespringEquiv E) where
  mul g h := ⟨g.1 * h.1, SheetRestriction.mul_mem g.2 h.2⟩

instance : One (ShaleStinespringEquiv E) where
  one := ⟨1, SheetRestriction.one_mem⟩

instance : Inv (ShaleStinespringEquiv E) where
  inv g := ⟨g.1⁻¹, SheetRestriction.inv_mem g.2⟩

instance : Group (ShaleStinespringEquiv E) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc a b c := by
    cases a
    cases b
    cases c
    rfl
  one_mul a := by
    cases a
    rfl
  mul_one a := by
    cases a
    rfl
  inv_mul_cancel a := by
    apply Subtype.ext
    exact (inv_mul_cancel (a := (a : RestrictedSheetContinuousEquiv E)))

@[simp] theorem val_mul (g h : ShaleStinespringEquiv E) :
    ((g * h : ShaleStinespringEquiv E) : RestrictedSheetContinuousEquiv E)
      = (g : RestrictedSheetContinuousEquiv E) * (h : RestrictedSheetContinuousEquiv E) := rfl

@[simp] theorem val_one :
    ((1 : ShaleStinespringEquiv E) : RestrictedSheetContinuousEquiv E) = 1 := rfl

@[simp] theorem val_inv (g : ShaleStinespringEquiv E) :
    ((g⁻¹ : ShaleStinespringEquiv E) : RestrictedSheetContinuousEquiv E)
      = (g : RestrictedSheetContinuousEquiv E)⁻¹ := rfl

/-- Doubled lifted operator on the restricted shell. -/
noncomputable def liftedOperator (g : ShaleStinespringEquiv E) : EndH :=
  RestrictedSheetContinuousEquiv.liftedOperator (E := E) g.1

@[simp] theorem liftedOperator_coe (g : ShaleStinespringEquiv E) :
    liftedOperator g = RestrictedSheetContinuousEquiv.liftedOperator (E := E) g.1 := rfl

@[simp] theorem liftedOperator_mul (g h : ShaleStinespringEquiv E) :
    liftedOperator (g * h) = (liftedOperator g).comp (liftedOperator h) := by
  simpa [liftedOperator] using
    RestrictedSheetContinuousEquiv.liftedOperator_mul (E := E)
      (g := (g : RestrictedSheetContinuousEquiv E))
      (h := (h : RestrictedSheetContinuousEquiv E))

@[simp] theorem plusProjectorFlux_liftedOperator (g : ShaleStinespringEquiv E) :
    plusProjectorFlux (E := E) (liftedOperator g) = 0 := by
  simp [liftedOperator]

@[simp] theorem minusProjectorFlux_liftedOperator (g : ShaleStinespringEquiv E) :
    minusProjectorFlux (E := E) (liftedOperator g) = 0 := by
  simp [liftedOperator]

end Basic

end ShaleStinespringEquiv

section NamedRestrictions

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Gauge-balanced transports: both sheets evolve identically. -/
def gaugeBalancedSheetRestriction : SheetRestriction E where
  Holds g := RestrictedSheetContinuousEquiv.IsGaugeBalanced g
  one_mem := RestrictedSheetContinuousEquiv.isGaugeBalanced_one (E := E)
  mul_mem := by
    intro g h hg hh
    exact RestrictedSheetContinuousEquiv.IsGaugeBalanced.mul hg hh
  inv_mem := by
    intro g hg
    exact RestrictedSheetContinuousEquiv.IsGaugeBalanced.inv hg

@[simp] theorem gaugeBalancedSheetRestriction_holds_iff
    (g : RestrictedSheetContinuousEquiv E) :
    (gaugeBalancedSheetRestriction (E := E)).Holds g ↔ RestrictedSheetContinuousEquiv.IsGaugeBalanced g :=
  Iff.rfl

/-- The gauge-balanced restricted shell. -/
abbrev GaugeBalancedEquiv :=
  @ShaleStinespringEquiv E _ _ _ (gaugeBalancedSheetRestriction (E := E))

namespace GaugeBalancedEquiv

local instance : SheetRestriction E := gaugeBalancedSheetRestriction (E := E)
local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

@[simp] theorem isGaugeBalanced (g : GaugeBalancedEquiv (E := E)) :
    RestrictedSheetContinuousEquiv.IsGaugeBalanced (g : RestrictedSheetContinuousEquiv E) :=
  g.2

@[simp] theorem liftedOperator_eq_dualSheetLift (g : GaugeBalancedEquiv (E := E)) :
    ShaleStinespringEquiv.liftedOperator (E := E) g =
      dualSheetLift (E := E) ((g : RestrictedSheetContinuousEquiv E).plus.toContinuousLinearMap) := by
  simpa [ShaleStinespringEquiv.liftedOperator] using
    RestrictedSheetContinuousEquiv.liftedOperator_eq_dualSheetLift_of_isGaugeBalanced
      (E := E) (g := (g : RestrictedSheetContinuousEquiv E)) g.2

@[simp] theorem plusProjectorFlux_liftedOperator (g : GaugeBalancedEquiv (E := E)) :
    plusProjectorFlux (E := E) (ShaleStinespringEquiv.liftedOperator (E := E) g) = 0 := by
  rw [liftedOperator_eq_dualSheetLift]
  simp

@[simp] theorem minusProjectorFlux_liftedOperator (g : GaugeBalancedEquiv (E := E)) :
    minusProjectorFlux (E := E) (ShaleStinespringEquiv.liftedOperator (E := E) g) = 0 := by
  rw [liftedOperator_eq_dualSheetLift]
  simp

end GaugeBalancedEquiv

end NamedRestrictions

/-- Compatibility name for the genuine gauge-balanced sheet restriction. -/
def trivialSheetRestriction (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    SheetRestriction E where
  Holds := RestrictedSheetContinuousEquiv.IsGaugeBalanced
  one_mem := RestrictedSheetContinuousEquiv.isGaugeBalanced_one
  mul_mem := by
    intro g h hg hh
    exact RestrictedSheetContinuousEquiv.IsGaugeBalanced.mul hg hh
  inv_mem := by
    intro g hg
    exact RestrictedSheetContinuousEquiv.IsGaugeBalanced.inv hg

end InfoGeometry.Canonical.RestrictedSheetContinuous
