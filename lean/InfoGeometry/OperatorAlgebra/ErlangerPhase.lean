/-
InfoGeometry/OperatorAlgebra/ErlangerPhase.lean

Erlanger phase geometry for operator algebras.

The primitive morphisms are phase-preserving intertwiners.  Geometry is then
read through invariants under the chosen admissible morphism class.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/-! ## Phase-preserving morphisms -/

/--
A phase-preserving morphism is an intertwiner for the Hestenes phase axis.

This is the first Erlanger layer: the morphism respects the internal phase
structure before any metric, positivity, or arithmetic hypotheses are imposed.
-/
def PhasePreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (K₁ : H₁ →L[ℝ] H₁)
    (K₂ : H₂ →L[ℝ] H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp K₁ = K₂.comp F

namespace PhasePreserving

variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
variable {K₁ : H₁ →L[ℝ] H₁} {K₂ : H₂ →L[ℝ] H₂}
variable {F : H₁ →L[ℝ] H₂}

/-- Pointwise form of phase preservation. -/
theorem map_K
    (hF : PhasePreserving K₁ K₂ F)
    (v : H₁) :
    F (K₁ v) = K₂ (F v) := by
  have h := congrArg (fun L : H₁ →L[ℝ] H₂ => L v) hF
  simpa [PhasePreserving, ContinuousLinearMap.comp_apply] using h

end PhasePreserving

/-! ## Phase centralizer algebra -/

/--
The phase centralizer algebra: operators commuting with a fixed phase axis `K`.
-/
def PhaseLinear
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : H →L[ℝ] H)
    (T : H →L[ℝ] H) : Prop :=
  T.comp K = K.comp T

namespace PhaseLinear

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {K : H →L[ℝ] H}

/-- Pointwise form of phase-linearity. -/
theorem map_K
    {T : H →L[ℝ] H}
    (hT : PhaseLinear K T)
    (v : H) :
    T (K v) = K (T v) := by
  have h := congrArg (fun L : H →L[ℝ] H => L v) hT
  simpa [PhaseLinear, ContinuousLinearMap.comp_apply] using h

/-- The identity operator is phase-linear. -/
theorem one :
    PhaseLinear K (1 : H →L[ℝ] H) := by
  ext v
  simp

/-- The composition of phase-linear operators is phase-linear. -/
theorem comp
    {S T : H →L[ℝ] H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S.comp T) := by
  ext v
  change S (T (K v)) = K (S (T v))
  rw [map_K hT v, map_K hS (T v)]

/--
Conjugation by an invertible phase-linear operator preserves the phase
centralizer algebra.
-/
theorem conjugation
    (g : Units (H →L[ℝ] H))
    {T : H →L[ℝ] H}
    (hT : PhaseLinear K T)
    (hg : PhaseLinear K g.val)
    (hgi : PhaseLinear K (g⁻¹).val) :
    PhaseLinear K ((g.val.comp T).comp (g⁻¹).val) := by
  ext v
  change g.val (T ((g⁻¹).val (K v))) = K (g.val (T ((g⁻¹).val v)))
  calc
    g.val (T ((g⁻¹).val (K v)))
        = g.val (T (K ((g⁻¹).val v))) := by
          rw [map_K hgi v]
    _ = g.val (K (T ((g⁻¹).val v))) := by
          rw [map_K hT ((g⁻¹).val v)]
    _ = K (g.val (T ((g⁻¹).val v))) := by
          rw [map_K hg (T ((g⁻¹).val v))]

end PhaseLinear

/-! ## Metric-preserving refinements -/

/--
A linear map preserves the real Hilbert/Krein-background pairing represented
by the current real inner product.

Krein-specific indefinite forms can later replace this field with the
appropriate bilinear pairing datum.
-/
def MetricPreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (F : H₁ →L[ℝ] H₂) : Prop :=
  ∀ v w : H₁, inner (𝕜 := ℝ) (F v) (F w) = inner (𝕜 := ℝ) v w

/--
Second Erlanger layer: a morphism preserving both phase and metric structure.
-/
def PhaseMetricPreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (K₁ : H₁ →L[ℝ] H₁)
    (K₂ : H₂ →L[ℝ] H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  PhasePreserving K₁ K₂ F ∧ MetricPreserving F

/-! ## Erlanger invariants -/

/--
An Erlanger invariant is a readout unchanged by admissible phase conjugation.

This packages the slogan that the geometry is determined by the objects,
admissible morphisms, and readouts invariant under those morphisms.
-/
def ErlangerInvariant
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : H →L[ℝ] H)
    (α : Type*) : Type _ :=
  {read : (H →L[ℝ] H) → α //
    ∀ (g : Units (H →L[ℝ] H)) (T : H →L[ℝ] H),
      PhaseLinear K g.val →
      PhaseLinear K (g⁻¹).val →
      read ((g.val.comp T).comp (g⁻¹).val) = read T}

namespace ErlangerInvariant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {K : H →L[ℝ] H} {α : Type*}

/-- The operator readout carried by an Erlanger invariant. -/
abbrev read (I : ErlangerInvariant K α) : (H →L[ℝ] H) → α :=
  I.1

/-- The phase-conjugation law carried by an Erlanger invariant. -/
theorem invariant_under_phase_conjugation
    (I : ErlangerInvariant K α)
    (g : Units (H →L[ℝ] H))
    (T : H →L[ℝ] H)
    (hg : PhaseLinear K g.val)
    (hgi : PhaseLinear K (g⁻¹).val) :
    read I ((g.val.comp T).comp (g⁻¹).val) = read I T :=
  I.2 g T hg hgi

/-- Named re-export of phase-conjugation invariance. -/
theorem phase_conjugation
    (I : ErlangerInvariant K α)
    (g : Units (H →L[ℝ] H))
    (T : H →L[ℝ] H)
    (hg : PhaseLinear K g.val)
    (hgi : PhaseLinear K (g⁻¹).val) :
    I.read ((g.val.comp T).comp (g⁻¹).val) = I.read T :=
  invariant_under_phase_conjugation I g T hg hgi

end ErlangerInvariant

end InfoGeometry.OperatorAlgebra
