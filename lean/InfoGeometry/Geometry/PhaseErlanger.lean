/-
InfoGeometry/Geometry/PhaseErlanger.lean

Erlanger phase geometry for Hestenes/Krein structures.

This file formalizes the first invariant layer:

  geometry = objects + admissible morphisms + invariants.

The primitive admissible morphism is phase preservation:

  F ∘ K₁ = K₂ ∘ F.

This implies functoriality of the phase centralizer algebra and, after a
complexified/split chiral axis is supplied, functoriality of the chiral
polarization projectors.
-/

import Mathlib.Tactic
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Geometry.PhaseErlanger

/-! ## 1. Basic phase-preserving morphisms -/

/-- Bounded real-linear endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/--
A phase-preserving morphism is an intertwiner for the Hestenes phase axes.

This is the first Erlanger morphism class.
-/
def PhasePreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (K₁ : EndR H₁)
    (K₂ : EndR H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp K₁ = K₂.comp F

namespace PhasePreserving

variable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {F : H₁ →L[ℝ] H₂}

/-- Pointwise form of phase preservation. -/
theorem map_K
    (hF : PhasePreserving K₁ K₂ F)
    (x : H₁) :
    F (K₁ x) = K₂ (F x) := by
  change (F.comp K₁) x = (K₂.comp F) x
  rw [hF]

end PhasePreserving

/--
The phase centralizer condition on one carrier.

`PhaseLinear K T` means `T` belongs to `End_K(H)`.
-/
def PhaseLinear
    {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (T : EndR H) : Prop :=
  T.comp K = K.comp T

namespace PhaseLinear

variable
    {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H}

/-- Pointwise form of phase-linearity. -/
theorem map_K
    {T : EndR H}
    (hT : PhaseLinear K T)
    (x : H) :
    T (K x) = K (T x) := by
  change (T.comp K) x = (K.comp T) x
  rw [hT]

/-- The identity operator is phase-linear. -/
theorem id :
    PhaseLinear K (ContinuousLinearMap.id ℝ H) := by
  ext x
  rfl

/-- The zero operator is phase-linear. -/
theorem zero :
    PhaseLinear K (0 : EndR H) := by
  ext x
  simp

/-- Sums of phase-linear operators are phase-linear. -/
theorem add
    {S T : EndR H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S + T) := by
  ext x
  simp [
    ContinuousLinearMap.comp_apply,
    map_K hS x,
    map_K hT x
  ]

/-- Negatives of phase-linear operators are phase-linear. -/
theorem neg
    {T : EndR H}
    (hT : PhaseLinear K T) :
    PhaseLinear K (-T) := by
  ext x
  simp [
    ContinuousLinearMap.comp_apply,
    map_K hT x
  ]

/-- Differences of phase-linear operators are phase-linear. -/
theorem sub
    {S T : EndR H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S - T) := by
  simpa [sub_eq_add_neg] using add hS (neg hT)

/-- Real scalar multiples of phase-linear operators are phase-linear. -/
theorem smul
    (a : ℝ)
    {T : EndR H}
    (hT : PhaseLinear K T) :
    PhaseLinear K (a • T) := by
  ext x
  simp [
    map_K hT x
  ]

/-- Compositions of phase-linear operators are phase-linear. -/
theorem comp
    {S T : EndR H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S.comp T) := by
  ext x
  change S (T (K x)) = K (S (T x))
  rw [map_K hT x, map_K hS (T x)]

end PhaseLinear

/-! ## 2. Phase centralizer and phase isomorphisms -/

/--
The phase centralizer algebra as a bundled type.

This packages operators satisfying `T K = K T`.
-/
structure PhaseCentralizer
    {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) where
  op : EndR H
  phase_linear : PhaseLinear K op

/--
A phase isomorphism between two Hestenes phase carriers.

This is the isomorphism-level Erlanger morphism.
-/
structure PhaseIsomorphism
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (K₁ : EndR H₁)
    (K₂ : EndR H₂) where
  toLinear : H₁ →L[ℝ] H₂
  invLinear : H₂ →L[ℝ] H₁

  left_inv :
    invLinear.comp toLinear = ContinuousLinearMap.id ℝ H₁

  right_inv :
    toLinear.comp invLinear = ContinuousLinearMap.id ℝ H₂

  phase_to :
    PhasePreserving K₁ K₂ toLinear

  phase_inv :
    PhasePreserving K₂ K₁ invLinear

namespace PhaseIsomorphism

variable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}

/-- Conjugation of an operator by a phase isomorphism. -/
def conjugateOperator
    (Φ : PhaseIsomorphism K₁ K₂)
    (T : EndR H₁) : EndR H₂ :=
  (Φ.toLinear.comp T).comp Φ.invLinear

/--
Phase-linearity is invariant under phase-preserving conjugation.

If `T K₁ = K₁ T`, then `Φ T Φ⁻¹` commutes with `K₂`.
-/
theorem conjugate_phaseLinear
    (Φ : PhaseIsomorphism K₁ K₂)
    {T : EndR H₁}
    (hT : PhaseLinear K₁ T) :
    PhaseLinear K₂ (conjugateOperator Φ T) := by
  ext y
  change
    Φ.toLinear (T (Φ.invLinear (K₂ y))) =
      K₂ (Φ.toLinear (T (Φ.invLinear y)))
  calc
    Φ.toLinear (T (Φ.invLinear (K₂ y)))
        = Φ.toLinear (T (K₁ (Φ.invLinear y))) := by
          rw [PhasePreserving.map_K Φ.phase_inv y]
    _ = Φ.toLinear (K₁ (T (Φ.invLinear y))) := by
          rw [PhaseLinear.map_K hT (Φ.invLinear y)]
    _ = K₂ (Φ.toLinear (T (Φ.invLinear y))) := by
          rw [PhasePreserving.map_K Φ.phase_to (T (Φ.invLinear y))]

/-- Conjugation restricts to a map of phase centralizer algebras. -/
def conjugateCentralizer
    (Φ : PhaseIsomorphism K₁ K₂)
    (T : PhaseCentralizer K₁) :
    PhaseCentralizer K₂ where
  op := conjugateOperator Φ T.op
  phase_linear := conjugate_phaseLinear Φ T.phase_linear

end PhaseIsomorphism

/-! ## 3. Chiral polarization after supplying a split/complexified axis -/

/--
A chiral axis associated to a phase carrier.

In the real file we do not define `χ := iK`. Instead, after complexification
or after supplying a split involution, the chiral axis is data satisfying
`χ² = 1`.

This avoids reintroducing a scalar imaginary unit into the purely real phase
layer.
-/
structure ChiralAxis
    {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) where
  chi : EndR H

  /-- The chiral involution is compatible with the phase axis. -/
  chi_phase_linear :
    PhaseLinear K chi

  /-- The chiral operator is a split involution. -/
  chi_square_one :
    chi.comp chi = ContinuousLinearMap.id ℝ H

namespace ChiralAxis

variable
    {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H}

/-- Left chiral projector, formally `(1 + χ) / 2`. -/
def leftProjector
    (χ : ChiralAxis K) : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H + χ.chi)

/-- Right chiral projector, formally `(1 - χ) / 2`. -/
def rightProjector
    (χ : ChiralAxis K) : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H - χ.chi)

/-- The left chiral projector is phase-linear. -/
theorem leftProjector_phaseLinear
    (χ : ChiralAxis K) :
    PhaseLinear K χ.leftProjector := by
  exact PhaseLinear.smul (1 / 2 : ℝ)
    (PhaseLinear.add PhaseLinear.id χ.chi_phase_linear)

/-- The right chiral projector is phase-linear. -/
theorem rightProjector_phaseLinear
    (χ : ChiralAxis K) :
    PhaseLinear K χ.rightProjector := by
  exact PhaseLinear.smul (1 / 2 : ℝ)
    (PhaseLinear.sub PhaseLinear.id χ.chi_phase_linear)

/-- The two chiral projectors add up to the identity. -/
theorem leftProjector_add_rightProjector
    (χ : ChiralAxis K) :
    χ.leftProjector + χ.rightProjector = ContinuousLinearMap.id ℝ H := by
  ext x
  calc
    (χ.leftProjector + χ.rightProjector) x
        = (1 / 2 : ℝ) • (x + χ.chi x) + (1 / 2 : ℝ) • (x - χ.chi x) := by
            rfl
    _ = (1 / 2 : ℝ) • ((x + χ.chi x) + (x - χ.chi x)) := by
            rw [← smul_add]
    _ = (1 / 2 : ℝ) • (x + x) := by
            simp [add_assoc]
    _ = x := by
            rw [show x + x = (2 : ℝ) • x by simp [two_smul]]
            rw [smul_smul]
            norm_num

/-- The right and left chiral projectors add up to the identity. -/
theorem rightProjector_add_leftProjector
    (χ : ChiralAxis K) :
    χ.rightProjector + χ.leftProjector = ContinuousLinearMap.id ℝ H := by
  simpa [add_comm] using leftProjector_add_rightProjector (K := K) χ

end ChiralAxis

/-- A map preserves chiral axes if it intertwines the supplied chiral involutions. -/
def ChiralPreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    (χ₁ : ChiralAxis K₁)
    (χ₂ : ChiralAxis K₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp χ₁.chi = χ₂.chi.comp F

namespace ChiralPreserving

variable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {χ₁ : ChiralAxis K₁}
    {χ₂ : ChiralAxis K₂}
    {F : H₁ →L[ℝ] H₂}

/-- Pointwise form of chiral preservation. -/
theorem map_chi
    (hF : ChiralPreserving χ₁ χ₂ F)
    (x : H₁) :
    F (χ₁.chi x) = χ₂.chi (F x) := by
  change (F.comp χ₁.chi) x = (χ₂.chi.comp F) x
  rw [hF]

/-- A chiral-preserving map intertwines the left chiral projectors. -/
theorem leftProjector_intertwines
    (hF : ChiralPreserving χ₁ χ₂ F) :
    F.comp χ₁.leftProjector =
      χ₂.leftProjector.comp F := by
  ext x
  simp [
    ChiralAxis.leftProjector,
    map_chi hF x
  ]

/-- A chiral-preserving map intertwines the right chiral projectors. -/
theorem rightProjector_intertwines
    (hF : ChiralPreserving χ₁ χ₂ F) :
    F.comp χ₁.rightProjector =
      χ₂.rightProjector.comp F := by
  ext x
  simp [
    ChiralAxis.rightProjector,
    map_chi hF x
  ]

end ChiralPreserving

/-! ## 4. Metric and positivity preserving refinements -/

/--
Metric preservation for a real Hilbert/Krein carrier modeled by the ambient
real inner product.

For an indefinite Krein form, replace this with the repository's Krein pairing.
-/
def MetricPreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (F : H₁ →L[ℝ] H₂) : Prop :=
  ∀ x y : H₁, inner (𝕜 := ℝ) (F x) (F y) = inner (𝕜 := ℝ) x y

/--
A phase-and-metric preserving morphism.

This is the second Erlanger layer.
-/
structure PhaseMetricMorphism
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (K₁ : EndR H₁)
    (K₂ : EndR H₂) where
  toLinear : H₁ →L[ℝ] H₂
  phase_preserving :
    PhasePreserving K₁ K₂ toLinear
  metric_preserving :
    MetricPreserving toLinear

/-! ## 5. Erlanger invariants -/

/--
An Erlanger invariant is a readout unchanged by admissible phase conjugation.

The readout is defined on the phase centralizer because the first geometry is
the category of phase-linear operators.
-/
structure ErlangerInvariant
    {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (α : Type*) where
  read : PhaseCentralizer K → α

  invariant_under_phase_conjugation :
    ∀ (Φ : PhaseIsomorphism K K)
      (T : PhaseCentralizer K),
      read (PhaseIsomorphism.conjugateCentralizer Φ T) = read T

/-! ## 6. Owner target -/

/--
Owner target for the first Erlanger phase layer.

The target is intentionally structural: it does not assert a preferred metric,
a preferred upper-half-plane cone, or a modular subgroup. Those are later
Erlanger refinements.
-/
@[owner_target_tag]
def PhaseErlangerOwnerTarget : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H),
    PhaseLinear K (ContinuousLinearMap.id ℝ H)

theorem phaseErlangerOwnerTarget :
    PhaseErlangerOwnerTarget := by
  intro H _ _ K
  exact PhaseLinear.id

/-- Every phase axis has a canonical phase-centralizer element: the identity. -/
def phaseCentralizer_id
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) : PhaseCentralizer K where
  op := ContinuousLinearMap.id ℝ H
  phase_linear := phaseErlangerOwnerTarget H K

@[simp] theorem phaseCentralizer_id_op
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) :
    (phaseCentralizer_id H K).op = ContinuousLinearMap.id ℝ H :=
  rfl

end InfoGeometry.Geometry.PhaseErlanger
