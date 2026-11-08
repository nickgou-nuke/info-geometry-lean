/-
InfoGeometry/Geometry/ErlangerPhaseGeometry.lean

Erlanger phase geometry for the Krein-Hestenes upper half-plane.

This module isolates the categorical/morphism layer:

* phase-preserving morphisms;
* phase-linear centralizer algebra;
* conjugation invariance;
* metric-preserving phase morphisms;
* preservation of the K-height form;
* optional chiral polarization data.

It does not introduce coordinates and does not define chirality as `iK` in the
real layer. Chiral projectors are supplied as proof-carrying data, or later
derived after complexification.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Geometry.ErlangerPhase

/-! ## 1. Real bounded endomorphisms -/

/-- Real bounded endomorphisms of a normed real vector space. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-! ## 2. Phase-preserving morphisms and phase-linear operators -/

/--
A phase-preserving morphism is an intertwiner for Hestenes phase axes:

`F K₁ = K₂ F`.
-/
def PhasePreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (K₁ : EndR H₁)
    (K₂ : EndR H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp K₁ = K₂.comp F

/--
The phase centralizer condition on one carrier:

`T K = K T`.
-/
def PhaseLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (T : EndR H) : Prop :=
  PhasePreserving K K T

namespace PhasePreserving

variable
    {H₁ H₂ H₃ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [NormedAddCommGroup H₃] [NormedSpace ℝ H₃]

/-- Pointwise form of phase preservation. -/
theorem map_K
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {F : H₁ →L[ℝ] H₂}
    (hF : PhasePreserving K₁ K₂ F)
    (v : H₁) :
    F (K₁ v) = K₂ (F v) := by
  change (F.comp K₁) v = (K₂.comp F) v
  rw [hF]

/-- Composition of phase-preserving morphisms is phase-preserving. -/
theorem comp
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {K₃ : EndR H₃}
    {F : H₁ →L[ℝ] H₂}
    {G : H₂ →L[ℝ] H₃}
    (hG : PhasePreserving K₂ K₃ G)
    (hF : PhasePreserving K₁ K₂ F) :
    PhasePreserving K₁ K₃ (G.comp F) := by
  ext v
  change G (F (K₁ v)) = K₃ (G (F v))
  rw [map_K hF v, map_K hG (F v)]

end PhasePreserving

namespace PhaseLinear

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H}

/-- Pointwise form of phase-linearity. -/
theorem map_K
    {T : EndR H}
    (hT : PhaseLinear K T)
    (v : H) :
    T (K v) = K (T v) :=
  PhasePreserving.map_K hT v

/-- The zero endomorphism is phase-linear. -/
theorem zero :
    PhaseLinear K (0 : EndR H) := by
  ext v
  simp

/-- The identity endomorphism is phase-linear. -/
theorem one :
    PhaseLinear K (1 : EndR H) := by
  ext v
  simp

/-- Sums of phase-linear endomorphisms are phase-linear. -/
theorem add
    {S T : EndR H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S + T) := by
  ext v
  change S (K v) + T (K v) = K (S v + T v)
  rw [map_K hS v, map_K hT v]
  simp

/-- Negatives of phase-linear endomorphisms are phase-linear. -/
theorem neg
    {T : EndR H}
    (hT : PhaseLinear K T) :
    PhaseLinear K (-T) := by
  ext v
  change -T (K v) = K (-T v)
  rw [map_K hT v]
  simp

/-- Differences of phase-linear endomorphisms are phase-linear. -/
theorem sub
    {S T : EndR H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S - T) := by
  simpa [sub_eq_add_neg] using add hS (neg hT)

/-- Real scalar multiples of phase-linear endomorphisms are phase-linear. -/
theorem smul
    (a : ℝ)
    {T : EndR H}
    (hT : PhaseLinear K T) :
    PhaseLinear K (a • T) := by
  ext v
  change a • T (K v) = K (a • T v)
  rw [map_K hT v]
  simp

/-- Compositions of phase-linear endomorphisms are phase-linear. -/
theorem comp
    {S T : EndR H}
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S.comp T) := by
  ext v
  change S (T (K v)) = K (S (T v))
  rw [map_K hT v, map_K hS (T v)]

end PhaseLinear

/--
The phase centralizer as an `ℝ`-submodule of bounded endomorphisms.

Multiplicative closure is given separately by `PhaseLinear.comp`.
-/
def PhaseCentralizer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) :
    Submodule ℝ (EndR H) where
  carrier := {T | PhaseLinear K T}
  zero_mem' := PhaseLinear.zero
  add_mem' := by
    intro S T hS hT
    exact PhaseLinear.add hS hT
  smul_mem' := by
    intro a T hT
    exact PhaseLinear.smul a hT

/-! ## 3. Phase-preserving conjugation -/

/-- Conjugation by a bounded invertible operator. -/
def phaseConjugate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (g : Units (EndR H))
    (T : EndR H) : EndR H :=
  (g.val.comp T).comp g.inv

/--
A phase-preserving unit is an invertible endomorphism whose value and inverse
both commute with `K`.
-/
structure PhaseUnit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) where
  unit : Units (EndR H)
  val_phase :
    PhaseLinear K unit.val
  inv_phase :
    PhaseLinear K unit.inv

namespace PhaseUnit

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : EndR H}

/-- Conjugation by a phase-preserving unit. -/
def conjugate
    (g : PhaseUnit K)
    (T : EndR H) : EndR H :=
  phaseConjugate g.unit T

/-- Phase-preserving conjugation preserves the phase centralizer. -/
theorem conjugate_phaseLinear
    (g : PhaseUnit K)
    {T : EndR H}
    (hT : PhaseLinear K T) :
    PhaseLinear K (g.conjugate T) := by
  dsimp [conjugate, phaseConjugate]
  exact PhaseLinear.comp
    (PhaseLinear.comp g.val_phase hT)
    g.inv_phase

end PhaseUnit

/-- An Erlanger invariant is a readout unchanged under admissible phase conjugation. -/
structure ErlangerInvariant
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (α : Type*) where
  read : EndR H → α

  invariant_under_phase_conjugation :
    ∀ (g : PhaseUnit K) (T : EndR H),
      PhaseLinear K T →
        read (g.conjugate T) = read T

/-! ## 4. Metric-preserving phase morphisms -/

/-- A bounded linear map preserves the real inner product. -/
def MetricPreserving
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (F : H₁ →L[ℝ] H₂) : Prop :=
  ∀ v w : H₁, inner (𝕜 := ℝ) (F v) (F w) = inner (𝕜 := ℝ) v w

/-- A phase-and-metric-preserving morphism. -/
structure PhaseMetricMorphism
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (K₁ : EndR H₁)
    (K₂ : EndR H₂) where
  toLinear : H₁ →L[ℝ] H₂
  phase :
    PhasePreserving K₁ K₂ toLinear
  metric :
    MetricPreserving toLinear

/-! ## 5. Intertwining arbitrary operators and preserving K-height -/

/--
A morphism intertwines operators `T₁` and `T₂` when

`F T₁ = T₂ F`.
-/
def IntertwinesOperator
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (T₁ : EndR H₁)
    (T₂ : EndR H₂)
    (F : H₁ →L[ℝ] H₂) : Prop :=
  F.comp T₁ = T₂.comp F

namespace IntertwinesOperator

variable
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]

/-- Pointwise form of operator intertwining. -/
theorem map_op
    {T₁ : EndR H₁}
    {T₂ : EndR H₂}
    {F : H₁ →L[ℝ] H₂}
    (hF : IntertwinesOperator T₁ T₂ F)
    (v : H₁) :
    F (T₁ v) = T₂ (F v) := by
  change (F.comp T₁) v = (T₂.comp F) v
  rw [hF]

end IntertwinesOperator

/--
Raw `Kτ` inner expression.

For the upper-half-plane positivity convention, the sign condition is usually

`KHeightInner K τ v v < 0`.
-/
def KHeightInner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K τ : EndR H)
    (v w : H) : ℝ :=
  inner (𝕜 := ℝ) v (K (τ w))

/--
Positive height form

`h_τ(v,w) = -⟪v, K τ w⟫`.
-/
def KHeightForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K τ : EndR H)
    (v w : H) : ℝ :=
  -KHeightInner K τ v w

/-- Metric and operator intertwiners preserve the raw `Kτ` inner expression. -/
theorem kHeightInner_preserved
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {τ₁ : EndR H₁}
    {τ₂ : EndR H₂}
    {F : H₁ →L[ℝ] H₂}
    (hK : PhasePreserving K₁ K₂ F)
    (hτ : IntertwinesOperator τ₁ τ₂ F)
    (hmetric : MetricPreserving F)
    (v w : H₁) :
    KHeightInner K₂ τ₂ (F v) (F w) =
      KHeightInner K₁ τ₁ v w := by
  dsimp [KHeightInner]
  have hτw : τ₂ (F w) = F (τ₁ w) := by
    exact (IntertwinesOperator.map_op hτ w).symm
  have hKw : K₂ (τ₂ (F w)) = F (K₁ (τ₁ w)) := by
    rw [hτw]
    exact (PhasePreserving.map_K hK (τ₁ w)).symm
  rw [hKw]
  exact hmetric v (K₁ (τ₁ w))

/-- Metric and operator intertwiners preserve the positive `K`-height form. -/
theorem kHeightForm_preserved
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {τ₁ : EndR H₁}
    {τ₂ : EndR H₂}
    {F : H₁ →L[ℝ] H₂}
    (hK : PhasePreserving K₁ K₂ F)
    (hτ : IntertwinesOperator τ₁ τ₂ F)
    (hmetric : MetricPreserving F)
    (v w : H₁) :
    KHeightForm K₂ τ₂ (F v) (F w) =
      KHeightForm K₁ τ₁ v w := by
  dsimp [KHeightForm]
  rw [kHeightInner_preserved hK hτ hmetric v w]

/-- Upper-half-plane positivity for a phase-axis/operator pair. -/
def KHalfPlanePositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K τ : EndR H) : Prop :=
  ∀ v : H, v ≠ 0 → KHeightInner K τ v v < 0

/-- Surjective phase-and-metric intertwiners transfer upper-half-plane positivity. -/
theorem KHalfPlanePositive.transfer_of_surjective
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    {τ₁ : EndR H₁}
    {τ₂ : EndR H₂}
    {F : H₁ →L[ℝ] H₂}
    (hK : PhasePreserving K₁ K₂ F)
    (hτ : IntertwinesOperator τ₁ τ₂ F)
    (hmetric : MetricPreserving F)
    (hsurj : Function.Surjective F)
    (hpos : KHalfPlanePositive K₁ τ₁) :
    KHalfPlanePositive K₂ τ₂ := by
  intro y hy
  rcases hsurj y with ⟨x, rfl⟩
  have hx : x ≠ 0 := by
    intro hx
    apply hy
    simp [hx]
  have hEq :
      KHeightInner K₂ τ₂ (F x) (F x) =
        KHeightInner K₁ τ₁ x x :=
    kHeightInner_preserved hK hτ hmetric x x
  rw [hEq]
  exact hpos x hx

/-! ## 6. Optional chiral polarization layer -/

/--
A real chiral polarization associated to a phase axis.

This is deliberately not defined as `χ = iK` in the real layer. It may later
be derived after complexification, or supplied by a real involution that is
compatible with the phase structure.
-/
structure ChiralPolarization
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H) where
  PL : EndR H
  PR : EndR H

  PL_phase :
    PhaseLinear K PL
  PR_phase :
    PhaseLinear K PR

  PL_idempotent :
    PL.comp PL = PL
  PR_idempotent :
    PR.comp PR = PR

  complementary :
    PL + PR = 1

  disjoint_left :
    PL.comp PR = 0
  disjoint_right :
    PR.comp PL = 0

/-- A phase-preserving morphism preserves specified chiral projectors. -/
structure PhaseChiralMorphism
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    {K₁ : EndR H₁}
    {K₂ : EndR H₂}
    (C₁ : ChiralPolarization K₁)
    (C₂ : ChiralPolarization K₂) where
  toLinear : H₁ →L[ℝ] H₂

  phase :
    PhasePreserving K₁ K₂ toLinear

  preserves_left :
    IntertwinesOperator C₁.PL C₂.PL toLinear

  preserves_right :
    IntertwinesOperator C₁.PR C₂.PR toLinear

end InfoGeometry.Geometry.ErlangerPhase
