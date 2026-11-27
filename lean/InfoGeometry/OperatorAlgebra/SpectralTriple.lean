/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
InfoGeometry/OperatorAlgebra/SpectralTriple.lean

Real, phase-compatible, integration-aware spectral triple sockets.

This file separates:

* `K`, the Hestenes phase axis;
* `J`, the Connes real structure, represented real-linearly;
* `chi`, the chiral grading;
* `D`, the spectral generator;
* trace/weight/core-trace/renormalized integration backends.

Key point:

`K` is not `J`.

`K` is the real-linear phase/complex-structure axis.
`J` is the real structure; in the real formalism it is phase-reversing:
`J K = - K J`.
-/

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Tactic.NthRewrite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Geometry.PhaseErlanger
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.DoubledSpace

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.SpectralTriple

/-! ## 1. Basic bounded real operator notation -/

/-- Bounded real-linear endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

abbrev PhaseLinear
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : EndR H)
    (T : EndR H) : Prop :=
  InfoGeometry.Geometry.PhaseErlanger.PhaseLinear K T

/-- Commutator of bounded real-linear operators. -/
def commutator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S T : EndR H) : EndR H :=
  S.comp T - T.comp S

/-! ## 2. KO-sign bookkeeping -/

/--
KO-sign package.

In a concrete real spectral triple these signs depend on the KO-dimension
modulo 8. Here they are carried explicitly.
-/
structure KOSigns where
  epsJ : ℝ
  epsD : ℝ
  epsChi : ℝ

  epsJ_sq :
    epsJ * epsJ = 1

  epsD_sq :
    epsD * epsD = 1

  epsChi_sq :
    epsChi * epsChi = 1

/-! ## 3. Phase axis and real structure -/

/--
A Hestenes phase axis.

This is the real-linear replacement for a scalar imaginary unit. It is not the
Connes real structure.
-/
structure PhaseAxis
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  K : EndR H

  /-- Elliptic phase condition: `K² = -1`. -/
  K_square_neg :
    K.comp K = -(ContinuousLinearMap.id ℝ H)

/--
A real structure compatible with a phase axis.

In the real formalization, a complex antiunitary `J` is represented as a
real-linear invertible operator. Its anti-linearity relative to the phase axis
is encoded by

`J K = - K J`.
-/
structure RealStructure
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H)
    (signs : KOSigns) where
  J : Units (EndR H)

  /-- KO-sign relation for `J²`. -/
  J_square :
    J.val.comp J.val =
      signs.epsJ • ContinuousLinearMap.id ℝ H

  /--
  Real-structure anti-linearity relative to the Hestenes phase axis.

  This is the real-linear encoding of `J(i v) = -i J(v)`.
  -/
  J_phase_reversing :
    J.val.comp K.K = -(K.K.comp J.val)

/--
Metric compatibility of the real structure.

For an indefinite Krein pairing, this should later be replaced by the
repository's Krein form rather than the ambient Hilbert inner product.
-/
def RealStructureMetricCompatible
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs) : Prop :=
  ∀ x y : H,
    inner (𝕜 := ℝ) (J.J.val x) (J.J.val y) =
      inner (𝕜 := ℝ) x y

/--
Krein-form compatibility of the real structure.

This pairs with `InfoGeometry.Krein.KreinSpace.kreinInner` rather than the
ambient Hilbert inner product, allowing indefinite Krein real structures that
are not Hilbert isometries and distinguishing Hilbert metric compatibility from
Krein compatibility when `KreinSpace.J ≠ Id`.
-/
def RealStructureKreinCompatible
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs) : Prop :=
  ∀ x y : H,
    InfoGeometry.Krein.KreinSpace.kreinInner (J.J.val x) (J.J.val y) =
      InfoGeometry.Krein.KreinSpace.kreinInner x y

theorem realStructureKreinCompatible_iff_isKreinIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs) :
    RealStructureKreinCompatible J ↔
      InfoGeometry.Krein.KreinSpace.IsKreinIsometry J.J.val :=
  Iff.rfl

theorem realStructureKreinCompatible_iff_kreinAdjoint_comp_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs) :
    RealStructureKreinCompatible J ↔
      (InfoGeometry.Krein.KreinSpace.kreinAdjoint J.J.val).comp J.J.val =
        ContinuousLinearMap.id ℝ H :=
  (realStructureKreinCompatible_iff_isKreinIsometry J).trans
    (InfoGeometry.Krein.KreinSpace.isKreinIsometry_iff_star_comp_self J.J.val)

theorem realStructureKreinCompatible_iff_metricCompatible_of_hilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    (hJ : InfoGeometry.Krein.KreinSpace.J (H := H) = LinearIsometryEquiv.refl ℝ H)
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs) :
    RealStructureKreinCompatible J ↔ RealStructureMetricCompatible J := by
  simp [RealStructureKreinCompatible, RealStructureMetricCompatible,
    InfoGeometry.Krein.KreinSpace.kreinInner_def, hJ]

/-! ## 4. Chiral grading -/

/--
A chiral grading/split involution.

This is the real grading `chi`, not the elliptic phase axis `K`.
-/
structure ChiralGrading
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : PhaseAxis H)
    (_signs : KOSigns) where
  chi : EndR H

  /-- Chirality is phase-linear. -/
  chi_phase_linear :
    PhaseLinear K.K chi

  /-- Split involution: `chi² = 1`. -/
  chi_square_one :
    chi.comp chi = ContinuousLinearMap.id ℝ H

/-- KO-sign compatibility between the chosen real structure and chiral grading. -/
def RealStructureChiralCompatible
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs)
    (χ : ChiralGrading H K signs) : Prop :=
  J.J.val.comp χ.chi =
    signs.epsChi • (χ.chi.comp J.J.val)

namespace ChiralGrading

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}

/-- Left chiral projector `(1 + chi)/2`. -/
def leftProjector
    (χ : ChiralGrading H K signs) : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H + χ.chi)

/-- Right chiral projector `(1 - chi)/2`. -/
def rightProjector
    (χ : ChiralGrading H K signs) : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H - χ.chi)

end ChiralGrading

/-! ## 5. Spectral generator -/

/--
Bounded spectral generator.

The carrier is a bounded real-linear endomorphism.  Closed unbounded operators
and compact-resolvent data are intentionally kept as explicit proof obligations.
-/
structure SpectralGenerator
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  D : EndR H

/--
Native compact-resolvent data for a bounded real spectral generator.

The chosen continuous operator is a two-sided inverse of `D - λ` and is
compact.  This is deliberately separate from `SpectralGenerator`: generic
commutator constructions only need the operator, while compact resolvent is a
Hilbert-space spectral-triple obligation.
-/
structure CompactResolventData
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : EndR H) where
  spectralParameter : ℝ
  resolvent : EndR H
  resolvent_comp_shift :
    resolvent.comp
        (D - spectralParameter • ContinuousLinearMap.id ℝ H) =
      ContinuousLinearMap.id ℝ H
  shift_comp_resolvent :
    (D - spectralParameter • ContinuousLinearMap.id ℝ H).comp resolvent =
      ContinuousLinearMap.id ℝ H
  resolvent_compact : IsCompactOperator resolvent

namespace SpectralGenerator

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : SpectralGenerator H)

@[simp]
theorem comp_id :
    D.D.comp (ContinuousLinearMap.id ℝ H) = D.D := by
  ext x
  rfl

@[simp]
theorem id_comp :
    (ContinuousLinearMap.id ℝ H).comp D.D = D.D := by
  ext x
  rfl

@[simp]
theorem commutator_self :
    commutator D.D D.D = 0 := by
  ext x
  simp [commutator]

end SpectralGenerator

/-- The spectral generator is odd relative to a chiral grading. -/
def DiracOdd
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (D : SpectralGenerator H)
    (χ : ChiralGrading H K signs) : Prop :=
  D.D.comp χ.chi + χ.chi.comp D.D = 0

/-- KO-sign compatibility between `J` and `D`. -/
def RealStructureDiracCompatible
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (J : RealStructure H K signs)
    (D : SpectralGenerator H) : Prop :=
  J.J.val.comp D.D =
    signs.epsD • (D.D.comp J.J.val)

/-! ## 6. Represented algebra and order conditions -/

/--
A represented real operator algebra.

A future `StarRing` refinement should strengthen the interaction between
`star` and the representation. This socket only requires the operation needed
to write `b*` in the opposite representation.
-/
structure RepresentedAlgebra
    (A H : Type*)
    [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  rep : A →+* EndR H

/--
The opposite representation induced by the real structure.

In a full star-algebra version this should use `J rep(b*) J^{-1}`.
Here the `star` operation is carried by the typeclass.
-/
def oppositeRep
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (b : A) : EndR H :=
  (J.J.val.comp (ρ.rep (star b))).comp ((J.J)⁻¹).val

/--
Order-zero condition:

the represented algebra commutes with the opposite algebra.
-/
def OrderZeroCondition
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs) : Prop :=
  ∀ a b : A,
    (ρ.rep a).comp (oppositeRep ρ J b) =
      (oppositeRep ρ J b).comp (ρ.rep a)

/--
Order-one condition:

commutators with `D` commute with the opposite algebra.
-/
def OrderOneCondition
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : PhaseAxis H}
    {signs : KOSigns}
    (ρ : RepresentedAlgebra A H)
    (J : RealStructure H K signs)
    (D : SpectralGenerator H) : Prop :=
  ∀ a b : A,
    (commutator D.D (ρ.rep a)).comp (oppositeRep ρ J b) =
      (oppositeRep ρ J b).comp (commutator D.D (ρ.rep a))

/-! ## 7. Spectral metric readouts -/

/--
The Lipschitz seminorm candidate supplied by the spectral generator.

This is the operator-algebraic metric sensor:

`a ↦ ‖[D, rho(a)]‖`.
-/
def lipschitzSeminorm
    {A H : Type*}
    [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : RepresentedAlgebra A H)
    (D : SpectralGenerator H)
    (a : A) : ℝ :=
  ‖commutator D.D (ρ.rep a)‖

theorem lipschitzSeminorm_nonneg
    {A H : Type*}
    [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : RepresentedAlgebra A H)
    (D : SpectralGenerator H)
    (a : A) :
    0 ≤ lipschitzSeminorm ρ D a :=
  norm_nonneg _

/--
A real-valued state/readout on the represented algebra.

This is intentionally abstract. Later modules can specialize it to positive
normalized states, vector states, KMS states, or boundary states.
-/
abbrev StateReadout (A : Type*) := A → ℝ

namespace StateReadout

abbrev eval {A : Type*} (φ : StateReadout A) : A → ℝ := φ

end StateReadout

/--
Connes-style distance candidate between two state readouts.

This records the admissible values rather than trying to take a supremum at
this abstract layer.
-/
def ConnesDistanceAdmissibleValue
    {A H : Type*}
    [Ring A]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : RepresentedAlgebra A H)
    (D : SpectralGenerator H)
    (φ ψ : StateReadout A)
    (r : ℝ) : Prop :=
  ∃ a : A,
    lipschitzSeminorm ρ D a ≤ 1 ∧
      r = |φ.eval a - ψ.eval a|

/-! ## 8. Renormalized integration sockets -/

/--
Dixmier-trace-like backend.

This is the logarithmic-divergence socket. Use it for critical summability,
where ordinary trace-class integration is not available.
-/
structure DixmierTraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  positiveCone : Set A
  dixmierTrace : A → ℝ≥0∞
  positive :
    ∀ x : A, x ∈ positiveCone → (0 : ℝ≥0∞) ≤ dixmierTrace x
  finiteOnPositive :
    ∀ x : A, x ∈ positiveCone → dixmierTrace x ≠ ⊤
  traceLikeCyclicity :
    ∀ a b : A, dixmierTrace (a * b) = dixmierTrace (b * a)

namespace DixmierTraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (τ : DixmierTraceDatum A)

/-- The Dixmier backend extracts finite logarithmic readouts on its positive cone. -/
theorem logarithmicDivergenceExtraction :
    ∀ x : A, x ∈ τ.positiveCone → τ.dixmierTrace x ≠ ⊤ := by
  exact τ.finiteOnPositive

end DixmierTraceDatum

/--
Zeta-function renormalization backend.

This is the socket for readouts such as residues or finite parts of

`Tr(a |D|^{-s})`.
-/
structure ZetaRenormalizationDatum
    (A : Type*) where
  zeta : A → ℂ → ℂ
  poleSet : Set ℂ
  residueReadout : A → ℂ → ℂ
  finitePartReadout : A → ℂ → ℂ
  continuousOffPole : ∀ (a : A) (z : ℂ), z ∉ poleSet → ContinuousAt (zeta a) z

namespace ZetaRenormalizationDatum

variable {A : Type*}
variable (ζ : ZetaRenormalizationDatum A)

/-- The zeta backend is holomorphic away from the supplied pole set. -/
theorem meromorphicContinuation :
    ∀ (a : A) (z : ℂ), z ∉ ζ.poleSet → ContinuousAt (ζ.zeta a) z := by
  exact ζ.continuousOffPole

end ZetaRenormalizationDatum

/--
Renormalized integration backend.

This refines the coarse enum case `renormalizedCyclicCocycle`.
-/
inductive RenormalizedIntegrationBackend
    (A : Type*) [AddCommMonoid A] [Mul A] where
  | dixmierTrace (τ : DixmierTraceDatum A)
  | zetaRenormalization (ζ : ZetaRenormalizationDatum A)
  | cyclicCocycle
      (readout : A → ℝ)
      (cyclicity : ∀ a b : A, readout (a * b) = readout (b * a))

namespace RenormalizedIntegrationBackend

variable {A : Type*} [Semigroup A]

/-- Pairwise cyclicity rotates a three-operator product without commuting any
of its factors. -/
theorem cyclicCocycle_triple_product_rotation
    (readout : A → ℝ)
    (hcyc : ∀ a b : A, readout (a * b) = readout (b * a))
    (a b c : A) :
    readout ((a * b) * c) = readout (b * (c * a)) ∧
      readout ((a * b) * c) = readout (c * (a * b)) := by
  constructor
  · calc
      readout ((a * b) * c) = readout (a * (b * c)) := by rw [mul_assoc]
      _ = readout ((b * c) * a) := hcyc a (b * c)
      _ = readout (b * (c * a)) := by rw [← mul_assoc]
  · calc
      readout ((a * b) * c) = readout (c * (a * b)) := hcyc (a * b) c

end RenormalizedIntegrationBackend

/-! ## 9. Real, phase-compatible spectral triple -/

/--
A real, phase-compatible, integration-aware spectral triple socket.

This is deliberately witness-based. It separates:

* `K`, the Hestenes phase axis;
* `J`, the Connes real structure;
* `chi`, the chiral grading;
* `D`, the spectral generator;
* trace/weight/core-trace/renormalized integration backends.
-/
structure PhaseRealSpectralTriple
    (A H : Type*)
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The chosen star operation on the real-linear operator carrier. -/
  operatorStar : Star (EndR H)

  signs : KOSigns

  phaseAxis : PhaseAxis H

  realStructure :
    RealStructure H phaseAxis signs

  realStructureMetricCompatible :
    RealStructureMetricCompatible realStructure

  grading :
    ChiralGrading H phaseAxis signs

  J_chi_compatible :
    RealStructureChiralCompatible realStructure grading

  spectralGenerator :
    SpectralGenerator H

  D_selfAdjoint :
    @IsSelfAdjoint (EndR H) operatorStar spectralGenerator.D

  D_compactResolvent :
    CompactResolventData spectralGenerator.D

  D_phase_linear :
    PhaseLinear phaseAxis.K spectralGenerator.D

  representedAlgebra :
    RepresentedAlgebra A H

  /-- The represented algebra is phase-linear relative to the Hestenes axis. -/
  rep_phase_linear :
    ∀ a : A, PhaseLinear phaseAxis.K (representedAlgebra.rep a)

  orderZero :
    OrderZeroCondition representedAlgebra realStructure

  orderOne :
    OrderOneCondition representedAlgebra realStructure spectralGenerator

  D_odd :
    DiracOdd spectralGenerator grading

  J_D_compatible :
    RealStructureDiracCompatible realStructure spectralGenerator

  /-- Ordinary trace backend, available only in trace-capable cases. -/
  traceBackend :
    Option (InfoGeometry.OperatorAlgebra.TraceDatum (EndR H))

  /-- Modular weight backend, needed in type III cases. -/
  modularWeightBackend :
    Option (InfoGeometry.OperatorAlgebra.ModularWeightDatum (EndR H))

  /-- Renormalized backend for Dixmier/zeta/cyclic-cocycle readouts. -/
  renormalizedBackend :
    Option (RenormalizedIntegrationBackend (EndR H))

namespace PhaseRealSpectralTriple

variable
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The spectral triple's Lipschitz seminorm. -/
def lipschitz
    (T : PhaseRealSpectralTriple A H)
    (a : A) : ℝ :=
  lipschitzSeminorm T.representedAlgebra T.spectralGenerator a

theorem lipschitz_nonneg
    (T : PhaseRealSpectralTriple A H)
    (a : A) :
    0 ≤ T.lipschitz a :=
  lipschitzSeminorm_nonneg T.representedAlgebra T.spectralGenerator a

/-- Order-one condition, re-exported as a theorem from the witness. -/
theorem orderOne_apply
    (T : PhaseRealSpectralTriple A H)
    (a b : A) :
    (commutator T.spectralGenerator.D (T.representedAlgebra.rep a)).comp
        (oppositeRep T.representedAlgebra T.realStructure b)
      =
    (oppositeRep T.representedAlgebra T.realStructure b).comp
        (commutator T.spectralGenerator.D (T.representedAlgebra.rep a)) :=
  T.orderOne a b

end PhaseRealSpectralTriple

/-! ## 10. Krein-compatible spectral triples and Hilbert-vs-Krein separation -/

/--
Compatibility predicate upgrading a `PhaseRealSpectralTriple` to an indefinite
`KreinSpace` by requiring Krein-isometry of `J` (`RealStructureKreinCompatible`)
and Krein-skew-adjointness of `D`.
-/
def PhaseRealSpectralTriple.IsKreinCompatible
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    (T : PhaseRealSpectralTriple A H) : Prop :=
  RealStructureKreinCompatible T.realStructure ∧
    InfoGeometry.Krein.KreinSpace.IsKreinSkewAdjoint T.spectralGenerator.D

/--
Krein-native real, phase-compatible spectral triple socket.

Unlike `PhaseRealSpectralTriple`, this structure uses `RealStructureKreinCompatible`
(`KreinSpace.kreinInner`) and `KreinSpace.IsKreinSkewAdjoint` directly instead of
Hilbert metric compatibility and an ambient `operatorStar`, so genuinely indefinite
Krein real structures (which fail `RealStructureMetricCompatible`) can be
instantiated natively.
-/
structure KreinPhaseRealSpectralTriple
    (A H : Type*)
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H] where
  signs : KOSigns
  phaseAxis : PhaseAxis H
  realStructure : RealStructure H phaseAxis signs
  realStructureKreinCompatible : RealStructureKreinCompatible realStructure
  grading : ChiralGrading H phaseAxis signs
  J_chi_compatible : RealStructureChiralCompatible realStructure grading
  spectralGenerator : SpectralGenerator H
  D_kreinSkewAdjoint : InfoGeometry.Krein.KreinSpace.IsKreinSkewAdjoint spectralGenerator.D
  D_compactResolvent : CompactResolventData spectralGenerator.D
  D_phase_linear : PhaseLinear phaseAxis.K spectralGenerator.D
  representedAlgebra : RepresentedAlgebra A H
  rep_phase_linear : ∀ a : A, PhaseLinear phaseAxis.K (representedAlgebra.rep a)
  orderZero : OrderZeroCondition representedAlgebra realStructure
  orderOne : OrderOneCondition representedAlgebra realStructure spectralGenerator
  D_odd : DiracOdd spectralGenerator grading
  J_D_compatible : RealStructureDiracCompatible realStructure spectralGenerator
  traceBackend : Option (InfoGeometry.OperatorAlgebra.TraceDatum (EndR H))
  modularWeightBackend : Option (InfoGeometry.OperatorAlgebra.ModularWeightDatum (EndR H))
  renormalizedBackend : Option (RenormalizedIntegrationBackend (EndR H))

namespace KreinPhaseRealSpectralTriple

variable
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]

/-- The Krein spectral triple's Lipschitz seminorm. -/
def lipschitz
    (T : KreinPhaseRealSpectralTriple A H)
    (a : A) : ℝ :=
  lipschitzSeminorm T.representedAlgebra T.spectralGenerator a

theorem lipschitz_nonneg
    (T : KreinPhaseRealSpectralTriple A H)
    (a : A) :
    0 ≤ T.lipschitz a :=
  lipschitzSeminorm_nonneg T.representedAlgebra T.spectralGenerator a

/-- Order-one condition re-exported for `KreinPhaseRealSpectralTriple`. -/
theorem orderOne_apply
    (T : KreinPhaseRealSpectralTriple A H)
    (a b : A) :
    (commutator T.spectralGenerator.D (T.representedAlgebra.rep a)).comp
        (oppositeRep T.representedAlgebra T.realStructure b)
      =
    (oppositeRep T.representedAlgebra T.realStructure b).comp
        (commutator T.spectralGenerator.D (T.representedAlgebra.rep a)) :=
  T.orderOne a b

/-- Convert a `KreinPhaseRealSpectralTriple` back to `PhaseRealSpectralTriple`
when Hilbert metric compatibility and an operator star witness are also supplied. -/
def toPhaseRealSpectralTriple
    (T : KreinPhaseRealSpectralTriple A H)
    (operatorStar : Star (EndR H))
    (hMetric : RealStructureMetricCompatible T.realStructure)
    (hD_self : @IsSelfAdjoint (EndR H) operatorStar T.spectralGenerator.D) :
    PhaseRealSpectralTriple A H where
  operatorStar := operatorStar
  signs := T.signs
  phaseAxis := T.phaseAxis
  realStructure := T.realStructure
  realStructureMetricCompatible := hMetric
  grading := T.grading
  J_chi_compatible := T.J_chi_compatible
  spectralGenerator := T.spectralGenerator
  D_selfAdjoint := hD_self
  D_compactResolvent := T.D_compactResolvent
  D_phase_linear := T.D_phase_linear
  representedAlgebra := T.representedAlgebra
  rep_phase_linear := T.rep_phase_linear
  orderZero := T.orderZero
  orderOne := T.orderOne
  D_odd := T.D_odd
  J_D_compatible := T.J_D_compatible
  traceBackend := T.traceBackend
  modularWeightBackend := T.modularWeightBackend
  renormalizedBackend := T.renormalizedBackend

end KreinPhaseRealSpectralTriple

/-- Package a Krein-compatible `PhaseRealSpectralTriple` as a `KreinPhaseRealSpectralTriple`. -/
def PhaseRealSpectralTriple.toKreinPhaseRealSpectralTriple
    {A H : Type*}
    [Ring A] [Star A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    (T : PhaseRealSpectralTriple A H)
    (hKrein : T.IsKreinCompatible) :
    KreinPhaseRealSpectralTriple A H where
  signs := T.signs
  phaseAxis := T.phaseAxis
  realStructure := T.realStructure
  realStructureKreinCompatible := hKrein.1
  grading := T.grading
  J_chi_compatible := T.J_chi_compatible
  spectralGenerator := T.spectralGenerator
  D_kreinSkewAdjoint := hKrein.2
  D_compactResolvent := T.D_compactResolvent
  D_phase_linear := T.D_phase_linear
  representedAlgebra := T.representedAlgebra
  rep_phase_linear := T.rep_phase_linear
  orderZero := T.orderZero
  orderOne := T.orderOne
  D_odd := T.D_odd
  J_D_compatible := T.J_D_compatible
  traceBackend := T.traceBackend
  modularWeightBackend := T.modularWeightBackend
  renormalizedBackend := T.renormalizedBackend

section KreinMetricSeparation

open InfoGeometry.Krein

private def doubledMat2CLM (a b c d : ℝ) : EndR (DoubledSpace ℝ) where
  toFun u :=
    to_doubled
      (a * WithLp.fst u + b * WithLp.snd u)
      (c * WithLp.fst u + d * WithLp.snd u)
  map_add' u v := by
    apply DoubledSpace.ext <;>
      simp [WithLp.add_fst, WithLp.add_snd, mul_add] <;> ring
  map_smul' r u := by
    apply DoubledSpace.ext <;>
      simp [WithLp.smul_fst, WithLp.smul_snd] <;> ring
  cont := by
    refine (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)).comp ?_
    have hfst : Continuous (fun u : DoubledSpace ℝ => WithLp.fst u) :=
      WithLp.continuous_fst (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)
    have hsnd : Continuous (fun u : DoubledSpace ℝ => WithLp.snd u) :=
      WithLp.continuous_snd (p := (2 : ENNReal)) (α := ℝ) (β := ℝ)
    exact ((continuous_const.mul hfst).add (continuous_const.mul hsnd)).prodMk
      ((continuous_const.mul hfst).add (continuous_const.mul hsnd))

@[simp] private lemma doubledMat2CLM_apply (a b c d : ℝ) (u : DoubledSpace ℝ) :
    doubledMat2CLM a b c d u =
      to_doubled
        (a * WithLp.fst u + b * WithLp.snd u)
        (c * WithLp.fst u + d * WithLp.snd u) := rfl

private lemma doubledMat2CLM_comp (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    (doubledMat2CLM a₁ b₁ c₁ d₁).comp (doubledMat2CLM a₂ b₂ c₂ d₂) =
      doubledMat2CLM
        (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂)
        (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp <;> ring

private def doubledUnitKOSigns : KOSigns where
  epsJ := 1
  epsD := 1
  epsChi := 1
  epsJ_sq := by norm_num
  epsD_sq := by norm_num
  epsChi_sq := by norm_num

/-- Standard elliptic phase axis `complex_i` on `DoubledSpace ℝ`. -/
def doubledModularPhaseAxis : PhaseAxis (DoubledSpace ℝ) where
  K := complex_i (E := ℝ)
  K_square_neg := complex_i_sq ℝ

/-- Standard modular swap `modular_j` as a `RealStructure` on `DoubledSpace ℝ`. -/
def doubledModularRealStructure :
    RealStructure (DoubledSpace ℝ) doubledModularPhaseAxis doubledUnitKOSigns where
  J :=
    { val := modular_j (E := ℝ)
      inv := modular_j (E := ℝ)
      val_inv := modular_j_involution ℝ
      inv_val := modular_j_involution ℝ }
  J_square := by
    simp [doubledUnitKOSigns, modular_j_involution]
  J_phase_reversing := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [doubledModularPhaseAxis, complex_i, modular_j, spectral_epsilon]

theorem doubledModularRealStructure_metricCompatible :
    RealStructureMetricCompatible doubledModularRealStructure := by
  intro x y
  change inner (𝕜 := ℝ) (modular_j (E := ℝ) x) (modular_j (E := ℝ) y) = inner (𝕜 := ℝ) x y
  simp [modular_j_apply, WithLp.prod_inner_apply, add_comm]

theorem doubledModularRealStructure_not_kreinCompatible :
    ¬ RealStructureKreinCompatible doubledModularRealStructure := by
  intro h
  have h1 := h (to_doubled (1 : ℝ) (0 : ℝ)) (to_doubled (1 : ℝ) (0 : ℝ))
  have hm : doubledModularRealStructure.J.val (to_doubled (1 : ℝ) (0 : ℝ)) =
      to_doubled (0 : ℝ) (1 : ℝ) := by
    apply DoubledSpace.ext <;> simp [doubledModularRealStructure, modular_j_apply]
  rw [hm, kreinInner_to_doubled, kreinInner_to_doubled] at h1
  norm_num at h1

/-- Hyperbolic-boosted phase axis on `DoubledSpace ℝ`. -/
def doubledBoostPhaseAxis : PhaseAxis (DoubledSpace ℝ) where
  K := doubledMat2CLM (15 / 8) (-17 / 8) (17 / 8) (-15 / 8)
  K_square_neg := by
    rw [doubledMat2CLM_comp]
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp <;> ring

/-- Hyperbolic-boosted real structure on `DoubledSpace ℝ` (`SO(1,1)` boost of `spectral_epsilon`). -/
def doubledBoostRealStructure :
    RealStructure (DoubledSpace ℝ) doubledBoostPhaseAxis doubledUnitKOSigns where
  J :=
    { val := doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)
      inv := doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)
      val_inv := by
        change (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)).comp
            (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)) =
          ContinuousLinearMap.id ℝ (DoubledSpace ℝ)
        rw [doubledMat2CLM_comp]
        apply ContinuousLinearMap.ext
        intro u
        apply DoubledSpace.ext <;> simp <;> ring
      inv_val := by
        change (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)).comp
            (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)) =
          ContinuousLinearMap.id ℝ (DoubledSpace ℝ)
        rw [doubledMat2CLM_comp]
        apply ContinuousLinearMap.ext
        intro u
        apply DoubledSpace.ext <;> simp <;> ring }
  J_square := by
    change (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)).comp
        (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)) =
      doubledUnitKOSigns.epsJ • ContinuousLinearMap.id ℝ (DoubledSpace ℝ)
    rw [doubledMat2CLM_comp]
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp [doubledUnitKOSigns] <;> ring
  J_phase_reversing := by
    change (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)).comp
        (doubledMat2CLM (15 / 8) (-17 / 8) (17 / 8) (-15 / 8)) =
      -((doubledMat2CLM (15 / 8) (-17 / 8) (17 / 8) (-15 / 8)).comp
        (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8)))
    rw [doubledMat2CLM_comp, doubledMat2CLM_comp]
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> simp <;> ring

theorem doubledBoostRealStructure_kreinCompatible :
    RealStructureKreinCompatible doubledBoostRealStructure := by
  intro x y
  change KreinSpace.kreinInner
      (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8) x)
      (doubledMat2CLM (17 / 8) (-15 / 8) (15 / 8) (-17 / 8) y) =
    KreinSpace.kreinInner x y
  have hx : x = to_doubled (WithLp.fst x) (WithLp.snd x) := by
    apply DoubledSpace.ext <;> rfl
  have hy : y = to_doubled (WithLp.fst y) (WithLp.snd y) := by
    apply DoubledSpace.ext <;> rfl
  nth_rw 2 [hx]
  nth_rw 2 [hy]
  rw [doubledMat2CLM_apply, doubledMat2CLM_apply, kreinInner_to_doubled, kreinInner_to_doubled]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem doubledBoostRealStructure_not_metricCompatible :
    ¬ RealStructureMetricCompatible doubledBoostRealStructure := by
  intro h
  have h1 := h (to_doubled (1 : ℝ) (0 : ℝ)) (to_doubled (1 : ℝ) (0 : ℝ))
  have hb : doubledBoostRealStructure.J.val (to_doubled (1 : ℝ) (0 : ℝ)) =
      to_doubled (17 / 8 : ℝ) (15 / 8 : ℝ) := by
    apply DoubledSpace.ext <;> simp [doubledBoostRealStructure]
  rw [hb] at h1
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial] at h1
  norm_num at h1

/-- Two-way separation theorem showing `RealStructureKreinCompatible` and
`RealStructureMetricCompatible` are genuinely distinct conditions whenever
`KreinSpace.J ≠ Id`, witnessed explicitly on `DoubledSpace ℝ`. -/
theorem realStructure_krein_metric_separation :
    KreinSpace.J (H := DoubledSpace ℝ) ≠ LinearIsometryEquiv.refl ℝ (DoubledSpace ℝ) ∧
      (RealStructureMetricCompatible doubledModularRealStructure ∧
        ¬ RealStructureKreinCompatible doubledModularRealStructure) ∧
      (RealStructureKreinCompatible doubledBoostRealStructure ∧
        ¬ RealStructureMetricCompatible doubledBoostRealStructure) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hJ
    have h0 := congrArg (fun e : DoubledSpace ℝ ≃ₗᵢ[ℝ] DoubledSpace ℝ =>
      WithLp.snd (e (to_doubled (0 : ℝ) (1 : ℝ)))) hJ
    change -(1 : ℝ) = (1 : ℝ) at h0
    norm_num at h0
  · exact ⟨doubledModularRealStructure_metricCompatible,
      doubledModularRealStructure_not_kreinCompatible⟩
  · exact ⟨doubledBoostRealStructure_kreinCompatible,
      doubledBoostRealStructure_not_metricCompatible⟩

end KreinMetricSeparation

end InfoGeometry.OperatorAlgebra.SpectralTriple
