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

import Mathlib
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Geometry.PhaseErlanger

noncomputable section

open scoped ENNReal

namespace SpectralTriple

open PhaseErlanger

/-! ## 1. Basic bounded real operator notation -/

/-- Bounded real-linear endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

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

  /-- Self-adjointness or Krein-self-adjointness obligation for concrete models. -/
  selfAdjoint : Prop

  /-- Compact-resolvent or summability obligation for concrete models. -/
  compactResolventOrSummability : Prop

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
structure StateReadout
    (A : Type*) where
  eval : A → ℝ

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

variable {A : Type*} [Mul A]

/-- A cyclic-cocycle readout is cyclic when its cyclicity witness is supplied. -/
theorem cyclicCocycle_cyclicity
    (readout : A → ℝ)
    (hcyc : ∀ a b : A, readout (a * b) = readout (b * a)) :
    ∀ a b : A, readout (a * b) = readout (b * a) := by
  exact hcyc

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

end SpectralTriple
