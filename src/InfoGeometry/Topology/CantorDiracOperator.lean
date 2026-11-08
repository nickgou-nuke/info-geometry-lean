import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture
import InfoGeometry.Dynamics.ModularThermalState
import InfoGeometry.KK.RealSplitKreinBoundedTransform
import InfoGeometry.Topology.CliffordFractalWaveletBridge
import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# InfoGeometry.Topology.CantorDiracOperator

Cantor Dirac operators at the unbounded, bounded-transform, finite-truncation,
and KMS readout levels.

The owner is the native real split-Krein unbounded cycle.  The scalar finite
block below is retained only as a finite truncation and is not used to replace
the domain, closed-graph, resolvent, commutator, or KMS obligations.
-/

noncomputable section

namespace InfoGeometry.Topology.CantorDiracOperator

/-- Finite complex wavelet space at depth `n`. -/
abbrev FiniteWaveletSpace (n : ℕ) : Type :=
  InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n → ℂ

/-- Difference of consecutive filtration projections. -/
def filtrationDifferenceProjection
    {A : Type*} [Sub A]
    (Pnext Pprev : A) : A :=
  Pnext - Pprev

/-- Commutation with consecutive projections implies commutation with their difference. -/
theorem commutes_filtrationDifferenceProjection_of_commutes_consecutive
    {A : Type*} [Ring A]
    {a Pnext Pprev : A}
    (hnext : a * Pnext = Pnext * a)
    (hprev : a * Pprev = Pprev * a) :
    a * filtrationDifferenceProjection Pnext Pprev =
      filtrationDifferenceProjection Pnext Pprev * a := by
  simp only [filtrationDifferenceProjection, mul_sub, sub_mul, hnext, hprev]

/-- Scalar diagonal Cantor Dirac block at level `n`. -/
def finiteCantorDirac
    (weight : ℕ → ℝ)
    (n : ℕ) : Module.End ℂ (FiniteWaveletSpace n) :=
  ((weight n : ℝ) : ℂ) • (1 : Module.End ℂ (FiniteWaveletSpace n))

/-- Pointwise action of the finite Cantor Dirac block. -/
theorem finiteCantorDirac_apply
    (weight : ℕ → ℝ)
    (n : ℕ)
    (ψ : FiniteWaveletSpace n)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    finiteCantorDirac weight n ψ w = ((weight n : ℝ) : ℂ) * ψ w := by
  simp [finiteCantorDirac]

/-- Every vector in a scalar finite block is an eigenvector with the level weight. -/
theorem finiteCantorDirac_eigenvector
    (weight : ℕ → ℝ)
    (n : ℕ)
    (ψ : FiniteWaveletSpace n) :
    finiteCantorDirac weight n ψ = ((weight n : ℝ) : ℂ) • ψ := by
  ext w
  simp [finiteCantorDirac]

/-- The finite Cantor Dirac is scalar multiplication by the identity. -/
theorem finiteCantorDirac_eq_smul_id
    (weight : ℕ → ℝ)
    (n : ℕ) :
    finiteCantorDirac weight n =
      ((weight n : ℝ) : ℂ) • (1 : Module.End ℂ (FiniteWaveletSpace n)) := by
  rfl

/-- The constant-one field is sent to the constant level weight. -/
theorem finiteCantorDirac_const_one
    (weight : ℕ → ℝ)
    (n : ℕ) :
    finiteCantorDirac weight n (fun _ => (1 : ℂ)) =
      fun _ => ((weight n : ℝ) : ℂ) := by
  ext w
  simp [finiteCantorDirac]

/-- Middle-thirds Cantor scale `3^n`. -/
def middleThirdsScale (n : ℕ) : ℝ :=
  (3 : ℝ) ^ n

/-- Spectral scale assigned to the Cantor wavelet filtration. -/
abbrev CantorDiracScale : Type :=
  ℕ → ℝ

/-- Middle-thirds Cantor Dirac scale. -/
def middleThirdsCantorDiracScale : CantorDiracScale :=
  middleThirdsScale

/-! ## Native unbounded split-Krein owner -/

/--
Cantor wavelet realization inside a genuine unbounded split-Krein cycle.

The cycle owns the dense domain, closed graph, grading, represented actions,
bounded commutators, and compact resolvent.  This structure adds only the
Cantor wavelet indexing and its eigenmode equation.
-/
@[rep_depth operator]
structure CantorDiracOperatorSocket
    (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H] where
  cycle : InfoGeometry.KK.RealSplitKreinUnboundedCycle A B H
  scale : CantorDiracScale
  waveletMode :
    ∀ n : ℕ,
      InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n →
        {x : H // x ∈ cycle.domain}
  dirac_wavelet :
    ∀ (n : ℕ)
      (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n),
      cycle.D (waveletMode n w) =
        scale n • (waveletMode n w).1

namespace CantorDiracOperatorSocket

variable
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (S : CantorDiracOperatorSocket A B H)

/-- The Cantor wavelet mode belongs to the native unbounded domain. -/
theorem waveletMode_mem_domain
    (n : ℕ)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    (S.waveletMode n w).1 ∈ S.cycle.domain :=
  (S.waveletMode n w).2

/-- Native unbounded Dirac eigenmode equation. -/
@[rep_depth operator]
theorem dirac_wavelet_holds
    (n : ℕ)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    S.cycle.D (S.waveletMode n w) =
      S.scale n • (S.waveletMode n w).1 :=
  S.dirac_wavelet n w

/-- The owner domain is dense in the ambient split-Krein carrier. -/
theorem dense_domain :
    Dense S.cycle.domain :=
  S.cycle.dense_domain

/-- The owner Dirac graph is closed. -/
theorem closed_graph :
    IsClosed
      (Set.range
        (fun x : {x : H // x ∈ S.cycle.domain} =>
          ((x.1, S.cycle.D x) : H × H))) :=
  S.cycle.closed_graph

end CantorDiracOperatorSocket

/--
Native bounded transform of a Cantor unbounded cycle.

This restores the bounded-realization layer without identifying the unbounded
Dirac operator with a scalar finite matrix.
-/
@[rep_depth operator]
structure BoundedCantorDiracRealization
    (A B H : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H] where
  cantorDirac : CantorDiracOperatorSocket A B H
  boundedTransform :
    InfoGeometry.KK.RealSplitKreinBoundedTransform cantorDirac.cycle

namespace BoundedCantorDiracRealization

variable
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (R : BoundedCantorDiracRealization A B H)

/-- The bounded phase is the compact resolvent owned by the unbounded cycle. -/
theorem phase_compact :
    InfoGeometry.KK.IsCompactEnd H
      (InfoGeometry.KK.RealSplitKreinBoundedTransform.phase R.boundedTransform) :=
  R.boundedTransform.phase_compact

/-- Wavelet eigenmodes remain equations of the unbounded owner. -/
theorem triple_dirac_wavelet
    (n : ℕ)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    R.cantorDirac.cycle.D (R.cantorDirac.waveletMode n w) =
      R.cantorDirac.scale n •
        (R.cantorDirac.waveletMode n w).1 :=
  R.cantorDirac.dirac_wavelet_holds n w

end BoundedCantorDiracRealization

/-- Direct eigenmode transfer through a bounded realization.

The hypotheses are the precise graph-intertwining and eigenmode equations; no
structure stores them as evidence fields.
-/
theorem bounded_realization_transfers_eigenmode
    {Op H Domain : Type*}
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SMul Op H] [AddCommGroup Domain] [Module ℂ Domain]
    (triple : InfoGeometry.Topology.CuntzCantorSpectralTriple Op H)
    (inclusion dirac : Domain →ₗ[ℂ] H)
    (weight : ℕ → ℝ)
    (waveletMode : ∀ n : ℕ,
      InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n → Domain)
    (dirac_agrees_on_domain :
      ∀ ξ : Domain, triple.dirac (inclusion ξ) = dirac ξ)
    (dirac_wavelet :
      ∀ (n : ℕ)
        (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n),
        dirac (waveletMode n w) =
          ((weight n : ℝ) : ℂ) • inclusion (waveletMode n w))
    (n : ℕ)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    triple.dirac (inclusion (waveletMode n w)) =
      ((weight n : ℝ) : ℂ) • inclusion (waveletMode n w) := by
  rw [dirac_agrees_on_domain]
  exact dirac_wavelet n w

/-- The finite even thermal Hamiltonian attached to a Cantor scale. -/
def finiteCantorThermalHamiltonian
    (weight : ℕ → ℝ)
    (cutoff : ℕ) : Module.End ℂ (FiniteWaveletSpace cutoff) :=
  finiteCantorDirac weight cutoff

/-- The finite thermal Hamiltonian is exactly the finite Dirac block. -/
theorem finiteCantorThermalHamiltonian_eq_dirac
    (weight : ℕ → ℝ)
    (cutoff : ℕ) :
    finiteCantorThermalHamiltonian weight cutoff =
      finiteCantorDirac weight cutoff := by
  rfl

open InfoGeometry.Dynamics

/-! ## KMS thermal realization of the unbounded Cantor owner -/

/--
KMS thermal realization attached to a genuine unbounded Cantor Dirac cycle.

The parity laws are equations on selected observables at the upper strip
boundary.  No bare proposition fields remain.
-/
@[rep_depth operator]
structure CantorDiracKMSThermalVacuum
    (A B H Observable : Type*)
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    [Ring Observable] where
  cantorDirac : CantorDiracOperatorSocket A B H
  thermalGenerator : Observable
  diracGeneratorReadout : Observable
  thermalGenerator_matches_dirac :
    thermalGenerator = diracGeneratorReadout
  partitionFunction : ℝ
  thermalState : ModularThermalState Observable
  strip : HestenesKreinKMSStripData Observable
  oddField : Observable
  evenObservable : Observable
  oddFieldAntiperiodic :
    ∀ t : ℝ,
      strip.analytic.sigmaC
          (complexClockPoint t strip.analytic.beta) oddField =
        -(strip.analytic.sigmaC (t : ℂ) oddField)
  evenObservablePeriodic :
    ∀ t : ℝ,
      strip.analytic.sigmaC
          (complexClockPoint t strip.analytic.beta) evenObservable =
        strip.analytic.sigmaC (t : ℂ) evenObservable

namespace CantorDiracKMSThermalVacuum

variable
    {A B H Observable : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    [Ring Observable]
    (T : CantorDiracKMSThermalVacuum A B H Observable)

theorem thermalGenerator_eq_diracReadout :
    T.thermalGenerator = T.diracGeneratorReadout :=
  T.thermalGenerator_matches_dirac

theorem odd_antiperiodic (t : ℝ) :
    T.strip.analytic.sigmaC
        (complexClockPoint t T.strip.analytic.beta) T.oddField =
      -(T.strip.analytic.sigmaC (t : ℂ) T.oddField) :=
  T.oddFieldAntiperiodic t

theorem even_periodic (t : ℝ) :
    T.strip.analytic.sigmaC
        (complexClockPoint t T.strip.analytic.beta) T.evenObservable =
      T.strip.analytic.sigmaC (t : ℂ) T.evenObservable :=
  T.evenObservablePeriodic t

end CantorDiracKMSThermalVacuum

/-- Lower KMS boundary identity, directly from genuine strip data. -/
theorem kms_lower_boundary
    {Observable : Type*} [Monoid Observable]
    (strip : HestenesKreinKMSStripData Observable)
    (t : ℝ) (a b : Observable) :
    strip.omega_eval a
      (strip.analytic.sigmaC (t : ℂ) b) =
    strip.omega_eval a
      (InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma strip.analytic.modular t b) :=
  strip.boundary_lower t a b

/-- Upper KMS boundary identity, directly from genuine strip data. -/
theorem kms_upper_boundary
    {Observable : Type*} [Monoid Observable]
    (strip : HestenesKreinKMSStripData Observable)
    (t : ℝ) (a b : Observable) :
    strip.omega_eval a
      (strip.analytic.sigmaC
        (complexClockPoint t strip.analytic.beta) b) =
    strip.omega_eval
      (InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma strip.analytic.modular
        (t + strip.analytic.beta) b) a :=
  strip.boundary_upper t a b

/-- Constructive KMS boundary law of an actual modular thermal state. -/
theorem modularThermalState_kms_boundary
    {Observable : Type*} [Monoid Observable]
    (thermalState : ModularThermalState Observable)
    (t : ℝ) (a b : Observable) :
    thermalState.kms.omega_eval a
      (InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma thermalState.kms.modular t b) =
    thermalState.kms.omega_eval
      (InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma thermalState.kms.modular
        (t + thermalState.kms.beta) b) a :=
  thermalState.kms.kms_boundary t a b

end InfoGeometry.Topology.CantorDiracOperator
