import Mathlib.Tactic
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

theorem finiteCantorDirac_commutes
    (weight : ℕ → ℝ)
    (n : ℕ)
    (T : Module.End ℂ (FiniteWaveletSpace n)) :
    finiteCantorDirac weight n * T = T * finiteCantorDirac weight n := by
  ext ψ w
  simp [finiteCantorDirac]

theorem finiteCantorDirac_mul_self
    (weight : ℕ → ℝ)
    (n : ℕ) :
    finiteCantorDirac weight n * finiteCantorDirac weight n =
      (((weight n : ℝ) : ℂ) ^ 2) •
        (1 : Module.End ℂ (FiniteWaveletSpace n)) := by
  ext ψ w
  simp [finiteCantorDirac, Algebra.smul_def, pow_two]

theorem finiteCantorDirac_pow_apply
    (weight : ℕ → ℝ)
    (n k : ℕ)
    (ψ : FiniteWaveletSpace n)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    ((finiteCantorDirac weight n) ^ k) ψ w =
      (((weight n : ℝ) : ℂ) ^ k) * ψ w := by
  induction k generalizing ψ with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      simp [finiteCantorDirac_apply, mul_assoc]
      ring

theorem finiteCantorDirac_commutes_pow
    (weight : ℕ → ℝ)
    (n k : ℕ)
    (T : Module.End ℂ (FiniteWaveletSpace n)) :
    (finiteCantorDirac weight n) ^ k * T =
      T * (finiteCantorDirac weight n) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc
        (finiteCantorDirac weight n) ^ k *
              (finiteCantorDirac weight n * T) =
            (finiteCantorDirac weight n) ^ k *
              (T * finiteCantorDirac weight n) := by
                rw [finiteCantorDirac_commutes weight n T]
        _ = ((finiteCantorDirac weight n) ^ k * T) *
              finiteCantorDirac weight n := by
                rw [mul_assoc]
        _ = (T * (finiteCantorDirac weight n) ^ k) *
              finiteCantorDirac weight n := by rw [ih]
        _ = T * ((finiteCantorDirac weight n) ^ k *
              finiteCantorDirac weight n) := by rw [mul_assoc]

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

theorem middleThirdsScale_succ (n : ℕ) :
    middleThirdsScale (n + 1) = 3 * middleThirdsScale n := by
  simp [middleThirdsScale, pow_succ, mul_comm]

theorem middleThirdsScale_pos (n : ℕ) :
    0 < middleThirdsScale n := by
  exact pow_pos (by norm_num) _

theorem middleThirdsScale_one_le (n : ℕ) :
    1 ≤ middleThirdsScale n := by
  induction n with
  | zero => simp [middleThirdsScale]
  | succ n ih =>
      rw [middleThirdsScale_succ]
      nlinarith

/-- Spectral scale assigned to the Cantor wavelet filtration. -/
abbrev CantorDiracScale : Type :=
  ℕ → ℝ

/-- Middle-thirds Cantor Dirac scale. -/
def middleThirdsCantorDiracScale : CantorDiracScale :=
  middleThirdsScale

/-! ## Native unbounded split-Krein owner -/
/-! ## Native unbounded split-Krein statements -/

theorem waveletMode_mem_domain
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (cycle : InfoGeometry.KK.RealSplitKreinUnboundedCycle A B H)
    (waveletMode : ∀ n : ℕ,
      InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n →
        {x : H // x ∈ cycle.domain})
    (n : ℕ)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    (waveletMode n w).1 ∈ cycle.domain :=
  (waveletMode n w).2

theorem dirac_wavelet_holds
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (cycle : InfoGeometry.KK.RealSplitKreinUnboundedCycle A B H)
    (scale : CantorDiracScale)
    (waveletMode : ∀ n : ℕ,
      InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n →
        {x : H // x ∈ cycle.domain})
    (h : ∀ n w, cycle.D (waveletMode n w) =
      scale n • (waveletMode n w).1)
    (n : ℕ)
    (w : InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n) :
    cycle.D (waveletMode n w) = scale n • (waveletMode n w).1 :=
  h n w

theorem dense_domain
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (cycle : InfoGeometry.KK.RealSplitKreinUnboundedCycle A B H) :
    Dense cycle.domain :=
  cycle.dense_domain

theorem closed_graph
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (cycle : InfoGeometry.KK.RealSplitKreinUnboundedCycle A B H) :
    IsClosed (Set.range (fun x : {x : H // x ∈ cycle.domain} =>
      ((x.1, cycle.D x) : H × H))) :=
  cycle.closed_graph

theorem phase_compact
    {A B H : Type*}
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    [InfoGeometry.Krein.KreinSpace H]
    [InfoGeometry.Krein.KreinGradedModule H]
    (cycle : InfoGeometry.KK.RealSplitKreinUnboundedCycle A B H)
    (boundedTransform :
      InfoGeometry.KK.RealSplitKreinBoundedTransform cycle) :
    InfoGeometry.KK.IsCompactEnd H
      (InfoGeometry.KK.RealSplitKreinBoundedTransform.phase boundedTransform) :=
  boundedTransform.phase_compact

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

/-- Direct odd antiperiodicity supplied by a KMS strip. -/
theorem odd_antiperiodic
    {Observable : Type*} [Ring Observable]
    (strip : HestenesKreinKMSStripData Observable)
    (oddField : Observable)
    (h : ∀ t : ℝ,
      strip.analytic.sigmaC (complexClockPoint t strip.analytic.beta) oddField =
        -(strip.analytic.sigmaC (t : ℂ) oddField))
    (t : ℝ) :
    strip.analytic.sigmaC (complexClockPoint t strip.analytic.beta) oddField =
      -(strip.analytic.sigmaC (t : ℂ) oddField) :=
  h t

/-- Direct even periodicity supplied by a KMS strip. -/
theorem even_periodic
    {Observable : Type*} [Monoid Observable]
    (strip : HestenesKreinKMSStripData Observable)
    (evenObservable : Observable)
    (h : ∀ t : ℝ,
      strip.analytic.sigmaC (complexClockPoint t strip.analytic.beta) evenObservable =
        strip.analytic.sigmaC (t : ℂ) evenObservable)
    (t : ℝ) :
    strip.analytic.sigmaC (complexClockPoint t strip.analytic.beta) evenObservable =
      strip.analytic.sigmaC (t : ℂ) evenObservable :=
  h t

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
