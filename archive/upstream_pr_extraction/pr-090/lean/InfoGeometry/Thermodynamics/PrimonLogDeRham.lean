import Mathlib.Tactic
import InfoGeometry.Thermodynamics.TomitaModularDeviance
import InfoGeometry.Canonical.VonMangoldtPrimonExplicitBridge
import InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra
import InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge

/-!
# Finite real primon logarithmic readouts

This owner keeps the prime-mode layer finite and real.  A mode weight is a
real coefficient of a one-dimensional logarithmic readout; bosonic and
signed-Möbius connections cancel algebraically.  The score theorem is stated
for a finite list with an actual normalization and mean-energy hypothesis.

The terms "connection", "score", and "Fisher" below are finite coefficient
readouts.  They do not construct a differential manifold, a complex
logarithm, or an infinite Dirichlet series.  The local divisor/residue
replacement is owned by `EulerLaurentHestenesDivisor` and
`RiemannPoleZeroMonodromy`.

No complex fugacity, infinite Euler product, analytic continuation, contour
integral, or Riemann-zero residue theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.PrimonLogDeRham

open InfoGeometry.Thermodynamics.TomitaModularDeviance
open InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra
open InfoGeometry.Arithmetic.PrimeBitFiniteKernelIndexBridge
open InfoGeometry.Arithmetic.IndexTheorem

/-! ## Finite prime-mode one-forms -/

/-- The real one-dimensional logarithmic readout of a prime mode. -/
def primeMode1Form (p : ℕ) (ds : ℝ) : ℝ :=
  -Real.log (p : ℝ) * ds

theorem primeMode1Form_eq_neg_vonMangoldt
    {p : ℕ} (hp : p.Prime) (ds : ℝ) :
    primeMode1Form p ds =
      -(ArithmeticFunction.vonMangoldt p) * ds := by
  simp [primeMode1Form,
    InfoGeometry.Canonical.VonMangoldtPrimonExplicitBridge.vonMangoldt_prime hp]

/-! ## Bosonic and signed-fermionic connection data -/

/-- A finite real connection coefficient and its two graded signs. -/
structure DeRhamSystem where
  coefficient : ℝ

def bosonicConnection (P : DeRhamSystem) (ds : ℝ) : ℝ :=
  -P.coefficient * ds

def signedFermionicConnection (P : DeRhamSystem) (ds : ℝ) : ℝ :=
  P.coefficient * ds

@[simp] theorem primon_signed_connection_cancel
    (P : DeRhamSystem) (ds : ℝ) :
    bosonicConnection P ds + signedFermionicConnection P ds = 0 := by
  simp [bosonicConnection, signedFermionicConnection]

@[simp] theorem signedFermionicConnection_eq_neg_bosonic
    (P : DeRhamSystem) (ds : ℝ) :
    signedFermionicConnection P ds = -bosonicConnection P ds := by
  simp [bosonicConnection, signedFermionicConnection]

@[simp] theorem bosonicConnection_eq_neg_signedFermionic
    (P : DeRhamSystem) (ds : ℝ) :
    bosonicConnection P ds = -signedFermionicConnection P ds := by
  simp [bosonicConnection, signedFermionicConnection]

/-! ## Finite weighted logarithmic score -/

/-- A finite microstate carrying a probability weight and energy readout. -/
structure Microstate where
  prob : ℝ
  energy : ℝ

/-- The score one-form of a state relative to a supplied mean energy. -/
def score1Form (m : Microstate) (mean ds : ℝ) : ℝ :=
  -(m.energy - mean) * ds

/-- The weighted finite score sum. -/
def weightedScore (states : List Microstate) (mean ds : ℝ) : ℝ :=
  (states.map (fun m => m.prob * score1Form m mean ds)).sum

/-- Normalization and mean-energy matching imply zero expected score. -/
theorem primon_score_mean_zero
    (states : List Microstate)
    (mean ds : ℝ)
    (h_norm : (states.map Microstate.prob).sum = 1)
    (h_mean : (states.map (fun m => m.prob * m.energy)).sum = mean) :
    weightedScore states mean ds = 0 := by
  unfold weightedScore score1Form
  have h_identity : ∀ (xs : List Microstate),
      (xs.map (fun m => m.prob * (-(m.energy - mean) * ds))).sum =
        -((xs.map (fun m => m.prob * m.energy)).sum -
          mean * (xs.map Microstate.prob).sum) * ds := by
    intro xs
    induction xs with
    | nil => simp
    | cons m xs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  rw [h_identity states, h_norm, h_mean]
  ring

/-- Explicit finite expansion of the weighted score one-form. -/
theorem weightedScore_eq_centered_energy
    (states : List Microstate) (mean ds : ℝ) :
    weightedScore states mean ds =
      -((states.map (fun m => m.prob * m.energy)).sum -
        mean * (states.map Microstate.prob).sum) * ds := by
  unfold weightedScore score1Form
  induction states with
  | nil => simp
  | cons m states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- With nonzero differential scale, zero weighted score is equivalent to
the weighted-energy balance equation. -/
theorem weightedScore_eq_zero_iff
    (states : List Microstate) (mean ds : ℝ)
    (hds : ds ≠ 0) :
    weightedScore states mean ds = 0 ↔
      (states.map (fun m => m.prob * m.energy)).sum =
        mean * (states.map Microstate.prob).sum := by
  rw [weightedScore_eq_centered_energy]
  constructor
  · intro h
    have hprod :
        ((states.map (fun m => m.prob * m.energy)).sum -
          mean * (states.map Microstate.prob).sum) * ds = 0 := by
      linarith
    have hdiff := (mul_eq_zero.mp hprod).resolve_right hds
    linarith
  · intro h
    rw [h]
    ring

/-! ## Finite Fisher/variance readouts -/

/-- The finite weighted centered energy variance. -/
def weightedCenteredVariance
    (states : List Microstate) (mean : ℝ) : ℝ :=
  (states.map (fun m => m.prob * (m.energy - mean) ^ 2)).sum

theorem weightedCenteredVariance_nonneg
    (states : List Microstate) (mean : ℝ)
    (hprob : ∀ m, m ∈ states → 0 ≤ m.prob) :
    0 ≤ weightedCenteredVariance states mean := by
  unfold weightedCenteredVariance
  induction states with
  | nil => simp
  | cons m states ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact mul_nonneg (hprob m (by simp)) (sq_nonneg _)
      · apply ih
        intro n hn
        exact hprob n (by simp [hn])

/-- The squared finite score readout is the variance multiplied by the square
of the coordinate differential. -/
def weightedScoreSquare
    (states : List Microstate) (mean ds : ℝ) : ℝ :=
  (states.map (fun m => m.prob * (score1Form m mean ds) ^ 2)).sum

theorem weightedScoreSquare_eq_variance
    (states : List Microstate) (mean ds : ℝ) :
    weightedScoreSquare states mean ds =
      ds ^ 2 * weightedCenteredVariance states mean := by
  unfold weightedScoreSquare weightedCenteredVariance score1Form
  induction states with
  | nil => simp
  | cons m states ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem weightedScoreSquare_nonneg
    (states : List Microstate) (mean ds : ℝ)
    (hprob : ∀ m, m ∈ states → 0 ≤ m.prob) :
    0 ≤ weightedScoreSquare states mean ds := by
  rw [weightedScoreSquare_eq_variance]
  exact mul_nonneg (sq_nonneg ds)
    (weightedCenteredVariance_nonneg states mean hprob)

/-! ## Finite modular-mode deviance -/

/-- The Tomita deviance of the real prime-mode modular parameter. -/
def primeModeDeviance (p : ℕ) (s : ℝ) : ℝ :=
  scalar (s * Real.log (p : ℝ))

theorem primeModeDeviance_nonneg (p : ℕ) (s : ℝ) :
    0 ≤ primeModeDeviance p s := by
  exact scalar_nonneg _

theorem primeModeDeviance_pos
    {p : ℕ} {s : ℝ}
    (h : s * Real.log (p : ℝ) ≠ 0) :
    0 < primeModeDeviance p s := by
  exact scalar_pos h

theorem primeModeDeviance_eq_finiteDiagonalDeviance
    (p : ℕ) (s : ℝ) :
    primeModeDeviance p s =
      finiteDiagonalDeviance s (fun _ : Unit => Real.log (p : ℝ)) () := by
  rfl

theorem primeModeDeviance_eq_zero_iff
    (p : ℕ) (s : ℝ) :
    primeModeDeviance p s = 0 ↔ s * Real.log (p : ℝ) = 0 := by
  exact scalar_eq_zero_iff _

/-- The prime-mode deviance vanishes only at the zero deformation parameter. -/
theorem primeModeDeviance_eq_zero_iff_of_prime
    {p : ℕ} (hp : p.Prime) (s : ℝ) :
    primeModeDeviance p s = 0 ↔ s = 0 := by
  have hp_real : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp_real
  rw [primeModeDeviance_eq_zero_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hs | hlog_zero
    · exact hs
    · exact False.elim ((ne_of_gt hlog) hlog_zero)
  · intro hs
    simp [hs]

/-! ## Finite weighted modular deviance -/

/-
This is the finite state-space synthesis of the two existing owners:
`Microstate` supplies the real energy readout and
`TomitaModularDeviance.scalar` supplies the nonnegative tangent subtraction.
It is deliberately a finite list statement; it does not identify a zeta
partition function or an analytic operator functional calculus.
-/
def weightedMicrostateDeviance
    (states : List Microstate) (s : ℝ) : ℝ :=
  (states.map (fun m => m.prob * scalar (s * m.energy))).sum

theorem weightedMicrostateDeviance_nonneg
    (states : List Microstate) (s : ℝ)
    (hprob : ∀ m, m ∈ states → 0 ≤ m.prob) :
    0 ≤ weightedMicrostateDeviance states s := by
  unfold weightedMicrostateDeviance
  induction states with
  | nil => simp
  | cons m states ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact mul_nonneg (hprob m (by simp)) (scalar_nonneg _)
      · apply ih
        intro n hn
        exact hprob n (by simp [hn])

/-- With strictly positive finite probabilities, the weighted Tomita deviance
    vanishes exactly when every mode has zero modular parameter. -/
theorem weightedMicrostateDeviance_eq_zero_iff
    (states : List Microstate) (s : ℝ)
    (hprob : ∀ m, m ∈ states → 0 < m.prob) :
    weightedMicrostateDeviance states s = 0 ↔
      ∀ m, m ∈ states → s * m.energy = 0 := by
  revert hprob
  induction states with
  | nil =>
      intro hprob
      constructor
      · intro h _ hm
        simp at hm
      · intro h
        simp [weightedMicrostateDeviance]
  | cons m states ih =>
      intro hprob
      have hm_pos : 0 < m.prob := hprob m (by simp)
      have htail_pos : ∀ x, x ∈ states → 0 < x.prob := by
        intro x hx
        exact hprob x (by simp [hx])
      constructor
      · intro hzero x hx
        have hhead_nonneg :
            0 ≤ m.prob * scalar (s * m.energy) :=
          mul_nonneg (le_of_lt hm_pos) (scalar_nonneg _)
        have htail_nonneg :
            0 ≤ weightedMicrostateDeviance states s :=
          weightedMicrostateDeviance_nonneg states s
            (fun y hy => (htail_pos y hy).le)
        have hzero' :
            m.prob * scalar (s * m.energy) +
                weightedMicrostateDeviance states s = 0 := by
          simpa [weightedMicrostateDeviance] using hzero
        have hhead_zero : m.prob * scalar (s * m.energy) = 0 := by
          linarith [hzero', htail_nonneg]
        have htail_zero : weightedMicrostateDeviance states s = 0 := by
          linarith [hzero', hhead_nonneg]
        simp only [List.mem_cons] at hx
        rcases hx with hxm | hx
        · have hscalar : scalar (s * m.energy) = 0 :=
            (mul_eq_zero.mp hhead_zero).resolve_left (ne_of_gt hm_pos)
          have hmode : s * m.energy = 0 := (scalar_eq_zero_iff _).mp hscalar
          simpa [hxm] using hmode
        · exact (ih htail_pos).mp htail_zero x hx
      · intro hzero
        have hhead : scalar (s * m.energy) = 0 :=
          (scalar_eq_zero_iff _).2 (hzero m (by simp))
        have htail : weightedMicrostateDeviance states s = 0 := by
          apply (ih htail_pos).mpr
          intro x hx
          exact hzero x (by simp [hx])
        change m.prob * scalar (s * m.energy) +
            weightedMicrostateDeviance states s = 0
        rw [hhead, mul_zero, htail, add_zero]

/-- Under strictly positive finite probabilities, the weighted deviance is
    positive exactly when at least one modular mode is nonzero. -/
theorem weightedMicrostateDeviance_pos_iff
    (states : List Microstate) (s : ℝ)
    (hprob : ∀ m, m ∈ states → 0 < m.prob) :
    0 < weightedMicrostateDeviance states s ↔
      ∃ m, m ∈ states ∧ s * m.energy ≠ 0 := by
  have hprob_nonneg : ∀ m, m ∈ states → 0 ≤ m.prob := by
    intro m hm
    exact (hprob m hm).le
  constructor
  · intro hpos
    by_contra hnone
    have hzero : ∀ m, m ∈ states → s * m.energy = 0 := by
      intro m hm
      by_contra hne
      exact hnone ⟨m, hm, hne⟩
    have hvanish :=
      (weightedMicrostateDeviance_eq_zero_iff states s hprob).2 hzero
    linarith
  · rintro ⟨m, hm, hmode⟩
    have hnonneg :=
      weightedMicrostateDeviance_nonneg states s hprob_nonneg
    have hnezero : weightedMicrostateDeviance states s ≠ 0 := by
      intro hzero
      have hmode_zero :=
        (weightedMicrostateDeviance_eq_zero_iff states s hprob).1 hzero m hm
      exact hmode hmode_zero
    exact lt_of_le_of_ne hnonneg (Ne.symm hnezero)

theorem finite_real_primon_readout_closure_with_deviance
    (P : DeRhamSystem)
    (states : List Microstate)
    (mean ds s : ℝ)
    (h_norm : (states.map Microstate.prob).sum = 1)
    (h_mean : (states.map (fun m => m.prob * m.energy)).sum = mean)
    (hprob : ∀ m, m ∈ states → 0 ≤ m.prob) :
    bosonicConnection P ds + signedFermionicConnection P ds = 0 ∧
    weightedScore states mean ds = 0 ∧
      0 ≤ weightedScoreSquare states mean ds ∧
          0 ≤ weightedMicrostateDeviance states s := by
  refine ⟨primon_signed_connection_cancel P ds,
    primon_score_mean_zero states mean ds h_norm h_mean,
    weightedScoreSquare_nonneg states mean ds hprob,
    weightedMicrostateDeviance_nonneg states s hprob⟩

/-- The finite Fisher information metric admits the usual second-moment form.
    This is the finite algebraic form of
    `g_F = E[E²] - E[E]²`, without an analytic zeta identification. -/
theorem primon_fisher_metric_eq_variance
    (states : List Microstate)
    (mean : ℝ)
    (h_norm : (states.map Microstate.prob).sum = 1)
    (h_mean : (states.map (fun m => m.prob * m.energy)).sum = mean) :
    weightedCenteredVariance states mean =
      (states.map (fun m => m.prob * m.energy ^ 2)).sum - mean ^ 2 := by
  unfold weightedCenteredVariance
  have h_identity : ∀ xs : List Microstate,
      (xs.map (fun m => m.prob * (m.energy - mean) ^ 2)).sum =
        (xs.map (fun m => m.prob * m.energy ^ 2)).sum -
          2 * mean * (xs.map (fun m => m.prob * m.energy)).sum +
            mean ^ 2 * (xs.map Microstate.prob).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons m xs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  rw [h_identity, h_norm, h_mean]
  ring

/-- The finite score-square readout in Fisher second-moment form. -/
theorem weightedScoreSquare_eq_fisher_secondMoment
    (states : List Microstate)
    (mean ds : ℝ)
    (h_norm : (states.map Microstate.prob).sum = 1)
    (h_mean : (states.map (fun m => m.prob * m.energy)).sum = mean) :
    weightedScoreSquare states mean ds =
      ds ^ 2 *
        ((states.map (fun m => m.prob * m.energy ^ 2)).sum - mean ^ 2) := by
  rw [weightedScoreSquare_eq_variance]
  rw [primon_fisher_metric_eq_variance states mean h_norm h_mean]

/-- The finite real capstone with the Fisher second-moment identity exposed.

This is the valid synthesis of the two finite owners: the signed connection
and normalized score are exact algebraic cancellations, the score square is
the centered-energy second moment, and the Tomita term is a nonnegative
finite tangent deviance.  No complex differential form or infinite partition
function is introduced by this theorem.
-/
theorem finite_real_primon_readout_closure_with_fisher_and_deviance
    (P : DeRhamSystem)
    (states : List Microstate)
    (mean ds s : ℝ)
    (h_norm : (states.map Microstate.prob).sum = 1)
    (h_mean : (states.map (fun m => m.prob * m.energy)).sum = mean)
    (hprob : ∀ m, m ∈ states → 0 ≤ m.prob) :
    bosonicConnection P ds + signedFermionicConnection P ds = 0 ∧
      weightedScore states mean ds = 0 ∧
        weightedScoreSquare states mean ds =
          ds ^ 2 *
            ((states.map (fun m => m.prob * m.energy ^ 2)).sum - mean ^ 2) ∧
          0 ≤ weightedMicrostateDeviance states s := by
  refine ⟨primon_signed_connection_cancel P ds,
    primon_score_mean_zero states mean ds h_norm h_mean,
    weightedScoreSquare_eq_fisher_secondMoment states mean ds h_norm h_mean,
    weightedMicrostateDeviance_nonneg states s hprob⟩

/-! ## Finite real synthesis -/

/-
This capstone deliberately packages only the finite readouts owned by this
module.  The graded connection cancellation, normalized score identity,
nonnegative finite Fisher readout, and scalar modular deviance are separate
facts; no analytic zeta quotient, contour residue, determinant identity, or
divisor-to-Witten index identification is inferred from their conjunction.
The final kernel-index theorem below is finite and explicit: it uses the
prime-register parity complex, not a formal trace or a divisor analogy.
-/
theorem finite_real_primon_readout_closure
    (P : DeRhamSystem)
    (states : List Microstate)
    (mean ds : ℝ)
    (h_norm : (states.map Microstate.prob).sum = 1)
    (h_mean : (states.map (fun m => m.prob * m.energy)).sum = mean)
    (hprob : ∀ m, m ∈ states → 0 ≤ m.prob)
    (p : ℕ) (s : ℝ) :
    bosonicConnection P ds + signedFermionicConnection P ds = 0 ∧
      weightedScore states mean ds = 0 ∧
        0 ≤ weightedScoreSquare states mean ds ∧
          0 ≤ primeModeDeviance p s := by
  refine ⟨primon_signed_connection_cancel P ds,
    primon_score_mean_zero states mean ds h_norm h_mean,
    weightedScoreSquare_nonneg states mean ds hprob,
    primeModeDeviance_nonneg p s⟩

/-! ## Finite supertrace and genuine kernel-index bridge -/

/-
The following theorem is the valid finite replacement for identifying a
supertrace with a divisor or residue index.  The source is an explicit
two-term complex owned by `PrimeBitFiniteKernelIndexBridge`; no analytic
determinant, contour integral, or infinite zeta calibration is inferred.
-/
theorem finite_primon_witten_index_eq_kernel_index
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) :
    finiteKernelIndex (primeRegisterParityComplex P) =
      finitePrimonWittenIndex P := by
  rw [finite_kernel_index_prime_register_parity]
  rfl

/-!
The divisor readout is composed only after passing through the genuine
finite kernel index.  This is deliberately not a residue theorem for an
analytic zeta function: `primeRegisterParityCharge` is the explicit finite
prime-bit charge owned by `PrimeBitFiniteKernelIndexBridge`.
-/
theorem finite_primon_witten_index_eq_prime_divisor_index
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) :
    finitePrimonWittenIndex P =
      InfoGeometry.Algebra.EulerLaurentDerivation.divisorIndex
        P.primes.powerset primeRegisterParityCharge := by
  rw [← finite_primon_witten_index_eq_kernel_index P]
  exact finite_kernel_index_prime_register_parity_eq_divisorIndex P

/-
Finite boson/signed-fermion cancellation is a product identity.  It is kept
separate from the Berezinian ratio API, whose reciprocal-block theorem gives
the square of the determinant block rather than the unit.
-/
theorem finite_primon_signed_partition_cancellation
    {ι R : Type*} [Field R]
    (S : Finset ι) (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    finiteBosonPrimonPartition S x *
        finiteSignedFermionPrimonPartition S x = 1 := by
  exact finite_boson_signedFermion_cancel S x h

end InfoGeometry.Thermodynamics.PrimonLogDeRham

end noncomputable section
