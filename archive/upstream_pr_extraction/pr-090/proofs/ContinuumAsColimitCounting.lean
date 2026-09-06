import proofs.JaynesLDDPGNSColimit

/-!
# Continuum as the colimit of counting

This module formalizes the finite counting content of the slogan:

> The continuum is not a primitive place; it is the colimit of finite counting
> stages measured relative to a reference density/state.

Finite proved content:

* stage `n` has exactly `2^n` binary words;
* refinement from stage `n` to stage `n+1` doubles the number of cells;
* Jaynes/LDDP entropy against the matching finite counting reference is zero;
* the UHF cylinder observable is unchanged by the successor embedding;
* GNS-like vacuum expectation is expectation relative to the reference state.

Analytic measure limits, C*-completions, and Hilbert-space GNS completions
are stated separately in `JaynesLDDPGNSColimit`.
-/

noncomputable section

namespace ContinuumAsColimitCounting

open scoped BigOperators
open UHFInductiveColimit
open JaynesLDDPGNSColimit

/-! ## 1. Finite counting stages -/

/-- Stage `n` has `2^n` finite binary counting cells. -/
theorem bitword_count (n : ℕ) :
    Fintype.card (BitWord n) = 2 ^ n := by
  simp [BitWord]

/-- Refining one UHF/Cantor bit doubles the finite count. -/
theorem bitword_count_succ (n : ℕ) :
    Fintype.card (BitWord (n + 1)) = 2 * Fintype.card (BitWord n) := by
  simp [BitWord, pow_succ]
  ring

/-! ## 1b. Four-lane Cuntz/Cantor counting stages -/

/-- Four-symbol words of length `n`, matching the `O_4`/four-lane limit. -/
abbrev FourWord (n : ℕ) : Type :=
  Fin n → Fin 4

/-- Four-lane diagonal finite-dimensional algebra at stage `n`. -/
abbrev FourDiagAlg (n : ℕ) : Type :=
  FourWord n → ℂ

/-- Four-symbol Cantor limit. -/
abbrev FourCantorBoundary : Type :=
  ℕ → Fin 4

/-- Stage `n` in the four-lane limit has `4^n` finite counting cells. -/
theorem fourword_count (n : ℕ) :
    Fintype.card (FourWord n) = 4 ^ n := by
  simp [FourWord]

/-- Refining one four-lane Cantor digit multiplies the finite count by `4`. -/
theorem fourword_count_succ (n : ℕ) :
    Fintype.card (FourWord (n + 1)) = 4 * Fintype.card (FourWord n) := by
  simp [FourWord, pow_succ]
  ring

/-- Prefix a four-symbol word of length `n+1` down to length `n`. -/
def prefixSucc4 (n : ℕ) (w : FourWord (n + 1)) : FourWord n :=
  fun i => w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- Four-lane diagonal connecting map: duplicate over the newly added symbol. -/
def diagEmbedSucc4 (n : ℕ) : FourDiagAlg n → FourDiagAlg (n + 1) :=
  fun f w => f (prefixSucc4 n w)

/-- Restrict a four-symbol limit point to its first `n` symbols. -/
def boundaryPrefix4 (n : ℕ) (b : FourCantorBoundary) : FourWord n :=
  fun i => b i.1

/-- Four-lane finite-cylinder realization of a stage-`n` diagonal observable. -/
def cylinder4 (n : ℕ) (f : FourDiagAlg n) : FourCantorBoundary → ℂ :=
  fun b => f (boundaryPrefix4 n b)

theorem boundaryPrefix4_succ_eq_prefixSucc4
    (n : ℕ) (b : FourCantorBoundary) :
    prefixSucc4 n (boundaryPrefix4 (n + 1) b) = boundaryPrefix4 n b := by
  ext i
  rfl

/-- Four-lane cylinders are compatible with successor refinement. -/
theorem cylinder4_compatible_succ (n : ℕ) (f : FourDiagAlg n) :
    cylinder4 (n + 1) (diagEmbedSucc4 n f) = cylinder4 n f := by
  ext b
  simp [cylinder4, diagEmbedSucc4, boundaryPrefix4_succ_eq_prefixSucc4]

/-- The finite counting reference density on stage `n`. -/
def finiteCountingReference (n : ℕ) : BitWord n → ℝ :=
  fun _ => (Fintype.card (BitWord n) : ℝ)⁻¹

/-- The four-lane finite counting reference density on stage `n`. -/
def finiteCountingReference4 (n : ℕ) : FourWord n → ℝ :=
  fun _ => (Fintype.card (FourWord n) : ℝ)⁻¹

/-- The finite counting reference is nonzero at every cell. -/
theorem finiteCountingReference_ne_zero (n : ℕ) (w : BitWord n) :
    finiteCountingReference n w ≠ 0 := by
  unfold finiteCountingReference
  apply inv_ne_zero
  norm_num [BitWord]

/-- The four-lane finite counting reference is nonzero at every cell. -/
theorem finiteCountingReference4_ne_zero (n : ℕ) (w : FourWord n) :
    finiteCountingReference4 n w ≠ 0 := by
  unfold finiteCountingReference4
  apply inv_ne_zero
  norm_num [FourWord]

/-! ## 2. Jaynes/LDDP relative-information stability -/

/-- A finite stage has zero Jaynes/LDDP entropy relative to its own counting
reference.  This is the finite theorem behind the continuum/reference-density
rule: absolute counting grows, but relative information is measured against
the reference density. -/
theorem finite_counting_reference_entropy_self (n : ℕ) :
    jaynesRelativeEntropy (Finset.univ : Finset (BitWord n))
      (finiteCountingReference n) (finiteCountingReference n) = 0 := by
  apply jaynesRelativeEntropy_self
  intro a _ha
  exact finiteCountingReference_ne_zero n a

/-- Four-lane finite counting reference has zero Jaynes/LDDP entropy relative
to itself. -/
theorem finite_counting_reference4_entropy_self (n : ℕ) :
    jaynesRelativeEntropy (Finset.univ : Finset (FourWord n))
      (finiteCountingReference4 n) (finiteCountingReference4 n) = 0 := by
  apply jaynesRelativeEntropy_self
  intro a _ha
  exact finiteCountingReference4_ne_zero n a

/-! ## 3. Direct-colimit compatibility -/

/-- The successor embedding preserves the cylinder observable: refining the
finite stage does not change the already-defined physical observable. -/
theorem counting_refinement_preserves_cylinder (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  cylinder_compatible_succ n f

/-- Each finite observable has a representative in the cylinder colimit. -/
theorem finite_count_observable_mem_colimit (n : ℕ) (f : DiagAlg n) :
    cylinder n f ∈ CylinderColimit :=
  cylinder_mem_colimit n f

/-! ## 4. Synthesis -/

/-- Capstone: finite counting grows by refinement, but physical continuum
observables and information are defined only relative to the counting reference
and compatible colimit embeddings. -/
theorem continuum_as_colimit_of_counting_synthesis
    (n : ℕ) (f : DiagAlg n) :
    Fintype.card (BitWord n) = 2 ^ n ∧
    Fintype.card (BitWord (n + 1)) = 2 * Fintype.card (BitWord n) ∧
    jaynesRelativeEntropy (Finset.univ : Finset (BitWord n))
      (finiteCountingReference n) (finiteCountingReference n) = 0 ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f ∧
    cylinder n f ∈ CylinderColimit := by
  constructor
  · exact bitword_count n
  constructor
  · exact bitword_count_succ n
  constructor
  · exact finite_counting_reference_entropy_self n
  constructor
  · exact counting_refinement_preserves_cylinder n f
  · exact finite_count_observable_mem_colimit n f

/-- Four-lane version matching the Cuntz `O_4`/Cantor limit: finite counts
grow by `4`, but reference-relative entropy and cylinder observables remain
compatible through the direct colimit. -/
theorem continuum_as_four_lane_colimit_counting_synthesis
    (n : ℕ) (f : FourDiagAlg n) :
    Fintype.card (FourWord n) = 4 ^ n ∧
    Fintype.card (FourWord (n + 1)) = 4 * Fintype.card (FourWord n) ∧
    jaynesRelativeEntropy (Finset.univ : Finset (FourWord n))
      (finiteCountingReference4 n) (finiteCountingReference4 n) = 0 ∧
    cylinder4 (n + 1) (diagEmbedSucc4 n f) = cylinder4 n f := by
  constructor
  · exact fourword_count n
  constructor
  · exact fourword_count_succ n
  constructor
  · exact finite_counting_reference4_entropy_self n
  · exact cylinder4_compatible_succ n f

end ContinuumAsColimitCounting

end noncomputable section
