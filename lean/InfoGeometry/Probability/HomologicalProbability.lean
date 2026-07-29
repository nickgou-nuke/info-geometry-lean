import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Probability.HomologicalProbability

Lean owner surface for the theorem bank on probability, symmetry, and
homological probability.

This module formalizes the **structural shapes** of the theorems in the bank.
It does not claim analytic proofs.  Statements are classified as:

- `theorem ... := by ...`    — mechanically verified
- `theorem ... := by by rfl`  — mathematically stated, analytic proof deferred
- `def ...`                  — definitional / structural surface
- `-- CONJECTURE:`           — open problem, not asserted in Lean

## Contents

- §0  Naming and invariance (Poincaré–Grothendieck principle)
- §1  Classical probability (Hardy–Weinberg, LLN shape, entropy, Fisher metric)
- §2  Kinetic probability shapes (BBGKY hierarchy type)
- §3–4 Percolation and self-avoiding walk shapes
- §5  Protein folding filtration
- §6  Language probability
- §7  Homological probability definitions
- §8  Cycle spaces, volume filtration, Almgren type, Weyl law shape
- §9  Waist and packing shapes
- §10 Curvature width bound shape
- §11 Quantum probability shapes
- §12 Homological probability principle (master schema)
- §13 Invertibility and homological probability (Drazin, null cones)
- §14 Noncommutative probability (C*-states, GNS, projection lattice)
- §15 Type III probability and modular flow
- §16 Split Clifford superlattices (CAR relations, Boolean lattice shadow)
- §17 Krein structure, grading, and chirality (V₄, Cartan split)
- §18 Division algebras and Hurwitz obstruction
- §19 Lattices, duality, and defects (K-theory shapes)
- §20 Clifford probability systems (full Clifford probability structure)
- §21 Final synthesis (full pipeline, invertibility boundary)
- §22 Five-graded Erlangen symmetry, affine closure, and GW bundle isomorphism
       (Kantor–Koecher–Tits, Fan–Lee arXiv:1607.00740, Erlangen–Langlands program)
- §23 Klein-Gromov Synthesis: curves as Lie-group orbits, Weyl-graph localization
       (G/P homogeneous targets, coroot SL₂ orbits, virtual localization pipeline)
- §24 Gromov homological probability roadmap
       (momentum-map probability, homological measures, moving-ball configurations,
        cycle-volume spectra, Weyl gauge of volume)
- §25 Tomita–Gromov modular thermodynamic bridge
       (classical Radon–Nikodym → relative modular operator → Araki entropy;
        Gibbs–KMS thermodynamics; GKSL dissipative dynamics; grand capstone dictionary)
- §26 Modular volume potentials bridge
       (state = e^{-potential} × volume; spectral volume vs spectral weight;
        Weyl/KMS synthesis; supertrace/supervolume; grand capstone slogans)
- §27 Spectral thermal normalization
       (partition function = Boltzmann normalization of spectral volume;
        log-RN potential = βE + log Z_β; free-energy identity; Weyl gauge;
        type III caveat; extended modular bridge)
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Probability.Homological

-- ---------------------------------------------------------------------------
-- §0  Meta-principle: naming / invariance
-- ---------------------------------------------------------------------------

/--
A common invariant structure shared by two classes of objects.
Safer than asserting `α ≃ β`.
-/
structure CommonInvariantStructure (α β I : Type*) where
  leftInvariant  : α → I
  rightInvariant : β → I

/--
Poincaré–Grothendieck naming principle, as data rather than a false theorem.
-/
def PoincareGrothendieckNamingPrinciple (α β I : Type*) :=
  CommonInvariantStructure α β I

-- ---------------------------------------------------------------------------
-- §1  Classical probability
-- ---------------------------------------------------------------------------

section ClassicalProbability

/--
Total mass of a finite matrix.
-/
def matrixTotalMass {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j

/--
Hardy–Weinberg recombination map.

`T A` replaces `A i j` by the product of the row and column marginals.
-/
def hardyWeinbergMap {n : ℕ} (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    (∑ k, A i k) * (∑ k, A k j)

/--
**Theorem 1.2 — Event algebras have zero divisors.**

For disjoint nonempty events `A` and `B`, the pointwise indicators satisfy
`1_A · 1_B = 0` with neither factor zero.
-/
theorem indicator_zeroDivisors_of_disjoint {ι : Type*} (A B : Set ι)
    (hAB : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    Set.indicator A (fun _ : ι => (1 : ℝ)) *
      Set.indicator B (fun _ : ι => (1 : ℝ)) = 0 ∧
    Set.indicator A (fun _ : ι => (1 : ℝ)) ≠ 0 ∧
    Set.indicator B (fun _ : ι => (1 : ℝ)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [Pi.mul_apply, Pi.zero_apply]
    by_cases hxA : x ∈ A
    · simp [hxA, Set.disjoint_left.mp hAB hxA]
    · simp [hxA]
  · obtain ⟨x, hxA⟩ := hA
    intro h
    have := congr_fun h x
    simp [hxA] at this
  · obtain ⟨x, hxB⟩ := hB
    intro h
    have := congr_fun h x
    simp [hxB] at this


/--
Unnormalized iterate: `T(T(A)) = (matrixTotalMass A)² · T(A)`.

Idempotence requires the normalization `matrixTotalMass A = 1`.
-/
theorem hardyWeinbergMap_iterate {n : ℕ} (A : Fin n → Fin n → ℝ) :
    hardyWeinbergMap (hardyWeinbergMap A) =
    fun i j => (matrixTotalMass A) ^ 2 * hardyWeinbergMap A i j := by
  funext i j
  have hrow :
      (∑ k, hardyWeinbergMap A i k) =
        (∑ k, A i k) * matrixTotalMass A := by
    have hrowSum : matrixTotalMass A = ∑ k, ∑ l, A l k := by
      simpa [matrixTotalMass] using
        (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun l k => A k l)).symm
    calc
      (∑ k, hardyWeinbergMap A i k)
          = ∑ k, (∑ l, A i l) * ∑ l, A l k := by
              simp [hardyWeinbergMap]
      _ = (∑ l, A i l) * (∑ k, ∑ l, A l k) := by
            simpa using
              (Finset.mul_sum (s := Finset.univ) (f := fun k => ∑ l, A l k)
                (a := ∑ l, A i l)).symm
      _ = (∑ k, A i k) * matrixTotalMass A := by
            rw [hrowSum]
  have hcol :
      (∑ k, hardyWeinbergMap A k j) =
        matrixTotalMass A * (∑ k, A k j) := by
    calc
      (∑ k, hardyWeinbergMap A k j)
          = ∑ k, (∑ l, A k l) * ∑ l, A l j := by
              simp [hardyWeinbergMap]
      _ = (∑ k, ∑ l, A k l) * (∑ l, A l j) := by
            simpa using
              (Finset.sum_mul (s := Finset.univ) (f := fun k => ∑ l, A k l)
                (a := ∑ l, A l j)).symm
      _ = matrixTotalMass A * (∑ k, A k j) := by
            simp [matrixTotalMass]
  calc
    hardyWeinbergMap (hardyWeinbergMap A) i j
        = (∑ k, hardyWeinbergMap A i k) * (∑ k, hardyWeinbergMap A k j) := by
          rfl
    _ = ((∑ k, A i k) * matrixTotalMass A) *
          (matrixTotalMass A * (∑ k, A k j)) := by
          simp [hrow, hcol]
    _ = (matrixTotalMass A) ^ 2 * hardyWeinbergMap A i j := by
          calc
            ((∑ k, A i k) * matrixTotalMass A) * (matrixTotalMass A * (∑ k, A k j))
                = (matrixTotalMass A) ^ 2 * ((∑ k, A i k) * (∑ k, A k j)) := by
                  ring
            _ = (matrixTotalMass A) ^ 2 * hardyWeinbergMap A i j := by
                  simp [hardyWeinbergMap]

/--
**Theorem 1.1 — Hardy–Weinberg idempotence** (normalized case).

`T(T(A)) = T(A)` when `matrixTotalMass A = 1`.
-/
theorem hardyWeinbergMap_idempotent {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : matrixTotalMass A = 1) :
    hardyWeinbergMap (hardyWeinbergMap A) = hardyWeinbergMap A := by
  rw [hardyWeinbergMap_iterate A]
  funext i j
  simp [hA]

/--
Shannon entropy on an arbitrary finite index type.
-/
def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

/--
**Theorem 1.4 — Subadditivity of entropy (statement).**

Stated over abstract finite types to avoid brittle `Fin (n * m)` indexing.
-/
def EntropicSubadditivityStatement : Prop :=
  ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ)
    (_hpos : ∀ x, 0 ≤ p x)
    (_hsum : ∑ x, p x = 1),
    let pX : ι → ℝ := fun i => ∑ j : κ, p (i, j)
    let pY : κ → ℝ := fun j => ∑ i : ι, p (i, j)
    shannonEntropy p ≤ shannonEntropy pX + shannonEntropy pY

/--
**Theorem 1.5 — Fisher metric as Hessian of negative entropy (definition).**

On the interior of the probability simplex `∑ pᵢ = 1, pᵢ > 0`, the Fisher
metric in coordinates `p` is `gᵢⱼ = δᵢⱼ / pᵢ`.  The square-root map
`p ↦ 2 √p` converts this to the round sphere metric.
-/
def fisherMetricDiagonal (n : ℕ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  if p i > 0 then 1 / p i else 0

def squareRootEmbedding (n : ℕ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * Real.sqrt (p i)

end ClassicalProbability

-- ---------------------------------------------------------------------------
-- §2  Kinetic probability shapes
-- ---------------------------------------------------------------------------

section KineticProbability

/--
BBGKY hierarchy shape (Theorem 2.2).

The evolution of the `k`-particle marginal `f^(k)` depends on `f^(k+1)`
via a collision operator `C`.  This records the type of the hierarchy as a
family indexed by `k`.
-/
structure BBGKYHierarchy
    (Ω : Type*) [MeasureTheory.MeasureSpace Ω]
    (T : ℝ) where
  /-- `k`-particle marginal distribution at time `t`. -/
  marginal : ∀ (k : ℕ), ℝ → (Fin k → Ω) → ℝ
  /-- Collision operator coupling `k`-particle to `(k+1)`-particle marginal. -/
  collisionOp : ∀ (k : ℕ), ((Fin k → Ω) → ℝ) → ((Fin (k + 1) → Ω) → ℝ) → (Fin k → Ω) → ℝ

end KineticProbability

-- ---------------------------------------------------------------------------
-- §3  Percolation
-- ---------------------------------------------------------------------------

section Percolation

/--
**Theorem 3.1 — Branching-process threshold (statement).**

On a `d`-ary tree, bond percolation with retention probability `p` has a
positive probability of an infinite open cluster iff `d * p > 1`.
Critical value: `p_c = 1 / d`.
-/
def RegularTreePercolationThreshold (d : ℕ) (_hd : 0 < d) : ℝ :=
  1 / (d : ℝ)

theorem regularTreePercolationThreshold_eq (d : ℕ) (hd : 0 < d) :
    RegularTreePercolationThreshold d hd = 1 / (d : ℝ) := rfl

/--
**Conjecture 3.4 — Homological percolation duality (owner surface).**

For a closed `d`-manifold with dual cell decomposition, the appearance of
`k`-dimensional homological connectivity is coupled to the disappearance of
`(d - k - 1)`-dimensional dual obstructions.  In a self-dual case, the
critical parameter is often `p = 1/2`.

This `Prop` records the shape of the conjecture for `k = 0`.
-/
def HomologicalPercolationDualityStatement (d k : ℕ) (_hk : k + 1 ≤ d) : Prop :=
  ∃ (p_c : ℝ), 0 < p_c ∧ p_c < 1 ∧ p_c = 1 / 2

end Percolation

-- ---------------------------------------------------------------------------
-- §4  Self-avoiding walks
-- ---------------------------------------------------------------------------

section SelfAvoidingWalks

/--
**Theorem 4.1 — Existence of the connective constant.**

The number `c_n` of `n`-step self-avoiding walks grows as `μⁿ` where `μ`
is the connective constant.  This `def` records `μ` as a limit.
-/
noncomputable def connectiveConstant
    (c : ℕ → ℕ)  -- c n = number of n-step SAWs
    (_hsupmul : ∀ m n : ℕ, c (m + n) ≤ c m * c n) :  -- submultiplicativity
    ℝ :=
  Real.exp (iSup fun n : ℕ => if n = 0 then 0 else Real.log (c n) / n)

/--
**Theorem 4.2 — Honeycomb connective constant.**

For the hexagonal lattice `μ = √(2 + √2)`.  This records the numerical
constant; the proof of the value is Duminil-Copin–Smirnov 2012.
-/
def honeycombConnectiveConstant : ℝ :=
  Real.sqrt (2 + Real.sqrt 2)

theorem honeycombConnectiveConstant_pos : 0 < honeycombConnectiveConstant := by
  unfold honeycombConnectiveConstant
  positivity

end SelfAvoidingWalks

-- ---------------------------------------------------------------------------
-- §5  Protein folding as filtered topology
-- ---------------------------------------------------------------------------

section ProteinFolding

/--
**Definition 5.1 — Energy landscape filtration.**

The sublevel set `ℭ_{≤a}` of a configuration space at energy threshold `a`.
-/
def subLevelSet
    {C : Type*} (E : C → ℝ) (a : ℝ) : Set C :=
  { x | E x ≤ a }

/--
Reachability inside an energy sublevel set.

Replaces the false `reachability_iff_same_component`: path-connectedness is
strictly stronger than connected-component equality in arbitrary spaces.
-/
def EnergyReachable
    {C : Type*} [TopologicalSpace C]
    (E : C → ℝ) (a : ℝ) (p q : C) : Prop :=
  ∃ γ : Set.Icc (0 : ℝ) 1 → C,
    Continuous γ ∧
    γ ⟨0, by constructor <;> norm_num⟩ = p ∧
    γ ⟨1, by constructor <;> norm_num⟩ = q ∧
    ∀ t, E (γ t) ≤ a

/--
Energy-reachability implies both endpoints lie in the sublevel set.
Mechanically verified.
-/
theorem energyReachable_endpoints_mem
    {C : Type*} [TopologicalSpace C]
    (E : C → ℝ) (a : ℝ) (p q : C)
    (h : EnergyReachable E a p q) :
    p ∈ subLevelSet E a ∧ q ∈ subLevelSet E a := by
  rcases h with ⟨γ, _hγ, hp, hq, hsub⟩
  exact ⟨by simp only [subLevelSet, Set.mem_setOf_eq]; rw [← hp];
              exact hsub ⟨0, by constructor <;> norm_num⟩,
         by simp only [subLevelSet, Set.mem_setOf_eq]; rw [← hq];
              exact hsub ⟨1, by constructor <;> norm_num⟩⟩

end ProteinFolding

-- ---------------------------------------------------------------------------
-- §6  Language probability
-- ---------------------------------------------------------------------------

section LanguageProbability

/--
**Theorem 6.2 — Scalar frequency is not a linguistic invariant.**

Two strings can have equal empirical frequency but non-isomorphic context
trees.  Recorded as a `Prop` — the proof is a construction of an explicit
pair of strings (left to the linguistic/NLP layer).
-/
def ScalarFrequencyNotLinguisticInvariant : Prop :=
  ∃ (corpus : Type*) (freq : corpus → ℝ) (contextTree : corpus → Type*),
    ∃ w₁ w₂ : corpus,
      freq w₁ = freq w₂ ∧
      ¬ Nonempty (contextTree w₁ ≃ contextTree w₂)

/--
A Winograd pair: two sentences with the same syntactic form but different
required pronoun resolution.
-/
structure WinogradPair
    (Sentence SyntacticForm : Type*)
    (syntaxOf : Sentence → SyntacticForm)
    (resolution : Sentence → Bool) where
  s₁ : Sentence
  s₂ : Sentence
  sameSyntax : syntaxOf s₁ = syntaxOf s₂
  differentResolution : resolution s₁ ≠ resolution s₂

/--
**Theorem 6.3 — Winograd obstruction.** Mechanically verified.

A syntax-only resolver cannot simultaneously solve both sentences of any
Winograd pair.
-/
theorem syntaxOnlyFailsOnWinogradPair
    {Sentence SyntacticForm : Type*}
    {syntaxOf : Sentence → SyntacticForm}
    {resolution : Sentence → Bool}
    (w : WinogradPair Sentence SyntacticForm syntaxOf resolution) :
    ¬ ∃ f : SyntacticForm → Bool,
      f (syntaxOf w.s₁) = resolution w.s₁ ∧
      f (syntaxOf w.s₂) = resolution w.s₂ := by
  rintro ⟨f, h₁, h₂⟩
  exact w.differentResolution (h₁.symm.trans (by rw [w.sameSyntax]) |>.trans h₂)

/--
**Program theorem 6.4 — Language probability as a functor (shape).**

A probability theory for language assigns to each sentence a structured
context tree, not merely a scalar in [0,1].  This `def` records the type of
such an assignment.
-/
def LanguageProbabilityFunctor
    (Sentence ContextTree : Type*) : Type _ :=
  Sentence → ContextTree

end LanguageProbability

-- ---------------------------------------------------------------------------
-- §7  Homological probability
-- ---------------------------------------------------------------------------

section HomologicalProbability

/--
**Definition 7.1 — Observable map.**

An observation is modeled by a map `f : X → O` from state space to
observable space.  The pre-image `f⁻¹(U)` is the state-space event for
observable event `U`.
-/
def observablePreimage
    {X O : Type*}
    (f : X → O)
    (U : Set O) : Set X :=
  f ⁻¹' U

/--
**Definition 7.3 — Support invariant with measure-like properties.**

`Inv` may be ideals, subspaces, filtered modules, or spectra ordered by
inclusion.  The cup-product axiom requires a multiplication on `Inv`.
-/
structure SupportInvariantMeasureLike
    (O Inv : Type*) [Preorder Inv] [Mul Inv]
    (I : Set O → Inv) : Prop where
  mono            : ∀ (U V : Set O), U ⊆ V → I U ≤ I V
  cup_intersection : ∀ U V : Set O, I U * I V ≤ I (U ∩ V)

/--
**Definition 7.4 — Homological probability theory.**

Assigns an ordered invariant to each observable event, monotone w.r.t.
event inclusion.  The `[Preorder Inv]` makes the monotonicity axiom non-trivial.
-/
structure HomologicalProbabilityTheory (O Inv : Type*) [Preorder Inv] where
  assign : Set O → Inv
  mono   : ∀ (U V : Set O), U ⊆ V → assign U ≤ assign V

/--
Scalar probability as a decategorified shadow: `P(U) = shadow(assign(U))`.
-/
def decategorify
    {O Inv : Type*} [Preorder Inv]
    (theory : HomologicalProbabilityTheory O Inv)
    (shadow : Inv → ℝ)
    (U : Set O) : ℝ :=
  shadow (theory.assign U)

end HomologicalProbability

-- ---------------------------------------------------------------------------
-- §8  Cycle spaces and homological spectra
-- ---------------------------------------------------------------------------

section CycleSpaces

/--
**Theorem 8.1 — Almgren cycle-space theorem (statement shape).**

`π_i(𝒵_k(M; G)) ≅ H_{i+k}(M; G)`.

Recorded as a `Prop` over abstract types.  The full proof is in geometric
measure theory (Almgren 1962).
-/
def AlmgrenCycleSpaceStatement
    (HomologyGroup : ℕ → Type*)   -- H_{i+k}(M; G)
    (HomotopyGroup : ℕ → Type*)   -- π_i(𝒵_k)
    (k : ℕ) : Prop :=
  ∀ i : ℕ, Nonempty (HomotopyGroup i ≃ HomologyGroup (i + k))

/--
**Definition 8.2 — Volume filtration on cycle space (shape).**

The sublevel set `𝒵_k^{≤V}(M)` of `k`-cycles with volume at most `V`.
-/
def volumeSubLevelCycles
    {CycleSpace : Type*}
    (vol : CycleSpace → ℝ)
    (V : ℝ) : Set CycleSpace :=
  { Z | vol Z ≤ V }

/--
**Program theorem 8.3 — Homological spectrum of cycles (shape).**

The spectral value of a homology class `α` is the infimum volume at which
`α` is first detected in the filtration.
-/
def spectralValue
    {Class : Type*}
    (detected : ℝ → Class → Prop)  -- "α detected at volume threshold V"
    (α : Class) : ℝ :=
  sInf { V : ℝ | detected V α }

/--
**Theorem 8.5 — Rayleigh quotient as topological spectrum (statement).**

The critical values of the Rayleigh quotient `R_A([z]) = ⟨Az,z⟩ / ⟨z,z⟩`
on `ℂP^{n-1}` are exactly the eigenvalues of `A`.  This records the type
of the Rayleigh quotient.
-/
def rayleighQuotient
    {n : ℕ} (A : Fin n → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, A i j * z j * z i) / (∑ i, z i ^ 2)

end CycleSpaces

-- ---------------------------------------------------------------------------
-- §9  Waist and packing
-- ---------------------------------------------------------------------------

section WaistPacking

/--
**Theorem 9.1 — Gromov waist theorem for the sphere (statement shape).**

For any continuous `f : Sⁿ → ℝᵐ`, there exists a point `y ∈ ℝᵐ` such that
the `r`-neighborhood of `f⁻¹(y)` has volume ≥ that of the `r`-neighborhood
of an equatorial `S^{n-m}`.

Recorded as an existence statement over abstract spaces.
-/
def GromovWaistStatement
    (S Rm : Type*)
    (f : S → Rm)
    (neighborhood : ℝ → Set S → Set S)        -- r-neighborhood in S
    (vol : Set S → ℝ)
    (equatorialNeighborhoodVol : ℝ → ℝ) :     -- vol of r-nbhd of equatorial S^{n-m}
    Prop :=
  ∃ y : Rm, ∀ r > 0,
    vol (neighborhood r { x : S | f x = y }) ≥ equatorialNeighborhoodVol r

end WaistPacking

-- ---------------------------------------------------------------------------
-- §10  Curvature and sweepouts
-- ---------------------------------------------------------------------------

section CurvatureWidth

/--
**Theorem 10.1 — Scalar curvature width bound for S³.**

Parameterized by a metric type, avoiding the false universal statement
`∀ width scalarCurvature, scalarCurvature ≥ 6 → width ≤ 4π`.
-/
def ScalarCurvatureWidthBoundStatement
    (MetricOnS3 : Type*)
    (scalarCurvatureLowerBound : MetricOnS3 → ℝ)
    (simonSmithWidth : MetricOnS3 → ℝ) : Prop :=
  ∀ g : MetricOnS3,
    scalarCurvatureLowerBound g ≥ 6 →
    simonSmithWidth g ≤ 4 * Real.pi

-- CONJECTURE 10.2: Higher-dimensional scalar-curvature homological spectrum bound.
-- For M^n with R_g ≥ n(n-1), the homological spectra satisfy universal upper
-- bounds analogous to the round sphere.

end CurvatureWidth

-- ---------------------------------------------------------------------------
-- §11  Quantum probability
-- ---------------------------------------------------------------------------

section QuantumProbability

/--
**Theorem 11.1 — Quantum-to-classical moment map.**

The moment map `ℂPⁿ⁻¹ → Δⁿ⁻¹` sends `[z₁ : … : zₙ]` to the probability
vector `(|z₁|²/Σ|zⱼ|², …, |zₙ|²/Σ|zⱼ|²)`.

Recorded as a function on `Fin n → ℂ`.
-/
def momentMap {n : ℕ} (z : Fin n → ℂ) : Fin n → ℝ :=
  let norm2 := ∑ i, Complex.normSq (z i)
  fun i => if norm2 = 0 then 0 else Complex.normSq (z i) / norm2

theorem momentMap_sum_eq_one {n : ℕ} (z : Fin n → ℂ) (h : ∑ i, Complex.normSq (z i) ≠ 0) :
    ∑ i, momentMap z i = 1 := by
  have key : ∀ i : Fin n, momentMap z i =
      Complex.normSq (z i) / ∑ j : Fin n, Complex.normSq (z j) := fun i => by
    unfold momentMap; split_ifs with hif
    · exact absurd hif h
    · rfl
  simp_rw [key, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ h]

/--
**Definition 11.1 — Entropy of a probability spectrum.**

`entropyOfSpectrum λ = -∑ᵢ λᵢ log λᵢ`.

Replaces the incorrect `vonNeumannEntropy` which computed entropy of row sums
(not the von Neumann entropy).  The correct surface abstracts away the
eigenvalue layer.
-/
def entropyOfSpectrum {n : ℕ} (eigenvalues : Fin n → ℝ) : ℝ :=
  -∑ i, eigenvalues i * Real.log (eigenvalues i)

/--
**Theorem 11.2 — Quantum strong subadditivity (abstract form).**

`S(AB) + S(BC) ≥ S(B) + S(ABC)`.  State type and marginals are abstract.
Proof: Lieb–Ruskai theorem.
-/
def QuantumStrongSubadditivityStatement
    (State : Type*)
    (S : State → ℝ)
    (AB BC B ABC : State → State) : Prop :=
  ∀ ρ : State, S (AB ρ) + S (BC ρ) ≥ S (B ρ) + S (ABC ρ)

end QuantumProbability

-- ---------------------------------------------------------------------------
-- §12  Homological probability principle (master schema)
-- ---------------------------------------------------------------------------

section MasterSchema

/--
**Program theorem 12.1 — Homological probability principle.**

A probability theory for systems with topology assigns to each event `U`
a structured invariant `ℙ_hom(U)` in a category of modules, ideals, spectra,
or filtered homology groups.  The scalar probability is the decategorified
shadow `Φ(ℙ_hom(U))`.

This `def` records the full master schema as a `Prop` over abstract
categorical data.
-/
def HomologicalProbabilityPrinciple
    (O X Inv : Type*)            -- observable / state / invariant spaces
    (_f : X → O)                 -- observation map (structurally present; unused in shadow)
    (assign : Set O → Inv)       -- homological probability assignment
    (shadow : Inv → ℝ)           -- decategorification
    (scalarProb : Set O → ℝ)     -- ordinary probability
    : Prop :=
  ∀ U : Set O, scalarProb U = shadow (assign U)

/--
**Thesis — Core theorem pattern.**

Every robust theorem in this framework has the form:

  real phenomenon
    → configuration space
    → filtration
    → homological invariant
    → numerical shadow.

The numerical probability is the last step.  This `structure` records the
four-step pipeline.
-/
structure HomologicalProbabilityPipeline
    (Phenomenon ConfigSpace Filtration HomInv : Type*) where
  toConfigSpace     : Phenomenon → ConfigSpace
  toFiltration      : ConfigSpace → Filtration
  toHomInvariant    : Filtration → HomInv
  toNumericalShadow : HomInv → ℝ

def runPipeline
    {Phenomenon ConfigSpace Filtration HomInv : Type*}
    (pipe : HomologicalProbabilityPipeline Phenomenon ConfigSpace Filtration HomInv)
    (x : Phenomenon) : ℝ :=
  pipe.toNumericalShadow
    (pipe.toHomInvariant (pipe.toFiltration (pipe.toConfigSpace x)))

end MasterSchema

-- ---------------------------------------------------------------------------
-- §13  Invertibility and homological probability
-- ---------------------------------------------------------------------------

section InvertibilityObstruction

/--
A linear probability mechanism has an observable inverse when the evolution
operator is invertible on the observable quotient.
-/
structure ObservableInverse
    (V : Type*) [AddCommGroup V]
    (A : V → V)
    (Null Observable : Set V) : Prop where
  null_in_kernel            : ∀ x ∈ Null, A x = 0
  observable_disjoint_null  : Observable ∩ Null = ∅
  inverse_on_observable     : ∃ B : V → V, ∀ x ∈ Observable, B (A x) = x

/--
Drazin-style regularized probability.

When `A ~ N ⊕ C` with `N` nilpotent and `C` invertible, the Drazin inverse
`Aᴰ ~ 0 ⊕ C⁻¹` inverts the regular sector and annihilates the singular one.
-/
structure DrazinRegularizedProbability (State Inv : Type*) where
  singularSector            : Set State
  regularSector             : Set State
  projectionToRegular       : State → regularSector
  inverseOnRegular          : regularSector → regularSector
  invariantOfSingularSector : singularSector → Inv

/--
Structured probability replaces scalar probability when normalization breaks
down (kernel, null cone, nontrivial topology).

`P(U) = scalarShadow (assign U)`.
-/
structure StructuredProbability (Event Inv : Type*) where
  assign       : Event → Inv
  scalarShadow : Inv → ℝ

/--
Master conjecture: every scalar probability is a shadow of a structured one.
-/
def HomologicalProbabilityMasterConjecture
    (Event Inv : Type*)
    (P : Event → ℝ)
    (structured : StructuredProbability Event Inv) : Prop :=
  ∀ U : Event, P U = structured.scalarShadow (structured.assign U)

end InvertibilityObstruction

-- ---------------------------------------------------------------------------
-- §14  Noncommutative probability
-- ---------------------------------------------------------------------------

section NoncommutativeProbability

/--
**Theorem 14.1 — Positive-state criterion.**

A noncommutative probability law on a unital ring `A` is a normalized positive
functional.  Projections `p = p²` are the events; their state values are the
event probabilities.
-/
structure IsNoncommutativeProbabilityState
    {A : Type*} [Ring A]
    (φ : A → ℝ) : Prop where
  normalized : φ 1 = 1
  nonneg     : ∀ a : A, 0 ≤ φ (a * a)

/--
An element `p` is a **projection** (idempotent): `p² = p`.
Events in noncommutative probability are projections.
-/
def IsProjection {A : Type*} [Ring A] (p : A) : Prop :=
  p * p = p

/--
Two projections are **orthogonal** (mutually exclusive events): `p * q = 0`.
-/
def ProjectionsOrthogonal {A : Type*} [Ring A] (p q : A) : Prop :=
  p * q = 0

/--
**Theorem 14.4 — GNS representation (abstract shape).**

Every positive normalized state `φ` on `A` produces a representation `π` on
a Hilbert space `H` and a cyclic vector `Ω` such that `φ(a) = ⟨Ω, π(a)Ω⟩`.
-/
structure GNSData
    (A H : Type*)
    (φ : A → ℝ)
    (π : A → H → H)
    (Ω : H)
    (inner : H → H → ℝ) : Prop where
  normalized_vector : inner Ω Ω = 1
  reproduces_state  : ∀ a : A, φ a = inner Ω (π a Ω)

end NoncommutativeProbability

-- ---------------------------------------------------------------------------
-- §15  Type III probability and modular flow
-- ---------------------------------------------------------------------------

section TypeIIIProbability

/--
**Definition 15.1 — Tracial state.**

`φ` is tracial if `φ(ab) = φ(ba)` for all `a, b`.
Type III von Neumann factors admit no finite normal tracial state.
-/
def IsTracialState {A : Type*} [Ring A] (φ : A → ℝ) : Prop :=
  ∀ a b : A, φ (a * b) = φ (b * a)

/--
**Theorem 15.2 — Tracial state trivializes modular flow.**

When the state is tracial, the KMS modular automorphism group `σ_t^φ` is the
identity.  In genuinely nontracial type III situations, `σ_t^φ` is nontrivial.
-/
def ModularFlowTriviality
    (A : Type*) [Ring A]
    (φ : A → ℝ)
    (σ : ℝ → A → A) : Prop :=
  IsTracialState φ → ∀ t : ℝ, σ t = id

/--
**Program theorem 15.3 — Type III requires a nontracial state (shape).**

Type III behavior cannot appear in a finite matrix algebra (which always
admits a trace).  In infinite Clifford/CAR tensor products, a nontracial KMS
state may produce a type III GNS von Neumann algebra.
-/
def TypeIIIRequiresNontracialState
    (State : Type*) [Ring State]
    (φ : State → ℝ)
    (isTypeIII : (State → ℝ) → Prop) : Prop :=
  isTypeIII φ → ¬ IsTracialState φ

end TypeIIIProbability

-- ---------------------------------------------------------------------------
-- §16  Split Clifford superlattices
-- ---------------------------------------------------------------------------

section CliffordSuperlattice

/--
**Definition 16.1 — CAR relations.**

Creation `c` and annihilation `a` operators satisfy the canonical
anticommutation relations: `cᵢ² = 0`, `aᵢ² = 0`, `aᵢcⱼ + cⱼaᵢ = δᵢⱼ`.
-/
def CARRelations {A : Type*} [Ring A] {N : ℕ} (c a : Fin N → A) : Prop :=
  (∀ i, c i * c i = 0) ∧
  (∀ i, a i * a i = 0) ∧
  (∀ i j : Fin N, a i * c j + c j * a i = if i = j then 1 else 0)

/--
**Theorem 16.2 — Boolean lattice inside a split Clifford algebra.**

The rank-`N` split Clifford algebra `Cl(N,N) ≅ M_{2^N}(ℝ)` contains `2^N`
mutually orthogonal primitive idempotents `p_S` (indexed by subsets
`S ⊆ Fin N`) that partition unity: `p_S p_T = 0` for `S ≠ T`, `∑_S p_S = 1`.
-/
structure BooleanLatticeInAlgebra
    {A : Type*} [Ring A]
    (N : ℕ)
    (p : Finset (Fin N) → A) : Prop where
  idempotent : ∀ S, p S * p S = p S
  orthogonal : ∀ S T : Finset (Fin N), S ≠ T → p S * p T = 0
  partition  : ∑ S : Finset (Fin N), p S = 1

/--
**Definition 16.3 — Split Clifford superlattice.**

The rank-`N` split Clifford superlattice carries creation/annihilation
operators and a `ℤ₂`-parity grading `γ = (-1)^deg`.
-/
structure SplitCliffordSuperlattice (N : ℕ) (A : Type*) [Ring A] where
  c       : Fin N → A  -- creation elements cᵢ
  a       : Fin N → A  -- annihilation elements aᵢ
  numProj : Fin N → A  -- number projectors nᵢ = cᵢ aᵢ
  parity  : A → A       -- ℤ₂-grading γ = (-1)^deg

/--
**Theorem 16.4 — Classical probability as the diagonal shadow.**

Restricting a state `φ` to the Boolean idempotents `p_S` yields a classical
probability distribution on `2^N` outcomes: `P(S) = φ(p_S) ≥ 0`, `∑_S P(S) = 1`.
-/
def ClassicalShadowOfCliffordState
    {A : Type*} [Ring A]
    {N : ℕ}
    (p : Finset (Fin N) → A)
    (φ : A → ℝ) : Prop :=
  (∀ S : Finset (Fin N), 0 ≤ φ (p S)) ∧
  ∑ S : Finset (Fin N), φ (p S) = 1

end CliffordSuperlattice

-- ---------------------------------------------------------------------------
-- §17  Krein structure, grading, and chirality
-- ---------------------------------------------------------------------------

section KreinGrading

/--
An endomorphism squaring to the identity: `f ∘ f = id`.
-/
def IsInvolution {X : Type*} (f : X → X) : Prop :=
  ∀ x, f (f x) = x

/--
**Theorem 17.1 — Klein-four grading symmetry.**

Two commuting involutions `γ` (super-parity) and `J` (Krein/fundamental
symmetry) generate `{1, γ, J, γJ} ≅ V₄ = ℤ₂ × ℤ₂`.
-/
def HasKleinFourGrading {A : Type*} (γ J : A → A) : Prop :=
  IsInvolution γ ∧ IsInvolution J ∧ ∀ a, γ (J a) = J (γ a)

/--
**Theorem 17.2 — Cartan split of Cl(1,1).**

In the split Clifford cell with `e² = 1`, `f² = -1`, `ef = -fe`, the
pseudoscalar `ω = ef` satisfies `ω² = 1`.  Hence `p± = (1 ± ω) / 2` are
orthogonal idempotents, written here as `2p± = 1 ± ω` to avoid division.
-/
def CartanSplitStatement
    {A : Type*} [Ring A]
    (e f ω pPlus pMinus : A) : Prop :=
  e * e = 1 ∧
  f * f = -1 ∧
  e * f = -(f * e) ∧
  ω = e * f ∧
  ω * ω = 1 ∧
  pPlus  + pPlus  = 1 + ω ∧
  pMinus + pMinus = 1 - ω ∧
  IsProjection pPlus ∧
  IsProjection pMinus ∧
  pPlus * pMinus = 0

end KreinGrading

-- ---------------------------------------------------------------------------
-- §18  Division algebras and Hurwitz obstruction
-- ---------------------------------------------------------------------------

section DivisionAlgebras

/--
**Theorem 18.1 — Hurwitz obstruction.**

Normed real division algebras exist only in dimensions 1, 2, 4, 8
(ℝ, ℂ, ℍ, 𝕆).
-/
def HurwitzDimension (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8

theorem hurwitzDimension_spec :
    { n : ℕ | HurwitzDimension n } = {1, 2, 4, 8} := by
  ext n
  simp only [Set.mem_setOf_eq, HurwitzDimension,
             Set.mem_insert_iff, Set.mem_singleton_iff]

/--
**Principle 18.2 — Hurwitz enters as exceptional symmetry.**

Ordinary probability does not require a division algebra.  Hurwitz algebras
appear only in amplitude, spinorial, Jordan, or exceptional symmetric contexts.
Parameterized by a divisibility hypothesis `isNormedRealDivAlg` on type `D`.
-/
def HurwitzExceptionalPrinciple
    (_D : Type*) (dim : ℕ)
    (isNormedRealDivAlg : Prop) : Prop :=
  isNormedRealDivAlg → HurwitzDimension dim

end DivisionAlgebras

-- ---------------------------------------------------------------------------
-- §19  Lattices, duality, and defects
-- ---------------------------------------------------------------------------

section LatticeDefects

/--
**Definition 19.1 — Probability defect.**

A defect in a noncommutative probability lattice is a failure to globally
choose a classicalizing structure: polarization, grading, trace, or vacuum.
Recorded as the non-existence of a global choice space.
-/
def HasProbabilityDefect (GlobalChoiceSpace : Type*) : Prop :=
  ¬ Nonempty GlobalChoiceSpace

/--
**Theorem 19.2 — Projections define K₀-defect classes.**

Every projection in an algebra defines an abstract K₀-class encoding its
stable homotopy defect.  The map `classOf` is the abstract K₀ functor.
-/
def projectionDefectClass
    {A K0A : Type*} [Ring A]
    (classOf : A → K0A)
    (p : A) (_ : IsProjection p) : K0A :=
  classOf p

/--
**Theorem 19.3 — Unitaries define K₁-defect classes.**

Invertible elements define K₁-classes; projections define K₀-classes.
Together they encode the full topological defect data of a noncommutative
probability space:  events → K₀, phases/unitaries → K₁.
-/
def unitaryDefectClass
    {A K1A : Type*}
    (k1Of : A → K1A)
    (u : A) : K1A :=
  k1Of u

end LatticeDefects

-- ---------------------------------------------------------------------------
-- §20  Clifford probability systems
-- ---------------------------------------------------------------------------

section CliffordProbabilitySystems

/--
**Definition 20.1 — Clifford probability system.**

A Clifford probability system of rank `N` combines:
- creation/annihilation operators satisfying CAR relations,
- a `ℤ₂`-parity grading `γ` and a Krein symmetry `J` (commuting involutions),
- a positive normalized state `φ`.
-/
structure CliffordProbabilitySystem (N : ℕ) (A : Type*) [Ring A] where
  c         : Fin N → A  -- creation elements cᵢ
  a         : Fin N → A  -- annihilation elements aᵢ
  parity    : A → A       -- ℤ₂-grading γ
  jSymmetry : A → A       -- fundamental/Krein symmetry J
  state     : A → ℝ       -- positive normalized state φ

/--
Well-formedness: a Clifford probability system satisfies CAR relations,
admits a Klein-four grading, and carries a noncommutative probability state.
-/
def CliffordProbabilitySystemAxioms
    {N : ℕ} {A : Type*} [Ring A]
    (sys : CliffordProbabilitySystem N A) : Prop :=
  CARRelations sys.c sys.a ∧
  HasKleinFourGrading sys.parity sys.jSymmetry ∧
  IsNoncommutativeProbabilityState sys.state

/--
**Theorem 20.2 — Classical probability as diagonal shadow.**

Restricting the state of a Clifford probability system to the Boolean
idempotent lattice `p_S` recovers a classical probability distribution.
-/
def CliffordProbabilityHasClassicalShadow
    {N : ℕ} {A : Type*} [Ring A]
    (sys : CliffordProbabilitySystem N A)
    (p : Finset (Fin N) → A) : Prop :=
  ClassicalShadowOfCliffordState p sys.state

/--
**Program theorem 20.3 — Infinite Clifford probability and type III.**

An infinite Clifford/CAR tensor product equipped with a nontracial state
may produce a type III GNS von Neumann algebra.  Recorded as an implication
over abstract state and type-III predicate types.
-/
def InfiniteCliffordTypeIII
    (InfAlgState : Type*) [Ring InfAlgState]
    (φ : InfAlgState → ℝ)
    (isTypeIII : (InfAlgState → ℝ) → Prop) : Prop :=
  isTypeIII φ ↔ ¬ IsTracialState φ

end CliffordProbabilitySystems

-- ---------------------------------------------------------------------------
-- §21  Final synthesis
-- ---------------------------------------------------------------------------

section FinalSynthesis

/--
**Thesis 21.1 — Full probability pipeline.**

The complete master pipeline:
  real phenomenon → configuration space → observable algebra
    → state → filtration → homological/modular invariant → numerical shadow.

Extends `HomologicalProbabilityPipeline` (§12) with an explicit algebra layer.
-/
structure FullProbabilityPipeline
    (Phenomenon ConfigSpace ObsAlg HomInv : Type*) where
  toConfigSpace : Phenomenon → ConfigSpace
  toAlgebra     : ConfigSpace → ObsAlg
  toInvariant   : ObsAlg → HomInv
  toNumerical   : HomInv → ℝ

def runFullPipeline
    {Phenomenon ConfigSpace ObsAlg HomInv : Type*}
    (pipe : FullProbabilityPipeline Phenomenon ConfigSpace ObsAlg HomInv)
    (x : Phenomenon) : ℝ :=
  pipe.toNumerical (pipe.toInvariant (pipe.toAlgebra (pipe.toConfigSpace x)))

/--
**Thesis 21.2 — Invertibility boundary is the null cone.**

The boundary of probability (zero-probability conditioning denominators,
Fisher metric singularities, non-invertible transfer operators) is disjoint
from the observable/regular region — analogous to the null cone in Clifford
geometry where invertibility fails.
-/
def InvertibilityBoundaryStatement
    (State : Type*)
    (observableRegion nullCone : Set State) : Prop :=
  Disjoint observableRegion nullCone

/--
**Thesis 21.3 — Scalar probability is the last step.**

Every robust probability theorem factors as:
  `scalarProb U = shadow (structuredProb U)`.
Scalar probability is the final decategorification, not the primary object.
-/
def ScalarProbabilityAsLastStep
    (Event Inv : Type*)
    (structuredProb : Event → Inv)
    (shadow : Inv → ℝ)
    (scalarProb : Event → ℝ) : Prop :=
  ∀ U : Event, scalarProb U = shadow (structuredProb U)

end FinalSynthesis

-- ---------------------------------------------------------------------------
-- §22  Five-graded Erlangen symmetry, affine closure, and GW bundle isomorphism
--      (Kantor–Koecher–Tits decomposition, Fan–Lee 2018, arXiv:1607.00740)
-- ---------------------------------------------------------------------------

section FiveGradedErlangen

/--
**Definition 22.1 — Five-graded Lie algebra (KKT decomposition).**

A Lie algebra `G` with a ℤ-grading concentrated in {-2,-1,0,1,2}:
`G = G₋₂ ⊕ G₋₁ ⊕ G₀ ⊕ G₁ ⊕ G₂`.

This is the Kantor–Koecher–Tits (KKT) five-grading, the algebraic skeleton of
exceptional Lie groups (E₆, E₇, E₈, F₄, G₂) and their Erlangen geometries.
Index convention: `gradeSubspace k` ↔ degree `(k : ℤ) - 2`, so
`gradeSubspace 0 = G₋₂`, `gradeSubspace 2 = G₀`, `gradeSubspace 4 = G₂`.

- `G₀` (index 2): structure (Levi) algebra — symmetries preserving the grading
- `G_{±1}` (indices 1, 3): Jordan pair components — conformal directions
- `G_{±2}` (indices 0, 4): Freudenthal centers — Heisenberg-type directions

The Lie bracket is supplied as an explicit parameter to avoid importing
`Mathlib.Algebra.Lie.Basic`; this is an owner-surface shape, not a full proof.
-/
structure FiveGradedLieAlgebra (G : Type*) (bracket : G → G → G) where
  /-- The five grade-subspaces `G_{k-2}` for `k : Fin 5`. -/
  gradeSubspace : Fin 5 → Set G
  /-- Every element belongs to at least one grade. -/
  graded_cover : ∀ x : G, ∃ k : Fin 5, x ∈ gradeSubspace k
  /-- Grade-0 (structure algebra, index 2) is bracket-closed. -/
  structureAlgebra_closed : ∀ x y : G,
    x ∈ gradeSubspace ⟨2, by omega⟩ →
    y ∈ gradeSubspace ⟨2, by omega⟩ →
    bracket x y ∈ gradeSubspace ⟨2, by omega⟩
  /-- The KKT bracket identity: grade `i` and grade `j` land in grade `i+j`
      (clamped to the five-grading window). -/
  graded_bracket : ∀ (i j : Fin 5) (x y : G),
    x ∈ gradeSubspace i →
    y ∈ gradeSubspace j →
    bracket x y ∈ gradeSubspace ⟨min 4 (i.val + j.val), by omega⟩

/--
**Definition 22.2 — Five-graded symmetry group.**

A group `Sym` acting on a space `X` is *five-graded* if its Lie algebra `G`
admits a KKT five-grading and there is a graded exponential map `G → Sym`.

The grade-0 exponential image is the *structure subgroup* (stabilizer of the
grading), and `Sym / (structure subgroup)` is the Erlangen homogeneous space.

Typeclass instances are supplied as explicit function parameters so that this
owner surface compiles without extra imports.
-/
structure FiveGradedSymmetryGroup
    (Sym X G : Type*)
    (mulSym    : Sym → Sym → Sym)   -- group multiplication
    (oneSym    : Sym)               -- group identity
    (actSym    : Sym → X → X)       -- group action on X
    (bracket   : G → G → G) where   -- Lie bracket on G
  fiveGrading       : FiveGradedLieAlgebra G bracket
  expMap            : G → Sym
  structureSubgroup : Set Sym
  /-- The identity is in the structure subgroup. -/
  struct_one : oneSym ∈ structureSubgroup
  /-- The structure subgroup is closed under multiplication. -/
  struct_mul : ∀ g₁ g₂ : Sym,
    g₁ ∈ structureSubgroup → g₂ ∈ structureSubgroup →
    mulSym g₁ g₂ ∈ structureSubgroup
  /-- The grade-0 subalgebra exponentiates into the structure subgroup. -/
  exp_lands_in_struct : ∀ v : G,
    v ∈ fiveGrading.gradeSubspace ⟨2, by omega⟩ →
    expMap v ∈ structureSubgroup

/--
**Definition 22.3 — Affine closure of an Erlangen homogeneous space.**

For `Sym` acting on the open dense Erlangen model `X`, the *affine closure*
`XBar` compactifies `X` with a boundary stratum `BX` (the "at-infinity" locus).
The action of `Sym` extends to `XBar`; boundary strata are lower-dimensional
Erlangen sub-geometries.

Examples:
- `ℙⁿ` is the affine closure of affine space `𝔸ⁿ` (classical projective geometry)
- The Baily–Borel compactification is the affine closure of an arithmetic domain
- In GW theory (Fan–Lee 2018): `ℙ(E)` carries the affine closure data for `E`

`BX` replaces the notation `∂X` (boundary) since `∂` is a reserved Lean token.
-/
structure AffineClosure (Sym X XBar BX : Type*) where
  /-- Embedding of the open dense stratum. -/
  inclusion      : X → XBar
  /-- Extended group action on the compactification. -/
  extendedAction : Sym → XBar → XBar
  /-- Boundary-at-infinity stratum embedding. -/
  boundary       : BX → XBar
  /-- Every point of `XBar` lies in the open stratum or the boundary. -/
  decomposition  : ∀ p : XBar,
    (∃ x : X,  inclusion x = p) ∨
    (∃ b : BX, boundary b = p)
  /-- The action preserves the open stratum: `g · inclusion(x) = inclusion(g · x)`. -/
  action_preserves_open : ∀ (g : Sym) (x : X),
    ∃ y : X, extendedAction g (inclusion x) = inclusion y

/--
**Theorem 22.4 — GW bundle isomorphism principle (Fan–Lee 2018, arXiv:1607.00740).**

For two equivariant vector bundles `Ea`, `Eb` over an algebraic GKM manifold
with the same equivariant Chern classes, the genus-zero equivariant
Gromov–Witten theories of the projective bundles `ℙ(Ea)` and `ℙ(Eb)` are
naturally isomorphic.

In the Erlangen–Langlands framework: the GW invariant of a projective bundle
is determined by the Chern character shadow of the full K-theoretic datum.
This is an instance of the decategorification principle (§12, §21):
  `gwTheory Ea ≃ gwTheory Eb`  whenever  `chernClasses Ea = chernClasses Eb`.
-/
def GWBundleIsomorphismStatement
    (Bundle ChernClass : Type*)
    (chernClasses : Bundle → ChernClass)
    (gwTheory     : Bundle → Type*) : Prop :=
  ∀ Ea Eb : Bundle,
    chernClasses Ea = chernClasses Eb →
    Nonempty (gwTheory Ea ≃ gwTheory Eb)

/--
**Theorem 22.5 — Affine closure encodes GW boundary data.**

Owner-surface statement: an `AffineClosure` witness is sufficient to reconstruct
the GW bundle isomorphism — the boundary localization residues at `BX` determine
the quantum cohomology ring, hence the GW isomorphism between bundles with equal
equivariant Chern classes.
-/
def AffineClosureOwnerStatement
    (Sym X XBar BX Bundle ChernClass : Type*)
    (chernClasses : Bundle → ChernClass)
    (gwTheory     : Bundle → Type*) : Prop :=
  AffineClosure Sym X XBar BX →
  GWBundleIsomorphismStatement Bundle ChernClass chernClasses gwTheory

/--
**Definition 22.6 — Erlangen–Langlands five-graded owner witness.**

Packages the five-graded symmetry group acting on a homogeneous space, the
affine closure of that space, and the GW-bundle isomorphism principle into a
single owner witness.  This is the §22 Erlangen–Langlands owner target.
-/
structure ErlangenFiveGradedOwnerWitness
    (Sym X XBar BX G Bundle ChernClass : Type*)
    (mulSym       : Sym → Sym → Sym)
    (oneSym       : Sym)
    (actSym       : Sym → X → X)
    (bracket      : G → G → G)
    (chernClasses : Bundle → ChernClass)
    (gwTheory     : Bundle → Type*) where
  /-- The five-graded symmetry group acting on the homogeneous space `X`. -/
  fiveGradedSym    : FiveGradedSymmetryGroup Sym X G mulSym oneSym actSym bracket
  /-- The affine closure of the Erlangen homogeneous space. -/
  affineClosure    : AffineClosure Sym X XBar BX
  /-- The GW-bundle isomorphism holds for this geometry. -/
  gwIsomorphism    : GWBundleIsomorphismStatement Bundle ChernClass
    chernClasses gwTheory
  /-- The boundary stratum inherits its own five-graded structure. -/
  boundaryFiveGrading : FiveGradedLieAlgebra G bracket

/--
**Theorem 22.7 — Five-graded filtration instantiates the homological pipeline.**

The KKT five-grading on `G` provides a canonical 5-step filtration that
instantiates the `HomologicalProbabilityPipeline` of §12:

  `FiveGradedLieAlgebra G bracket`  →  grade-subspaces `(Fin 5 → Set G)`
    →  filtration (identity)  →  numerical shadow (= 5, the number of grades).

The grade count `5` is the numerical shadow of the homological probability on
the five-graded Erlangen geometry.
-/
def fiveGradedHomologicalPipeline (G : Type*) (bracket : G → G → G) :
    HomologicalProbabilityPipeline
      (FiveGradedLieAlgebra G bracket)
      (Fin 5 → Set G) (Fin 5 → Set G) (Fin 5 → Set G) :=
  { toConfigSpace     := fun fg => fg.gradeSubspace
    toFiltration      := id
    toHomInvariant    := id
    toNumericalShadow := fun _ => 5 }

/-- The five-graded homological pipeline has numerical shadow `5`. -/
@[simp]
theorem fiveGradedHomologicalPipeline_numericalShadow_five
    (G : Type*) (bracket : G → G → G) :
    (fiveGradedHomologicalPipeline G bracket).toNumericalShadow = fun _ => 5 := by
  rfl

end FiveGradedErlangen

-- ---------------------------------------------------------------------------
-- §23  Klein-Gromov Synthesis: curves as Lie-group orbits, Weyl-graph localization
--      (G/P homogeneous targets, coroot SL₂ orbits, virtual localization pipeline)
-- ---------------------------------------------------------------------------

section KleinGromovSynthesis

/--
**Principle 23.1 — Target space as Erlangen quotient (G/P).**

In the most structured GW computations, the target space is a projective
homogeneous space `X = G/P`, where `G` is a complex semisimple Lie group and
`P` is a parabolic subgroup.  All of the geometry of `X` is controlled by
the representation theory of `G`.  This is the Erlangen program viewpoint:
the geometry of `X` *is* the orbit structure of `G`.

`embed : P → G` is the inclusion; `pInvariant` records that right-`P`-translation
preserves the coset.
-/
structure HomogeneousTarget
    (G P X : Type*)
    (mulG  : G → G → G)
    (oneG  : G)
    (embed : P → G) where
  /-- The canonical projection `G → G/P`. -/
  quotientMap : G → X
  /-- Every point of `X` is the image of some `g : G`. -/
  surjective  : ∀ x : X, ∃ g : G, quotientMap g = x
  /-- Right `P`-translation preserves the coset: `gP = gp₂P` for all `p : P`. -/
  pInvariant  : ∀ (g : G) (p : P), quotientMap (mulG g (embed p)) = quotientMap g

/--
**Theorem 23.2 — Rational curves are coroot orbits (Klein-Gromov Synthesis).**

In `G/P`, the fundamental rational curves (`ℂℙ¹`s contributing to GW invariants)
are exactly the closures of orbits of `SL(2,ℂ)`-subgroups of `G` generated by
a positive root vector `Eα` and its negative `E_{-α}`.
The homological degree of such a curve is the **coroot** `αˇ ∈ CoRootLat`.

`TorusOrbits p q` is the type of 1-dimensional torus-orbit curves from fixed
point `p` to `q`; `orbitDegree` labels each by its coroot; `coroot_surjective`
asserts every positive coroot arises from some orbit curve.
-/
structure LieOrbitCurveWitness
    (G T FixedPts CoRootLat : Type*)
    (TorusOrbits : FixedPts → FixedPts → Type*) where
  /-- The homogeneous target space `G/P`. -/
  targetSpace       : Type*
  /-- Each torus-orbit curve between fixed points carries a coroot label. -/
  orbitDegree       : ∀ (p q : FixedPts), TorusOrbits p q → CoRootLat
  /-- Every coroot `α` is the degree of some orbit curve (surjectivity). -/
  coroot_surjective : ∀ α : CoRootLat, ∃ (p q : FixedPts),
    ∃ e : TorusOrbits p q, orbitDegree p q e = α
  /-- Curves with the same coroot label are degree-equivalent. -/
  degree_unique     : ∀ (p q : FixedPts) (e₁ e₂ : TorusOrbits p q),
    orbitDegree p q e₁ = orbitDegree p q e₂

/--
**Theorem 23.3 — Virtual localization collapses to Weyl-graph combinatorics.**

Under the torus action `T ⊂ G` on `X = G/P`, the moduli space of stable maps
`ℳ̄_{g,n}(X, β)` has T-fixed loci indexed by **labeled Weyl graphs**:

- **Vertices**: Weyl-group fixed points `v ∈ Xᵀ ≅ W / Stab`
- **Edges**: 1-dimensional `T`-invariant rational curves (coroot SL₂ orbits)
- **Edge labels**: coroots `αˇ ∈ CoRootLat` recording curve degrees

The infinite-dimensional integration over all stable maps collapses to a finite
sum over labeled graphs.  This is the virtual localization formula of
Atiyah-Bott, specialized to the Erlangen/homogeneous setting.
-/
structure WeylGraphLocalizationData
    (WeylGroup CoRootLat Vertex : Type*)
    (Edge : Vertex → Vertex → Type*) where
  /-- The Weyl fixed-point embedding `W → Xᵀ`. -/
  weylFixed  : WeylGroup → Vertex
  /-- Each edge (torus-orbit curve) carries a coroot degree. -/
  edgeDegree : ∀ (v w : Vertex), Edge v w → CoRootLat
  /-- Injectivity: distinct coroot labels produce distinct edge types. -/
  label_injective : ∀ (v w : Vertex) (e₁ e₂ : Edge v w),
    edgeDegree v w e₁ = edgeDegree v w e₂ → e₁ = e₂

/--
**Theorem 23.4 — GW invariant factors through Weyl-graph localization.**

The Gromov-Witten invariant at coroot degree `α` equals the shadow of the
Weyl-graph datum for that degree.  This is an instance of §12's principle:

  `GW(X, α) = locShadow(WeylGraphData at α)`.

Equivalently: every GW number is computable from pure combinatorics of the
Weyl group and coroot lattice.
-/
def KleinGromovAlignmentStatement
    (WeylGroup CoRootLat Vertex GWClass : Type*)
    (Edge        : Vertex → Vertex → Type*)
    (gwInvariant : CoRootLat → GWClass)
    (locShadow   : WeylGraphLocalizationData WeylGroup CoRootLat Vertex Edge → GWClass) :
    Prop :=
  ∀ α : CoRootLat,
    ∃ locData : WeylGraphLocalizationData WeylGroup CoRootLat Vertex Edge,
      gwInvariant α = locShadow locData

/--
**Definition 23.5 — Klein-Gromov master owner witness.**

Packages the full Klein-Gromov Synthesis:
- The Erlangen target `G/P` (homogeneous space structure)
- Torus-orbit curve witness (coroot SL₂ orbits = rational curves)
- Weyl-graph localization datum (virtual localization data)
- GW–localization alignment (GW = Weyl-graph shadow)

This is the §23 owner target for the Klein-Gromov Erlangen-GW program.
-/
structure KleinGromovOwnerWitness
    (G T P X WeylGroup CoRootLat Vertex GWClass : Type*)
    (mulG        : G → G → G)
    (oneG        : G)
    (embed       : P → G)
    (Edge        : Vertex → Vertex → Type*)
    (TorusOrbits : Vertex → Vertex → Type*)
    (gwInvariant : CoRootLat → GWClass)
    (locShadow   : WeylGraphLocalizationData WeylGroup CoRootLat Vertex Edge → GWClass) where
  /-- The Erlangen homogeneous target `G/P`. -/
  target      : HomogeneousTarget G P X mulG oneG embed
  /-- Rational curves are coroot-labeled torus-orbit closures. -/
  orbitCurves : LieOrbitCurveWitness G T Vertex CoRootLat TorusOrbits
  /-- Virtual localization reduces to Weyl-graph combinatorics. -/
  weylGraph   : WeylGraphLocalizationData WeylGroup CoRootLat Vertex Edge
  /-- GW invariants factor through the Weyl-graph localization shadow. -/
  alignment   : KleinGromovAlignmentStatement WeylGroup CoRootLat Vertex GWClass
    Edge gwInvariant locShadow

/--
**Theorem 23.6 — Klein-Gromov pipeline aligns Volume I and Volume II.**

The fundamental correspondence between the operator-algebraic (Vol.I) and
the Gromov-Witten/Erlangen (Vol.II) pipelines:

| Volume I: Op-Alg Thermodynamics    | Volume II: GW-Erlangen Geometry         |
|------------------------------------+-----------------------------------------|
| Nontracial state `φ_λ`            | Torus action `T ⊂ G`                   |
| Cantor diagonal `D_∞`             | Homogeneous space `G/P`                 |
| Root vectors `E_ij`                | Coroot SL₂ orbits (curves `ℂℙ¹`)      |
| Cartan modular flow `σ_t`          | 1-dimensional torus orbits              |
| Multi-head attention (finite blks) | Virtual localization (fixed pt graphs)  |
| Langlands adelic dual              | `D`-modules on `Bun_{ᴸG}(C)`           |

The scalar GW invariant `GW(X, α) ∈ ℝ` is the **last step**—the numerical
shadow of the Weyl-graph datum—mirroring how scalar probability is the last
step in §21.  This is the `ScalarProbabilityAsLastStep` principle applied
to Gromov-Witten theory.
-/
def KleinGromovPipelineStatement
    (WeylGroup CoRootLat Vertex GWClass : Type*)
    (Edge        : Vertex → Vertex → Type*)
    (gwInvariant : CoRootLat → GWClass)
    (locShadow   : WeylGraphLocalizationData WeylGroup CoRootLat Vertex Edge → GWClass)
    (toNumerical : GWClass → ℝ) : Prop :=
  KleinGromovAlignmentStatement WeylGroup CoRootLat Vertex GWClass
    Edge gwInvariant locShadow ∧
  ∀ α : CoRootLat, ∃ locData,
    toNumerical (gwInvariant α) = toNumerical (locShadow locData)

end KleinGromovSynthesis

-- ---------------------------------------------------------------------------
-- §24  Gromov homological probability roadmap
--      (momentum-map probability → homological measures → moving-ball
--       configurations → cycle-volume spectra → Weyl gauge of volume)
-- ---------------------------------------------------------------------------

section GromovRoadmap

/-!
## §24  Gromov's homological probability roadmap

Extracted from M. Gromov, "Probability, Symmetry, Linearity" (lecture).

The lecture's hidden spine:
  projective state → momentum map → probability simplex
    → entropy / Fisher geometry → homological measures
    → cycle-space volume filtration → Weyl volume gauge.

**Two key mechanisms:**

1. **Momentum map** (finite / symplectic):
   `μ : ℂPⁿ⁻¹ → Δⁿ⁻¹`, `[z] ↦ (|zᵢ|² / Σ|zⱼ|²)`.
   Classical probability vectors are *images* of projective quantum states
   under the diagonal-torus momentum map.  The entropy `H(p) = -Σ pᵢ log pᵢ`
   and the Fisher metric `gᵢᵢ = 1/pᵢ` are the metric shadows of the round
   sphere geometry hidden inside the simplex.

2. **Weyl gauge of volume** (asymptotic / spectral):
   `N(λ) ~ C_D · Vol(M) · λ^{D/2}` (Laplace Weyl law, 1912);
   `ωₚ(M) ~ a_D · Vol(M)^{(D-1)/D} · p^{1/D}` (cycle *p*-width Weyl law).
   Volume is the leading coefficient of asymptotic homological/spectral growth.

The five witness packets below track the exact chapter structure of the roadmap.
-/

/--
**Packet 24.1 — Momentum-map probability packet.**

The finite-dimensional prototype of homological probability.

Classical probability distributions arise as images of projective states
`[z] ∈ ℂPⁿ⁻¹` under the diagonal-torus momentum map:
  `μ([z]) = (|z₁|²/Σ|zⱼ|², …, |zₙ|²/Σ|zⱼ|²) ∈ Δⁿ⁻¹`.

See §11 for the concrete `momentMap` definition.
The entropy function on the simplex is the metric shadow of round-sphere geometry
via the square-root embedding `pᵢ = xᵢ²` (see §1 `squareRootEmbedding`).
-/
abbrev MomentumMapProbabilityPacket : Type _ :=
  Σ' ProjectiveStateSpace : Type*,
    Σ' ProbabilitySimplex : Type*,
      Σ' momentumMap : ProjectiveStateSpace → ProbabilitySimplex,
        ProbabilitySimplex → ℝ

namespace MomentumMapProbabilityPacket

abbrev ProjectiveStateSpace (P : MomentumMapProbabilityPacket) : Type _ := P.1
abbrev ProbabilitySimplex (P : MomentumMapProbabilityPacket) : Type _ := P.2.1
abbrev momentumMap (P : MomentumMapProbabilityPacket) :
    ProjectiveStateSpace P → ProbabilitySimplex P := P.2.2.1
abbrev entropyFn (P : MomentumMapProbabilityPacket) : ProbabilitySimplex P → ℝ := P.2.2.2

end MomentumMapProbabilityPacket

/--
**Concrete instance — §11 `momentMap` as a momentum-map packet.**

The `momentMap` and `entropyOfSpectrum` of §11 instantiate
`MomentumMapProbabilityPacket` for `n`-outcome quantum systems.
Mechanically verified: no `by rfl`.
-/
def momentumMapPacketFromFinDim (n : ℕ) : MomentumMapProbabilityPacket :=
  ⟨Fin n → ℂ, Fin n → ℝ, momentMap, entropyOfSpectrum⟩

/--
**Packet 24.2 — Homological measure packet.**

Gromov's replacement of numerical probability by cohomological support ideals.

For an observation map `f : StateSpace → ObservableSpace` and event `U ⊆ O`:
  `I(U) = ker(H*(X) → H*(X \ f⁻¹(U)))` (abstract cohomological support ideal).

Monotonicity: `U ⊆ V → I(U) ≤ I(V)` (larger events have larger support).
Cup product: `I(U) * I(V) ≤ I(U ∩ V)` (cup is compatible with intersection).

See §7's `SupportInvariantMeasureLike` for the related Prop-level version.
-/
abbrev HomologicalMeasurePacket : Type _ :=
  Σ' StateSpace : Type*,
    Σ' ObservableSpace : Type*,
      Σ' CohomologyAlgebra : Type*,
        Σ' observableMap : StateSpace → ObservableSpace,
          Σ' supportIdeal : Set ObservableSpace → CohomologyAlgebra,
            Σ' idealLeq : CohomologyAlgebra → CohomologyAlgebra → Prop,
              Σ' idealMul : CohomologyAlgebra → CohomologyAlgebra → CohomologyAlgebra,
                Σ' mono : ∀ U V : Set ObservableSpace,
                  U ⊆ V → idealLeq (supportIdeal U) (supportIdeal V),
                  ∀ U V : Set ObservableSpace,
                    idealLeq (idealMul (supportIdeal U) (supportIdeal V))
                      (supportIdeal (U ∩ V))

namespace HomologicalMeasurePacket

abbrev StateSpace (P : HomologicalMeasurePacket) : Type _ := P.1
abbrev ObservableSpace (P : HomologicalMeasurePacket) : Type _ := P.2.1
abbrev CohomologyAlgebra (P : HomologicalMeasurePacket) : Type _ := P.2.2.1
abbrev observableMap (P : HomologicalMeasurePacket) : StateSpace P → ObservableSpace P := P.2.2.2.1
abbrev supportIdeal (P : HomologicalMeasurePacket) : Set (ObservableSpace P) → CohomologyAlgebra P :=
  P.2.2.2.2.1
abbrev idealLeq (P : HomologicalMeasurePacket) : CohomologyAlgebra P → CohomologyAlgebra P → Prop :=
  P.2.2.2.2.2.1
abbrev idealMul (P : HomologicalMeasurePacket) :
    CohomologyAlgebra P → CohomologyAlgebra P → CohomologyAlgebra P := P.2.2.2.2.2.2.1
abbrev mono (P : HomologicalMeasurePacket) := P.2.2.2.2.2.2.2.1
abbrev cup_intersection (P : HomologicalMeasurePacket) := P.2.2.2.2.2.2.2.2

end HomologicalMeasurePacket

/--
**Packet 24.3 — Moving-ball configuration packet.**

Small balls (radius `ε`) moving in a manifold.  Varying the radius `ε` gives
a filtered space whose homology measures packing / covering complexity.

`configurationSpace ε` is the space of `ParticleNumber` balls with exclusion
radius `ε` in the manifold.  Gromov's key point: the homology of the
configuration space (as a function of `ε`) detects volume constraints on cycles.
-/
abbrev MovingBallConfigurationPacket : Type _ :=
  Σ' Manifold : Type*,
    Σ' ParticleNumber : ℕ,
      Σ' RadiusParameter : Type*,
        Σ' configurationSpace : RadiusParameter → Type*,
          Σ' baseConfigSpace : Type*,
            ∀ ε : RadiusParameter, configurationSpace ε → baseConfigSpace

namespace MovingBallConfigurationPacket

abbrev Manifold (P : MovingBallConfigurationPacket) : Type _ := P.1
abbrev ParticleNumber (P : MovingBallConfigurationPacket) : ℕ := P.2.1
abbrev RadiusParameter (P : MovingBallConfigurationPacket) : Type _ := P.2.2.1
abbrev configurationSpace (P : MovingBallConfigurationPacket) : RadiusParameter P → Type* :=
  P.2.2.2.1
abbrev baseConfigSpace (P : MovingBallConfigurationPacket) : Type _ := P.2.2.2.2.1
abbrev inclusionInBase (P : MovingBallConfigurationPacket) := P.2.2.2.2.2

end MovingBallConfigurationPacket

/--
**Packet 24.4 — Cycle-volume spectrum packet.**

The volume filtration on the space of `k`-cycles `𝒵_k(M)` gives a
homological spectrum:
  `λ(α) = inf { V | α detected in 𝒵_k^{≤V}(M) }`.

For `k = n-1` (hypersurfaces), the sorted spectral values are the *p*-widths
`ωₚ(M)` (Gromov–Guth volume spectrum; Liokumovich–Marques–Neves 2018).

The `spectralVal_eq` field connects to the `spectralValue` definition of §8.
-/
abbrev CycleVolumeSpectrumPacket : Type _ :=
  Σ' Manifold : Type*,
    Σ' HomologyClass : Type*,
      Σ' CycleSpace : Type*,
        Σ' cycleVolume : CycleSpace → ℝ,
          Σ' detected : ℝ → HomologyClass → Prop,
            Σ' spectralVal : HomologyClass → ℝ,
              ∀ α : HomologyClass,
                spectralVal α = sInf { V : ℝ | detected V α }

namespace CycleVolumeSpectrumPacket

abbrev Manifold (P : CycleVolumeSpectrumPacket) : Type _ := P.1
abbrev HomologyClass (P : CycleVolumeSpectrumPacket) : Type _ := P.2.1
abbrev CycleSpace (P : CycleVolumeSpectrumPacket) : Type _ := P.2.2.1
abbrev cycleVolume (P : CycleVolumeSpectrumPacket) : CycleSpace P → ℝ := P.2.2.2.1
abbrev detected (P : CycleVolumeSpectrumPacket) : ℝ → HomologyClass P → Prop := P.2.2.2.2.1
abbrev spectralVal (P : CycleVolumeSpectrumPacket) : HomologyClass P → ℝ := P.2.2.2.2.2.1
abbrev spectralVal_eq (P : CycleVolumeSpectrumPacket) := P.2.2.2.2.2.2

end CycleVolumeSpectrumPacket

/--
**Theorem 24.4a — Cycle-spectrum packet agrees with §8 `spectralValue`.**

The `spectralVal` of a `CycleVolumeSpectrumPacket` equals the `spectralValue`
of §8 (mechanically verified directly from the `spectralVal_eq` axiom).
-/
theorem cycleSpectrumPacket_spectralVal_eq
    (pkt : CycleVolumeSpectrumPacket) (α : pkt.HomologyClass) :
    pkt.spectralVal α = spectralValue pkt.detected α :=
  pkt.spectralVal_eq α

/--
**Packet 24.5 — Weyl volume gauge packet.**

Volume is the leading coefficient of asymptotic spectral / homological growth.

Two Weyl-law instances:
- **Laplace Weyl law**: `N(λ) ~ C_D · Vol(M) · λ^{D/2}` (Weyl 1912).
- ***p*-width Weyl law**: `ωₚ(M) ~ a_D · Vol(M)^{(D-1)/D} · p^{1/D}`
  (Gromov–Guth; Liokumovich–Marques–Neves 2018).

The `weylConstant = C_D` and `pWidthConstant = a_D` are the dimension-dependent
leading coefficients.  Full asymptotic proofs are not formalized here.
-/
structure WeylVolumeGaugePacket where
  /-- The manifold. -/
  Manifold : Type*
  /-- Riemannian dimension `D`. -/
  dimension : ℕ
  /-- Riemannian volume of the manifold. -/
  volume : ℝ
  /-- Laplace eigenvalue sequence: `spectrum k = λ_k`. -/
  spectrum : ℕ → ℝ
  /-- *p*-width sequence: `pWidth p = ωₚ(M)`. -/
  pWidth : ℕ → ℝ
  /-- Weyl constant `C_D > 0` (Laplace Weyl law leading coefficient). -/
  weylConstant : ℝ
  /-- Cycle *p*-width constant `a_D > 0` (volume-spectrum leading coefficient). -/
  pWidthConstant : ℝ

/--
**Owner-level positivity sanity check for the Weyl volume gauge.**

All constants and the volume must be positive for the Weyl law to make sense.

Full asymptotic:
- Laplace: `N(λ) ~ C_D · Vol · λ^{D/2}`
- Cycle widths: `ωₚ ~ a_D · Vol^{(D-1)/D} · p^{1/D}`

The analytic asymptotic proofs require additional imports beyond this surface.
-/
def WeylVolumeIsLeadingCoefficient (pkt : WeylVolumeGaugePacket) : Prop :=
  0 < pkt.weylConstant ∧
  0 < pkt.pWidthConstant ∧
  0 < pkt.volume ∧
  (∀ k : ℕ, 0 ≤ pkt.spectrum k) ∧
  (∀ p : ℕ, 0 ≤ pkt.pWidth p)

/--
**Definition 24.6 — Gromov homological probability roadmap packet.**

Integrates all five geometric mechanisms from the Gromov lecture:

1. **Momentum-map probability** (projective → simplex → entropy / Fisher)
2. **Homological measures** (events → cohomological support ideals)
3. **Moving-ball configuration spaces** (radius filtration → packing)
4. **Cycle-volume spectrum** (volume filtration → homological spectrum)
5. **Weyl volume gauge** (asymptotic spectral growth → volume readout)

## Volume I ↔ Volume II dictionary (Gromov refined)

| Volume I (momentum / finite)       | Volume II (Weyl / asymptotic)                      |
|------------------------------------+----------------------------------------------------|
| Projective state `[z] ∈ ℂPⁿ⁻¹`   | Manifold `M^D`                                     |
| Momentum map `μ`                   | Eigenvalue counting function `N(λ)`                |
| Probability simplex `Δⁿ⁻¹`        | Volume `Vol(M)`                                    |
| Entropy `H = -Σ pᵢ log pᵢ`        | Weyl asymptote `C_D · Vol · λ^{D/2}`              |
| Fisher metric `gᵢᵢ = 1/pᵢ`        | *p*-width `ωₚ ~ a_D · Vol^{(D-1)/D} · p^{1/D}`   |
| Observable event `U`               | Cohomological support ideal `I(U)`                 |
| Moving ball radius `ε`             | Volume filtration threshold `V`                     |
-/
structure GromovHomologicalProbabilityRoadmapPacket where
  /-- Momentum-map probability (finite-dimensional / symplectic prototype). -/
  momentum        : MomentumMapProbabilityPacket
  /-- Homological measure (events → cohomological support ideals). -/
  homologicalMeas : HomologicalMeasurePacket
  /-- Moving-ball configuration space (radius-filtered packing geometry). -/
  movingBalls     : MovingBallConfigurationPacket
  /-- Cycle-volume spectrum (volume filtration → homological spectrum). -/
  cycleSpectrum   : CycleVolumeSpectrumPacket
  /-- Weyl volume gauge (asymptotic spectral growth → volume readout). -/
  weylGauge       : WeylVolumeGaugePacket

/--
**Theorem 24.7 — Roadmap constructor from explicit witnesses.**

Providing explicit sub-packets for all five mechanisms assembles the full
Gromov homological probability roadmap packet.
Mechanically verified: no `by rfl`.
-/
def constructGromovRoadmap
    (m : MomentumMapProbabilityPacket)
    (h : HomologicalMeasurePacket)
    (b : MovingBallConfigurationPacket)
    (c : CycleVolumeSpectrumPacket)
    (w : WeylVolumeGaugePacket) :
    GromovHomologicalProbabilityRoadmapPacket :=
  { momentum        := m
    homologicalMeas := h
    movingBalls     := b
    cycleSpectrum   := c
    weylGauge       := w }

/--
**Theorem 24.8 — Gromov roadmap induces the §12 homological probability pipeline.**

The roadmap packet specializes to a `HomologicalProbabilityPipeline` (§12):
  observable event (Set ObservableSpace)
    → support ideal (CohomologyAlgebra)      [= toConfigSpace]
    → identity filtration                     [= toFiltration = id]
    → homological invariant                   [= toHomInvariant = id]
    → Weyl volume shadow (volume : ℝ).        [= toNumericalShadow]

Mechanically verified: no `by rfl`.
-/
def gromovRoadmapPipeline
    (pkt : GromovHomologicalProbabilityRoadmapPacket) :
    HomologicalProbabilityPipeline
      (Set pkt.homologicalMeas.ObservableSpace)
      pkt.homologicalMeas.CohomologyAlgebra
      pkt.homologicalMeas.CohomologyAlgebra
      pkt.homologicalMeas.CohomologyAlgebra :=
  { toConfigSpace     := pkt.homologicalMeas.supportIdeal
    toFiltration      := id
    toHomInvariant    := id
    toNumericalShadow := fun _ => pkt.weylGauge.volume }

/--
**Definition 24.9 — Momentum-map / homological-measure compatibility.**

The scalar probability obtained via the momentum map equals the shadow
of the cohomological support ideal:
  `probCoord (μ(state)) = shadow (I(stateToEvent(state)))`.

This is the `ScalarProbabilityAsLastStep` principle of §21 instantiated
for Gromov's two-mechanism homological probability:
- The momentum map gives the *event coordinates* (finite / symplectic).
- The Weyl gauge gives their *asymptotic size scale*.
-/
def MomentumMapHomologicalCompatibility
    (momPkt : MomentumMapProbabilityPacket)
    (homPkt : HomologicalMeasurePacket)
    (shadow  : homPkt.CohomologyAlgebra → ℝ)
    (probCoord : momPkt.ProbabilitySimplex → ℝ)
    (stateToEvent : momPkt.ProjectiveStateSpace → Set homPkt.ObservableSpace) :
    Prop :=
  ∀ state : momPkt.ProjectiveStateSpace,
    probCoord (momPkt.momentumMap state) =
      shadow (homPkt.supportIdeal (stateToEvent state))

end GromovRoadmap

-- ---------------------------------------------------------------------------
-- §25  Tomita–Gromov modular thermodynamic bridge
--      classical RN → relative modular operator → Araki entropy → free energy
--      → Weyl volume gauge → homological spectral sectors
-- ---------------------------------------------------------------------------

section ModularThermodynamicBridge

/-!
## §25  Tomita–Gromov modular thermodynamic bridge

**Capstone theorem (Tomita–Takesaki):**
  Modular theory is noncommutative Radon–Nikodym theory.

The relative modular operator `Δ_{ψ|φ}` (or Connes cocycle `[Dψ:Dφ]_t`)
is the correct noncommutative analogue of `dψ/dφ`.  Araki relative entropy
is the von Neumann-algebraic extension of KL divergence.

**Seven-step grand synthesis:**
```
volume              =  positive normal weight / trace / state;
relative volume     =  Radon–Nikodym derivative dψ/dφ;
log relative vol.   =  relative modular Hamiltonian log Δ_{ψ|φ};
expected mod. pot.  =  Araki relative entropy S(ψ|φ);
temp-reg. rel. ent. =  free energy (β⁻¹ D(ρ|σ_β) = F_β(ρ) − F_β(σ_β));
dissipative dyn.    =  free-energy relaxation (GKSL);
homological prob.   =  spectral sectors that scalar thermodynamics integrates out.
```

**Correction on momentum map:** The momentum map `μ : ℂPⁿ⁻¹ → Δⁿ⁻¹` and the
Radon–Nikodym derivative `dψ/dφ` are *not* the same object.  Both are shadow
maps from structured geometry to scalar density data, but the momentum map is a
symplectic/finite-dimensional object while RN is a measure-comparison object.
Compatibility (`§25.7`) is a separate condition.
-/

/--
**Packet 25.1 — Classical Radon–Nikodym layer.**

Three-step classical pattern:
  `dν/dμ`  →  `log(dν/dμ)`  →  `D_KL(ν|μ) = 𝔼_ν[log(dν/dμ)]`.

The logarithm converts multiplicative change-of-measure into additive
thermodynamic potential; entropy / relative entropy are expectations of this
logarithmic potential.
-/
abbrev ClassicalRadonNikodymPacket : Type _ :=
  Σ' StateSpace : Type*,
    Σ' measurableSpace : MeasurableSpace StateSpace,
      Σ' referenceMeasure : @MeasureTheory.Measure StateSpace measurableSpace,
        Σ' targetMeasure : @MeasureTheory.Measure StateSpace measurableSpace,
          Σ' rnDensity : StateSpace → ENNReal,
            Σ' targetMeasure_eq_withDensity :
              targetMeasure = referenceMeasure.withDensity rnDensity,
              Σ' logLikelihood : StateSpace → ℝ,
                Σ' logLikelihood_eq : ∀ x : StateSpace,
                  logLikelihood x = Real.log ((rnDensity x).toReal),
                  Σ' surprisal : StateSpace → ℝ,
                    Σ' surprisal_eq : ∀ x : StateSpace,
                      surprisal x = logLikelihood x,
                      ℝ

namespace ClassicalRadonNikodymPacket

abbrev StateSpace (P : ClassicalRadonNikodymPacket) : Type _ := P.1
abbrev measurableSpace (P : ClassicalRadonNikodymPacket) : MeasurableSpace (StateSpace P) := P.2.1
abbrev referenceMeasure (P : ClassicalRadonNikodymPacket) :
    @MeasureTheory.Measure (StateSpace P) (measurableSpace P) := P.2.2.1
abbrev targetMeasure (P : ClassicalRadonNikodymPacket) :
    @MeasureTheory.Measure (StateSpace P) (measurableSpace P) := P.2.2.2.1
abbrev rnDensity (P : ClassicalRadonNikodymPacket) : StateSpace P → ENNReal := P.2.2.2.2.1
abbrev targetMeasure_eq_withDensity (P : ClassicalRadonNikodymPacket) := P.2.2.2.2.2.1
abbrev logLikelihood (P : ClassicalRadonNikodymPacket) : StateSpace P → ℝ := P.2.2.2.2.2.2.1
abbrev logLikelihood_eq (P : ClassicalRadonNikodymPacket) := P.2.2.2.2.2.2.2.1
abbrev surprisal (P : ClassicalRadonNikodymPacket) : StateSpace P → ℝ := P.2.2.2.2.2.2.2.2.1
abbrev surprisal_eq (P : ClassicalRadonNikodymPacket) := P.2.2.2.2.2.2.2.2.2.1
abbrev klDivergence (P : ClassicalRadonNikodymPacket) : ℝ := P.2.2.2.2.2.2.2.2.2.2

end ClassicalRadonNikodymPacket

/--
**Packet 25.2 — Noncommutative Radon–Nikodym / Tomita–Takesaki layer.**

Theorem-bank safe: packages comparison witnesses rather than asserting
type-isomorphism between modular operators and classical RN densities.

- `Δ_{ψ|φ}` or `[Dψ:Dφ]_t` plays the role of `dψ/dφ`.
- `log Δ_{ψ|φ}` is the relative modular Hamiltonian (= `-log(dφ/dψ)`).
- Expectation of `log Δ_{ψ|φ}` is Araki relative entropy `S(ψ|φ)`.

Connes' and Pedersen–Takesaki-style Radon–Nikodym theorems for weights are
precisely the operator-algebraic framework behind this package.
-/
abbrev ModularRadonNikodymPacket : Type _ :=
  Σ' VonNeumannAlgebra : Type*,
    Σ' ReferenceState : Type*,
      Σ' TargetState : Type*,
        Σ' RelativeModularOperator : Type*,
          Σ' ConnescCocycle : Type*,
            Σ' RelativeModularHamiltonian : Type*,
              Σ' modularNCRadonNikodymWitness :
                RelativeModularOperator → ConnescCocycle → Prop,
                ℝ

namespace ModularRadonNikodymPacket

abbrev VonNeumannAlgebra (P : ModularRadonNikodymPacket) : Type _ := P.1
abbrev ReferenceState (P : ModularRadonNikodymPacket) : Type _ := P.2.1
abbrev TargetState (P : ModularRadonNikodymPacket) : Type _ := P.2.2.1
abbrev RelativeModularOperator (P : ModularRadonNikodymPacket) : Type _ := P.2.2.2.1
abbrev ConnescCocycle (P : ModularRadonNikodymPacket) : Type _ := P.2.2.2.2.1
abbrev RelativeModularHamiltonian (P : ModularRadonNikodymPacket) : Type _ :=
  P.2.2.2.2.2.1
abbrev modularNCRadonNikodymWitness (P : ModularRadonNikodymPacket) :=
  P.2.2.2.2.2.2.1
abbrev arakiRelativeEntropy (P : ModularRadonNikodymPacket) : ℝ := P.2.2.2.2.2.2.2

end ModularRadonNikodymPacket

/--
**Theorem 25.2a — Classical RN packet embeds into the modular RN packet.**

Every classical Radon–Nikodym packet provides a commutative specialization
of the modular RN packet: multiplication by `dν/dμ` is the relative modular
operator, and `log(dν/dμ)` is the modular Hamiltonian in the commutative case.
Mechanically verified: no `by rfl`.
-/
def classicalToModularWitness
    (cl : ClassicalRadonNikodymPacket) : ModularRadonNikodymPacket :=
  ⟨cl.StateSpace → ℝ,
    cl.StateSpace,
    cl.StateSpace,
    cl.StateSpace → ℝ,
    cl.StateSpace → ℝ,
    cl.StateSpace → ℝ,
    (fun relativeOperator cocycle => relativeOperator = cocycle),
    cl.klDivergence⟩

/--
In the commutative specialization, the modular Radon-Nikodym witness is the
actual equality of the multiplication operator readout and the cocycle readout.
-/
theorem classicalToModularWitness_modularNCRadonNikodymWitness_iff
    (cl : ClassicalRadonNikodymPacket)
    (relativeOperator cocycle : cl.StateSpace → ℝ) :
    (classicalToModularWitness cl).modularNCRadonNikodymWitness relativeOperator cocycle
      ↔ relativeOperator = cocycle := by
  rfl

/--
**Packet 25.3 — Gibbs–KMS thermodynamic layer.**

`σ_β = e^{-βH}/Z_β` is the Gibbs/KMS reference state.  The key identity:
  `D(ρ|σ_β) = β · (F_β(ρ) − F_β(σ_β))`.

Equivalently: **free-energy excess = β⁻¹ relative entropy to equilibrium**.

Every faithful normal state is KMS for its own modular automorphism group
(Tomita–Takesaki).  This is the operator-algebraic reason type III probability
is dynamical rather than tracial.
-/
abbrev GibbsKMSPacket : Type _ :=
  Σ' ObservableAlgebra : Type*,
    Σ' HamiltonianSpace : Type*,
      Σ' beta : ℝ,
        Σ' partitionFunction : ℝ,
          Σ' gibbsState : ObservableAlgebra,
            Σ' freeEnergy : ObservableAlgebra → ℝ,
              Σ' relativeEntropyToGibbs : ObservableAlgebra → ℝ,
                ∀ ρ : ObservableAlgebra,
                  relativeEntropyToGibbs ρ =
                    beta * (freeEnergy ρ - freeEnergy gibbsState)

namespace GibbsKMSPacket

abbrev ObservableAlgebra (P : GibbsKMSPacket) : Type _ := P.1
abbrev HamiltonianSpace (P : GibbsKMSPacket) : Type _ := P.2.1
abbrev beta (P : GibbsKMSPacket) : ℝ := P.2.2.1
abbrev partitionFunction (P : GibbsKMSPacket) : ℝ := P.2.2.2.1
abbrev gibbsState (P : GibbsKMSPacket) : ObservableAlgebra P := P.2.2.2.2.1
abbrev freeEnergy (P : GibbsKMSPacket) : ObservableAlgebra P → ℝ := P.2.2.2.2.2.1
abbrev relativeEntropyToGibbs (P : GibbsKMSPacket) : ObservableAlgebra P → ℝ :=
  P.2.2.2.2.2.2.1
abbrev freeEnergyEntropyRelation (P : GibbsKMSPacket) := P.2.2.2.2.2.2.2

end GibbsKMSPacket

namespace GibbsKMSPacket

/--
Owner-target readback for the Gibbs/KMS free-energy identity.

This packages the actual packet theorem as a graph-visible proof surface.
-/
@[owner_target_tag]
theorem freeEnergyEntropyRelation_ownerTarget
    (gk : GibbsKMSPacket) :
    ∀ ρ : gk.ObservableAlgebra,
      gk.relativeEntropyToGibbs ρ =
        gk.beta * (gk.freeEnergy ρ - gk.freeEnergy gk.gibbsState) :=
  gk.freeEnergyEntropyRelation

/--
Free-energy gap nonnegativity from the Gibbs/KMS identity.

In concrete models this is the sink statement of the KL nonnegativity source:
once the relative entropy is nonnegative and `β > 0`, the Gibbs state
minimizes the free energy.
-/
theorem freeEnergy_gap_nonneg_of_relativeEntropy_nonneg
    (gk : GibbsKMSPacket)
    (ρ : gk.ObservableAlgebra)
    (hrel : 0 ≤ gk.relativeEntropyToGibbs ρ)
    (hβ : 0 < gk.beta) :
    0 ≤ gk.freeEnergy ρ - gk.freeEnergy gk.gibbsState := by
  have h := gk.freeEnergyEntropyRelation ρ
  nlinarith

/--
The Gibbs/KMS reference state is a free-energy minimizer whenever the relative
entropy is nonnegative and the inverse temperature is positive.
-/
theorem freeEnergy_ge_gibbs_of_relativeEntropy_nonneg
    (gk : GibbsKMSPacket)
    (ρ : gk.ObservableAlgebra)
    (hrel : 0 ≤ gk.relativeEntropyToGibbs ρ)
    (hβ : 0 < gk.beta) :
    gk.freeEnergy gk.gibbsState ≤ gk.freeEnergy ρ := by
  have hgap :=
    freeEnergy_gap_nonneg_of_relativeEntropy_nonneg gk ρ hrel hβ
  linarith

end GibbsKMSPacket

/--
**Packet 25.4 — GKSL dissipative dynamics layer.**

Lindblad/GKSL generator for quantum Markov semigroups:
  `ℒ(ρ) = -i[H,ρ] + Σ_k (L_k ρ L_k* − ½{L_k*L_k, ρ})`.

Dynamical extension of the modular bridge:
- KMS/Tomita = equilibrium modular geometry (unitary, reversible);
- GKSL       = dissipative dynamics of open quantum systems;
- Relative entropy decay = free-energy dissipation along the semigroup.
-/
abbrev GKSLDissipativeDynamicsPacket : Type _ :=
  Σ' StateSpace : Type*,
    Σ' CoherentHamiltonian : Type*,
      Σ' JumpOperators : Type*,
        Σ' lindbladGenerator : StateSpace → StateSpace,
          Σ' dissipationFunctional : StateSpace → ℝ,
            Σ' equilibriumState : StateSpace,
              ∀ ρ : StateSpace,
                dissipationFunctional (lindbladGenerator ρ) ≤
                  dissipationFunctional ρ

namespace GKSLDissipativeDynamicsPacket

abbrev StateSpace (P : GKSLDissipativeDynamicsPacket) : Type _ := P.1
abbrev CoherentHamiltonian (P : GKSLDissipativeDynamicsPacket) : Type _ := P.2.1
abbrev JumpOperators (P : GKSLDissipativeDynamicsPacket) : Type _ := P.2.2.1
abbrev lindbladGenerator (P : GKSLDissipativeDynamicsPacket) : StateSpace P → StateSpace P :=
  P.2.2.2.1
abbrev dissipationFunctional (P : GKSLDissipativeDynamicsPacket) : StateSpace P → ℝ :=
  P.2.2.2.2.1
abbrev equilibriumState (P : GKSLDissipativeDynamicsPacket) : StateSpace P := P.2.2.2.2.2.1
abbrev entropyDecay (P : GKSLDissipativeDynamicsPacket) := P.2.2.2.2.2.2

end GKSLDissipativeDynamicsPacket

/--
**Definition 25.5 — Modular thermodynamic bridge packet (grand synthesis).**

Integrates all layers of the Tomita–Gromov synthesis.

## Grand dictionary

| Information geometry | Operator algebra | Gromov / homological |
|---|---|---|
| prob. distribution | normal state / weight | homological support |
| reference measure | reference weight/state | reference volume gauge |
| `dP/dQ` | relative modular op. / Connes cocycle | rel. spectral vol. density |
| `−log(dQ/dP)` | relative modular Hamiltonian | energy / volume potential |
| `D_KL(P|Q)` | Araki relative entropy | expected spectral-vol. mismatch |
| Gibbs distribution | KMS state | localized equilibrium sector |
| free energy | β⁻¹ relative entropy to KMS | regularized volume functional |
| partition function | `Tr(e^{-βH})` | Weyl spectral-volume asymptotic |
| signed cancellation | supertrace | supervolume / index |
-/
abbrev ModularThermodynamicBridgePacket : Type _ :=
  Σ' classicalRN : ClassicalRadonNikodymPacket,
    Σ' modularRN : ModularRadonNikodymPacket,
      Σ' gibbsKMS : GibbsKMSPacket,
        Σ' gkslDynamics : GKSLDissipativeDynamicsPacket,
          Σ' gromovRoadmap : GromovHomologicalProbabilityRoadmapPacket,
            Σ' SpectralWeights : Type*,
              Σ' SpectralVolumes : Type*,
                Σ' spectralWeightVolumeComparison :
                  SpectralWeights → SpectralVolumes → Prop,
                  Σ' SuperVolumeWeight : Type*,
                    Type*

namespace ModularThermodynamicBridgePacket

abbrev classicalRN (P : ModularThermodynamicBridgePacket) : ClassicalRadonNikodymPacket := P.1
abbrev modularRN (P : ModularThermodynamicBridgePacket) : ModularRadonNikodymPacket := P.2.1
abbrev gibbsKMS (P : ModularThermodynamicBridgePacket) : GibbsKMSPacket := P.2.2.1
abbrev gkslDynamics (P : ModularThermodynamicBridgePacket) : GKSLDissipativeDynamicsPacket :=
  P.2.2.2.1
abbrev gromovRoadmap (P : ModularThermodynamicBridgePacket) :
    GromovHomologicalProbabilityRoadmapPacket := P.2.2.2.2.1
abbrev SpectralWeights (P : ModularThermodynamicBridgePacket) : Type _ := P.2.2.2.2.2.1
abbrev SpectralVolumes (P : ModularThermodynamicBridgePacket) : Type _ := P.2.2.2.2.2.2.1
abbrev spectralWeightVolumeComparison (P : ModularThermodynamicBridgePacket) :=
  P.2.2.2.2.2.2.2.1
abbrev SuperVolumeWeight (P : ModularThermodynamicBridgePacket) : Type _ :=
  P.2.2.2.2.2.2.2.2.1
abbrev WeylGaugeRecovery (P : ModularThermodynamicBridgePacket) : Type _ :=
  P.2.2.2.2.2.2.2.2.2

end ModularThermodynamicBridgePacket

/--
**Theorem 25.6 — Constructor from explicit layer witnesses.**

Providing all five layers plus spectral comparison data assembles the full
Tomita–Gromov modular thermodynamic bridge packet.
Mechanically verified: no `by rfl`.
-/
def constructModularThermodynamicBridge
    (cl  : ClassicalRadonNikodymPacket)
    (mr  : ModularRadonNikodymPacket)
    (gk  : GibbsKMSPacket)
    (dyn : GKSLDissipativeDynamicsPacket)
    (gr  : GromovHomologicalProbabilityRoadmapPacket)
    (SW  : Type*)
    (SV  : Type*)
    (cmp : SW → SV → Prop)
    (SUV : Type*)
    (WGR : Type*) :
    ModularThermodynamicBridgePacket :=
  ⟨cl, mr, gk, dyn, gr, SW, SV, cmp, SUV, WGR⟩

/--
**Definition 25.7 — Momentum-map / Radon–Nikodym compatibility condition.**

**Correction**: The momentum map `μ : ℂPⁿ⁻¹ → Δⁿ⁻¹` and the Radon–Nikodym
derivative `dψ/dφ` are NOT the same object:
- Momentum map: projective state space → probability simplex (symplectic shadow).
- Radon–Nikodym: comparison between two measures or states (relative density).

Both are shadow maps from structured geometry to scalar density data, but
they are distinct constructions.  Compatibility holds when the probability
coordinate extracted by the momentum map equals the scalar shadow of the
relative modular operator — this is a *condition*, not an identity.

Cf. §24 `MomentumMapHomologicalCompatibility` for the homological version.
-/
def MomentumMapModularCompatibility
    (bridge : ModularThermodynamicBridgePacket)
    (probCoord    : bridge.gromovRoadmap.momentum.ProbabilitySimplex → ℝ)
    (modularShadow : bridge.modularRN.RelativeModularOperator → ℝ)
    (stateToModular :
      bridge.gromovRoadmap.momentum.ProjectiveStateSpace →
      bridge.modularRN.RelativeModularOperator) :
    Prop :=
  ∀ state : bridge.gromovRoadmap.momentum.ProjectiveStateSpace,
    probCoord (bridge.gromovRoadmap.momentum.momentumMap state) =
      modularShadow (stateToModular state)

/--
**Definition 25.8 — Grand capstone coherence conditions.**

Owner-level sanity checks encoding the seven-step synthesis:
```
volume             = positive normal weight;
relative volume    = Radon–Nikodym derivative;
log relative vol.  = modular potential;
expected mod. pot. = relative entropy;
temp-reg. rel. ent = free energy;
dissipative dyn.   = free-energy relaxation;
homological prob.  = spectral sectors scalar thermodynamics integrates out.
```
-/
def GrandCapstoneSlogans
    (bridge : ModularThermodynamicBridgePacket) : Prop :=
  -- Inverse temperature is nonzero (thermal).
  bridge.gibbsKMS.beta ≠ 0 ∧
  -- Partition function is positive.
  0 < bridge.gibbsKMS.partitionFunction ∧
  -- Dissipative flow is non-increasing on the free-energy functional.
  (∀ ρ : bridge.gkslDynamics.StateSpace,
    bridge.gkslDynamics.dissipationFunctional
      (bridge.gkslDynamics.lindbladGenerator ρ) ≤
    bridge.gkslDynamics.dissipationFunctional ρ) ∧
  -- Araki relative entropy is the operator-algebraic extension of KL divergence.
  bridge.modularRN.arakiRelativeEntropy = bridge.classicalRN.klDivergence

/--
**Theorem 25.9 — Slogans hold for the bridge constructor output.**

The constructor `constructModularThermodynamicBridge` produces a packet
satisfying `GrandCapstoneSlogans` when supplied with matching classical RN and
modular RN packets (same `klDivergence = arakiRelativeEntropy`) and a
positive-temperature Gibbs packet with non-increasing dissipation.
Mechanically verified: no `by rfl`.
-/
theorem constructBridge_slogans
    (cl  : ClassicalRadonNikodymPacket)
    (mr  : ModularRadonNikodymPacket)
    (gk  : GibbsKMSPacket)
    (dyn : GKSLDissipativeDynamicsPacket)
    (gr  : GromovHomologicalProbabilityRoadmapPacket)
    (SW SV SUV WGR : Type*)
    (cmp : SW → SV → Prop)
    (hbeta : gk.beta ≠ 0)
    (hpart : 0 < gk.partitionFunction)
    (hdiss : ∀ ρ : dyn.StateSpace,
      dyn.dissipationFunctional (dyn.lindbladGenerator ρ) ≤
      dyn.dissipationFunctional ρ)
    (hentropy : mr.arakiRelativeEntropy = cl.klDivergence) :
    GrandCapstoneSlogans
      (constructModularThermodynamicBridge cl mr gk dyn gr SW SV cmp SUV WGR) :=
  ⟨hbeta, hpart, hdiss, hentropy⟩

end ModularThermodynamicBridge

-- ---------------------------------------------------------------------------
-- §26  Modular volume potentials bridge
--      (state = e^{-potential} × volume; spectral volume vs weight;
--       Weyl/KMS synthesis; supertrace/supervolume; capstone slogans)
-- ---------------------------------------------------------------------------

section ModularVolumeBridge

/-!
## §26  Modular volume potentials bridge

**Theorem-safe capstone (corrected):**
  Tomita–Takesaki modular theory is noncommutative logarithmic Radon–Nikodym
  theory *without a trace*.

The precise replacements are:
  `dψ/dφ` ⤳ relative modular operator `Δ_{ψ|φ}` or Connes cocycle `[Dψ:Dφ]_t`;
  `-log(dφ/dψ)` ⤳ relative modular Hamiltonian;
  `D_KL` ⤳ Araki relative entropy.

**Seven-slogan capstone:**
1. A state is volume × exponential logarithmic potential: `dμ = e^{-Φ} dν`.
2. Relative entropy = expected relative log RN derivative: `D_KL = 𝔼_μ[log(dμ/dν)]`.
3. Free energy = temperature-scaled relative entropy to KMS equilibrium.
4. Tomita–Takesaki = noncommutative log RN theory (no trace needed in type III).
5. Araki relative entropy = noncommutative KL divergence.
6. Weyl volume = asymptotic spectral volume (density-of-states leading coefficient).
7. KMS thermodynamics = Boltzmann weighting of spectral volume by modular potential.

**Correction:** `D_KL` ≠ Gromov–Hausdorff distance.
- KL/Araki: divergence *between states/weights* on the same algebra.
- Quantum GH distance: metric *between quantum metric spaces* (Rieffel 2000).
  They can interact in a broader variational framework but are distinct objects.

**Correction on spectral volume vs spectral weight:**
  `v_i = τ(P_i)` (tracial/geometric volume of sector `i`) ≠
  `w_i(β) = v_i e^{-βE_i} / Z_β` (Boltzmann-tilted probability weight).
  The mismatch `-log w_i = βE_i - log v_i + log Z_β` is the logarithmic
  Radon–Nikodym potential between them.
-/

/--
**Packet 26.1 — Spectral volume and spectral weight bridge.**

Spectral volume = density of states `{v_i}` (geometric degeneracy / tracial charge).
Spectral weight = Boltzmann tilt of spectral volume: `w_i(β) = v_i e^{-βE_i}/Z_β`.

Logarithmic RN potential between them:
  `-log w_i = βE_i - log v_i + log Z_β`.
The term `-log v_i` is the entropic volume correction.

Weyl laws recover `Vol(M)` from asymptotics of the density of states:
  `N(λ) ~ C_D · Vol(M) · λ^{D/2}` (Laplace Weyl law);
  `ω_p(M) ~ a_D · Vol(M)^{(D-1)/D} · p^{1/D}` (Liokumovich–Marques–Neves 2018).
-/
abbrev SpectralVolumeWeightPacket : Type _ :=
  Σ' n : ℕ,
    Σ' energyLevel : Fin n → ℝ,
      Σ' spectralVolume : Fin n → ℝ,
        Σ' beta : ℝ,
          Σ' partitionFunction : ℝ,
            Σ' boltzmannWeight : Fin n → ℝ,
              Σ' spectralVolume_nonneg : ∀ i : Fin n, 0 ≤ spectralVolume i,
                Σ' partitionFunction_pos : 0 < partitionFunction,
                  ∀ i : Fin n,
                    boltzmannWeight i =
                      spectralVolume i * Real.exp (-(beta * energyLevel i)) /
                        partitionFunction

namespace SpectralVolumeWeightPacket

abbrev n (P : SpectralVolumeWeightPacket) : ℕ := P.1
abbrev energyLevel (P : SpectralVolumeWeightPacket) : Fin P.n → ℝ := P.2.1
abbrev spectralVolume (P : SpectralVolumeWeightPacket) : Fin P.n → ℝ := P.2.2.1
abbrev beta (P : SpectralVolumeWeightPacket) : ℝ := P.2.2.2.1
abbrev partitionFunction (P : SpectralVolumeWeightPacket) : ℝ := P.2.2.2.2.1
abbrev boltzmannWeight (P : SpectralVolumeWeightPacket) : Fin P.n → ℝ := P.2.2.2.2.2.1
abbrev spectralVolume_nonneg (P : SpectralVolumeWeightPacket) := P.2.2.2.2.2.2.1
abbrev partitionFunction_pos (P : SpectralVolumeWeightPacket) := P.2.2.2.2.2.2.2.1
abbrev boltzmannWeight_eq (P : SpectralVolumeWeightPacket) := P.2.2.2.2.2.2.2.2

end SpectralVolumeWeightPacket

/--
**Theorem 26.1a — Spectral weight is Boltzmann-tilted spectral volume.**

The Boltzmann weight `w_i(β) = v_i e^{-βE_i}/Z_β` by the packet axiom.
Mechanically verified: no `by rfl`.
-/
theorem spectralWeight_is_boltzmannTilt
    (pkt : SpectralVolumeWeightPacket) (i : Fin pkt.n) :
    pkt.boltzmannWeight i =
      pkt.spectralVolume i * Real.exp (-(pkt.beta * pkt.energyLevel i)) /
      pkt.partitionFunction :=
  pkt.boltzmannWeight_eq i

/--
**Packet 26.2 — Supertrace / supervolume packet.**

In supergeometry, volume is replaced by a Berezinian or supervolume:
  `Str(A) = Tr(A_even) - Tr(A_odd)`.
The superpartition function is `Z_super(β) = Str(e^{-βH})`.

Arithmetic prime-gas example (Spector):
  `Str(e^{-sH_F}) = Σ_{n≥1} μ(n)/n^s = 1/ζ(s)`.

**Precision:** A supertrace is NOT a positive measure.  It is a signed/graded
index-type functional.  Positivity must be recovered by restricting to an even
sector, choosing a physical state, or passing to a Hilbert/Krein realization.
-/
abbrev SupertraceSupervolumePacket : Type _ :=
  Σ' GradedSpace : Type*,
    Σ' evenTrace : GradedSpace → ℝ,
      Σ' oddTrace : GradedSpace → ℝ,
        Σ' superTrace : GradedSpace → ℝ,
          Σ' superTrace_eq : ∀ a : GradedSpace,
            superTrace a = evenTrace a - oddTrace a,
            Σ' GradedHamiltonianType : Type*,
              ℝ

namespace SupertraceSupervolumePacket

abbrev GradedSpace (P : SupertraceSupervolumePacket) : Type _ := P.1
abbrev evenTrace (P : SupertraceSupervolumePacket) : GradedSpace P → ℝ := P.2.1
abbrev oddTrace (P : SupertraceSupervolumePacket) : GradedSpace P → ℝ := P.2.2.1
abbrev superTrace (P : SupertraceSupervolumePacket) : GradedSpace P → ℝ := P.2.2.2.1
abbrev superTrace_eq (P : SupertraceSupervolumePacket) := P.2.2.2.2.1
abbrev GradedHamiltonianType (P : SupertraceSupervolumePacket) : Type _ := P.2.2.2.2.2.1
abbrev superPartitionFunction (P : SupertraceSupervolumePacket) : ℝ := P.2.2.2.2.2.2

end SupertraceSupervolumePacket

/--
**Theorem 26.2a — Supertrace axiom stated cleanly.**

The supertrace is the even-minus-odd difference by axiom.
Mechanically verified: no `by rfl`.
-/
theorem supertrace_eq_even_minus_odd
    (pkt : SupertraceSupervolumePacket) (a : pkt.GradedSpace) :
    pkt.superTrace a = pkt.evenTrace a - pkt.oddTrace a :=
  pkt.superTrace_eq a

/--
**Packet 26.3 — Modular volume bridge packet (grand synthesis hub).**

Thin witness hub collecting comparison data between:
- Classical logarithmic measure model (log RN density, KL divergence);
- Von Neumann modular model (relative modular operator, Araki entropy);
- Spectral/Weyl geometry (density of states, asymptotic volume).

**Theorem-safe doctrine:**
- `modularData` is not literally isomorphic to `classicalLogPotential`.
  `entropyComparison` records the commutative/semifinite reduction in which they agree.
- `D_KL` (≡ `klDivergenceData`) is not the same object as GH distance.
  See `KLDivergenceDistinctFromGromovHausdorff` below.
-/
abbrev ModularVolumeBridgePacket : Type _ :=
  Σ' ClassicalMeasureSpace : Type*,
    Σ' VonNeumannSystem : Type*,
      Σ' SpectralGeometry : Type*,
        Σ' classicalVolume : Type*,
          Σ' classicalState : Type*,
            Σ' classicalLogPotential : Type*,
              Σ' modularWeight : Type*,
                Σ' modularData : Type*,
                  Σ' modularHamiltonian : Type*,
                    Σ' klDivergenceData : Type*,
                      Σ' arakiRelativeEntropyData : Type*,
                        Σ' freeEnergyData : Type*,
                          Σ' spectralVolumeData : Type*,
                            Σ' weylVolumeGaugeData : Type*,
                              Σ' entropyComparison : Type*,
                                Σ' freeEnergyComparison : Type*,
                                  Type*

namespace ModularVolumeBridgePacket

abbrev tail₁ (P : ModularVolumeBridgePacket) := P.2
abbrev tail₂ (P : ModularVolumeBridgePacket) := (tail₁ P).2
abbrev tail₃ (P : ModularVolumeBridgePacket) := (tail₂ P).2
abbrev tail₄ (P : ModularVolumeBridgePacket) := (tail₃ P).2
abbrev tail₅ (P : ModularVolumeBridgePacket) := (tail₄ P).2
abbrev tail₆ (P : ModularVolumeBridgePacket) := (tail₅ P).2
abbrev tail₇ (P : ModularVolumeBridgePacket) := (tail₆ P).2
abbrev tail₈ (P : ModularVolumeBridgePacket) := (tail₇ P).2
abbrev tail₉ (P : ModularVolumeBridgePacket) := (tail₈ P).2
abbrev tail₁₀ (P : ModularVolumeBridgePacket) := (tail₉ P).2
abbrev tail₁₁ (P : ModularVolumeBridgePacket) := (tail₁₀ P).2
abbrev tail₁₂ (P : ModularVolumeBridgePacket) := (tail₁₁ P).2
abbrev tail₁₃ (P : ModularVolumeBridgePacket) := (tail₁₂ P).2
abbrev tail₁₄ (P : ModularVolumeBridgePacket) := (tail₁₃ P).2
abbrev tail₁₅ (P : ModularVolumeBridgePacket) := (tail₁₄ P).2
abbrev tail₁₆ (P : ModularVolumeBridgePacket) := (tail₁₅ P).2

abbrev ClassicalMeasureSpace (P : ModularVolumeBridgePacket) : Type _ := P.1
abbrev VonNeumannSystem (P : ModularVolumeBridgePacket) : Type _ := (tail₁ P).1
abbrev SpectralGeometry (P : ModularVolumeBridgePacket) : Type _ := (tail₂ P).1
abbrev classicalVolume (P : ModularVolumeBridgePacket) : Type _ := (tail₃ P).1
abbrev classicalState (P : ModularVolumeBridgePacket) : Type _ := (tail₄ P).1
abbrev classicalLogPotential (P : ModularVolumeBridgePacket) : Type _ := (tail₅ P).1
abbrev modularWeight (P : ModularVolumeBridgePacket) : Type _ := (tail₆ P).1
abbrev modularData (P : ModularVolumeBridgePacket) : Type _ := (tail₇ P).1
abbrev modularHamiltonian (P : ModularVolumeBridgePacket) : Type _ := (tail₈ P).1
abbrev klDivergenceData (P : ModularVolumeBridgePacket) : Type _ := (tail₉ P).1
abbrev arakiRelativeEntropyData (P : ModularVolumeBridgePacket) : Type _ := (tail₁₀ P).1
abbrev freeEnergyData (P : ModularVolumeBridgePacket) : Type _ := (tail₁₁ P).1
abbrev spectralVolumeData (P : ModularVolumeBridgePacket) : Type _ := (tail₁₂ P).1
abbrev weylVolumeGaugeData (P : ModularVolumeBridgePacket) : Type _ := (tail₁₃ P).1
abbrev entropyComparison (P : ModularVolumeBridgePacket) : Type _ := (tail₁₄ P).1
abbrev freeEnergyComparison (P : ModularVolumeBridgePacket) : Type _ := (tail₁₅ P).1
abbrev spectralVolumeComparison (P : ModularVolumeBridgePacket) : Type _ := tail₁₆ P

end ModularVolumeBridgePacket

/--
**Theorem 26.4 — Constructor for the modular volume bridge packet.**

Providing explicit type witnesses for all seventeen fields assembles the hub.
Mechanically verified: no `by rfl`.
-/
def constructModularVolumeBridgePacket
    (CMS VNS SG CV CS LP MW MD MH KL AR FE SV WG EC FC SC : Type*) :
    ModularVolumeBridgePacket :=
  ⟨CMS, VNS, SG, CV, CS, LP, MW, MD, MH, KL, AR, FE, SV, WG, EC, FC, SC⟩

/--
**Definition 26.6 — Grand modular volume bridge capstone slogans.**

Owner-level encoding of the seven-step synthesis:
1. (Structural) State = volume × exponential potential (`dμ = e^{-Φ} dν`).
2. (Structural) `D_KL = 𝔼_μ[log(dμ/dν)]` (expectation of log-RN derivative).
3. **(Checkable)** Free energy is β⁻¹ relative entropy to KMS equilibrium.
4. (Structural) Tomita–Takesaki = noncommutative log-RN theory (no trace).
5. (Structural) Araki relative entropy = noncommutative KL divergence.
6. **(Checkable)** Spectral weights are Boltzmann-tilted spectral volumes.
7. **(Checkable)** Partition function and spectral volumes are positive/non-negative.

Conditions 3, 6, 7 are mechanically checkable from the packet axioms.
Conditions 1, 2, 4, 5 are encoded in the packet structure and docstrings.
-/
def ModularVolumeBridgeCapstoneSlogans
    (svw : SpectralVolumeWeightPacket)
    (gk  : GibbsKMSPacket) : Prop :=
  -- (3) Free-energy relation: D(ρ|σ_β) = β (F_β(ρ) - F_β(σ_β)).
  (∀ ρ : gk.ObservableAlgebra,
    gk.relativeEntropyToGibbs ρ =
      gk.beta * (gk.freeEnergy ρ - gk.freeEnergy gk.gibbsState)) ∧
  -- (6) Boltzmann tilt: w_i = v_i e^{-βE_i}/Z_β.
  (∀ i : Fin svw.n,
    svw.boltzmannWeight i =
      svw.spectralVolume i * Real.exp (-(svw.beta * svw.energyLevel i)) /
      svw.partitionFunction) ∧
  -- (7a) Thermal consistency: partition function > 0.
  0 < svw.partitionFunction ∧
  -- (7b) Spectral volumes ≥ 0.
  (∀ i : Fin svw.n, 0 ≤ svw.spectralVolume i)

/--
**Theorem 26.7 — Capstone slogans hold for compliant packets.**

Given well-formed `SpectralVolumeWeightPacket` and `GibbsKMSPacket` (each
satisfying their internal axioms), all checkable slogans hold.
Mechanically verified: no `by rfl`.
-/
theorem modularVolumeBridgeSlogans_hold
    (svw : SpectralVolumeWeightPacket)
    (gk  : GibbsKMSPacket) :
    ModularVolumeBridgeCapstoneSlogans svw gk :=
  ⟨gk.freeEnergyEntropyRelation,
   svw.boltzmannWeight_eq,
   svw.partitionFunction_pos,
   svw.spectralVolume_nonneg⟩

/--
**Theorem 26.8 — §25 `ClassicalRadonNikodymPacket` specializes to §26 hub.**

The classical RN packet of §25 provides explicit data for the classical layers
of the `ModularVolumeBridgePacket`: log potential, KL divergence, and state/volume.
Mechanically verified: no `by rfl`.
-/
def classicalRNToVolumeBridgeHub
    (cl : ClassicalRadonNikodymPacket) : ModularVolumeBridgePacket :=
  constructModularVolumeBridgePacket
    -- ClassicalMeasureSpace, VonNeumannSystem, SpectralGeometry
    cl.StateSpace cl.StateSpace cl.StateSpace
    -- classicalVolume, classicalState, classicalLogPotential
    cl.StateSpace cl.StateSpace (cl.StateSpace → ℝ)
    -- modularWeight, modularData, modularHamiltonian
    (cl.StateSpace → ℝ) (cl.StateSpace → ℝ) (cl.StateSpace → ℝ)
    -- klDivergenceData, arakiRelativeEntropyData
    ℝ ℝ
    -- freeEnergyData, spectralVolumeData, weylVolumeGaugeData
    ℝ ℝ ℝ
    -- entropyComparison, freeEnergyComparison, spectralVolumeComparison
    ℝ ℝ ℝ

end ModularVolumeBridge

-- ---------------------------------------------------------------------------
-- §27  Spectral thermal normalization
--      (Z_β = Boltzmann normalization of spectral volume;
--       log-RN potential = βE + log Z_β; free-energy identity; Weyl gauge;
--       type III caveat; extended modular bridge packet)
-- ---------------------------------------------------------------------------


section SpectralThermalNormalization

/-!
## §27 Spectral thermal normalization

The former packet stored analytic claims as `Type*` witnesses.  The native
operator-first owner is `Canonical.SouriauOperatorialLogPotential`, whose
`SouriauLieThermoData` carries the moment map, geometric inverse temperature,
pairing, positive partition function, and statewise Gibbs log generator.
-/

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

abbrev SpectralThermalNormalizationData (State LieAlgebra LieDual : Type*) :=
  SouriauLieThermoData State LieAlgebra LieDual

theorem boltzmannPotential_is_beta_times_energy
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual)
    (e : State) :
    D.K_beta e = D.pairing (D.momentMap e) D.beta :=
  D.K_beta_eq_pairing e

theorem spectralThermalNormalization_partition_pos
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual) :
    0 < D.partitionFunction :=
  D.partitionFunction_pos

theorem logRN_potential_form
    (pkt : SpectralVolumeWeightPacket)
    (hv : ∀ i : Fin pkt.n, pkt.spectralVolume i = 1)
    (i : Fin pkt.n) :
    pkt.boltzmannWeight i * pkt.partitionFunction =
      Real.exp (-(pkt.beta * pkt.energyLevel i)) := by
  have h := pkt.boltzmannWeight_eq i
  change pkt.boltzmannWeight i =
    pkt.spectralVolume i * Real.exp (-(pkt.beta * pkt.energyLevel i)) /
      pkt.partitionFunction at h
  rw [hv i, one_mul] at h
  rw [h]
  field_simp [ne_of_gt pkt.partitionFunction_pos]

theorem spectralThermalNormalization_statewise_log_generator
    {State LieAlgebra LieDual : Type*}
    (D : SpectralThermalNormalizationData State LieAlgebra LieDual)
    (e : State) :
    D.K_beta e = -Real.log (D.gibbsDensity e) - D.partitionPotential :=
  D.modularHamiltonian_statewise_neg_log_gibbs_sub_PartitionPotential e

end SpectralThermalNormalization

end InfoGeometry.Probability.Homological
