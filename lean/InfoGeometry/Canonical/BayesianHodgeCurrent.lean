import InfoGeometry.Canonical.MaximumCaliberKLSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.DiscreteHodgeStabilizer

/-!
# Bayesian Hodge Current

Finite theorem layer connecting Bayesian/MaxCal current readbacks to the
degree-one discrete Hodge stabilizer decomposition.

The edge-current space is the finite cochain space `Fin n₁ → ℝ`.  Exact
currents model gradient/detailed-balance data, coexact currents model
loop-current/entropy data, and harmonic currents model the protected kernel of
the degree-one Hodge Hamiltonian.

#### BUCKET 1: CLOSED FINITE THEOREMS
Exact currents are closed under the explicit cochain-complex premise.  Coexact
currents are coclosed under the explicit adjoint-complex premise.  Harmonic
currents are exactly the kernel of the stabilizer/Hodge Hamiltonian and are
orthogonal to exact and coexact local current sectors.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
Bayesian update, MaxCal calibration, KMS stationarity, and entropy-current
interpretations enter only through named finite hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  Analytic m-projection existence, quantum Markov semigroup generation,
KMS uniqueness, and continuum Hodge decomposition are intentionally outside
this finite file.
-/

open Matrix

namespace InfoGeometry.Canonical.BayesianHodgeCurrent

open MaximumCaliberKLSplit
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Topology.DiscreteHodgeStabilizer

noncomputable section

variable {n0 n1 n2 : ℕ}

/-- A finite Bayesian/MaxCal edge current is a degree-one real cochain. -/
abbrev EdgeCurrent (n1 : ℕ) := Fin n1 → ℝ

/-- A Bayesian update operator on finite edge currents. -/
abbrev CurrentUpdate (n1 : ℕ) := EdgeCurrent n1 → EdgeCurrent n1

/-- Exact currents: gradient/detailed-balance sector. -/
def IsDetailedBalanceCurrent
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (j : EdgeCurrent n1) : Prop :=
  IsExactOneForm d0 j

/-- Coexact currents: loop-current / entropy-production sector. -/
def IsEntropyLoopCurrent
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (j : EdgeCurrent n1) : Prop :=
  IsCoexactOneForm d1 j

/-- Harmonic currents: protected topological sector. -/
def IsProtectedHarmonicCurrent
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (j : EdgeCurrent n1) : Prop :=
  IsHarmonicCodeState d0 d1 j

/--
Finite Bayesian projection readback: the update sends a prior current to a
posterior current satisfying a named constraint.
-/
def BayesianProjectionReadout
    (T : CurrentUpdate n1)
    (constraint : EdgeCurrent n1 → Prop)
    (prior posterior : EdgeCurrent n1) : Prop :=
  T prior = posterior ∧ constraint posterior

/-- Exact/detailed-balance currents have zero discrete curl when `d₁ d₀ = 0`. -/
theorem detailedBalanceCurrent_closed
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    {j : EdgeCurrent n1}
    (hj : IsDetailedBalanceCurrent d0 j) :
    d1.mulVec j = 0 := by
  rcases hj with ⟨φ, hφ⟩
  rw [← hφ]
  have hmat : (d1 * d0).mulVec φ = 0 := by
    rw [hComplex]
    simp
  simpa [Matrix.mulVec_mulVec] using hmat

/-- Coexact/loop currents are coclosed under the explicit adjoint-complex premise. -/
theorem entropyLoopCurrent_coclosed
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hAdjoint : d0.transpose * d1.transpose = 0)
    {j : EdgeCurrent n1}
    (hj : IsEntropyLoopCurrent d1 j) :
    d0.transpose.mulVec j = 0 := by
  rcases hj with ⟨ψ, hψ⟩
  rw [← hψ]
  have hmat : (d0.transpose * d1.transpose).mulVec ψ = 0 := by
    rw [hAdjoint]
    simp
  simpa [Matrix.mulVec_mulVec] using hmat

/-- Protected harmonic currents are exactly the kernel of the Hodge stabilizer Hamiltonian. -/
theorem protectedHarmonicCurrent_iff_hamiltonian_kernel
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (j : EdgeCurrent n1) :
    IsProtectedHarmonicCurrent d0 d1 j ↔
      (stabilizerHamiltonian1 d0 d1).mulVec j = 0 :=
  harmonic_iff_stabilizerHamiltonian1_kernel d0 d1 j

/-- A harmonic current is closed and coclosed. -/
theorem protectedHarmonicCurrent_closed_coclosed
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {j : EdgeCurrent n1}
    (hj : IsProtectedHarmonicCurrent d0 d1 j) :
    d1.mulVec j = 0 ∧ d0.transpose.mulVec j = 0 :=
  harmonicCodeState_annihilated_by_stabilizers d0 d1 hj

/-- Detailed-balance and entropy-loop sectors are orthogonal in a cochain complex. -/
theorem detailedBalance_orthogonal_entropyLoop
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    {jDB jLoop : EdgeCurrent n1}
    (hDB : IsDetailedBalanceCurrent d0 jDB)
    (hLoop : IsEntropyLoopCurrent d1 jLoop) :
    eckmannDot jDB jLoop = 0 :=
  exact_orthogonal_coexact d0 d1 hComplex hDB hLoop

/-- Protected harmonic currents are orthogonal to detailed-balance currents. -/
theorem protected_orthogonal_detailedBalance
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {j h : EdgeCurrent n1}
    (hh : IsProtectedHarmonicCurrent d0 d1 h)
    (hj : IsDetailedBalanceCurrent d0 j) :
    eckmannDot h j = 0 :=
  harmonic_orthogonal_exact d0 d1 hh hj

/-- Protected harmonic currents are orthogonal to entropy-loop currents. -/
theorem protected_orthogonal_entropyLoop
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {j h : EdgeCurrent n1}
    (hh : IsProtectedHarmonicCurrent d0 d1 h)
    (hj : IsEntropyLoopCurrent d1 j) :
    eckmannDot h j = 0 :=
  harmonic_orthogonal_coexact d0 d1 hh hj

/--
If a Bayesian update selects the protected harmonic sector, its posterior is
orthogonal to both local current sectors.
-/
theorem bayesianProjection_to_harmonic_protected
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior jDB jLoop : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hDB : IsDetailedBalanceCurrent d0 jDB)
    (hLoop : IsEntropyLoopCurrent d1 jLoop) :
    T prior = posterior ∧
      eckmannDot posterior jDB = 0 ∧ eckmannDot posterior jLoop = 0 :=
  ⟨hproj.1,
    protected_orthogonal_detailedBalance d0 d1 hproj.2 hDB,
    protected_orthogonal_entropyLoop d0 d1 hproj.2 hLoop⟩

/-- MaxCal zero log-ratio reads as detailed balance for equal path constraints. -/
theorem maxCal_zero_logRatio_of_equal_path_constraints
    (lambda c : ℝ) :
    maxCalLogRatio lambda c c = 0 :=
  maxCalLogRatio_eq_zero_of_equal_constraints lambda c

/--
If the antisymmetric MaxCal current is calibrated to an entropy-loop current
amplitude, then the supplied amplitude changes sign under path reversal.
-/
theorem entropyLoopAmplitude_swap
    (lambda forward backward : ℝ) :
    maxCalLogRatio lambda backward forward =
      - maxCalLogRatio lambda forward backward :=
  maxCalLogRatio_swap lambda forward backward

end

end InfoGeometry.Canonical.BayesianHodgeCurrent
