import InfoGeometry.Canonical.BayesianHodgeCurrent

/-!
# Bayesian Hodge Stabilizer Bridge

Theorem-safe readback from a finite Bayesian current update into the discrete
Hodge stabilizer code layer.

#### BUCKET 1: CLOSED FINITE THEOREMS
If a finite Bayesian current update selects the harmonic/Hodge kernel, then
the selected current is closed, coclosed, lies in the stabilizer Hamiltonian
kernel, and is orthogonal to exact and coexact local error sectors.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The Bayesian update itself, the selected posterior, and the local error-sector
memberships are explicit hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  This file does not assert analytic KMS uniqueness, continuum Markov
semigroups, or existence of information-geometric projections.
-/

open Matrix

namespace InfoGeometry.Canonical.BayesianHodgeStabilizerBridge

open InfoGeometry.Canonical.BayesianHodgeCurrent
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Topology.DiscreteHodgeStabilizer

noncomputable section

variable {n0 n1 n2 : ℕ}

/--
Finite bridge theorem: a Bayesian update whose posterior is a protected
harmonic Hodge current lands in the stabilizer kernel and is orthogonal to the
local exact/coexact error sectors.
-/
theorem bayesian_harmonic_stabilizer_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    T prior = posterior ∧
      (stabilizerHamiltonian1 d0 d1).mulVec posterior = 0 ∧
      d1.mulVec posterior = 0 ∧
      d0.transpose.mulVec posterior = 0 ∧
      eckmannDot posterior exactErr = 0 ∧
      eckmannDot posterior coexactErr = 0 := by
  have hkernel :
      (stabilizerHamiltonian1 d0 d1).mulVec posterior = 0 :=
    (protectedHarmonicCurrent_iff_hamiltonian_kernel d0 d1 posterior).mp hproj.2
  have hchecks :
      d1.mulVec posterior = 0 ∧ d0.transpose.mulVec posterior = 0 :=
    protectedHarmonicCurrent_closed_coclosed d0 d1 hproj.2
  have horth :
      eckmannDot posterior exactErr = 0 ∧
        eckmannDot posterior coexactErr = 0 :=
    hodge_orthogonal_protection d0 d1 hproj.2 hexact hcoexact
  exact ⟨hproj.1, hkernel, hchecks.1, hchecks.2, horth.1, horth.2⟩

/-- The Bayesian update component of the stabilizer bridge is explicit. -/
theorem bayesian_update_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    T prior = posterior :=
  (bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact).1

/-- The stabilizer-kernel component of the bridge is explicit. -/
theorem stabilizer_kernel_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    (stabilizerHamiltonian1 d0 d1).mulVec posterior = 0 :=
  (bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact).2.1

/-- The closedness component of the bridge is explicit. -/
theorem closed_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    d1.mulVec posterior = 0 :=
  (bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact).2.2.1

/-- The coclosedness component of the bridge is explicit. -/
theorem coclosed_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    d0.transpose.mulVec posterior = 0 :=
  (bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact).2.2.2.1

/-- Orthogonality to the exact error sector is explicit. -/
theorem exact_orthogonal_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    eckmannDot posterior exactErr = 0 :=
  (bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact).2.2.2.2.1

/-- Orthogonality to the coexact error sector is explicit. -/
theorem coexact_orthogonal_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {prior posterior exactErr coexactErr : EdgeCurrent n1}
    (hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) prior posterior)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    eckmannDot posterior coexactErr = 0 :=
  (bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact).2.2.2.2.2

/--
If the finite Bayesian update is stationary on a protected harmonic current,
then the stationary current is in the Hodge kernel and is orthogonal to local
exact/coexact sectors.
-/
theorem stationary_bayesian_harmonic_current_protected
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {stationary exactErr coexactErr : EdgeCurrent n1}
    (hstationary : T stationary = stationary)
    (hharmonic : IsProtectedHarmonicCurrent d0 d1 stationary)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    (stabilizerHamiltonian1 d0 d1).mulVec stationary = 0 ∧
      eckmannDot stationary exactErr = 0 ∧
      eckmannDot stationary coexactErr = 0 := by
  have hproj :
      BayesianProjectionReadout T (IsProtectedHarmonicCurrent d0 d1) stationary stationary :=
    ⟨hstationary, hharmonic⟩
  have h :=
    bayesian_harmonic_stabilizer_readout d0 d1 T hproj hexact hcoexact
  rcases h with ⟨_, hkernel, _, _, hExactOrth, hCoexactOrth⟩
  exact ⟨hkernel, hExactOrth, hCoexactOrth⟩

/-- The stationary current readout is explicit. -/
theorem stationary_current_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {stationary exactErr coexactErr : EdgeCurrent n1}
    (hstationary : T stationary = stationary)
    (_hharmonic : IsProtectedHarmonicCurrent d0 d1 stationary)
    (_hexact : IsExactOneForm d0 exactErr)
    (_hcoexact : IsCoexactOneForm d1 coexactErr) :
    T stationary = stationary :=
  hstationary

/-- The stationary stabilizer kernel readout is explicit. -/
theorem stationary_stabilizer_kernel_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {stationary exactErr coexactErr : EdgeCurrent n1}
    (hstationary : T stationary = stationary)
    (hharmonic : IsProtectedHarmonicCurrent d0 d1 stationary)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    (stabilizerHamiltonian1 d0 d1).mulVec stationary = 0 :=
  (stationary_bayesian_harmonic_current_protected d0 d1 T hstationary hharmonic hexact hcoexact).1

/-- The stationary exact-sector orthogonality is explicit. -/
theorem stationary_exact_orthogonal_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {stationary exactErr coexactErr : EdgeCurrent n1}
    (hstationary : T stationary = stationary)
    (hharmonic : IsProtectedHarmonicCurrent d0 d1 stationary)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    eckmannDot stationary exactErr = 0 :=
  ((stationary_bayesian_harmonic_current_protected d0 d1 T hstationary hharmonic hexact hcoexact).2).1

/-- The stationary coexact-sector orthogonality is explicit. -/
theorem stationary_coexact_orthogonal_readout
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (T : CurrentUpdate n1)
    {stationary exactErr coexactErr : EdgeCurrent n1}
    (hstationary : T stationary = stationary)
    (hharmonic : IsProtectedHarmonicCurrent d0 d1 stationary)
    (hexact : IsExactOneForm d0 exactErr)
    (hcoexact : IsCoexactOneForm d1 coexactErr) :
    eckmannDot stationary coexactErr = 0 :=
  ((stationary_bayesian_harmonic_current_protected d0 d1 T hstationary hharmonic hexact hcoexact).2).2

end

end InfoGeometry.Canonical.BayesianHodgeStabilizerBridge
