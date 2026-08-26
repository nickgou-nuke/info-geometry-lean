import DAG.ChiralDiracAnticommutation
import DAG.MatrixRepresentation
import InfoGeometry.Clifford.CliffordBott

noncomputable section

/-!
# DAG.GradedBottPeriodicity

Checked bridge for the DAG chiral grading and the repo-native split Clifford
Bott tower.

The finite graph Dirac anticommutation is owned by `DAG.MatrixRepresentation`
and `DAG.ChiralDiracAnticommutation`.  The split Clifford direct-limit Bott
data is owned by `InfoGeometry.Clifford.CliffordBott`.  This module only
records the common interface used by DAG code; it does not reimplement the
recursive Clifford tower.
-/

namespace DAG.GradedBottPeriodicity

open InfoGeometry.Clifford.CliffordBott
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-! ## Finite DAG chiral grading -/

/-- The DAG parity used by the finite block Dirac operator. -/
abbrev cellParity {n0 n1 n2 : ℕ} :
    DAG.MatrixRepresentation.Cell n0 n1 n2 → ℚ :=
  DAG.MatrixRepresentation.cellParity

/-- The finite chiral grading `Γ = diag(+1,-1,+1)`. -/
abbrev chiralGamma {n0 n1 n2 : ℕ} :
    Matrix (DAG.MatrixRepresentation.Cell n0 n1 n2)
      (DAG.MatrixRepresentation.Cell n0 n1 n2) ℚ :=
  DAG.MatrixRepresentation.chiralGamma

/-- The finite DAG Dirac operator `D = ∂ + ∂*`. -/
abbrev diracOp {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    Matrix (DAG.MatrixRepresentation.Cell n0 n1 n2)
      (DAG.MatrixRepresentation.Cell n0 n1 n2) ℚ :=
  DAG.MatrixRepresentation.diracOp B1 B2

/--
Finite graded anticommutation for the DAG Dirac operator.

This is the matrix-level instance of the chiral grading law.  It delegates to
the owner theorem in `DAG.MatrixRepresentation`.
-/
theorem finiteDirac_anticommutes_chiral {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℚ)
    (B2 : Matrix (Fin n1) (Fin n2) ℚ) :
    chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) * diracOp B1 B2
      + diracOp B1 B2 * chiralGamma (n0 := n0) (n1 := n1) (n2 := n2) = 0 :=
  DAG.MatrixRepresentation.chiral_anticommutation B1 B2

/--
Real-coefficient version of the same finite DAG anticommutation law.

This delegates to the older concrete owner theorem in
`DAG.ChiralDiracAnticommutation`.
-/
theorem finiteDirac_anticommutes_chiral_real {n0 n1 n2 : ℕ}
    (B1 : Matrix (Fin n0) (Fin n1) ℝ)
    (B2 : Matrix (Fin n1) (Fin n2) ℝ) :
    DAG.ChiralDiracAnticommutation.chiralGamma
        * DAG.ChiralDiracAnticommutation.diracOp B1 B2
      + DAG.ChiralDiracAnticommutation.diracOp B1 B2
        * DAG.ChiralDiracAnticommutation.chiralGamma = 0 :=
  DAG.ChiralDiracAnticommutation.dirac_anticommutes_gamma B1 B2

/-! ## Split Clifford Bott direct-limit readout -/

/-- Repo-native finite split Clifford stage. -/
abbrev SplitStage (n : ℕ) : Type :=
  SplitClNNAlg n

/-- Repo-native infinite split Clifford direct limit. -/
abbrev SplitLimit : Type :=
  Cl_infty

/-- The canonical nilpotent seed in the finite split tower. -/
abbrev finiteNilpotentSeed : SplitStage 1 :=
  finiteNilpotentShield

@[simp]
theorem finiteNilpotentSeed_sq :
    finiteNilpotentSeed * finiteNilpotentSeed = 0 :=
  finiteNilpotentShield_sq

/-- The direct-limit nilpotent shield. -/
abbrev nilpotentShield : SplitLimit :=
  clInfinityNilpotentShield

@[simp]
theorem nilpotentShield_sq :
    nilpotentShield * nilpotentShield = 0 :=
  clInfinityNilpotentShield_sq

/-- The seed transported to stage `1 + k`. -/
abbrev stableStage (k : ℕ) : SplitStage (1 + k) :=
  stableNilpotentShieldStage k

@[simp]
theorem stableStage_sq (k : ℕ) :
    stableStage k * stableStage k = 0 :=
  stableNilpotentShieldStage_sq k

@[simp]
theorem stableStage_lifts (k : ℕ) :
    ofStage (1 + k) (stableStage k) = nilpotentShield :=
  stableNilpotentShieldStage_lifts k

/-- The same seed sampled along the eight-step Bott clock. -/
abbrev bottClockStage (k : ℕ) : SplitStage (1 + 8 * k) :=
  bottClockNilpotentStage k

@[simp]
theorem bottClockStage_sq (k : ℕ) :
    bottClockStage k * bottClockStage k = 0 :=
  bottClockNilpotentStage_sq k

@[simp]
theorem bottClockStage_lifts (k : ℕ) :
    ofStage (1 + 8 * k) (bottClockStage k) = nilpotentShield :=
  bottClockNilpotentStage_lifts k

end DAG.GradedBottPeriodicity

end
