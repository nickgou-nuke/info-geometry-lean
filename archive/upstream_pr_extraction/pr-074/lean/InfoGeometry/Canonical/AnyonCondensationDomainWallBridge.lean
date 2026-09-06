import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace AnyonCondensationDomainWallBridge

/-- Condensable Boson in a Parent MTC 𝒞:
    A condensable anyon A ∈ 𝒞 must be a self-dual boson (topological spin θ_A = 1) 
    with quantum dimension d_A ≥ 1. -/
abbrev CondensedBoson := {q : ℝ // 1 ≤ q}

namespace CondensedBoson

abbrev quantumDimA (b : CondensedBoson) : ℝ := b.1

abbrev h_dim_ge_one (b : CondensedBoson) : b.quantumDimA ≥ 1 := b.2

def mk (quantumDimA : ℝ) (h_dim_ge_one : quantumDimA ≥ 1) : CondensedBoson :=
  ⟨quantumDimA, h_dim_ge_one⟩

end CondensedBoson

/-- Condensed Phase Total Quantum Dimension 𝒟_cond = 𝒟_parent / d_A. -/
def condensedTotalDim (b : CondensedBoson) (D_parent : ℝ) : ℝ :=
  D_parent / b.quantumDimA

/-- **Theorem**: Total Quantum Dimension Factorization: 𝒟_cond * d_A = 𝒟_parent. -/
theorem condensed_quantum_dim_factorization (b : CondensedBoson) (D_parent : ℝ) (hA : b.quantumDimA ≠ 0) :
    condensedTotalDim b D_parent * b.quantumDimA = D_parent := by
  dsimp [condensedTotalDim]
  exact div_mul_cancel₀ D_parent hA

/-- Toric Code e-Boson Condensation (D(ℤ₂) → Trivial Phase). -/
def toricCodeElectricBoson : CondensedBoson :=
  CondensedBoson.mk 1 (by norm_num)

/-- **Theorem**: Toric Code e-Condensation Dimension Match: 𝒟_cond = 2 / 1 = 2. -/
theorem toric_code_e_condensation_dim :
    condensedTotalDim toricCodeElectricBoson 2 = 2 := by
  change (2 : ℝ) / 1 = 2
  norm_num

namespace DomainWall

/-- Domain Wall Particle States across a gapped TQFT interface. -/
inductive DomainWallParticle : Type
  | bulkLeft  : DomainWallParticle
  | bulkRight : DomainWallParticle
  | wallFixed : DomainWallParticle
  deriving DecidableEq

open DomainWallParticle

/-- Orientation reflection σ across the domain wall interface. -/
def wallOrientationQuotient : DomainWallParticle → DomainWallParticle
  | bulkLeft  => bulkRight
  | bulkRight => bulkLeft
  | wallFixed => wallFixed

/-- **Theorem**: Domain Wall Orientation Swap Involutivity: σ² = id. -/
theorem domain_wall_orientation_involutive (p : DomainWallParticle) :
    wallOrientationQuotient (wallOrientationQuotient p) = p := by
  cases p <;> rfl

end DomainWall

end AnyonCondensationDomainWallBridge
