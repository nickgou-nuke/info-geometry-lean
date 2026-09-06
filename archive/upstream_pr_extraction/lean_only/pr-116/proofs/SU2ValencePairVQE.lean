import proofs.NuclearChartSquareCalibration
import proofs.XanaduSpinNetworkCodeDigest

/-!
# SU(2) valence-pair VQE

Finite bridge from the Xanadu `Spin_2` Schur gate to the valence-pair and
nuclear-chart-square Hamiltonians.

The executable script uses the upstream Schur matrix

```text
S₂ = {|00⟩, (|01⟩+|10⟩)/√2, |11⟩, (|01⟩-|10⟩)/√2}
```

and the variational unitary `S₂ᵀ diag(1,1,1,e^{iθ}) S₂` to minimize the
Rayleigh energy of the fitted four-vertex square Hamiltonian.  This Lean layer
records the finite algebraic facts that do not depend on numerical optimization.
-/

noncomputable section

namespace SU2ValencePairVQE

/-- One `Spin_2` Schur-gate parameter per variational block. -/
def spin2VQEParamCount (blocks : ℕ) : ℕ := blocks

@[simp] theorem spin2_vqe_params_four_blocks :
    spin2VQEParamCount 4 = 4 := by
  norm_num [spin2VQEParamCount]

/-- Two-level real Rayleigh quotient for a normalized vector `(c,s)`. -/
def rayleigh2 (E₁ E₂ flow c s : ℝ) : ℝ :=
  E₁ * c ^ 2 + E₂ * s ^ 2 + 2 * flow * c * s

@[simp] theorem rayleigh2_left_endpoint (E₁ E₂ flow : ℝ) :
    rayleigh2 E₁ E₂ flow 1 0 = E₁ := by
  simp [rayleigh2]

@[simp] theorem rayleigh2_right_endpoint (E₁ E₂ flow : ℝ) :
    rayleigh2 E₁ E₂ flow 0 1 = E₂ := by
  simp [rayleigh2]

theorem rayleigh2_zero_flow_convex
    (E₁ E₂ c s : ℝ) :
    rayleigh2 E₁ E₂ 0 c s = E₁ * c ^ 2 + E₂ * s ^ 2 := by
  simp [rayleigh2]

end SU2ValencePairVQE

end noncomputable section
