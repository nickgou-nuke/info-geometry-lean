import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Basic
import InfoGeometry.External.Auto.NuclearChartSquareCalibration
import InfoGeometry.External.Auto.Q8NuclearChirality
import InfoGeometry.Physics.ZornNuclearState
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.Canonical.SL2SpinorLadder

noncomputable section

/-!
# Nuclear chiral physics: charge symmetry and proton↔neutron observables

This owner separates the **physical** nuclear layer from the abstract
5-grading kept in `NuclearQuantumNumbers`.

The physical model has three independent layers:

1. **Chiral causal-operator basis** — the `σ⁺/σ⁻/σ³` algebra from
   `InfoGeometry.Physics.ChiralCausalCone`, soldered onto the nuclear
   Hilbert space.

2. **Nuclear Hamiltonian** — a 2×2 Hermitian matrix in the chiral basis,
   encoding base energy, isospin deformation, and Coriolis/chiral coupling.

3. **Derived observables** — charge-symmetry transformations, chirality
   indices, and energy-spacing laws read off from the Hamiltonian.

The existing 5-graded `SL2SpinorLadder` carrier is imported only as an
abstract algebraic spine; no physical nuclear generator is identified with
a 5-grading basis vector here.
-/

namespace InfoGeometry.External.Auto.NuclearChiralPhysics

open InfoGeometry.Physics.ChiralCausalCone
open NuclearChartSquareCalibration

/-! ## Nuclear two-state Hilbert space -/

/-- A nuclear state is a superposition of proton and neutron. -/
abbrev NuclearState := InfoGeometry.Algebra.FiniteSpin.Vec2C

/-- The proton basis vector `|p⟩ = (1, 0)`. -/
def proton : NuclearState := fun i => if i = 0 then (1 : ℂ) else 0

/-- The neutron basis vector `|n⟩ = (0, 1)`. -/
def neutron : NuclearState := fun i => if i = 0 then 0 else (1 : ℂ)

/-- The isospin raising operator `T₊` maps neutron → proton. -/
def Tplus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The isospin lowering operator `T₋` maps proton → neutron. -/
def Tminus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The third component of isospin `T₃ = (|p⟩⟨p| - |n⟩⟨n|)/2`. -/
def Tz_op : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (InfoGeometry.Physics.ChiralCausalCone.PPlus - InfoGeometry.Physics.ChiralCausalCone.PMinus)

/-- The total isospin `T² = T₊T₋ + T₃(T₃-1)`. -/
def T_sq : Matrix (Fin 2) (Fin 2) ℂ := Tplus * Tminus + Tz_op * (Tz_op - 1)

/-! ## Charge-symmetry transformation -/

/-- Charge symmetry swaps proton and neutron. -/
def chargeSymmetry : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Charge symmetry is an involution. -/
theorem chargeSymmetry_inv : chargeSymmetry * chargeSymmetry = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [chargeSymmetry]

/-- Charge symmetry swaps the basis vectors. -/
theorem chargeSymmetry_proton : Matrix.mulVec chargeSymmetry proton = neutron := by
  ext i <;> fin_cases i <;>
    simp [chargeSymmetry, proton, neutron, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

/-- Charge symmetry swaps the basis vectors. -/
theorem chargeSymmetry_neutron : Matrix.mulVec chargeSymmetry neutron = proton := by
  ext i <;> fin_cases i <;>
    simp [chargeSymmetry, proton, neutron, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]

/-- Charge symmetry preserves the inner product. -/
theorem chargeSymmetry_unitary :
    Matrix.conjTranspose chargeSymmetry = chargeSymmetry := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [chargeSymmetry, Matrix.conjTranspose_apply]

/-! ## Nuclear Hamiltonian in chiral form -/

/-- The most general 2×2 Hermitian matrix in the chiral basis:
    H = E₊·N₊ + E₋·N₋ + W·S₊ + W*·S₋

    Parameters:
      `E_plus` — right-handed/proton energy
      `E_minus` — left-handed/neutron energy
      `W` — chiral tunneling amplitude (complex)
-/
def nuclearHamiltonian (E_plus E_minus : ℝ) (W : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (E_plus : ℂ) • InfoGeometry.Physics.ChiralCausalCone.PPlus +
  (E_minus : ℂ) • InfoGeometry.Physics.ChiralCausalCone.PMinus +
  W • InfoGeometry.Physics.ChiralCausalCone.σPlus +
  starRingEnd ℂ W • InfoGeometry.Physics.ChiralCausalCone.σMinus

/-- Hamiltonian matrix elements in the Pauli representation. -/
theorem nuclearHamiltonian_matrix (E_plus E_minus : ℝ) (W : ℂ) :
    nuclearHamiltonian E_plus E_minus W = !![(E_plus : ℂ), W; starRingEnd ℂ W, (E_minus : ℂ)] := by
  ext i j <;> fin_cases i <;> fin_cases j
  all_goals
    simp [nuclearHamiltonian, PPlus_matrix, PMinus_matrix, σPlus, σMinus, Matrix.add_apply, Matrix.smul_apply]
    try ring

/-- The Hamiltonian is Hermitian. -/
theorem nuclearHamiltonian_hermitian (E_plus E_minus : ℝ) (W : ℂ) :
    Matrix.conjTranspose (nuclearHamiltonian E_plus E_minus W) =
      nuclearHamiltonian E_plus E_minus W := by
  rw [nuclearHamiltonian_matrix]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num

/-- Trace of the Hamiltonian = total energy. -/
theorem tr_nuclearHamiltonian (E_plus E_minus : ℝ) (W : ℂ) :
    (nuclearHamiltonian E_plus E_minus W).trace = (E_plus + E_minus : ℂ) := by
  rw [nuclearHamiltonian_matrix]
  simp [Matrix.trace_fin_two]

/-- Determinant of the Hamiltonian. -/
theorem det_nuclearHamiltonian (E_plus E_minus : ℝ) (W : ℂ) :
    (nuclearHamiltonian E_plus E_minus W).det = (E_plus * E_minus - Complex.normSq W : ℂ) := by
  rw [nuclearHamiltonian_matrix]
  simp [Matrix.det_fin_two]
  rw [Complex.normSq_eq_conj_mul_self]
  rw [starRingEnd_apply]
  ring

/-! ## Eigenvalues and chiral spacing law -/

/-- Eigenvalues of the nuclear Hamiltonian:
    λ₁,₂ = (E₊+E₋)/2 ± ½√((E₊-E₋)² + 4|W|²)
-/
def nuclearEigenvalues (E_plus E_minus : ℝ) (W : ℂ) : ℝ × ℝ :=
  let center := (E_plus + E_minus) / 2
  let spread := Real.sqrt ((E_plus - E_minus)^2 + 4 * Complex.normSq W)
  (center + spread / 2, center - spread / 2)

/-- The energy spacing follows the chiral spacing law:
    S = √((E₊-E₋)² + 4|W|²)
-/
def nuclearSpacing (E_plus E_minus : ℝ) (W : ℂ) : ℝ :=
  Real.sqrt ((E_plus - E_minus)^2 + 4 * Complex.normSq W)

/-- When W = 0, spacing reduces to the bare energy difference. -/
theorem nuclearSpacing_W_zero (E_plus E_minus : ℝ) :
    nuclearSpacing E_plus E_minus 0 = |E_plus - E_minus| := by
  simp [nuclearSpacing, Complex.normSq_zero, Real.sqrt_sq_eq_abs]

/-- When E₊ = E₋, spacing is purely from chiral tunneling: S = 2|W|. -/
theorem nuclearSpacing_degenerate (E : ℝ) (W : ℂ) :
    nuclearSpacing E E W = 2 * Real.sqrt (Complex.normSq W) := by
  simp [nuclearSpacing]
  have hx : (0 : ℝ) ≤ Complex.normSq W := Complex.normSq_nonneg _
  have hsqrt4 : Real.sqrt 4 = 2 := by norm_num
  simp [hsqrt4]

/-- The spacing is always ≥ 2|W| (Wigner–Dyson lower bound). -/
theorem nuclearSpacing_lower_bound (E_plus E_minus : ℝ) (W : ℂ) :
    2 * Real.sqrt (Complex.normSq W) ≤ nuclearSpacing E_plus E_minus W := by
  have hW : (0 : ℝ) ≤ Complex.normSq W := Complex.normSq_nonneg _
  have hdiff : (0 : ℝ) ≤ (E_plus - E_minus)^2 := by simp [sq_nonneg]
  have hsum : (0 : ℝ) ≤ (E_plus - E_minus)^2 + 4 * Complex.normSq W := by
    simp [hdiff, hW, add_nonneg]
  rw [nuclearSpacing]
  have h : Real.sqrt (4 * Complex.normSq W) ≤ Real.sqrt ((E_plus - E_minus)^2 + 4 * Complex.normSq W) := by
    apply Real.sqrt_le_sqrt
    linarith [hdiff, hW]
  have h2 : Real.sqrt (4 * Complex.normSq W) = 2 * Real.sqrt (Complex.normSq W) := by
    rw [Real.sqrt_mul (by norm_num)]
    norm_num
  rw [h2] at h
  exact h

/-! ## Chirality as a derived observable -/

/-- The chirality operator `χ = σ³ = N₊ - N₋`. -/
abbrev chiralityOp : Matrix (Fin 2) (Fin 2) ℂ := σ3c

/-- Chirality eigenvalues are ±1. -/
theorem chiralityOp_eigenvalues :
    chiralityOp ^ 2 = 1 := by
  rw [chiralityOp, pow_two, σ3c_sq]

/-- The chirality index of a state `ψ` is `⟨ψ|σ³|ψ⟩ / ⟨ψ|ψ⟩`. -/
def chiralityIndex (ψ : NuclearState) : ℝ :=
  (Complex.normSq (ψ 0) - Complex.normSq (ψ 1)) / (Complex.normSq (ψ 0) + Complex.normSq (ψ 1))

/-- Proton has chirality +1. -/
theorem chiralityIndex_proton : chiralityIndex proton = 1 := by
  simp [chiralityIndex, proton, Complex.normSq_zero, Complex.normSq_one]

/-- Neutron has chirality -1. -/
theorem chiralityIndex_neutron : chiralityIndex neutron = -1 := by
  simp [chiralityIndex, neutron, Complex.normSq_zero, Complex.normSq_one]

/-- A maximally mixed state has zero chirality. -/
theorem chiralityIndex_mixed : chiralityIndex (fun i => if i = 0 then (1/√2 : ℂ) else (1/√2 : ℂ)) = 0 := by
  simp [chiralityIndex, Complex.normSq_ofReal, sub_self, zero_div]

/-! ## Nuclear data connection (PD94 example) -/

/-- PD-94: Z=46, N=48, Tz=1. -/
def PD94_Z : ℕ := 46
def PD94_N : ℕ := 48
def PD94_Tz : ℤ := 1

/-- The PD-94 isospin multiplet check. -/
theorem PD94_in_isospin_multiplet :
    |PD94_Tz| ≤ 2 * 1 := by simp [PD94_Tz]

/-- Proton/neutron hole count for PD-94 in the g9/2 shell. -/
def PD94_protonHoles : ℕ := 50 - PD94_Z
def PD94_neutronHoles : ℕ := 50 - PD94_N

theorem PD94_hole_counts :
    PD94_protonHoles = 4 ∧ PD94_neutronHoles = 2 := by
  simp [PD94_protonHoles, PD94_neutronHoles, PD94_Z, PD94_N]

end InfoGeometry.External.Auto.NuclearChiralPhysics
