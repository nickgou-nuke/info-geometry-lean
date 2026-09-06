import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section

open Matrix

namespace InfoGeometry.Nuclear.ChiralPRM

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Frauendorf Triaxial Particle-Rotor Model (PRM) & Nuclear Chirality Bridge

This module formalizes the exact algebraic structure of chiral doublet bands in triaxial nuclei:
1. **Triaxial Inertia Tensor**:
   Moments of inertia $(\mathcal{J}_s, \mathcal{J}_m, \mathcal{J}_l)$ with intermediate-axis dominance
   $\mathcal{J}_m > \mathcal{J}_s, \mathcal{J}_l$ generating a stable aplanar chiral frame.
2. **Chiral Doublet Matrix Model**:
   In the left/right handed basis $\{|L\rangle, |R\rangle\}$, the total PRM Hamiltonian is
   $\mathcal{H}_{\text{PRM}} = \begin{pmatrix} E_{\text{diag}} & -\Delta \\ -\Delta & E_{\text{diag}} \end{pmatrix}$,
   where $\Delta = \langle L | \mathcal{H}_{\text{PRM}} | R \rangle$ is the quantum tunneling matrix element.
3. **Chiral Parity Projectors**:
   $P_\pm = \frac{1}{2}(1 \pm \sigma_1)$ with $P_\pm^2 = P_\pm, P_+ P_- = 0, P_+ + P_- = 1$.
4. **Energy Splitting & Static Degeneracy**:
   $E_\pm = E_{\text{diag}} \mp \Delta \implies \Delta E(I) = E_- - E_+ = 2\Delta$.
   When the chiral geometry is rigidly stable ($\Delta = 0$), $E_+ = E_- = E_{\text{diag}}$ (exact spontaneous chiral symmetry breaking).

All proofs are complete in native Mathlib 4 with 0 `sorry`s.
-/

/-! ### 1. Triaxial Moments of Inertia -/

/-- Hydrodynamic moments of inertia for a triaxial nucleus with intermediate-axis dominance. -/
structure TriaxialMoments where
  J_s : ℝ  -- Short axis
  J_m : ℝ  -- Intermediate axis (dominant moment of inertia)
  J_l : ℝ  -- Long axis
  pos_s : 0 < J_s
  pos_m : 0 < J_m
  pos_l : 0 < J_l
  intermediate_dominant : J_s < J_m ∧ J_l < J_m

/-! ### 2. Chiral Doublet State & Energy Splitting -/

/-- Chiral doublet state parameters in the $\{|L\rangle, |R\rangle\}$ basis. -/
structure ChiralDoubletState where
  E_diag : ℝ  -- Diagonal rotational core energy
  Delta : ℝ   -- Tunneling matrix element between left- and right-handed orientations

/-- Positive parity chiral band energy: $E_+ = E_{\text{diag}} - \Delta$. -/
def energyPlus (state : ChiralDoubletState) : ℝ :=
  state.E_diag - state.Delta

/-- Negative parity chiral band energy: $E_- = E_{\text{diag}} + \Delta$. -/
def energyMinus (state : ChiralDoubletState) : ℝ :=
  state.E_diag + state.Delta

/-- **THE CHIRAL DOUBLET ENERGY SPLITTING THEOREM**:
    $\Delta E(I) = E_-(I) - E_+(I) = 2\Delta$. -/
theorem chiral_doublet_energy_splitting (state : ChiralDoubletState) :
  energyMinus state - energyPlus state = 2 * state.Delta := by
  dsimp [energyMinus, energyPlus]
  ring

/-- The physical (nonnegative) gap is independent of the sign convention for
the off-diagonal tunnelling matrix element. -/
theorem chiral_doublet_absolute_gap (state : ChiralDoubletState) :
    |energyMinus state - energyPlus state| = 2 * |state.Delta| := by
  rw [chiral_doublet_energy_splitting]
  rw [abs_mul]
  norm_num

/-- **THE CHIRAL STATIC DEGENERACY THEOREM**:
    In the rigid limit with zero tunneling ($\Delta = 0$), the doublet bands are strictly degenerate:
    $E_+ = E_- = E_{\text{diag}}$. -/
theorem chiral_static_degeneracy (state : ChiralDoubletState) (h_tunnel : state.Delta = 0) :
    energyPlus state = energyMinus state := by
  dsimp [energyPlus, energyMinus]
  rw [h_tunnel]
  ring

/-! ### 3. Matrix Model & Fundamental Peirce Projectors -/

/-- The $2\times 2$ PRM Hamiltonian in the $\{|L\rangle, |R\rangle\}$ basis. -/
def prmMatrix (state : ChiralDoubletState) : M2R :=
  !![state.E_diag, -state.Delta; -state.Delta, state.E_diag]

/-- The chiral flip operator $\mathcal{A} = \sigma_1$ exchanging $|L\rangle \leftrightarrow |R\rangle$. -/
def chiralFlip : M2R := !![0, 1; 1, 0]

/-- Positive parity Peirce projector $P_+ = \frac{1}{2}(1 + \sigma_1)$. -/
def peircePlus : M2R := !![1/2, 1/2; 1/2, 1/2]

/-- Negative parity Peirce projector $P_- = \frac{1}{2}(1 - \sigma_1)$. -/
def peirceMinus : M2R := !![1/2, -1/2; -1/2, 1/2]

/-- **Theorem**: Chiral flip involution: $\mathcal{A}^2 = 1$. -/
theorem chiralFlip_sq : chiralFlip * chiralFlip = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiralFlip]

/-- **Theorem**: $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peircePlus_sq : peircePlus * peircePlus = peircePlus := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peircePlus]; ring)

/-- **Theorem**: $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceMinus_sq : peirceMinus * peirceMinus = peirceMinus := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peirceMinus]; ring)

/-- **Theorem**: $P_+$ and $P_-$ are orthogonal: $P_+ P_- = 0$. -/
theorem peirce_orthogonal : peircePlus * peirceMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peircePlus, peirceMinus]; ring)

/-- **Theorem**: Completeness of chiral Peirce decomposition: $P_+ + P_- = 1$. -/
theorem peirce_completeness : peircePlus + peirceMinus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [peircePlus, peirceMinus]; ring)

/-- The chiral doublet Hamiltonian has the Peirce spectral normal form. -/
theorem prmMatrix_peirce_spectral_decomposition (state : ChiralDoubletState) :
    prmMatrix state = energyPlus state • peircePlus + energyMinus state • peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prmMatrix, energyPlus, energyMinus, peircePlus, peirceMinus]
  <;> ring

/-- **Theorem**: Characteristic determinant of the chiral doublet matrix:
    $\det(\mathcal{H}_{\text{PRM}} - E I_2) = (E - E_+)(E - E_-)$. -/
theorem prm_determinant_eq (state : ChiralDoubletState) (E : ℝ) :
    det (prmMatrix state - E • (1 : M2R)) = (E - energyPlus state) * (E - energyMinus state) := by
  dsimp [prmMatrix, energyPlus, energyMinus]
  simp [det_fin_two]
  ring

/-! ### 4. Grand Nuclear Chiral PRM Synthesis -/

/-
🏆 **GRAND SYNTHESIS: Frauendorf Particle-Rotor Model (PRM) & Nuclear Chirality**

Unifies:
1. Chiral flip involution and Peirce projectors: $\mathcal{A}^2 = 1, P_\pm^2 = P_\pm, P_+ P_- = 0, P_+ + P_- = 1$.
2. Exact doublet energy splitting: $E_-(I) - E_+(I) = 2\Delta$.
3. Exact static degeneracy under vanishing tunneling: $\Delta = 0 \implies E_+ = E_-$.
4. Secular characteristic equation: $\det(\mathcal{H}_{\text{PRM}} - E I) = (E - E_+)(E - E_-)$.
-/
end InfoGeometry.Nuclear.ChiralPRM
