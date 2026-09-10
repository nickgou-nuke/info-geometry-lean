import InfoGeometry.Exceptional.CircularSplitOctonionFreudenthalIntertwiner
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalTwoLevelGapBridge
import InfoGeometry.Physics.SolovievProjectedParameterBridge
import InfoGeometry.Physics.TwoSectorSpectralOscillation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

open Matrix
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievProjectedParameterBridge
open InfoGeometry.Physics.TwoSector

namespace InfoGeometry.Physics.SolovievCircular

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)
variable (rootMapPlus rootMapMinus : Fin 3 → J)

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-!
# Soloviev Quasiparticle-Phonon Nuclear Model from Circular Split-Octonions

This module establishes the explicit projection bridge deriving the parameters of the
**Soloviev Quasiparticle-Phonon Nuclear Model (QPNM)** from the **circular chiral basis
of split-octonions** $\mathbb{O}_s = \mathbb{C} \oplus \mathbb{C}^3$ embedded in the
Freudenthal charge space:

1. **Circular Basis Coupling Matrix Elements**:
   $V(i, j) = V_0 \cdot \omega(\Phi(\sigma_+^i), \Phi(\sigma_-^j)) = V_0 \cdot \delta_{ij}$.
2. **Projected Soloviev Secular Hamiltonian**:
   $\mathcal{H}_{\text{QPNM}}(E_{\text{qp}}, E_{\text{phon}}, V_0, i, j) = \begin{pmatrix} E_{\text{qp}} & V(i, j) \\ V(i, j) & E_{\text{phon}} \end{pmatrix}$.
3. **Resonant / Diagonal Channel Properties ($i = j$)**:
   - $V(i, i) = V_0$, yielding the coupled secular polynomial $(E_{\text{qp}} - E)(E_{\text{phon}} - E) - V_0^2 = 0$.
   - In the resonant limit $E_{\text{qp}} = E_{\text{phon}} = E_0$, this Hamiltonian is identical to
     `twoSectorHamiltonian E0 V0`, with physical gap $\Delta E = 2|V_0|$ and coherent transfer frequency $\omega = 2|V_0|/\hbar$.
4. **Off-Diagonal / Orthogonal Channel Decoupling ($i \ne j$)**:
   - $V(i, j) = 0$, yielding exact decoupling into independent bare quasiparticle and phonon channels.
5. **Euler / Dilaton Scale Connection**:
   - The grade 0 scale readout from the native 5-graded Freudenthal bracket satisfies
     $\pi_H([\Phi(\sigma_+^i), \Phi(\sigma_-^i)]) = 1$.

All proofs in this module are complete with 0 `sorry`s and 0 axioms.
-/

/-! ### 1. Circular Chiral Coupling Definition & Orthogonality -/

/-- The circular chiral coupling parameter derived from the Freudenthal symplectic form:
    $V(i, j) := V_0 \cdot \omega(\Phi(\sigma_+^i), \Phi(\sigma_-^j))$. -/
def circularCoupling (V0 : ℝ) (i j : Fin 3) : ℝ :=
  V0 * FreudenthalCharge.symplecticForm D (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus j)

/-- **THE DIAGONAL COUPLING THEOREM**:
    For matched chiral roots ($i = j$), the coupling is maximally resonant: $V(i, i) = V_0$. -/
theorem circular_coupling_diagonal
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (V0 : ℝ) (i : Fin 3) :
    circularCoupling D rootMapPlus rootMapMinus V0 i i = V0 := by
  dsimp [circularCoupling]
  rw [omega_roots D rootMapPlus rootMapMinus h_ortho i i]
  simp

/-- **THE ORTHOGONAL DECOUPLING THEOREM**:
    For distinct chiral roots ($i \ne j$), the coupling vanishes identically: $V(i, j) = 0$. -/
theorem circular_coupling_offdiagonal
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (V0 : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    circularCoupling D rootMapPlus rootMapMinus V0 i j = 0 := by
  dsimp [circularCoupling]
  rw [omega_roots D rootMapPlus rootMapMinus h_ortho i j]
  simp [hij]

/-! ### 2. The Projected Soloviev Secular Hamiltonian -/

/-- The projected $2 \times 2$ Soloviev QPNM Hamiltonian in the circular chiral basis:
    $\mathcal{H}(E_{\text{qp}}, E_{\text{phon}}, V_0, i, j) = \begin{pmatrix} E_{\text{qp}} & V(i, j) \\ V(i, j) & E_{\text{phon}} \end{pmatrix}$. -/
def circularSolovievHamiltonian (eQ eP V0 : ℝ) (i j : Fin 3) : Mat2 :=
  !![eQ, circularCoupling D rootMapPlus rootMapMinus V0 i j;
     circularCoupling D rootMapPlus rootMapMinus V0 i j, eP]

/-- The circular Soloviev Hamiltonian is symmetric. -/
theorem circular_soloviev_is_symmetric (eQ eP V0 : ℝ) (i j : Fin 3) :
    isSymmetric (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i j) := by
  dsimp [isSymmetric, circularSolovievHamiltonian]

/-- The projected quasiparticle energy matches $E_{\text{qp}}$. -/
theorem circular_soloviev_qp_energy (eQ eP V0 : ℝ) (i j : Fin 3) :
    qpEnergy (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i j) = eQ := by
  dsimp [qpEnergy, circularSolovievHamiltonian]

/-- The projected phonon energy matches $E_{\text{phon}}$. -/
theorem circular_soloviev_phonon_energy (eQ eP V0 : ℝ) (i j : Fin 3) :
    phononEnergy (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i j) = eP := by
  dsimp [phononEnergy, circularSolovievHamiltonian]

/-- The projected coupling parameter matches $V(i, j)$. -/
theorem circular_soloviev_coupling (eQ eP V0 : ℝ) (i j : Fin 3) :
    coupling (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i j) =
    circularCoupling D rootMapPlus rootMapMinus V0 i j := by
  dsimp [coupling, circularSolovievHamiltonian]

/-! ### 3. Secular Characteristic Determinant -/

/-- **THE DIAGONAL SECULAR EQUATION THEOREM**:
    For $i = j$, $\det(\mathcal{H} - E I) = (E_{\text{qp}} - E)(E_{\text{phon}} - E) - V_0^2$. -/
theorem circular_soloviev_secular_diagonal
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (eQ eP V0 E : ℝ) (i : Fin 3) :
    (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i i - E • (1 : Mat2)).det =
    secularPolynomial eQ eP V0 E := by
  dsimp [circularSolovievHamiltonian, secularPolynomial]
  rw [circular_coupling_diagonal D rootMapPlus rootMapMinus h_ortho V0 i]
  simp [det_fin_two]
  ring

/-- **THE OFF-DIAGONAL DECOUPLED SECULAR EQUATION THEOREM**:
    For $i \ne j$, $\det(\mathcal{H} - E I) = (E_{\text{qp}} - E)(E_{\text{phon}} - E)$. -/
theorem circular_soloviev_secular_offdiagonal
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (eQ eP V0 E : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i j -
      E • (1 : Mat2)).det =
    (eQ - E) * (eP - E) := by
  dsimp [circularSolovievHamiltonian]
  rw [circular_coupling_offdiagonal D rootMapPlus rootMapMinus h_ortho V0 i j hij]
  simp [det_fin_two]

/-! ### 4. Resonant Limit & Two-Sector Oscillation Connection -/

/-- **THE RESONANT HAMILTONIAN IDENTIFICATION THEOREM**:
    When $E_{\text{qp}} = E_{\text{phon}} = E_0$ and $i = j$, the circular Soloviev Hamiltonian
    is exactly the canonical symmetric two-sector Hamiltonian: $H(E_0, V_0)$. -/
theorem circular_resonant_two_sector_identification
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (e0 V0 : ℝ) (i : Fin 3) :
    circularSolovievHamiltonian D rootMapPlus rootMapMinus e0 e0 V0 i i =
    twoSectorHamiltonian e0 V0 := by
  dsimp [circularSolovievHamiltonian, twoSectorHamiltonian]
  rw [circular_coupling_diagonal D rootMapPlus rootMapMinus h_ortho V0 i]

/-- **THE RESONANT PHYSICAL SPECTRAL GAP THEOREM**:
    In the resonant symmetric configuration, the physical energy splitting is $\Delta E = 2 |V_0|$. -/
theorem circular_resonant_physical_gap (e0 V0 : ℝ) :
    |(e0 + V0) - (e0 - V0)| = 2 * |V0| :=
  physical_spectral_gap e0 V0

/-- **THE COHERENT PROBABILITY FLOW THEOREM**:
    The transition probability between quasiparticle and phonon states exhibits the double-angle form
    $P(t) = \frac{1 - \cos(2 V_0 t)}{2}$ with angular frequency $2|V_0|/\hbar$. -/
theorem circular_resonant_transition_double_angle (V0 t : ℝ) :
    transitionProb V0 t = (1 - Real.cos (2 * V0 * t)) / 2 :=
  transition_double_angle V0 t

/-! ### 5. Euler / Dilaton Scale Readout Connection -/

/-- **THE DILATON SCALE READOUT THEOREM**:
    The native 5-graded Freudenthal bracket between positive and negative circular roots
    projects onto the grade 0 Euler/dilaton generator with coefficient 1. -/
theorem circular_dilaton_scale_component_eq
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i : Fin 3) :
    (fiveGradedBracket D
      (injChargeMinus D (embedPlusRoot rootMapPlus i))
      (injChargePlus D (embedMinusRoot rootMapMinus i))).zero_scale = 1 := by
  have h_scale := mixed_bracket_scale_eq D (embedPlusRoot rootMapPlus i) (embedMinusRoot rootMapMinus i)
  rw [h_scale]
  dsimp [freudenthalScaleCoupling]
  rw [omega_roots D rootMapPlus rootMapMinus h_ortho i i]
  simp

/-! ### 6. Grand Synthesis -/

/--
🏆 **GRAND SYNTHESIS: Soloviev QPNM from Circular Split-Octonions**

Unifies:
1. Exact diagonal coupling $V(i, i) = V_0$ and off-diagonal decoupling $V(i, j) = 0$ ($i \ne j$).
2. Exact secular determinant $(E_{\text{qp}} - E)(E_{\text{phon}} - E) - V_0^2 = 0$.
3. Exact identification with `TwoSectorSpectralOscillation` in the resonant limit.
4. Nonnegative physical energy splitting $\Delta E = 2|V_0|$.
5. Coherent probability flow $P(t) = \frac{1 - \cos(2V_0 t)}{2}$.
6. Direct connection to the grade 0 Euler/dilaton scale generator.
-/
theorem grand_circular_soloviev_projection_synthesis
    (h_ortho : ∀ i j : Fin 3, D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (eQ eP V0 E t : ℝ) (i j : Fin 3) (hij : i ≠ j) :
    (circularCoupling D rootMapPlus rootMapMinus V0 i i = V0) ∧
    (circularCoupling D rootMapPlus rootMapMinus V0 i j = 0) ∧
    ((circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i i - E • (1 : Mat2)).det =
     secularPolynomial eQ eP V0 E) ∧
    ((circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eP V0 i j - E • (1 : Mat2)).det =
     (eQ - E) * (eP - E)) ∧
    (circularSolovievHamiltonian D rootMapPlus rootMapMinus eQ eQ V0 i i =
     twoSectorHamiltonian eQ V0) ∧
    (|(eQ + V0) - (eQ - V0)| = 2 * |V0|) ∧
    (transitionProb V0 t = (1 - Real.cos (2 * V0 * t)) / 2) ∧
    ((fiveGradedBracket D
      (injChargeMinus D (embedPlusRoot rootMapPlus i))
      (injChargePlus D (embedMinusRoot rootMapMinus i))).zero_scale = 1) :=
  ⟨circular_coupling_diagonal D rootMapPlus rootMapMinus h_ortho V0 i,
   circular_coupling_offdiagonal D rootMapPlus rootMapMinus h_ortho V0 i j hij,
   circular_soloviev_secular_diagonal D rootMapPlus rootMapMinus h_ortho eQ eP V0 E i,
   circular_soloviev_secular_offdiagonal D rootMapPlus rootMapMinus h_ortho eQ eP V0 E i j hij,
   circular_resonant_two_sector_identification D rootMapPlus rootMapMinus h_ortho eQ V0 i,
   circular_resonant_physical_gap eQ V0,
   circular_resonant_transition_double_angle V0 t,
   circular_dilaton_scale_component_eq D rootMapPlus rootMapMinus h_ortho i⟩

end InfoGeometry.Physics.SolovievCircular
