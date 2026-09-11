import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.KreinDoubledCartanPeirceBridge

/-!
# Stratum 38: Traceless Zorn Matrix as Bogoliubov–de Gennes (BdG) Operator

This module formalizes the traceless Zorn matrix as a Bogoliubov–de Gennes (BdG) Hamiltonian
operating on the doubled Krein space $\mathcal{K} = \mathcal{H}_+ \oplus \mathcal{H}_-$:

1. **Traceless Zorn Decomposition:**
   $\hat{Z}_{\text{BdG}} = \begin{pmatrix} \mathcal{D} & \Delta_1 \\ \Delta_2 & -\mathcal{D} \end{pmatrix}
   = \mathcal{D}_{\text{chiral}} + \hat{\boldsymbol{\Delta}}_{\text{mass}}$.
2. **Exact Particle-Hole Trace Vanishing:**
   $\operatorname{tr}(\hat{Z}_{\text{BdG}}) = \mathcal{D} + (-\mathcal{D}) = 0$.
3. **Fundamental Krein Pairing Anticommutation:**
   $\{\eta, \hat{\boldsymbol{\Delta}}_{\text{mass}}\} = \eta \hat{\boldsymbol{\Delta}} + \hat{\boldsymbol{\Delta}} \eta = 0$,
   confirming that the mass pairing is strictly off-diagonal and odd under the Cartan involution.
4. **Chiral Dirac Conservation:**
   $[\eta, \mathcal{D}_{\text{chiral}}] = 0$, confirming that massless chiral propagation is even under the Cartan grading.
5. **Secular Energy Spectrum & Mass Gap:**
   $\det(\hat{Z}_{\text{BdG}} - E \mathbf{1}) = E^2 - (\mathcal{D}^2 + \Delta_1 \Delta_2)$.
   For symmetric pairing $\Delta_1 = \Delta_2 = \Delta$, the energy roots satisfy $E^2 = \mathcal{D}^2 + \Delta^2$.
-/

namespace InfoGeometry.Canonical.ZornBdGHamiltonianChiral

open Matrix
open InfoGeometry.Canonical.KreinDoubledCartanPeirce

variable {R : Type*} [CommRing R]

/-- The Traceless Zorn Bogoliubov-de Gennes (BdG) Matrix. -/
def zornBdG (D Delta1 Delta2 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![D, Delta1; Delta2, -D]

/-- Off-diagonal chiral pairing component (Higgs condensate / superconducting gap). -/
def zornPairing (Delta1 Delta2 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, Delta1; Delta2, 0]

/-- Diagonal chiral Dirac component (massless Weyl propagation). -/
def zornChiralDirac (D : R) : Matrix (Fin 2) (Fin 2) R :=
  !![D, 0; 0, -D]

/-- Zorn BdG Hamiltonian decomposes into diagonal Dirac and off-diagonal pairing. -/
theorem zornBdG_decomp (D Delta1 Delta2 : R) :
    zornBdG D Delta1 Delta2 = zornChiralDirac D + zornPairing Delta1 Delta2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zornBdG, zornChiralDirac, zornPairing]

/-- Zero trace condition on the BdG Zorn matrix. -/
theorem zornBdG_trace_zero (D Delta1 Delta2 : R) :
    Matrix.trace (zornBdG D Delta1 Delta2) = 0 := by
  simp [zornBdG, Matrix.trace, Fin.sum_univ_two]

/-- Particle-hole pairing anticommutation with Krein metric: {η, Δ̂} = 0. -/
theorem eta_pairing_anticomm (Delta1 Delta2 : R) :
    eta * zornPairing (R := R) Delta1 Delta2 + zornPairing Delta1 Delta2 * eta = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, zornPairing]

/-- Chiral Dirac commutation with Krein metric: [η, D] = 0. -/
theorem eta_chiralDirac_comm (D : R) :
    eta * zornChiralDirac (R := R) D - zornChiralDirac D * eta = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta, zornChiralDirac]

/-- Determinant of the BdG Zorn matrix: det(Z_BdG) = -(D² + Δ₁Δ₂). -/
theorem zornBdG_det (D Delta1 Delta2 : R) :
    det (zornBdG D Delta1 Delta2) = -(D ^ 2 + Delta1 * Delta2) := by
  simp [zornBdG, det_fin_two]
  ring

/-- Secular characteristic polynomial: det(Z_BdG - E • 1) = E² - (D² + Δ₁Δ₂). -/
theorem zornBdG_secular_poly (D Delta1 Delta2 E : R) :
    det (zornBdG D Delta1 Delta2 - E • 1) = E ^ 2 - (D ^ 2 + Delta1 * Delta2) := by
  simp [zornBdG, det_fin_two]
  ring

/-- For symmetric pairing Δ₁ = Δ₂ = Δ, secular root equation is E² = D² + Δ². -/
theorem zornBdG_symmetric_secular (D Delta E : R) :
    det (zornBdG D Delta Delta - E • 1) = 0 ↔ E ^ 2 = D ^ 2 + Delta ^ 2 := by
  rw [zornBdG_secular_poly]
  have h_sq : Delta * Delta = Delta ^ 2 := by ring
  rw [h_sq]
  exact sub_eq_zero

/-- Master synthesis packet for Stratum 38. -/
structure ZornBdGHamiltonianPacket (R : Type*) [CommRing R] where
  traceless : ∀ D Delta1 Delta2 : R, Matrix.trace (zornBdG D Delta1 Delta2) = 0
  pairing_anticommutes : ∀ Delta1 Delta2 : R, eta * zornPairing (R := R) Delta1 Delta2 + zornPairing Delta1 Delta2 * eta = 0
  dirac_commutes : ∀ D : R, eta * zornChiralDirac (R := R) D - zornChiralDirac D * eta = 0
  secular_energy_spectrum : ∀ D Delta E : R, det (zornBdG D Delta Delta - E • 1) = 0 ↔ E ^ 2 = D ^ 2 + Delta ^ 2

/-- Zero-debt constructor for Stratum 38 packet. -/
def makeZornBdGHamiltonianPacket (R : Type*) [CommRing R] : ZornBdGHamiltonianPacket R where
  traceless := zornBdG_trace_zero
  pairing_anticommutes := eta_pairing_anticomm
  dirac_commutes := eta_chiralDirac_comm
  secular_energy_spectrum := zornBdG_symmetric_secular

end InfoGeometry.Canonical.ZornBdGHamiltonianChiral
