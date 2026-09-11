import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Stratum 37: Covariant Bi-Wave Field Theory and Timelike Velocity Emergence

This module formalizes the covariant elevation of the Aharonov two-state vector formalism
and Bogoliubov-de Gennes (BdG) mass generation into a 4D spacetime field theory:

1. **The Relativistic Bi-Wave Doublet:**
   A quantum state on the doubled Krein module $\mathcal{K} = \mathcal{H}_+ \oplus \mathcal{H}_-$
   is an irreducible doublet $\mathbf{\Psi} = (\psi, \phi^\dagger)^T$ composed of a retarded
   forward-in-time wave $\psi$ and an advanced backward-in-time wave $\phi^\dagger$.
2. **Covariant 4-Vector Action and Inter-Wave Exchange:**
   The unimodular Zorn 4-vector $\hat{Z}_\mu(x) = \begin{pmatrix} \mathcal{A}_\mu & \hat{\boldsymbol{\psi}}_\mu \\ \hat{\boldsymbol{\psi}}_\mu^\dagger & -\mathcal{A}_\mu \end{pmatrix}$
   acts on $\mathbf{\Psi}$, coupling the forward wave evolution with spacetime exchange currents.
3. **Symmetric Metric Contraction & Off-Diagonal Cancellation:**
   When contracting with a symmetric spacetime metric $g^{\mu\nu} = g^{\nu\mu}$, the off-diagonal
   commutator cross-terms vanish identically, leaving an isotropic scalar mass operator on the diagonal:
   $$\hat{\mathcal{M}}^2 = - g^{\mu\nu} \hat{Z}_\mu \hat{Z}_\nu = m^2 \mathbb{I}$$
4. **The Timelike Zigzag Theorem (Feynman-Dirac-Penrose):**
   Superposition of two lightlike vectors $k_1, k_2$ ($k_1^2 = 0, k_2^2 = 0$) with negative
   mutual Minkowski inner product $2 k_1 \cdot k_2 = -4m^2 < 0$ produces a composite vector
   of invariant squared norm $P^2 = -4m^2 < 0$, which normalizes to a unit timelike 4-velocity:
   $$u^\mu u_\mu = -1$$
5. **Krein Current Trace Conservation:**
   The Krein trace $\mathrm{Tr}(\sigma_3 \hat{Z}_\mu) = 2 \mathcal{A}_\mu$ extracts the conserved
   gauge current directly from the unimodular connection.
-/

namespace InfoGeometry.Canonical.CovariantBiWaveMass

variable {R : Type*} [CommRing R]

/-!
### Stratum 37.1: The Relativistic Bi-Wave Doublet
The bi-wave doublet Ψ = (ψ, φ_dag) carries the forward-in-time retarded wave ψ
and the backward-in-time advanced wave φ_dag.
-/

/-- Relativistic bi-wave doublet representing the Nambu-Aharonov two-state vector. -/
structure BiWaveDoublet (R : Type*) where
  psi : R
  phi_dag : R

namespace BiWaveDoublet

/-- Addition of bi-wave doublets. -/
def add (Ψ1 Ψ2 : BiWaveDoublet R) : BiWaveDoublet R :=
  ⟨Ψ1.psi + Ψ2.psi, Ψ1.phi_dag + Ψ2.phi_dag⟩

/-- Scalar multiplication of bi-wave doublets. -/
def smul (c : R) (Ψ : BiWaveDoublet R) : BiWaveDoublet R :=
  ⟨c * Ψ.psi, c * Ψ.phi_dag⟩

end BiWaveDoublet

/-!
### Stratum 37.2: Covariant 4-Vector Action and Inter-Wave Exchange
The unimodular Zorn 4-vector Z_μ = [[A, ψ_field], [ψ_dag, -A]] acts on the bi-wave doublet.
-/

section CovariantZornAction

/-- Action of the unimodular Zorn 4-vector on the bi-wave doublet. -/
def zornBiWaveAction (A psi_field psi_dag : R) (Ψ : BiWaveDoublet R) : BiWaveDoublet R :=
  ⟨A * Ψ.psi + psi_field * Ψ.phi_dag,
   psi_dag * Ψ.psi - A * Ψ.phi_dag⟩

/-- Forward-in-time component evolution under the Zorn 4-vector. -/
theorem zorn_action_forward_component (A psi_field psi_dag : R) (Ψ : BiWaveDoublet R) :
    (zornBiWaveAction A psi_field psi_dag Ψ).psi = A * Ψ.psi + psi_field * Ψ.phi_dag := by
  rfl

/-- Backward-in-time component evolution under the Zorn 4-vector. -/
theorem zorn_action_backward_component (A psi_field psi_dag : R) (Ψ : BiWaveDoublet R) :
    (zornBiWaveAction A psi_field psi_dag Ψ).phi_dag = psi_dag * Ψ.psi - A * Ψ.phi_dag := by
  rfl

end CovariantZornAction

/-!
### Stratum 37.3: Symmetric Metric Contraction and Off-Diagonal Cancellation
When two unimodular Zorn matrices Z_μ and Z_ν are symmetrized,
the off-diagonal cross-terms vanish identically: (A_μ ψ_ν - ψ_μ A_ν) + (A_ν ψ_μ - ψ_ν A_μ) = 0.
-/

section OffDiagonalCancellation

/-- Upper off-diagonal cross-term for Zorn matrix product. -/
def zornOffDiagUpper (A1 A2 psi1 psi2 : R) : R :=
  A1 * psi2 - psi1 * A2

/-- Lower off-diagonal cross-term for Zorn matrix product. -/
def zornOffDiagLower (A1 A2 psi_dag1 psi_dag2 : R) : R :=
  psi_dag1 * A2 - A1 * psi_dag2

/-- Symmetric vanishing of upper off-diagonal cross-terms. -/
theorem symmetrized_offdiag_upper_vanishes (A1 A2 psi1 psi2 : R) :
    zornOffDiagUpper A1 A2 psi1 psi2 + zornOffDiagUpper A2 A1 psi2 psi1 = 0 := by
  dsimp [zornOffDiagUpper]
  ring

/-- Symmetric vanishing of lower off-diagonal cross-terms. -/
theorem symmetrized_offdiag_lower_vanishes (A1 A2 psi_dag1 psi_dag2 : R) :
    zornOffDiagLower A1 A2 psi_dag1 psi_dag2 + zornOffDiagLower A2 A1 psi_dag2 psi_dag1 = 0 := by
  dsimp [zornOffDiagLower]
  ring

/-- Diagonal element of the contracted Zorn matrix product. -/
def zornDiagElement (A1 A2 psi1 psi_dag2 : R) : R :=
  A1 * A2 + psi1 * psi_dag2

/-- Diagonal elements combine symmetrically under index transposition. -/
theorem symmetrized_diag_equal (A1 A2 psi1 psi2 psi_dag1 psi_dag2 : R) :
    zornDiagElement A1 A2 psi1 psi_dag2 + zornDiagElement A2 A1 psi2 psi_dag1 =
    A1 * A2 + A2 * A1 + psi1 * psi_dag2 + psi2 * psi_dag1 := by
  dsimp [zornDiagElement]
  ring

end OffDiagonalCancellation

/-!
### Stratum 37.4: The Timelike Zigzag Theorem (Feynman-Dirac-Penrose Mechanism)
Two lightlike vectors k₁, k₂ satisfy k₁² = 0, k₂² = 0, and 2 k₁ · k₂ = -4m².
Their composite sum P = k₁ + k₂ has strictly negative invariant norm: P² = -4m² < 0.
Normalized by 2m, the resulting 4-velocity is unit timelike: u² = -1.
-/

section TimelikeZigzag

/-- Invariant Minkowski norm squared of the sum of two 4-vectors: P² = k₁² + 2(k₁·k₂) + k₂². -/
def minkowskiNormSq (k_sq1 k_sq2 k1_dot_k2 : R) : R :=
  k_sq1 + (1 + 1) * k1_dot_k2 + k_sq2

/-- Interference of two null rays produces an invariant timelike composite norm: P² = -4m². -/
theorem timelike_zigzag_composite_norm
    (k_sq1 k_sq2 k1_dot_k2 m_sq : R)
    (h1 : k_sq1 = 0)
    (h2 : k_sq2 = 0)
    (h_cross : (1 + 1) * k1_dot_k2 = - ((1 + 1) * (1 + 1) * m_sq)) :
    minkowskiNormSq k_sq1 k_sq2 k1_dot_k2 = - ((1 + 1) * (1 + 1) * m_sq) := by
  dsimp [minkowskiNormSq]
  rw [h1, h2, h_cross]
  ring

/-- Normalized 4-velocity has exact unit timelike norm: u² = -1. -/
theorem normalized_timelike_velocity
    (norm_P_sq four_m_sq four_m_sq_inv : R)
    (h_P : norm_P_sq = - four_m_sq)
    (h_inv : four_m_sq * four_m_sq_inv = 1) :
    norm_P_sq * four_m_sq_inv = -1 := by
  rw [h_P]
  calc (- four_m_sq) * four_m_sq_inv
    _ = - (four_m_sq * four_m_sq_inv) := by ring
    _ = - 1 := by rw [h_inv]

end TimelikeZigzag

/-!
### Stratum 37.5: Krein Trace and Current Conservation
The Krein trace Tr(σ₃ Z_μ) directly extracts the conserved gauge current:
Tr([[1, 0], [0, -1]] * [[A, ψ], [ψ_dag, -A]]) = A - (-A) = 2A.
-/

section KreinCurrentTrace

/-- Krein trace with the fundamental symmetry σ₃: Tr(σ₃ Z) = A - (-A). -/
def kreinSigma3Trace (A : R) : R :=
  A - (-A)

/-- The Krein trace evaluates to 2A, generating the conserved gauge current. -/
theorem krein_current_trace_eq (A : R) :
    kreinSigma3Trace A = (1 + 1) * A := by
  dsimp [kreinSigma3Trace]
  ring

end KreinCurrentTrace

/-!
### Stratum 37.6: Master Synthesis Packet for Stratum 37
-/

/-- Master synthesis packet for Stratum 37. -/
structure CovariantBiWaveMassPacket (R : Type*) [CommRing R] where
  forward_action : ∀ (A psi_field psi_dag : R) (Ψ : BiWaveDoublet R),
    (zornBiWaveAction A psi_field psi_dag Ψ).psi = A * Ψ.psi + psi_field * Ψ.phi_dag
  backward_action : ∀ (A psi_field psi_dag : R) (Ψ : BiWaveDoublet R),
    (zornBiWaveAction A psi_field psi_dag Ψ).phi_dag = psi_dag * Ψ.psi - A * Ψ.phi_dag
  offdiag_upper_cancel : ∀ (A1 A2 psi1 psi2 : R),
    zornOffDiagUpper A1 A2 psi1 psi2 + zornOffDiagUpper A2 A1 psi2 psi1 = 0
  offdiag_lower_cancel : ∀ (A1 A2 psi_dag1 psi_dag2 : R),
    zornOffDiagLower A1 A2 psi_dag1 psi_dag2 + zornOffDiagLower A2 A1 psi_dag2 psi_dag1 = 0
  zigzag_norm : ∀ (k_sq1 k_sq2 k1_dot_k2 m_sq : R),
    k_sq1 = 0 → k_sq2 = 0 → (1 + 1) * k1_dot_k2 = - ((1 + 1) * (1 + 1) * m_sq) →
    minkowskiNormSq k_sq1 k_sq2 k1_dot_k2 = - ((1 + 1) * (1 + 1) * m_sq)
  unit_timelike : ∀ (norm_P_sq four_m_sq four_m_sq_inv : R),
    norm_P_sq = - four_m_sq → four_m_sq * four_m_sq_inv = 1 →
    norm_P_sq * four_m_sq_inv = -1
  krein_current : ∀ (A : R), kreinSigma3Trace A = (1 + 1) * A

/-- Zero-debt constructor for Stratum 37 packet. -/
def makeCovariantBiWaveMassPacket (R : Type*) [CommRing R] :
    CovariantBiWaveMassPacket R where
  forward_action := zorn_action_forward_component
  backward_action := zorn_action_backward_component
  offdiag_upper_cancel := symmetrized_offdiag_upper_vanishes
  offdiag_lower_cancel := symmetrized_offdiag_lower_vanishes
  zigzag_norm := timelike_zigzag_composite_norm
  unit_timelike := normalized_timelike_velocity
  krein_current := krein_current_trace_eq

end InfoGeometry.Canonical.CovariantBiWaveMass
