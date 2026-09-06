import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Physics.PoincareLieAlgebraCapstoneBridge
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge

/-!
# Split-Octonion Poincaré Casimir and Pauli-Lubański Bridge

This owner module formalizes the exact connection between split-octonion geometry,
the four relativistic carriers ($T_x M, T_x^* M, P^\mu, W^\mu$), and the two Poincaré Casimirs:

1. **Pre-Metric Witt Carrier as $TM \oplus T^*M \cong \mathbb{R}^{4,4}$:**
   The four Witt pairs $(\sigma_\mu^+, \sigma_\mu^-)$ model vector and covector directions
   with canonical neutral pairing $N(X) = \frac{1}{2}(\xi(Y) + \eta(X))$.

2. **First Poincaré Casimir $C_1$ (Mass Shell):**
   $$C_1 = P_\mu P^\mu = \det(\slashed{P}) = N(X_{\mathrm{sym}})$$
   - $N = 0 \iff P^2 = 0$ (massless lightcone).
   - $N = m^2 \iff P^2 = m^2$ (massive relativistic hyperboloid).

3. **Pauli-Lubański Spin Pseudovector $W^\mu$:**
   $$W^\mu = \frac{1}{2} \epsilon^{\mu\nu\rho\sigma} P_\nu M_{\rho\sigma}$$
   representing the Hodge dual $W = *(P \wedge M)$.

4. **Orthogonality of Momentum and Spin:**
   $$P_\mu W^\mu = 0$$
   proved algebraically from the contraction of symmetric $P_\mu P_\nu$ with $\epsilon^{\mu\nu\rho\sigma}$.

5. **Second Poincaré Casimir substrate:**
   The finite spin-Casimir readout is supplied by the Pauli--Lubanski vector;
   representation-theoretic massive/massless classification is intentionally
   left downstream.
-/

noncomputable section

namespace InfoGeometry.Physics.SplitOctonionPoincareCasimirBridge

open Complex
open Matrix
open InfoGeometry.Physics.PoincareLieAlgebraCapstoneBridge
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Quantum.PauliSoldering

/-- Completely antisymmetric 4-tensor $\epsilon^{\mu\nu\rho\sigma}$ representing the 4D Levi-Civita volume form. -/
structure AntisymmetricTensor4 where
  val : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ
  antisymm_12 : ∀ μ ν ρ σ, val μ ν ρ σ = - val ν μ ρ σ
  antisymm_23 : ∀ μ ν ρ σ, val μ ν ρ σ = - val μ ρ ν σ
  antisymm_34 : ∀ μ ν ρ σ, val μ ν σ ρ = - val μ ν ρ σ

/-- Pauli--Lubanski readout for a supplied momentum, bivector, and volume
tensor.  The normalization is the conventional factor `1/2`. -/
def pauliLubanski (ε : AntisymmetricTensor4) (P : Fin 4 → ℝ)
    (M : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
    ε.val μ ν ρ σ * P ν * M ρ σ

@[simp] theorem pauliLubanski_apply (ε : AntisymmetricTensor4) (P : Fin 4 → ℝ)
    (M : Fin 4 → Fin 4 → ℝ) (μ : Fin 4) :
    pauliLubanski ε P M μ =
      (1 / 2 : ℝ) * ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        ε.val μ ν ρ σ * P ν * M ρ σ :=
  rfl

/-- 🏆 THEOREM 1: First Casimir is identical to the split-octonion symmetric fixed-section norm:
    $C_1(P) = \det(\slashed{P}) = N(X_{\mathrm{sym}})$. -/
theorem casimir1_eq_splitOctonion_fixed_norm (t x0 x1 x2 : ℝ) :
    (solder ((t : ℂ), (x0 : ℂ), (x1 : ℂ), (x2 : ℂ))).det =
      (wittNorm (symmSection t x0 x1 x2) : ℂ) := by
  exact solder_det_eq_wittNorm_symm t x0 x1 x2

/-- 🏆 THEOREM 2: Contraction of symmetric momentum product with antisymmetric Levi-Civita tensor vanishes:
    $\sum_{\mu, \nu} \epsilon^{\mu\nu\rho\sigma} P_\mu P_\nu = 0$. -/
theorem antisymmetric_symmetric_contraction (ε : AntisymmetricTensor4) (P : Fin 4 → ℝ) (ρ σ : Fin 4) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) = 0 := by
  have h_pair : ∀ μ ν, ε.val μ ν ρ σ * (P μ * P ν) + ε.val ν μ ρ σ * (P ν * P μ) = 0 := by
    intro μ ν
    rw [ε.antisymm_12 μ ν ρ σ]
    have hcomm : P ν * P μ = P μ * P ν := mul_comm (P ν) (P μ)
    rw [hcomm]
    ring
  have h_sum : (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) =
      (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val ν μ ρ σ * (P ν * P μ)) := by
    rw [Finset.sum_comm]
  have h_double : 2 * (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) = 0 := by
    calc
      2 * (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν))
        = (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) +
          (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) := by ring
      _ = (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) +
          (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val ν μ ρ σ * (P ν * P μ)) := by rw [h_sum]
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, (ε.val μ ν ρ σ * (P μ * P ν) + ε.val ν μ ρ σ * (P ν * P μ)) := by
        simp only [← Finset.sum_add_distrib]
      _ = ∑ μ : Fin 4, ∑ ν : Fin 4, (0 : ℝ) := by
        simp only [h_pair]
      _ = 0 := by simp
  linarith

/-- 🏆 THEOREM 3: Orthogonality of Pauli-Lubański vector and four-momentum:
    $P_\mu W^\mu = \frac{1}{2} \epsilon^{\mu\nu\rho\sigma} P_\mu P_\nu M_{\rho\sigma} = 0$. -/
theorem pauliLubanski_orthogonal_momentum (ε : AntisymmetricTensor4) (P : Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ) :
    (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ε.val μ ν ρ σ * (P μ * P ν) * M ρ σ) = 0 := by
  have h_inner : ∀ ρ σ, (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν) * M ρ σ) = 0 := by
    intro ρ σ
    calc
      (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν) * M ρ σ)
        = (∑ μ : Fin 4, ∑ ν : Fin 4, ε.val μ ν ρ σ * (P μ * P ν)) * M ρ σ := by
          simp only [← Finset.sum_mul]
      _ = 0 * M ρ σ := by rw [antisymmetric_symmetric_contraction ε P ρ σ]
      _ = 0 := by ring
  calc
    (∑ ρ : Fin 4, ∑ σ : Fin 4, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ε.val μ ν ρ σ * (P μ * P ν) * M ρ σ)
      = ∑ ρ : Fin 4, ∑ σ : Fin 4, (0 : ℝ) := by
        simp only [h_inner]
    _ = 0 := by simp

end InfoGeometry.Physics.SplitOctonionPoincareCasimirBridge
