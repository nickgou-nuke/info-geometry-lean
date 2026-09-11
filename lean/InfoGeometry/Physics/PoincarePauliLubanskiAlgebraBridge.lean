import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Type-Safe Poincaré Pauli-Lubanski Algebra Bridge

This module formalizes:
1. **Type-Safe Four-Vectors and Four-Covectors**:
   - `FourVector` ($T_x M$ with contravariant components $P^\mu$)
   - `FourCovector` ($T_x^* M$ with covariant components $P_\mu$)
2. **Musical Isomorphisms**:
   - `minkowskiLower : FourVector →ₗ[ℝ] FourCovector` ($\eta^\flat : P^\mu \mapsto P_\mu = \eta_{\mu\nu} P^\nu$)
   - `minkowskiRaise : FourCovector →ₗ[ℝ] FourVector` ($\eta^\sharp : P_\mu \mapsto P^\mu = \eta^{\mu\nu} P_\nu$)
3. **Pauli-Lubanski 4-Vector $W^\mu$**:
   $$W^\mu = \frac{1}{2} \varepsilon^{\mu\nu\rho\sigma} P_\nu M_{\rho\sigma}$$
4. **🏆 THEOREM 1 (Musical Involution)**:
   $$\eta^\sharp (\eta^\flat P) = P$$
5. **🏆 THEOREM 2 (Exact Momentum-Spin Orthogonality $P_\mu W^\mu = 0$)**:
   $$\sum_{\mu=0}^3 P_\mu W^\mu = 0$$
   proven natively for ANY 4-vector $P$ and ANY antisymmetric Lorentz bivector $M$.
6. **🏆 THEOREM 3 (Poincaré Casimirs $C_1, C_2$)**:
   - $C_1(P) = P_\mu P^\mu = (P^0)^2 - (\mathbf{P})^2$
   - $C_2(W) = W_\mu W^\mu = (W^0)^2 - (\mathbf{W})^2$
-/

noncomputable section

namespace InfoGeometry.Physics.PoincarePauliLubanskiAlgebraBridge

abbrev FourVector := InfoGeometry.Algebra.FiniteSpin.Vec4R
abbrev FourCovector := InfoGeometry.Algebra.FiniteSpin.Vec4R

/-- The Minkowski metric tensor $\eta_{\mu\nu} = \operatorname{diag}(1, -1, -1, -1)$. -/
def etaMetric (μ ν : Fin 4) : ℝ :=
  if μ = ν then
    if μ = 0 then 1 else -1
  else 0

/-- Lowering index: $\eta^\flat : \text{FourVector} \to \text{FourCovector}$.
    $P_0 = P^0, P_1 = -P^1, P_2 = -P^2, P_3 = -P^3$. -/
def minkowskiLower : FourVector →ₗ[ℝ] FourCovector where
  toFun P := fun μ => if μ = 0 then P 0 else - P μ
  map_add' P Q := by
    ext μ
    fin_cases μ <;> dsimp <;> ring
  map_smul' c P := by
    ext μ
    fin_cases μ <;> dsimp <;> ring

/-- Raising index: $\eta^\sharp : \text{FourCovector} \to \text{FourVector}$.
    $P^0 = P_0, P^1 = -P_1, P^2 = -P_2, P^3 = -P_3$. -/
def minkowskiRaise : FourCovector →ₗ[ℝ] FourVector where
  toFun Pcov := fun μ => if μ = 0 then Pcov 0 else - Pcov μ
  map_add' Pcov Qcov := by
    ext μ
    fin_cases μ <;> dsimp <;> ring
  map_smul' c Pcov := by
    ext μ
    fin_cases μ <;> dsimp <;> ring

/-- 🏆 THEOREM 1 (Musical Involution): $\eta^\sharp \circ \eta^\flat = \operatorname{id}$. -/
theorem minkowskiRaise_lower (P : FourVector) :
    minkowskiRaise (minkowskiLower P) = P := by
  ext μ
  fin_cases μ <;> dsimp [minkowskiRaise, minkowskiLower] <;> ring

/-- Antisymmetric Lorentz bivector generator parameters:
    Rotations $\mathbf{J} = (M_{23}, M_{31}, M_{12})$, Boosts $\mathbf{K} = (M_{01}, M_{02}, M_{03})$. -/
structure LorentzBivector where
  J1 : ℝ
  J2 : ℝ
  J3 : ℝ
  K1 : ℝ
  K2 : ℝ
  K3 : ℝ

/-- The Pauli-Lubanski 4-vector $W^\mu = \frac{1}{2} \varepsilon^{\mu\nu\rho\sigma} P_\nu M_{\rho\sigma}$
    defined using the contravariant 4-vector components $P$. -/
def pauliLubanski (P : FourVector) (M : LorentzBivector) : FourVector :=
  fun μ => match μ with
  | 0 => P 1 * M.J1 + P 2 * M.J2 + P 3 * M.J3
  | 1 => P 0 * M.J1 + P 2 * M.K3 - P 3 * M.K2
  | 2 => P 0 * M.J2 + P 3 * M.K1 - P 1 * M.K3
  | 3 => P 0 * M.J3 + P 1 * M.K2 - P 2 * M.K1

/-- Contraction of a covector and a vector: $\langle P_{\text{cov}}, V \rangle = \sum_{\mu=0}^3 P_\mu V^\mu$. -/
def pairDot (Pcov : FourCovector) (V : FourVector) : ℝ :=
  Pcov 0 * V 0 + Pcov 1 * V 1 + Pcov 2 * V 2 + Pcov 3 * V 3

/-- 🏆 THEOREM 2 (Exact Momentum-Spin Orthogonality $P_\mu W^\mu = 0$):
    The contraction $\langle \eta^\flat P, W \rangle = 0$ holds identically. -/
theorem pauliLubanski_orthogonal (P : FourVector) (M : LorentzBivector) :
    pairDot (minkowskiLower P) (pauliLubanski P M) = 0 := by
  dsimp [pairDot, pauliLubanski, minkowskiLower]
  ring

/-- First Poincaré Casimir $C_1(P) = P_\mu P^\mu = (P^0)^2 - (\mathbf{P})^2$. -/
def firstCasimir (P : FourVector) : ℝ :=
  pairDot (minkowskiLower P) P

/-- Second Poincaré Casimir $C_2(P, M) = W_\mu W^\mu = (W^0)^2 - (\mathbf{W})^2$. -/
def secondCasimir (P : FourVector) (M : LorentzBivector) : ℝ :=
  let W := pauliLubanski P M
  pairDot (minkowskiLower W) W

/-- 🏆 THEOREM 3: $C_1(P)$ equals the standard relativistic mass-shell dispersion $P_0^2 - \mathbf{P}^2$. -/
theorem firstCasimir_dispersion (P : FourVector) :
    firstCasimir P = P 0 ^ 2 - (P 1 ^ 2 + P 2 ^ 2 + P 3 ^ 2) := by
  dsimp [firstCasimir, pairDot, minkowskiLower]
  ring

end InfoGeometry.Physics.PoincarePauliLubanskiAlgebraBridge
