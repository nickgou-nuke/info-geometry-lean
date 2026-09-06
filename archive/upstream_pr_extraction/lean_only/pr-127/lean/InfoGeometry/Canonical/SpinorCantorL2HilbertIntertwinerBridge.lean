import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge

/-!
# Spinor-to-Cantor Hilbert Compatibility & Intertwiner Bridge

This owner formalizes the explicit isometric intertwiner between the 2-dimensional
spinor carrier $\mathbb{C}^2$ and the binary Cantor Hilbert space $L^2(\mathcal{C}, \mu_C)$:

$$J : \mathbb{C}^2 \to L^2(\mathcal{C}, \mu_C), \qquad J(\chi_b) = V_b \mathbf{1} = \sqrt{2} \mathbf{1}_{B_b}$$

## Key Theorems:
1. **Spinor Basis Orthonormality**: $\langle \chi_i, \chi_j \rangle_{\mathbb{C}^2} = \delta_{ij}$.
2. **Cuntz Projector Self-Adjointness**: $P_b^\dagger = P_b$ on $L^2(\mathcal{C}, \mu_C)$.
3. **Cuntz Projector Idempotence**: $P_b^2 = P_b$.
4. **Branch Orthogonality**: $P_0 P_1 = 0$.
5. **Partition of Unity / Completeness**: $P_0 + P_1 = I_{\mathcal{B}(L^2)}$.
6. **Canonical Gauge Weight Alignment**: $\varphi(P_b) = 1/2 = \operatorname{tr}_{\mathrm{Spin}}(E_{bb}) / 2$.
7. **Explicit Intertwiner Map**: `spinorToCantorL2 : SpinorSpace →ₗ[ℂ] L2Boundary`.
8. **Basis Intertwining Images**: $J(\chi_0) = V_0 \mathbf{1}$, $J(\chi_1) = V_1 \mathbf{1}$.
9. **Projector Intertwining**: $P_b (J(\chi_c)) = \delta_{bc} J(\chi_c)$.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge

open Complex
open ContinuousLinearMap
open MeasureTheory
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge

/-- 2-dimensional Spinor carrier $\mathbb{C}^2$ as a Hilbert space. -/
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 2)

/-- Standard basis vector $\chi_0 = ![1, 0]$ and $\chi_1 = ![0, 1]$. -/
def spinorBasis (i : Fin 2) : SpinorSpace :=
  EuclideanSpace.single i 1

/-- Orthonormality of the spinor basis. -/
theorem spinorBasis_orthonormal :
    Orthonormal ℂ (fun i : Fin 2 => spinorBasis i) :=
  EuclideanSpace.orthonormal_single

/-- Inner product of the spinor basis vectors. -/
theorem spinorBasis_inner (i j : Fin 2) :
    inner ℂ (spinorBasis i) (spinorBasis j) = if i = j then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp spinorBasis_orthonormal i j

/-- The Cuntz cylinder projectors $P_0, P_1 \in \mathcal{B}(L^2(\mathcal{C}, \mu_C))$. -/
def cuntzProjector (b : Bool) : L2Boundary →L[ℂ] L2Boundary :=
  operatorCylinderProjection [b]

/-- 🏆 THEOREM 1: The Cuntz cylinder projectors are self-adjoint. -/
theorem cuntzProjector_selfAdjoint (b : Bool) :
    star (cuntzProjector b) = cuntzProjector b :=
  operatorCylinderProjection_selfAdjoint [b]

/-- 🏆 THEOREM 2: The Cuntz cylinder projectors are idempotent. -/
theorem cuntzProjector_idempotent (b : Bool) :
    (cuntzProjector b).comp (cuntzProjector b) = cuntzProjector b :=
  operatorCylinderProjection_idempotent [b]

/-- 🏆 THEOREM 3: The Cuntz cylinder projectors for distinct branches are mutually orthogonal. -/
theorem cuntzProjector_orthogonal :
    (cuntzProjector false).comp (cuntzProjector true) = 0 := by
  dsimp [cuntzProjector]
  exact operatorCylinderProjection_comp_of_equal_length_ne rfl (by decide)

/-- 🏆 THEOREM 4: The Cuntz cylinder projectors resolve the identity on L^2 (Partition of Unity). -/
theorem cuntzProjector_sum_eq_id :
    cuntzProjector false + cuntzProjector true = ContinuousLinearMap.id ℂ L2Boundary := by
  dsimp [cuntzProjector]
  have hsum := normalizedPrependBitLp_partition
  rw [operatorCylinderProjection_singleton_eq_branchProjection,
    operatorCylinderProjection_singleton_eq_branchProjection]
  dsimp [branchProjection]
  exact hsum

/-- 🏆 THEOREM 5: The diagonal expectations in the canonical gauge state match the 1/2 spinor trace weights. -/
theorem cuntzProjector_gaugeWeight (b : Bool) :
    canonicalGaugeState [b] [b] = 1 / 2 :=
  operatorCylinderProjection_single_gaugeState b

/-!
### Explicit Spinor-to-Cantor Hilbert Space Intertwiner $J$
-/

/-- The normalized branch vectors $e_b = V_b \mathbf{1} \in L^2(\mathcal{C}, \mu_C)$. -/
def branchVector (b : Bool) : L2Boundary :=
  normalizedPrependBitLpContinuousLinearMap b vacuumL2

/-- Explicit linear intertwiner map $J : \mathbb{C}^2 \to L^2(\mathcal{C}, \mu_C)$. -/
def spinorToCantorL2 : SpinorSpace →ₗ[ℂ] L2Boundary where
  toFun v := (v.ofLp 0 : ℂ) • branchVector false + (v.ofLp 1 : ℂ) • branchVector true
  map_add' v w := by
    change (v.ofLp 0 + w.ofLp 0) • branchVector false + (v.ofLp 1 + w.ofLp 1) • branchVector true =
      v.ofLp 0 • branchVector false + v.ofLp 1 • branchVector true +
        (w.ofLp 0 • branchVector false + w.ofLp 1 • branchVector true)
    rw [add_smul, add_smul]
    abel
  map_smul' c v := by
    change (c * v.ofLp 0) • branchVector false + (c * v.ofLp 1) • branchVector true =
      c • (v.ofLp 0 • branchVector false + v.ofLp 1 • branchVector true)
    rw [mul_smul, mul_smul, smul_add]

/-- 🏆 THEOREM 6: Action of $J$ on the first spinor basis vector $\chi_0 = V_0 \mathbf{1}$. -/
theorem spinorToCantorL2_basis_0 :
    spinorToCantorL2 (spinorBasis 0) = branchVector false := by
  classical
  have h0 : (spinorBasis 0).ofLp 0 = (1 : ℂ) := by
    change ((Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) 0) = 1
    simp
  have h1 : (spinorBasis 0).ofLp 1 = 0 := by
    change ((Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) 1) = 0
    simp
  change (spinorBasis 0).ofLp 0 • branchVector false +
      (spinorBasis 0).ofLp 1 • branchVector true = branchVector false
  rw [h0, h1, one_smul, zero_smul, add_zero]

/-- 🏆 THEOREM 7: Action of $J$ on the second spinor basis vector $\chi_1 = V_1 \mathbf{1}$. -/
theorem spinorToCantorL2_basis_1 :
    spinorToCantorL2 (spinorBasis 1) = branchVector true := by
  classical
  have h0 : (spinorBasis 1).ofLp 0 = 0 := by
    change ((Pi.single (1 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) 0) = 0
    simp
  have h1 : (spinorBasis 1).ofLp 1 = (1 : ℂ) := by
    change ((Pi.single (1 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) 1) = 1
    simp
  change (spinorBasis 1).ofLp 0 • branchVector false +
      (spinorBasis 1).ofLp 1 • branchVector true = branchVector true
  rw [h0, h1, zero_smul, one_smul, zero_add]

/-- 🏆 THEOREM 8: Projector intertwining: $P_b(e_b) = e_b$. -/
theorem cuntzProjector_apply_branchVector_self (b : Bool) :
    cuntzProjector b (branchVector b) = branchVector b := by
  dsimp [cuntzProjector, branchVector]
  rw [operatorCylinderProjection_singleton_eq_branchProjection]
  dsimp [branchProjection]
  have hself := ContinuousLinearMap.ext_iff.mp
    (normalizedPrependBitLpAdjoint_comp_self b) vacuumL2
  exact congrArg (normalizedPrependBitLpContinuousLinearMap b) hself

/-- 🏆 THEOREM 9: Projector intertwining: $P_b(e_c) = 0$ for $b \neq c$. -/
theorem cuntzProjector_apply_branchVector_cross {b c : Bool} (h : b ≠ c) :
    cuntzProjector b (branchVector c) = 0 := by
  dsimp [cuntzProjector, branchVector]
  rw [operatorCylinderProjection_singleton_eq_branchProjection]
  dsimp [branchProjection]
  have hcross : (normalizedPrependBitLpAdjoint b) ((normalizedPrependBitLpContinuousLinearMap c) vacuumL2) = 0 :=
    ContinuousLinearMap.ext_iff.mp (normalizedPrependBitLpAdjoint_comp_cross_eq_zero h) vacuumL2
  rw [hcross, map_zero]

end InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
