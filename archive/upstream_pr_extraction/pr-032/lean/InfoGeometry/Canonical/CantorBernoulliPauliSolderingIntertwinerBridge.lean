import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
import InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
import InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-!
# Cantor-Bernoulli Pauli Soldering and Spacetime Intertwiner Bridge

This owner module formalizes the canonical Pauli soldering map and its transport
onto the Cantor $L^2(\mathcal{C}, \mu_C)$ Hilbert carrier:

1. **Cantor Pauli Operator Basis $\Sigma_C^\mu$:**
   $$\Sigma_C^\mu = \pi_{\mathrm{Cuntz}}(\sigma^\mu) \in \mathcal{B}(L^2(\mathcal{C}, \mu_C))$$
   satisfying the exact intertwining relation $\Sigma_C^\mu (J x) = J (\sigma^\mu x)$.

2. **Cantor Soldering Map $\operatorname{solder}_C(P)$:**
   $$\operatorname{solder}_C(P) = \sum_{\mu=0}^3 P_\mu \Sigma_C^\mu = \pi_{\mathrm{Cuntz}}(\slashed{P})$$
   with $\operatorname{solder}_C(P) (J x) = J (\slashed{P} x)$.

3. **Minkowski Casimir & Inverse Pauli Trace:**
   - $\det(\slashed{P}) = E^2 - \mathbf{p}^2 = P_\mu P^\mu$.
   - $P_\mu = \frac{1}{2} \operatorname{Tr}(\sigma_\mu \slashed{P})$.

4. **Commuting Translation Generators on the Branch Sector:**
   - For scalar translation components $P_\mu$, the generators $P_\mu^C = P_\mu \cdot I_{\mathrm{branch}}$
     strictly commute: $[P_\mu^C, P_\nu^C] = 0$.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliPauliSolderingIntertwinerBridge

open Complex
open ContinuousLinearMap
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
open InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
open InfoGeometry.Physics.ChiralPoincareSouriauBridge

abbrev B := InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator
abbrev Spinor := CantorBernoulliPauliMatrixIntertwiner.SpinorSpace

/-- The four Pauli matrices in $M_2(\mathbb{C})$. -/
def pauliMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 1 => InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
  | 2 => InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ2
  | 3 => InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ3

/-- The Cantor Pauli operator basis $\Sigma_C^\mu \in \mathcal{B}(L^2(\mathcal{C}, \mu_C))$. -/
def pauliBasisCuntz (μ : Fin 4) : B :=
  pauliCuntzMatrixRepresentation (pauliMatrix μ)

/-- 🏆 THEOREM 1: The Cantor Pauli basis intertwines with the spinor Pauli action:
    $\Sigma_C^\mu (J x) = J (\sigma^\mu x)$. -/
theorem pauliBasisCuntz_intertwines (μ : Fin 4) (x : Spinor) :
    pauliBasisCuntz μ (spinorToCantorL2 x) =
      spinorToCantorL2 (Matrix.toEuclideanLin (pauliMatrix μ) x) := by
  dsimp [pauliBasisCuntz]
  exact pauliCuntzMatrixRepresentation_intertwines (pauliMatrix μ) x

/-- The Cantor soldering map $\operatorname{solder}_C(P) = \sum_{\mu=0}^3 P_\mu \Sigma_C^\mu$. -/
def cantorSolder (P : FourMomentum) : B :=
  P.E • pauliBasisCuntz 0 +
  P.px • pauliBasisCuntz 1 +
  P.py • pauliBasisCuntz 2 +
  P.pz • pauliBasisCuntz 3

/-- 🏆 THEOREM 2: The Cantor soldering map intertwines with the physical spinor action:
    $\operatorname{solder}_C(P) (J x) = J (\slashed{P} x)$. -/
theorem cantorSolder_intertwines (P : FourMomentum) (x : Spinor) :
    cantorSolder P (spinorToCantorL2 x) =
      spinorToCantorL2 (Matrix.toEuclideanLin (pauliMomentum P) x) := by
  dsimp [cantorSolder]
  simp only [pauliBasisCuntz_intertwines]
  simp only [← map_smul, ← map_add]
  congr 1
  ext i
  fin_cases i
  · simp [pauliMomentum, pauliMatrix, Matrix.toEuclideanLin, Matrix.vecHead, Matrix.vecTail,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ2,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ3]
    ring_nf
  · simp [pauliMomentum, pauliMatrix, Matrix.toEuclideanLin, Matrix.vecHead, Matrix.vecTail,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ2,
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ3]
    ring_nf

/-! The two existing Cantor momentum readouts have the same action on the
spinor-generated branch sector.  This is a range-level coherence statement,
not an equality of arbitrary operators on all of `L²`. -/

theorem cantorSolder_agrees_with_pauliCuntzMomentum_on_spinor
    (P : FourMomentum) (x : Spinor) :
    cantorSolder P (spinorToCantorL2 x) =
      pauliCuntzMomentumRepresentation P (spinorToCantorL2 x) := by
  calc
    cantorSolder P (spinorToCantorL2 x) =
        spinorToCantorL2 (Matrix.toEuclideanLin (pauliMomentum P) x) :=
      cantorSolder_intertwines P x
    _ = pauliCuntzMomentumRepresentation P (spinorToCantorL2 x) :=
      (pauliCuntzMomentumRepresentation_intertwines P x).symm

/-- 🏆 THEOREM 3: The determinant of the soldered matrix recovers the Minkowski Casimir:
    $\det(\slashed{P}) = E^2 - \mathbf{p}^2$. -/
theorem cantorSolder_determinant_minkowski (P : FourMomentum) :
    (pauliMomentum P).det = minkowskiSq P :=
  det_pauliMomentum P

/-- 🏆 THEOREM 4: Inverse Pauli trace recovers the four-momentum coordinates:
    $E = \operatorname{recoverE}(\slashed{P})$,
    $p_x = \operatorname{recoverPx}(\slashed{P})$,
    $p_y = \operatorname{recoverPy}(\slashed{P})$,
    $p_z = \operatorname{recoverPz}(\slashed{P})$. -/
theorem cantorSolder_inverse_pauli_trace (P : FourMomentum) :
    P.E = recoverE (pauliMomentum P) ∧
    P.px = recoverPx (pauliMomentum P) ∧
    P.py = recoverPy (pauliMomentum P) ∧
    P.pz = recoverPz (pauliMomentum P) := by
  refine ⟨(recoverE_pauliMomentum P).symm,
          (recoverPx_pauliMomentum P).symm,
          (recoverPy_pauliMomentum P).symm,
          (recoverPz_pauliMomentum P).symm⟩

/-!
### Commuting Momentum Generators on the Cantor Branch Sector
-/

/-- The identity projector on the 2-dimensional branch subspace. -/
def branchSectorIdentity : B :=
  singletonMatrixUnit 0 0 + singletonMatrixUnit 1 1

/-- The physical 4-momentum translation operator acting on the Cantor branch subspace.
    For a scalar component $P_\mu \in \mathbb{C}$, the translation generator acts
    on the spinor sector as scalar multiplication $P_\mu \cdot I_{\mathrm{branch}}$. -/
def cantorTranslationGenerator (Pμ : ℂ) : B :=
  Pμ • branchSectorIdentity

/-- 🏆 THEOREM 5: Cantor translation generators commute: $[P_\mu^C, P_\nu^C] = 0$. -/
theorem cantorTranslationGenerator_comm (Pμ Qν : ℂ) :
    cantorTranslationGenerator Pμ * cantorTranslationGenerator Qν -
    cantorTranslationGenerator Qν * cantorTranslationGenerator Pμ = 0 := by
  dsimp [cantorTranslationGenerator]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_smul, smul_smul, mul_comm Qν Pμ, sub_self]

/-! A four-momentum-indexed family of the preceding scalar branch-sector
    readouts.  This is an explicit commuting family, but it is deliberately
    not called a translation representation: no one-parameter group or
    infinitesimal/domain theorem is asserted here. -/
def fourMomentumComponent (P : FourMomentum) : Fin 4 → ℂ :=
  ![P.E, P.px, P.py, P.pz]

def cantorScalarMomentumFamily (P : FourMomentum) (μ : Fin 4) : B :=
  cantorTranslationGenerator (fourMomentumComponent P μ)

theorem cantorScalarMomentumFamily_comm (P Q : FourMomentum) (μ ν : Fin 4) :
    cantorScalarMomentumFamily P μ * cantorScalarMomentumFamily Q ν -
      cantorScalarMomentumFamily Q ν * cantorScalarMomentumFamily P μ = 0 := by
  simpa [cantorScalarMomentumFamily] using
    (cantorTranslationGenerator_comm
      (fourMomentumComponent P μ) (fourMomentumComponent Q ν))

end InfoGeometry.Canonical.CantorBernoulliPauliSolderingIntertwinerBridge
