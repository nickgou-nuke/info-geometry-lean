import Mathlib
import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.KK.RealSplitKreinHilbertizationBridge
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge

/-!
# Cl(5,5) Spinor Master Kasparov Cycle Bridge

This module establishes the matrix-level finite Kasparov cycle data on the 32D spinor carrier
`S_{5,5}` of `Cl(5,5)`, equipped with the master chirality grading `MasterChirality` and the
normalized master Hodge-Dirac operator `F = (1 / √3) • D_H`.

## Mathematical Content
1. `normalizedMasterHodgeDirac`: $F = \frac{1}{\sqrt{3}} D_H \in \mathrm{Mat}_{32}(\mathbb{R})$.
2. Exact involution property: $F^2 = 1$.
3. Transpose self-adjointness: $Fᵀ = F$ and $\Gammaᵀ = \Gamma$.
4. Exact chirality anti-commutation: $\{F, \Gamma\} = 0$, establishing that $F$ is an odd operator.
5. Exact $\mathfrak{g}_{2(2)}$ equivariance: $[X, F] = 0$ for all $X \in \mathfrak{g}_{2(2)}$.
6. Finite-dimensional Fredholm properties: since $F^2 = 1$, the defect $F^2 - 1 = 0$ vanishes identically.
-/

noncomputable section

namespace InfoGeometry.KK.RealCl55KasparovCycleBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge

abbrev Mat32 := InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.Mat32

/-- Normalized master Hodge-Dirac operator on the 32D spinor carrier S_{5,5}. -/
noncomputable def normalizedMasterHodgeDirac : Mat32 :=
  (1 / Real.sqrt 3) • embeddedSplitOctonionHodgeDirac

/-- The normalized master Hodge-Dirac operator is transpose self-adjoint. -/
theorem normalizedMasterHodgeDirac_transpose :
    normalizedMasterHodgeDiracᵀ = normalizedMasterHodgeDirac := by
  dsimp [normalizedMasterHodgeDirac]
  rw [Matrix.transpose_smul, embeddedSplitOctonionHodgeDirac_transpose]

/-- The normalized master Hodge-Dirac operator satisfies the exact involutive identity $F^2 = 1$. -/
theorem normalizedMasterHodgeDirac_sq :
    normalizedMasterHodgeDirac * normalizedMasterHodgeDirac = 1 := by
  dsimp [normalizedMasterHodgeDirac]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [embeddedSplitOctonionHodgeDirac_sq]
  rw [smul_smul]
  have hsqrt : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) * 3 = 1 := by
    have h3 : (Real.sqrt 3) * (Real.sqrt 3) = 3 := Real.mul_self_sqrt (by norm_num)
    calc
      (1 / Real.sqrt 3) * (1 / Real.sqrt 3) * 3 =
          (1 / (Real.sqrt 3 * Real.sqrt 3)) * 3 := by ring
      _ = (1 / 3) * 3 := by rw [h3]
      _ = 1 := by norm_num
  rw [hsqrt]
  exact one_smul ℝ 1

/-- The defect $F^2 - 1$ vanishes identically. -/
theorem normalizedMasterHodgeDirac_defect_zero :
    normalizedMasterHodgeDirac * normalizedMasterHodgeDirac - 1 = 0 := by
  rw [normalizedMasterHodgeDirac_sq, sub_self]

/-- The normalized master Hodge-Dirac operator anticommutes with the master chirality $\Gamma$. -/
theorem normalizedMasterHodgeDirac_anticomm_chirality :
    normalizedMasterHodgeDirac * MasterChirality +
      MasterChirality * normalizedMasterHodgeDirac = 0 := by
  dsimp [normalizedMasterHodgeDirac]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add]
  have h := masterChirality_anticomm_hodge
  rw [add_comm] at h
  rw [h, smul_zero]

/-- The normalized master Hodge-Dirac operator commutes with every $\mathfrak{g}_{2(2)}$ spinor generator. -/
theorem normalizedMasterHodgeDirac_commutes_g2 (g : G2SpinorRepresentation) :
    g.rho * normalizedMasterHodgeDirac =
      normalizedMasterHodgeDirac * g.rho := by
  dsimp [normalizedMasterHodgeDirac]
  rw [mul_smul_comm, smul_mul_assoc]
  rw [g.commutes_hodge]

/-- The commutator $[X, F]$ vanishes identically for any $\mathfrak{g}_{2(2)}$ generator. -/
theorem normalizedMasterHodgeDirac_comm_g2_zero (g : G2SpinorRepresentation) :
    g.rho * normalizedMasterHodgeDirac - normalizedMasterHodgeDirac * g.rho = 0 := by
  rw [normalizedMasterHodgeDirac_commutes_g2 g, sub_self]

/--
Finite matrix-level Kasparov datum on the 32D spinor carrier $S_{5,5}$.
Packages the master chirality grading $\Gamma$, the involutive Hodge-Dirac phase $F$,
and the infinitesimal $\mathfrak{g}_{2(2)}$ intertwining relations.
-/
structure Cl55MasterKasparovDatum where
  gamma : Mat32
  F : Mat32
  gamma_sq : gamma * gamma = 1
  F_sq : F * F = 1
  gamma_transpose : gammaᵀ = gamma
  F_transpose : Fᵀ = F
  anticomm : F * gamma + gamma * F = 0
  g2_comm_gamma : ∀ g : G2SpinorRepresentation, g.rho * gamma = gamma * g.rho
  g2_comm_F : ∀ g : G2SpinorRepresentation, g.rho * F = F * g.rho

/-- The canonical master Kasparov datum on $S_{5,5}$. -/
noncomputable def canonicalCl55MasterKasparovDatum : Cl55MasterKasparovDatum where
  gamma := MasterChirality
  F := normalizedMasterHodgeDirac
  gamma_sq := masterChirality_sq
  F_sq := normalizedMasterHodgeDirac_sq
  gamma_transpose := masterChirality_transpose
  F_transpose := normalizedMasterHodgeDirac_transpose
  anticomm := normalizedMasterHodgeDirac_anticomm_chirality
  g2_comm_gamma g := g.even_parity
  g2_comm_F g := normalizedMasterHodgeDirac_commutes_g2 g

end InfoGeometry.KK.RealCl55KasparovCycleBridge
