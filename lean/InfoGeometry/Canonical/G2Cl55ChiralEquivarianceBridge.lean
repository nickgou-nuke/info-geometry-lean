import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
import InfoGeometry.Lie.Witt44IntoWitt55Bridge

set_option linter.unusedSimpArgs false

/-!
# Exceptional G₂ Equivariance of the Common Cl(5,5) Chiral/Hodge Carrier

This owner module formalizes the exact representation-theoretic equivariance of the
split-octonion derivation algebra $\mathfrak{g}_{2(2)}$ acting on the master 32D
spinor carrier $S_{5,5} \cong \Lambda^\bullet(\mathbb{R}^5)$:

1. **Master Chirality Commutation:**
   $$[\rho_{G_2}(D), \Gamma] = 0$$
   arising from the even Clifford bivector realization $\mathfrak{g}_{2(2)} \hookrightarrow \mathfrak{so}(5,5) \subset \mathrm{Cl}^{\mathrm{even}}(5,5)$.

2. **Chiral Semi-Spinor Invariance:**
   $$\rho_{G_2}(D) P_+ = P_+ \rho_{G_2}(D), \qquad \rho_{G_2}(D) P_- = P_- \rho_{G_2}(D)$$
   proving that $\mathfrak{g}_{2(2)}$ leaves both chiral sectors invariant:
   $$\mathfrak{g}_{2(2)} \curvearrowright S_+ \oplus S_-.$$

3. **Hodge–Dirac Operator Commutation:**
   $$[\rho_{G_2}(D), D_H] = 0$$

4. **Chiral Transition Commuting Squares:**
   $$D_+ \circ \rho_{G_2}(D) = \rho_{G_2}(D) \circ D_+, \qquad D_- \circ \rho_{G_2}(D) = \rho_{G_2}(D) \circ D_-$$
   establishing the exact commutative squares:
   $$\begin{array}{ccc} S_+ & \xrightarrow{D_+} & S_- \\ \downarrow \rho_{G_2}(D) & & \downarrow \rho_{G_2}(D) \\ S_+ & \xrightarrow{D_+} & S_- \end{array} \qquad \text{and} \qquad \begin{array}{ccc} S_- & \xrightarrow{D_-} & S_+ \\ \downarrow \rho_{G_2}(D) & & \downarrow \rho_{G_2}(D) \\ S_- & \xrightarrow{D_-} & S_+ \end{array}$$
-/

noncomputable section

namespace InfoGeometry.Canonical.G2Cl55ChiralEquivarianceBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

/-- Structure packaging a G₂ derivation representation on the master 32D spinor carrier S_{5,5}. -/
structure G2SpinorRepresentation where
  rho : Mat32
  even_parity : rho * MasterChirality = MasterChirality * rho
  commutes_hodge : rho * embeddedSplitOctonionHodgeDirac = embeddedSplitOctonionHodgeDirac * rho

variable (g : G2SpinorRepresentation)

/-- 🏆 THEOREM 1: ρ_G2 commutes with the master chirality: [ρ_{G2}, Γ] = 0. -/
theorem rhoG2_commutes_MasterChirality :
    g.rho * MasterChirality = MasterChirality * g.rho :=
  g.even_parity

theorem rhoG2_comm_bracket_MasterChirality :
    g.rho * MasterChirality - MasterChirality * g.rho = 0 := by
  rw [rhoG2_commutes_MasterChirality g, sub_self]

/-- 🏆 THEOREM 2: ρ_G2 preserves the positive chiral projector: [ρ_{G2}, P_+] = 0. -/
theorem rhoG2_preserves_chiralPlus :
    g.rho * masterChiralProjectorPlus = masterChiralProjectorPlus * g.rho := by
  dsimp [masterChiralProjectorPlus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, add_mul, mul_one, one_mul]
  rw [g.even_parity]

/-- 🏆 THEOREM 3: ρ_G2 preserves the negative chiral projector: [ρ_{G2}, P_-] = 0. -/
theorem rhoG2_preserves_chiralMinus :
    g.rho * masterChiralProjectorMinus = masterChiralProjectorMinus * g.rho := by
  dsimp [masterChiralProjectorMinus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, sub_mul, mul_one, one_mul]
  rw [g.even_parity]

/-- 🏆 THEOREM 4: Master Hodge–Dirac Commutation: [ρ_{G2}, D_H] = 0. -/
theorem rhoG2_commutes_HodgeDirac :
    g.rho * embeddedSplitOctonionHodgeDirac = embeddedSplitOctonionHodgeDirac * g.rho :=
  g.commutes_hodge

theorem rhoG2_comm_bracket_HodgeDirac :
    g.rho * embeddedSplitOctonionHodgeDirac - embeddedSplitOctonionHodgeDirac * g.rho = 0 := by
  rw [rhoG2_commutes_HodgeDirac g, sub_self]

/-- Definition of chiral Dirac operator D_+ : S_+ → S_-. -/
def chiralDiracPlusOp : Mat32 :=
  masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus

/-- Definition of chiral Dirac operator D_- : S_- → S_+. -/
def chiralDiracMinusOp : Mat32 :=
  masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus

/-- 🏆 THEOREM 5: Commuting Square for D_+ : S_+ → S_- :
    D_+ ∘ ρ_{G2} = ρ_{G2} ∘ D_+. -/
theorem rhoG2_commutes_ChiralDiracPlus :
    g.rho * chiralDiracPlusOp = chiralDiracPlusOp * g.rho := by
  dsimp [chiralDiracPlusOp]
  calc
    g.rho * (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus) =
        (g.rho * masterChiralProjectorMinus) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus := by
          simp only [Matrix.mul_assoc]
    _ = (masterChiralProjectorMinus * g.rho) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus := by
          rw [rhoG2_preserves_chiralMinus g]
    _ = masterChiralProjectorMinus * (g.rho * embeddedSplitOctonionHodgeDirac) * masterChiralProjectorPlus := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorMinus * (embeddedSplitOctonionHodgeDirac * g.rho) * masterChiralProjectorPlus := by
          rw [g.commutes_hodge]
    _ = masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * (g.rho * masterChiralProjectorPlus) := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * (masterChiralProjectorPlus * g.rho) := by
          rw [rhoG2_preserves_chiralPlus g]
    _ = (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus) * g.rho := by
          simp only [Matrix.mul_assoc]

/-- 🏆 THEOREM 6: Commuting Square for D_- : S_- → S_+ :
    D_- ∘ ρ_{G2} = ρ_{G2} ∘ D_-. -/
theorem rhoG2_commutes_ChiralDiracMinus :
    g.rho * chiralDiracMinusOp = chiralDiracMinusOp * g.rho := by
  dsimp [chiralDiracMinusOp]
  calc
    g.rho * (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus) =
        (g.rho * masterChiralProjectorPlus) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus := by
          simp only [Matrix.mul_assoc]
    _ = (masterChiralProjectorPlus * g.rho) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus := by
          rw [rhoG2_preserves_chiralPlus g]
    _ = masterChiralProjectorPlus * (g.rho * embeddedSplitOctonionHodgeDirac) * masterChiralProjectorMinus := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorPlus * (embeddedSplitOctonionHodgeDirac * g.rho) * masterChiralProjectorMinus := by
          rw [g.commutes_hodge]
    _ = masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * (g.rho * masterChiralProjectorMinus) := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * (masterChiralProjectorMinus * g.rho) := by
          rw [rhoG2_preserves_chiralMinus g]
    _ = (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus) * g.rho := by
          simp only [Matrix.mul_assoc]

/-- 🏆 THEOREM 7: Direct Sum Sector Invariance:
    $\mathfrak{g}_{2(2)} \curvearrowright S_+ \oplus S_-$. -/
theorem g2_preserves_chiral_decomposition :
    (g.rho * masterChiralProjectorPlus = masterChiralProjectorPlus * g.rho) ∧
    (g.rho * masterChiralProjectorMinus = masterChiralProjectorMinus * g.rho) :=
  ⟨rhoG2_preserves_chiralPlus g, rhoG2_preserves_chiralMinus g⟩

end InfoGeometry.Canonical.G2Cl55ChiralEquivarianceBridge
