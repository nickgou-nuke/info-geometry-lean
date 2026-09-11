import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
import InfoGeometry.Lie.Witt44IntoWitt55Bridge

set_option linter.unusedSimpArgs false

/-!
# Exceptional G₂ Equivariance of the Common Cl(5,5) Chiral/Hodge Carrier

This owner module packages the representation-theoretic equivariance data needed
for a split-octonion derivation action on the master 32D spinor carrier
$S_{5,5} \cong \Lambda^\bullet(\mathbb{R}^5)$.  The native
`Der(O_s) → so(5,5)` to spinor-lift identification is deliberately not asserted
here; it is a separate composition theorem.

1. **Master Chirality Commutation:**
   $$[\rho_{G_2}(D), \Gamma] = 0$$
   supplied as an explicit commuting constraint on the packaged representation.

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

namespace InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge

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

def g2SpinorBracket (g h : G2SpinorRepresentation) : G2SpinorRepresentation where
  rho := g.rho * h.rho - h.rho * g.rho
  even_parity := by
    have hg := g.even_parity
    have hh := h.even_parity
    calc
      (g.rho * h.rho - h.rho * g.rho) * MasterChirality =
          g.rho * (h.rho * MasterChirality) - h.rho * (g.rho * MasterChirality) := by
            simp only [Matrix.sub_mul, Matrix.mul_assoc]
      _ = g.rho * (MasterChirality * h.rho) - h.rho * (MasterChirality * g.rho) := by
            rw [hh, hg]
      _ = (g.rho * MasterChirality) * h.rho - (h.rho * MasterChirality) * g.rho := by
            simp only [Matrix.mul_assoc]
      _ = (MasterChirality * g.rho) * h.rho - (MasterChirality * h.rho) * g.rho := by
            rw [hg, hh]
      _ = MasterChirality * (g.rho * h.rho - h.rho * g.rho) := by
            simp only [Matrix.mul_sub, Matrix.mul_assoc]
  commutes_hodge := by
    have hg := g.commutes_hodge
    have hh := h.commutes_hodge
    calc
      (g.rho * h.rho - h.rho * g.rho) * embeddedSplitOctonionHodgeDirac =
          g.rho * (h.rho * embeddedSplitOctonionHodgeDirac) -
            h.rho * (g.rho * embeddedSplitOctonionHodgeDirac) := by
            simp only [Matrix.sub_mul, Matrix.mul_assoc]
      _ = g.rho * (embeddedSplitOctonionHodgeDirac * h.rho) -
            h.rho * (embeddedSplitOctonionHodgeDirac * g.rho) := by
            rw [hh, hg]
      _ = (g.rho * embeddedSplitOctonionHodgeDirac) * h.rho -
            (h.rho * embeddedSplitOctonionHodgeDirac) * g.rho := by
            simp only [Matrix.mul_assoc]
      _ = (embeddedSplitOctonionHodgeDirac * g.rho) * h.rho -
            (embeddedSplitOctonionHodgeDirac * h.rho) * g.rho := by
            rw [hg, hh]
      _ = embeddedSplitOctonionHodgeDirac * (g.rho * h.rho - h.rho * g.rho) := by
            simp only [Matrix.mul_sub, Matrix.mul_assoc]

@[simp] theorem g2SpinorBracket_rho (g h : G2SpinorRepresentation) :
    (g2SpinorBracket g h).rho = g.rho * h.rho - h.rho * g.rho := rfl

/-! The two commuting constraints form a genuine Lie subalgebra of the
spinor matrix algebra.  This packages the closure proved above without
identifying it with the image of the native octonion derivations. -/

def g2SpinorLieSubalgebra : LieSubalgebra ℝ Mat32 where
  carrier := {A | A * MasterChirality = MasterChirality * A ∧
    A * embeddedSplitOctonionHodgeDirac = embeddedSplitOctonionHodgeDirac * A}
  zero_mem' := by
    constructor <;> simp
  add_mem' := by
    intro A B hA hB
    constructor
    · calc
        (A + B) * MasterChirality = A * MasterChirality + B * MasterChirality := by
          rw [add_mul]
        _ = MasterChirality * A + MasterChirality * B := by rw [hA.1, hB.1]
        _ = MasterChirality * (A + B) := by rw [mul_add]
    · calc
        (A + B) * embeddedSplitOctonionHodgeDirac =
            A * embeddedSplitOctonionHodgeDirac +
              B * embeddedSplitOctonionHodgeDirac := by rw [add_mul]
        _ = embeddedSplitOctonionHodgeDirac * A +
              embeddedSplitOctonionHodgeDirac * B := by rw [hA.2, hB.2]
        _ = embeddedSplitOctonionHodgeDirac * (A + B) := by rw [mul_add]
  smul_mem' := by
    intro r A hA
    constructor
    · calc
        (r • A) * MasterChirality = r • (A * MasterChirality) := by
          rw [smul_mul_assoc]
        _ = r • (MasterChirality * A) := by rw [hA.1]
        _ = MasterChirality * (r • A) := by rw [mul_smul_comm]
    · calc
        (r • A) * embeddedSplitOctonionHodgeDirac =
            r • (A * embeddedSplitOctonionHodgeDirac) := by
          rw [smul_mul_assoc]
        _ = r • (embeddedSplitOctonionHodgeDirac * A) := by rw [hA.2]
        _ = embeddedSplitOctonionHodgeDirac * (r • A) := by
          rw [mul_smul_comm]
  lie_mem' := by
    intro A B hA hB
    change (A * MasterChirality = MasterChirality * A ∧
      A * embeddedSplitOctonionHodgeDirac = embeddedSplitOctonionHodgeDirac * A) at hA
    change (B * MasterChirality = MasterChirality * B ∧
      B * embeddedSplitOctonionHodgeDirac = embeddedSplitOctonionHodgeDirac * B) at hB
    constructor
    · change (A * B - B * A) * MasterChirality =
        MasterChirality * (A * B - B * A)
      calc
        (A * B - B * A) * MasterChirality =
            A * (B * MasterChirality) - B * (A * MasterChirality) := by
          simp only [sub_mul, Matrix.mul_assoc]
        _ = A * (MasterChirality * B) - B * (MasterChirality * A) := by
          rw [hB.1, hA.1]
        _ = (A * MasterChirality) * B - (B * MasterChirality) * A := by
          simp only [Matrix.mul_assoc]
        _ = (MasterChirality * A) * B - (MasterChirality * B) * A := by
          rw [hA.1, hB.1]
        _ = MasterChirality * (A * B - B * A) := by
          simp only [mul_sub, Matrix.mul_assoc]
    · change (A * B - B * A) * embeddedSplitOctonionHodgeDirac =
        embeddedSplitOctonionHodgeDirac * (A * B - B * A)
      calc
        (A * B - B * A) * embeddedSplitOctonionHodgeDirac =
            A * (B * embeddedSplitOctonionHodgeDirac) -
              B * (A * embeddedSplitOctonionHodgeDirac) := by
          simp only [sub_mul, Matrix.mul_assoc]
        _ = A * (embeddedSplitOctonionHodgeDirac * B) -
              B * (embeddedSplitOctonionHodgeDirac * A) := by
          rw [hB.2, hA.2]
        _ = (A * embeddedSplitOctonionHodgeDirac) * B -
              (B * embeddedSplitOctonionHodgeDirac) * A := by
          simp only [Matrix.mul_assoc]
        _ = (embeddedSplitOctonionHodgeDirac * A) * B -
              (embeddedSplitOctonionHodgeDirac * B) * A := by
          rw [hA.2, hB.2]
        _ = embeddedSplitOctonionHodgeDirac *
              (A * B - B * A) := by
          simp only [mul_sub, Matrix.mul_assoc]

theorem g2SpinorRepresentation_mem_subalgebra (g : G2SpinorRepresentation) :
    g.rho ∈ g2SpinorLieSubalgebra := by
  exact ⟨g.even_parity, g.commutes_hodge⟩

theorem g2SpinorBracket_mem_subalgebra
    (g h : G2SpinorRepresentation) :
    (g2SpinorBracket g h).rho ∈ g2SpinorLieSubalgebra := by
  exact g2SpinorRepresentation_mem_subalgebra (g2SpinorBracket g h)

variable (g : G2SpinorRepresentation)

/-- 🏆 THEOREM 1: ρ_G2 commutes with the master chirality: [ρ_{G2}, Γ] = 0. -/
theorem g2Spin_commutes_masterChirality :
    g.rho * MasterChirality = MasterChirality * g.rho :=
  g.even_parity

theorem g2Spin_comm_bracket_masterChirality :
    g.rho * MasterChirality - MasterChirality * g.rho = 0 := by
  rw [g2Spin_commutes_masterChirality g, sub_self]

/-- 🏆 THEOREM 2: ρ_G2 preserves the positive chiral projector: [ρ_{G2}, P_+] = 0. -/
theorem g2Spin_preserves_chiralPlus :
    g.rho * masterChiralProjectorPlus = masterChiralProjectorPlus * g.rho := by
  dsimp [masterChiralProjectorPlus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, add_mul, mul_one, one_mul]
  rw [g.even_parity]

/-- 🏆 THEOREM 3: ρ_G2 preserves the negative chiral projector: [ρ_{G2}, P_-] = 0. -/
theorem g2Spin_preserves_chiralMinus :
    g.rho * masterChiralProjectorMinus = masterChiralProjectorMinus * g.rho := by
  dsimp [masterChiralProjectorMinus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, sub_mul, mul_one, one_mul]
  rw [g.even_parity]

/-- 🏆 THEOREM 4: Master Hodge–Dirac Commutation: [ρ_{G2}, D_H] = 0. -/
theorem g2Spin_commutes_masterHodgeDirac :
    g.rho * embeddedSplitOctonionHodgeDirac = embeddedSplitOctonionHodgeDirac * g.rho :=
  g.commutes_hodge

def g2SpinorRepresentationOfSubalgebra
    (A : g2SpinorLieSubalgebra) : G2SpinorRepresentation where
  rho := A
  even_parity := A.property.1
  commutes_hodge := A.property.2

@[simp] theorem g2SpinorRepresentationOfSubalgebra_rho
    (A : g2SpinorLieSubalgebra) :
    (g2SpinorRepresentationOfSubalgebra A).rho = A := rfl

theorem g2SpinorSubalgebra_preserves_chiralPlus
    (A : g2SpinorLieSubalgebra) :
    (A : Mat32) * masterChiralProjectorPlus =
      masterChiralProjectorPlus * (A : Mat32) := by
  exact g2Spin_preserves_chiralPlus (g2SpinorRepresentationOfSubalgebra A)

theorem g2SpinorSubalgebra_preserves_chiralMinus
    (A : g2SpinorLieSubalgebra) :
    (A : Mat32) * masterChiralProjectorMinus =
      masterChiralProjectorMinus * (A : Mat32) := by
  exact g2Spin_preserves_chiralMinus (g2SpinorRepresentationOfSubalgebra A)

theorem g2SpinorSubalgebra_commutes_hodgeDirac
    (A : g2SpinorLieSubalgebra) :
    (A : Mat32) * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * (A : Mat32) := by
  exact g2Spin_commutes_masterHodgeDirac (g2SpinorRepresentationOfSubalgebra A)

theorem g2Spin_comm_bracket_masterHodgeDirac :
    g.rho * embeddedSplitOctonionHodgeDirac - embeddedSplitOctonionHodgeDirac * g.rho = 0 := by
  rw [g2Spin_commutes_masterHodgeDirac g, sub_self]

/-- Definition of chiral Dirac operator D_+ : S_+ → S_-. -/
def chiralDiracPlusOp : Mat32 :=
  masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus

/-- Definition of chiral Dirac operator D_- : S_- → S_+. -/
def chiralDiracMinusOp : Mat32 :=
  masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus

/-- 🏆 THEOREM 5: Commuting Square for D_+ : S_+ → S_- :
    D_+ ∘ ρ_{G2} = ρ_{G2} ∘ D_+. -/
theorem g2Spin_commutes_chiralDiracPlus :
    g.rho * chiralDiracPlusOp = chiralDiracPlusOp * g.rho := by
  dsimp [chiralDiracPlusOp]
  calc
    g.rho * (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus) =
        (g.rho * masterChiralProjectorMinus) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus := by
          simp only [Matrix.mul_assoc]
    _ = (masterChiralProjectorMinus * g.rho) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus := by
          rw [g2Spin_preserves_chiralMinus g]
    _ = masterChiralProjectorMinus * (g.rho * embeddedSplitOctonionHodgeDirac) * masterChiralProjectorPlus := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorMinus * (embeddedSplitOctonionHodgeDirac * g.rho) * masterChiralProjectorPlus := by
          rw [g.commutes_hodge]
    _ = masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * (g.rho * masterChiralProjectorPlus) := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * (masterChiralProjectorPlus * g.rho) := by
          rw [g2Spin_preserves_chiralPlus g]
    _ = (masterChiralProjectorMinus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorPlus) * g.rho := by
          simp only [Matrix.mul_assoc]

/-- 🏆 THEOREM 6: Commuting Square for D_- : S_- → S_+ :
    D_- ∘ ρ_{G2} = ρ_{G2} ∘ D_-. -/
theorem g2Spin_commutes_chiralDiracMinus :
    g.rho * chiralDiracMinusOp = chiralDiracMinusOp * g.rho := by
  dsimp [chiralDiracMinusOp]
  calc
    g.rho * (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus) =
        (g.rho * masterChiralProjectorPlus) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus := by
          simp only [Matrix.mul_assoc]
    _ = (masterChiralProjectorPlus * g.rho) * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus := by
          rw [g2Spin_preserves_chiralPlus g]
    _ = masterChiralProjectorPlus * (g.rho * embeddedSplitOctonionHodgeDirac) * masterChiralProjectorMinus := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorPlus * (embeddedSplitOctonionHodgeDirac * g.rho) * masterChiralProjectorMinus := by
          rw [g.commutes_hodge]
    _ = masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * (g.rho * masterChiralProjectorMinus) := by
          simp only [Matrix.mul_assoc]
    _ = masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * (masterChiralProjectorMinus * g.rho) := by
          rw [g2Spin_preserves_chiralMinus g]
    _ = (masterChiralProjectorPlus * embeddedSplitOctonionHodgeDirac * masterChiralProjectorMinus) * g.rho := by
          simp only [Matrix.mul_assoc]

/-- 🏆 THEOREM 7: Direct Sum Sector Invariance:
    $\mathfrak{g}_{2(2)} \curvearrowright S_+ \oplus S_-$. -/
theorem g2Spin_preserves_chiral_decomposition :
    (g.rho * masterChiralProjectorPlus = masterChiralProjectorPlus * g.rho) ∧
    (g.rho * masterChiralProjectorMinus = masterChiralProjectorMinus * g.rho) :=
  ⟨g2Spin_preserves_chiralPlus g, g2Spin_preserves_chiralMinus g⟩

end InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
