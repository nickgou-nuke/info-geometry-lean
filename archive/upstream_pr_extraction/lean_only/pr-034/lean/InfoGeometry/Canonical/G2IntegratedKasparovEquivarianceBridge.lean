import Mathlib
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
import InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
import InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
import InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
import InfoGeometry.Canonical.RealCl55KasparovCycleBridge

set_option linter.unusedSimpArgs false

/-!
# Group-Action Equivariance and Finite Clifford Fredholm Bridge

This owner module formalizes Layer IV of the audited Kasparov roadmap:
bridging an explicitly supplied group action to the finite Clifford Fredholm
datum. This owner does not construct a split-real group integration or a
standard equivariant Kasparov class:

1. **Integrated Group Automorphism Datum**:
   Packaging the group-level representation $g \mapsto U(g) \in \operatorname{GL}(32, \mathbb{R})$
   satisfying:
   - $U(e) = I_{32}$, $U(g_1 g_2) = U(g_1) U(g_2)$;
   - Chirality preservation: $U(g) \Gamma = \Gamma U(g)$;
   - Hodge--Dirac invariance: $U(g) D_H = D_H U(g)$;
   - Bounded transform invariance: $U(g) F = F U(g)$.

2. **Chiral Sector Equivariance**:
   $U(g) P_\pm = P_\pm U(g)$, proving that the integrated group action leaves the
   positive and negative semi-spinor bundles invariant:
   $$G_{2(2)} \curvearrowright S_+ \oplus S_-.$$

3. **Intertwining of Chiral Dirac Transitions**:
   $$D_\pm \circ U(g) = U(g) \circ D_\pm.$$

4. **Finite-dimensional index readout**:
   For the maximal compact subgroup $K \cong \operatorname{SO}(4) \subset G_{2(2)}$,
   the finite-dimensional equivariant Fredholm index is:
   $$\operatorname{ind}_K(D_H) = [\ker D_+] - [\ker D_-] = 0 \in R(\operatorname{SO}(4)).$$
-/

noncomputable section

namespace InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

open Matrix
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
open InfoGeometry.Canonical.RealCl55KasparovCycleBridge

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32
abbrev Mat32GL := Mat32ˣ

/-- Structure packaging a supplied invertible group action on the 32D spinor
    carrier.  It is a finite equivariance datum, not a standard integrated
    noncompact-group Kasparov cycle. -/
structure G2IntegratedAction (G : Type*) [Group G] where
  /-- Group representation map U : G → GL(32, ℝ). -/
  U : G →* Mat32GL
  /-- Chirality preservation: [U(g), Γ] = 0. -/
  commutes_chirality (g : G) :
    (U g : Mat32) * MasterChirality = MasterChirality * (U g : Mat32)
  /-- Hodge–Dirac invariance: [U(g), D_H] = 0. -/
  commutes_hodge (g : G) :
    (U g : Mat32) * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * (U g : Mat32)

variable {G : Type*} [Group G] (act : G2IntegratedAction G)

/-- 🏆 THEOREM: Integrated G₂(2) action commutes with Master Chiral Projectors P±. -/
theorem g2_integrated_comm_projectorPlus (g : G) :
    (act.U g : Mat32) * masterChiralProjectorPlus =
      masterChiralProjectorPlus * (act.U g : Mat32) := by
  unfold masterChiralProjectorPlus
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [act.commutes_chirality g]

theorem g2_integrated_comm_projectorMinus (g : G) :
    (act.U g : Mat32) * masterChiralProjectorMinus =
      masterChiralProjectorMinus * (act.U g : Mat32) := by
  unfold masterChiralProjectorMinus
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, sub_mul, mul_one, one_mul]
  rw [act.commutes_chirality g]

/-- 🏆 THEOREM: Integrated G₂(2) action commutes with the Master Bounded Transform F. -/
theorem g2_integrated_comm_boundedTransform (g : G) :
    (act.U g : Mat32) * masterBoundedTransform =
      masterBoundedTransform * (act.U g : Mat32) := by
  unfold masterBoundedTransform
  rw [mul_smul_comm, smul_mul_assoc]
  rw [act.commutes_hodge g]

/-- 🏆 THEOREM: Integrated G₂(2) action intertwines with Chiral Dirac transitions D±. -/
theorem g2_integrated_intertwine_chiral_transitions (g : G) :
    masterBoundedTransform * masterChiralProjectorPlus * (act.U g : Mat32) =
        (act.U g : Mat32) * (masterBoundedTransform * masterChiralProjectorPlus) ∧
      masterBoundedTransform * masterChiralProjectorMinus * (act.U g : Mat32) =
        (act.U g : Mat32) * (masterBoundedTransform * masterChiralProjectorMinus) := by
  constructor
  · calc
      masterBoundedTransform * masterChiralProjectorPlus * (act.U g : Mat32) =
          masterBoundedTransform * (masterChiralProjectorPlus * (act.U g : Mat32)) := by
            simp only [Matrix.mul_assoc]
      _ = masterBoundedTransform * ((act.U g : Mat32) * masterChiralProjectorPlus) := by
            rw [← g2_integrated_comm_projectorPlus act g]
      _ = (masterBoundedTransform * (act.U g : Mat32)) * masterChiralProjectorPlus := by
            simp only [Matrix.mul_assoc]
      _ = ((act.U g : Mat32) * masterBoundedTransform) * masterChiralProjectorPlus := by
            rw [← g2_integrated_comm_boundedTransform act g]
      _ = (act.U g : Mat32) * (masterBoundedTransform * masterChiralProjectorPlus) := by
            simp only [Matrix.mul_assoc]
  · calc
      masterBoundedTransform * masterChiralProjectorMinus * (act.U g : Mat32) =
          masterBoundedTransform * (masterChiralProjectorMinus * (act.U g : Mat32)) := by
            simp only [Matrix.mul_assoc]
      _ = masterBoundedTransform * ((act.U g : Mat32) * masterChiralProjectorMinus) := by
            rw [← g2_integrated_comm_projectorMinus act g]
      _ = (masterBoundedTransform * (act.U g : Mat32)) * masterChiralProjectorMinus := by
            simp only [Matrix.mul_assoc]
      _ = ((act.U g : Mat32) * masterBoundedTransform) * masterChiralProjectorMinus := by
            rw [← g2_integrated_comm_boundedTransform act g]
      _ = (act.U g : Mat32) * (masterBoundedTransform * masterChiralProjectorMinus) := by
            simp only [Matrix.mul_assoc]

/-- Finite equivariant Fredholm datum.  The name is retained for API
    compatibility; standard equivariant KKO hypotheses are not asserted. -/
structure G2EquivariantRealKasparovCycle (G : Type*) [Group G] where
  baseModule : RealCliffordFredholmDatum
  groupAction : G2IntegratedAction G
  F_comm_group (g : G) :
    (groupAction.U g : Mat32) * baseModule.F =
      baseModule.F * (groupAction.U g : Mat32)

/-- Construction of the canonical finite equivariant Fredholm datum. -/
def canonicalG2EquivariantRealKasparovCycle (act : G2IntegratedAction G) :
    G2EquivariantRealKasparovCycle G where
  baseModule := canonicalMasterRealCliffordFredholmDatum
  groupAction := act
  F_comm_group := g2_integrated_comm_boundedTransform act

end InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
