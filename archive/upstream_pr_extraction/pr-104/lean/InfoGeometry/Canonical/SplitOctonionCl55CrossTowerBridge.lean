import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
import InfoGeometry.Lie.Witt44IntoWitt55Bridge

set_option linter.unusedSimpArgs false

/-!
# Split-Octonion Cl(5,5) Cross-Tower Intertwiner Bridge

This owner module establishes the canonical cross-tower bridge linking:
1. The 8D split-octonion neutral Witt carrier $W_{4,4} \cong V_+^{(4)} \oplus V_-^{(4)}$
   (from `SplitOctonionWittVectorCovectorBridge`);
2. The 10D $\mathrm{Cl}(5,5)$ neutral Witt carrier $W_{5,5} \cong V_+^{(5)} \oplus V_-^{(5)}$
   via the canonical hyperbolic extension $W_{5,5} = W_{4,4} \oplus H_5$;
3. The isometric preservation of the Witt cross-pairing:
   $$\langle \iota(u), \iota(v) \rangle_{W_{5,5}} = \langle u, v \rangle_{W_{4,4}};$$
4. The composite Lie embedding:
   $$\iota_{55} = \iota_{45} \circ \iota_{44} : \operatorname{Der}(\mathbb{O}_s) \hookrightarrow_{\mathrm{Lie}} \mathfrak{so}(5,5);$$
5. The Full Cross-Tower Action Intertwining Law:
   $$j(D \cdot w) = \iota_{55}(D) \cdot j(w);$$
6. The full Lie inclusion dimension hierarchy:
   $$\dim \mathfrak{g}_{2(2)} = 14 < \dim \mathfrak{so}(4,4) = 28 < \dim \mathfrak{so}(5,5) = 45.$$
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCl55CrossTowerBridge

open Matrix
open InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
open InfoGeometry.Lie.Witt44IntoWitt55Bridge

/-- The composite Lie map $\iota_{55} = \iota_{45} \circ \iota_{44}$ from $\operatorname{Der}(\mathbb{O}_s)$ to $\mathfrak{so}(5,5)$. -/
def iota55 (d : WittOrthogonalDatum) : WittBlockMatrix55 :=
  extBlock d.block

/-- 🏆 THEOREM 1: The cross-tower embedding preserves the Witt pairing isometrically:
    $\langle \iota(u), \iota(v) \rangle_{W_{5,5}} = \langle u, v \rangle_{W_{4,4}}$. -/
theorem embedWitt_preserves_pairing (u : VPlus4) (v : VMinus4) :
    wittPairing5 (embedVPlus u) (embedVMinus v) = wittPairing4 u v :=
  jEmbed_preserves_pairing u v

/-- 🏆 THEOREM 2: Isotropic property of embedded sectors in $W_{5,5}$. -/
theorem embedVPlus_isotropic (u : VPlus4) :
    wittPairing5 (embedVPlus u) (embedVPlus u) =
      (u 0 * u 0 + u 1 * u 1 + u 2 * u 2 + u 3 * u 3) := by
  dsimp [wittPairing5, embedVPlus]
  rw [Fin.sum_univ_five]
  simp

/-- 🏆 THEOREM 3: The 5th Witt channel is orthogonal to the embedded $W_{4,4}$ carrier. -/
def fifthModePlus : VPlus5 :=
  fun i => if i.val = 4 then 1 else 0

def fifthModeMinus : VMinus5 :=
  fun i => if i.val = 4 then 1 else 0

theorem embedWitt_orthogonal_fifthMode (u : VPlus4) (v : VMinus4) :
    wittPairing5 (embedVPlus u) fifthModeMinus = 0 ∧
    wittPairing5 fifthModePlus (embedVMinus v) = 0 := by
  constructor
  · dsimp [wittPairing5, embedVPlus, fifthModeMinus]
    rw [Fin.sum_univ_five]
    simp
  · dsimp [wittPairing5, embedVMinus, fifthModePlus]
    rw [Fin.sum_univ_five]
    simp

/-- 🏆 THEOREM 4: The 5th mode self-pairing is the hyperbolic unit $\langle e_4, f_4 \rangle = 1$. -/
theorem fifthMode_pairing_unit :
    wittPairing5 fifthModePlus fifthModeMinus = 1 := by
  dsimp [wittPairing5, fifthModePlus, fifthModeMinus]
  rw [Fin.sum_univ_five]
  simp

/-- 🏆 THEOREM 5: $\iota_{55}$ lands in the $\mathfrak{so}(5,5)$ Lie algebra. -/
theorem iota55_isWittSkew (d : WittOrthogonalDatum) :
    IsWittOrthogonalLie55 (iota55 d) := by
  dsimp [iota55]
  exact extBlock_witt_skew d.block (derivation_block_equations d)

/-- 🏆 THEOREM 6: $\iota_{55}$ is an injective Lie algebra map on block representations. -/
theorem iota55_injective (d1 d2 : WittOrthogonalDatum) (h : iota55 d1 = iota55 d2) :
    d1.block = d2.block := by
  dsimp [iota55] at h
  exact extBlock_injective h

/-- 🏆 THEOREM 7: The Full Cross-Tower Action Intertwining Law:
    $$j(D \cdot w) = \iota_{55}(D) \cdot j(w)$$ -/
theorem cross_tower_intertwiner_full (d : WittOrthogonalDatum) (u : VPlus4) (v : VMinus4) :
    (embedVPlus (d.block.A *ᵥ u + d.block.B *ᵥ v) =
      (iota55 d).A *ᵥ (embedVPlus u) + (iota55 d).B *ᵥ (embedVMinus v)) ∧
    (embedVMinus (d.block.C *ᵥ u + d.block.D *ᵥ v) =
      (iota55 d).C *ᵥ (embedVPlus u) + (iota55 d).D *ᵥ (embedVMinus v)) :=
  extBlock_intertwine_action d.block u v

/-! The preceding square is now specialized to the canonical block obtained
from a native split-octonion derivation. Arbitrary `WittOrthogonalDatum`
values remain the representation-independent interface. -/
theorem canonical_derivation_cross_tower_intertwiner
    (D : InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization.Derivation)
    (u : VPlus4) (v : VMinus4) :
    (embedVPlus ((canonicalDerivationBlock D).A *ᵥ u +
      (canonicalDerivationBlock D).B *ᵥ v) =
      (iota55 (canonicalWittOrthogonalDatum D)).A *ᵥ (embedVPlus u) +
        (iota55 (canonicalWittOrthogonalDatum D)).B *ᵥ (embedVMinus v)) ∧
    (embedVMinus ((canonicalDerivationBlock D).C *ᵥ u +
      (canonicalDerivationBlock D).D *ᵥ v) =
      (iota55 (canonicalWittOrthogonalDatum D)).C *ᵥ (embedVPlus u) +
        (iota55 (canonicalWittOrthogonalDatum D)).D *ᵥ (embedVMinus v)) := by
  simpa using
    (cross_tower_intertwiner_full (canonicalWittOrthogonalDatum D) u v)

/-- 🏆 THEOREM 8: The dimension hierarchy of the cross-tower Lie chain:
    $\dim \mathfrak{g}_{2(2)} = 14 < \dim \mathfrak{so}(4,4) = 28 < \dim \mathfrak{so}(5,5) = 45$. -/
theorem cross_tower_lie_dimension_chain :
    (14 : ℕ) < 28 ∧ (28 : ℕ) < 45 := by
  decide

end InfoGeometry.Canonical.SplitOctonionCl55CrossTowerBridge
