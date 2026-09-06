/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.CircularChiralCausalConeBasis
import InfoGeometry.Algebra.CircularChiralDerivationsFourteen
import InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# The Matter-to-Gauge Bridge: explicit chiral witness derivations

This module formalizes the exact bridge connecting:
1. **The 8D Matter Layer**:
   The Circular Chiral Causal Cone Basis $(u^+, u^-, \text{up}_i, \text{down}_j) \in \text{ChiralBasis}$.
2. **The 14 Gauge Witness Pairs**:
   The 14 canonical pairs of `GaugeGenerator` indexed by:
   - 2 Cartan Torus Generators: $(u_0, v_0)$ and $(u_1, v_1)$
   - 6 $SL(3, \mathbb{R})$ Color Gluons: $(u_i, v_j)$ with $i \neq j$
   - 6 Chiral Lightlike Parafermions: $(u^+, u_i)$ and $(u^+, v_i)$
3. **The Operatorial Normal Form**:
   Proves the exact $-3 \cdot \text{associator}$ decomposition for all 14 gauge derivations.
4. **The canonical target dimension**:
   Records the existing finrank theorem for the canonical derivation carrier.

All proofs are complete in native Lean 4 + Mathlib with **0 sorrys, 0 admits, and 0 custom axioms**.
-/

namespace InfoGeometry.Algebra.ChiralGeneratorsToDerivationsBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CircularChiralDerivationsFourteen
open InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev VZ := ZornVectorMatrix ℝ
abbrev VDer := ZornVectorMatrix.Derivation (R := ℝ)

/-- Maps a ChiralBasis element to its vector-Zorn representation in VZ. -/
def chiralToVZ : ChiralBasis → VZ
  | ChiralBasis.uPlus => E11
  | ChiralBasis.uMinus => E22
  | ChiralBasis.up i => U i
  | ChiralBasis.down i => V i

/-- Maps a GaugeGenerator to its inner derivation in VDer. -/
noncomputable def derivationFromGaugeGenerator (g : GaugeGenerator) : VDer :=
  let (b1, b2) := gaugeWitnessPair g
  innerDerivation (chiralToVZ b1) (chiralToVZ b2)

/-- 🏆 THEOREM 1: The gauge derivation assignment is indexed by exactly 14 generators. -/
theorem gauge_derivations_count : Fintype.card GaugeGenerator = 14 :=
  gauge_generator_card

/-- 🏆 THEOREM 2: The canonical dimension of the derivation Lie algebra is exactly 14. -/
theorem g2_derivation_dim : Module.finrank ℝ canonicalZornDerivations = 14 :=
  canonical_derivation_finrank

/-- 🏆 THEOREM 3: Exact Operatorial Normal Form for all 14 Gauge Derivations.
    Every gauge derivation acts as standard Lie bracket plus $(-3 \cdot \text{associator})$. -/
theorem derivationFromGaugeGenerator_normal_form (g : GaugeGenerator) (z : VZ) :
    derivationFromGaugeGenerator g z =
      let x := chiralToVZ (gaugeWitnessPair g).1
      let y := chiralToVZ (gaugeWitnessPair g).2
      ((x * y - y * x) * z - z * (x * y - y * x)) -
        3 • ((x * y) * z - x * (y * z)) := by
  dsimp [derivationFromGaugeGenerator]
  exact innerDerivation_operatorial_normal_form
    (chiralToVZ (gaugeWitnessPair g).1)
    (chiralToVZ (gaugeWitnessPair g).2) z

/-- Tautological containment of the witness span in the ambient module.  This
    is not a span-equality or independence theorem. -/
theorem gauge_derivations_submodule_le_top :
    Submodule.span ℝ (Set.range derivationFromGaugeGenerator) ≤ ⊤ :=
  le_top

end InfoGeometry.Algebra.ChiralGeneratorsToDerivationsBridge
