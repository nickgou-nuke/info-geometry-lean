import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Canonical.CanonicalZornG2SimpleRootSL2Bridge
import InfoGeometry.Canonical.CanonicalZornG2SL3TriFactorBridge

/-!
# Canonical Zorn G₂ Dimension Ledger

This owner module records the dimension ledger shared by three canonical
presentations associated with the exceptional Lie algebra $G_2$:
1. **The Derivation Algebra $\operatorname{Der}(\mathbb{O}_s)$**:
   - The 14-dimensional Lie algebra of derivations of real split-octonions `canonicalZornDerivations`.
   - Dimension: $\dim_{\mathbb{R}}(\operatorname{Der}(\mathbb{O}_s)) = 14$ (proven via parameter coordinates).
2. **The Cartan-Weyl Root System $\mathfrak{g}_2(\text{roots})$**:
   - 2-dimensional Cartan subalgebra $\mathfrak{h}$.
   - 12 root spaces $\Phi_{G_2} = \pm\{\alpha_1, \alpha_2, \alpha_1+\alpha_2, 2\alpha_1+\alpha_2, 3\alpha_1+\alpha_2, 3\alpha_1+2\alpha_2\}$.
   - Dimension: $2 + 12 = 14$.
3. **The Tri-Factor $\mathbb{Z}_3$-Grading $\mathfrak{sl}_3 \oplus \mathbf{3} \oplus \mathbf{3}^*$**:
   - 8-dimensional core $\mathfrak{sl}_3$ (grade 0).
   - 3-dimensional fundamental representation $\mathbf{3}$ (grade 1).
   - 3-dimensional dual representation $\mathbf{3}^*$ (grade 2).
   - Dimension: $8 + 3 + 3 = 14$.

The proved content here is only the common dimension invariant:
$$\operatorname{finrank}_{\mathbb{R}}(G_2) = 14.$$
No Lie-algebra equivalence, root-space identification, or tri-factor
decomposition is constructed by this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornG2UnifiedLieBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Canonical.CanonicalZornG2SimpleRootSL2Bridge
open InfoGeometry.Canonical.CanonicalZornG2SL3TriFactorBridge

/-- 1. Derivation algebra dimension is exactly 14. -/
theorem g2_derivation_dim :
    Module.finrank ℝ canonicalZornDerivations = 14 :=
  finrank_canonicalZornDerivations

/-- 2. Tri-Factor dimension sum: 8 + 3 + 3 = 14. -/
theorem g2_trifactor_dim_sum :
    (8 : ℕ) + 3 + 3 = 14 := by rfl

/-- 3. Root system dimension sum: 2 (Cartan) + 12 (Root spaces) = 14. -/
theorem g2_root_system_dim_sum :
    (2 : ℕ) + 12 = 14 := by rfl

/-- 4. Dimension ledger: the derivation finrank agrees with the two
    supplied dimension sums.  This is not a Lie equivalence theorem. -/
theorem g2_dimension_unification :
    Module.finrank ℝ canonicalZornDerivations = (8 + 3 + 3) ∧
    Module.finrank ℝ canonicalZornDerivations = (2 + 12) := by
  rw [g2_derivation_dim]
  exact ⟨rfl, rfl⟩

/-- 5. The abstract Cartan subalgebra dimension in G2. -/
def g2CartanDim : ℕ := 2

/-- 6. Total number of roots in the G2 root system. -/
def g2TotalRoots : ℕ := 12

/-- Exact dimensional match between the Cartan root decomposition and derivation finrank. -/
theorem g2_cartan_add_roots_eq_finrank :
    g2CartanDim + g2TotalRoots = Module.finrank ℝ canonicalZornDerivations := by
  rw [g2CartanDim, g2TotalRoots, g2_derivation_dim]

end InfoGeometry.Canonical.CanonicalZornG2UnifiedLieBridge
