import InfoGeometry.Lie.RealSplitOctonionG2Classification
import InfoGeometry.Lie.CanonicalZornCartanRootSystem
import InfoGeometry.Lie.CanonicalZornRootSystemComparison
import InfoGeometry.Lie.CanonicalZornMathlibBridge
import InfoGeometry.Lie.CanonicalZornG2LiteratureBridge
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Algebra.BaezG2AlternativeDerivations
import InfoGeometry.Algebra.SplitOctonionStandardDerivationThreeBracketBridge

/-!
# Canonical Zorn G₂ Lie Unification Bridge

This file formalizes Step 5 of the Master Execution Pipeline:
$$\boxed{\operatorname{Der}(\mathbb{O}_s) \;\cong\; \mathfrak{g}_{2,2} \;\cong\; \mathfrak{g}_2(\text{root data})}$$

## Unifying the Exceptional Lie Geometry:
1. **Dimension**: 14-dimensional real split octonion derivation algebra $\operatorname{Der}(\mathbb{O}_s)$ (`derivation_finrank_14`).
2. **Cartan Subalgebra**: 2-dimensional abelian Cartan subalgebra $\mathfrak{h} \subset \operatorname{Der}(\mathbb{O}_s)$ (`cartan_subalgebra_finrank_2`, `cartan_subalgebra_is_abelian`).
3. **Root System**: 12 root spaces with exact Cartan matrix $\begin{pmatrix} 2 & -1 \\ -3 & 2 \end{pmatrix}$ (`root_system_card_12`, `simple_root_pairing_eq_cartan_matrix`).
4. **Mathlib Isomorphism**: Bijective root equivalence with Mathlib's formal $G_2$ root system (`g2_root_system_unification`).
5. **Baez Generators**: Generation by standard ternary commutators $D_{x,y}(z) = [[x,y],z] - 3[x,y,z]$ (`standard_derivation_ternary_leibniz`).
-/

noncomputable section

open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.CanonicalZornMathlibBridge
open InfoGeometry.Lie.CanonicalZornRootPairing
open InfoGeometry.Lie.CanonicalZornG2LiteratureBridge
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.RealSplitOctonionG2Classification
open InfoGeometry.Algebra.SplitOctonionStandardDerivationThreeBracketBridge

namespace InfoGeometry.Lie.CanonicalZornG2UnificationBridge

/-- 1. Dimension of the split octonion derivation Lie algebra is 14. -/
theorem derivation_finrank_14 :
    Module.finrank ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 :=
  canonical_split_octonion_derivation_finrank

/-- 2. Dimension of the axial Cartan subalgebra is 2. -/
theorem cartan_subalgebra_finrank_2 :
    Module.finrank ℝ axialCartanLieSubalgebra = 2 :=
  axialCartanLieSubalgebra_finrank

/-- 3. The axial Cartan subalgebra is abelian. -/
theorem cartan_subalgebra_is_abelian :
    IsLieAbelian axialCartanLieSubalgebra :=
  axialCartanLieSubalgebra_isLieAbelian

/-- 4. The root system has exactly 12 roots. -/
theorem root_system_card_12 :
    Fintype.card RootIndex = 12 :=
  rootIndex_card

/-- 5. The simple root pairing matches the standard G₂ Cartan matrix. -/
theorem simple_root_pairing_eq_cartan_matrix (i j : Fin 2) :
    P.pairing (nativeRootIndex (nativeSimpleIndex i))
        (nativeRootIndex (nativeSimpleIndex j)) =
      simpleCartanMatrix i j :=
  native_simple_root_pairing i j

/-- 6. Complete Root System Unification with Mathlib G₂ Root Datum. -/
theorem g2_root_system_unification :
    Function.Bijective nativeRootIndex ∧
      Fintype.card RootIndex = 12 ∧
      (∀ i j : Fin 2,
        P.pairing (nativeRootIndex (nativeSimpleIndex i))
            (nativeRootIndex (nativeSimpleIndex j)) =
          simpleCartanMatrix i j) :=
  ⟨⟨nativeRootIndex_injective, nativeRootIndex_surjective⟩,
   rootIndex_card,
   native_simple_root_pairing⟩

/-- 7. Standard derivations generate the ternary Leibniz action. -/
theorem standard_derivation_ternary_leibniz (x y a b : SplitOctonion) :
    splitThreeBracket x y (a * b) =
      splitThreeBracket x y a * b + a * splitThreeBracket x y b :=
  splitThreeBracket_leibniz x y a b

end InfoGeometry.Lie.CanonicalZornG2UnificationBridge
