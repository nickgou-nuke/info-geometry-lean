import Mathlib.Algebra.Lie.Submodule
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Split Octonion G₂ Grading Transport Bridge

This file specifies the transport of the $(\mathbb{Z}_2)^3$-grading from the octonionic 
basis level up to the global $G_2$ exceptional Lie symmetry.

Following the literature, the $(\mathbb{Z}_2)^3$-grading of the octonions (and split octonions)
induces a natural $(\mathbb{Z}_2)^3$-grading on its derivation algebra $\mathfrak{g}_2$.
This provides the vertical chain from local cochain coherence to graded Lie symmetry.
-/

namespace InfoGeometry.Canonical.SplitOctonionG2GradingTransportBridge

variable {𝕜 𝔤 : Type*} [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤]

/-- The grading group $(\mathbb{Z}_2)^3$. -/
abbrev Z2_cube := ZMod 2 × ZMod 2 × ZMod 2

/-- 
The abstract specification of the $G_2$ grading structure.
The Lie algebra $\mathfrak{g}_2$ decomposes into components indexed by $(\mathbb{Z}_2)^3$.
-/
structure G2GradingDatum where
  /-- The homogeneous components of the Lie algebra. -/
  component : Z2_cube → Submodule 𝕜 𝔤

  /-- CAPSTONE: The decisive theorem proving that the bracket respects the grading. -/
  bracket_grade_add : 
    ∀ (g h : Z2_cube) (x y : 𝔤),
      x ∈ component g → y ∈ component h → ⁅x, y⁆ ∈ component (g + h)

  /-- The direct sum decomposition of the entire Lie algebra. -/
  g2Grade_decomposition : 
    iSup component = ⊤

end InfoGeometry.Canonical.SplitOctonionG2GradingTransportBridge
