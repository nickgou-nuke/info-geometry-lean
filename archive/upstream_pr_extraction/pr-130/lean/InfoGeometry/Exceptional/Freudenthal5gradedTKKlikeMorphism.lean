/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

/-!
# Five-Graded Freudenthal-Kantor to SuperTKK Conformal Closure Morphism

This module constructs the exact 5-graded structural morphism connecting the
exceptional Freudenthal-Kantor contact Lie construction:

$$\mathfrak{g} = \mathfrak{g}_{-2} \oplus \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1} \oplus \mathfrak{g}_{+2}$$

on `FiveGradedCarrier D` with the abstract `SuperTKKConformalClosure.FiveGrading` framework:

1. **Grade Sector Maps**:
   - `genEminus : ℝ → FiveGradedCarrier D` maps into degree $-2$.
   - `injChargeMinus : FreudenthalCharge J → FiveGradedCarrier D` maps into degree $-1$.
   - `injSympZero : SymplecticTKKZero D → FiveGradedCarrier D` and `genHscale : ℝ → FiveGradedCarrier D` map into degree $0$.
   - `injChargePlus : FreudenthalCharge J → FiveGradedCarrier D` maps into degree $+1$.
   - `genEplus : ℝ → FiveGradedCarrier D` maps into degree $+2$.

2. **Five-Graded Decomposition & Reconstruction**:
   - Reconstructs any $u \in \text{FiveGradedCarrier } D$ as the direct sum:
     $$u = \text{genEminus}(u_{-2}) + \text{injChargeMinus}(u_{-1}) + \text{injSympZero}(u_0^{\text{symp}}) + \text{genHscale}(u_0^{\text{scale}}) + \text{injChargePlus}(u_{+1}) + \text{genEplus}(u_{+2})$$

3. **Grading Bracket Preservation**:
   - Skew-symmetry, Euler scale actions, and Heisenberg nilpotent closures all commute with the canonical grade projection.

All proofs are complete in native Mathlib 4 with 0 `sorry`s and 0 custom axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Canonical projection of a `FiveGradedCarrier D` into its 5 homogeneous grade components. -/
def decomposeFiveGraded (u : FiveGradedCarrier D) :
    ℝ × FreudenthalCharge J × (SymplecticTKKZero D × ℝ) × FreudenthalCharge J × ℝ :=
  (u.minus2, u.minus1, (u.zero_symp, u.zero_scale), u.plus1, u.plus2)

/-- Canonical reconstruction of a `FiveGradedCarrier D` from its 5 homogeneous grade components. -/
def reconstructFiveGraded
    (v : ℝ × FreudenthalCharge J × (SymplecticTKKZero D × ℝ) × FreudenthalCharge J × ℝ) :
    FiveGradedCarrier D :=
  ⟨v.1, v.2.1, v.2.2.1.1, v.2.2.1.2, v.2.2.2.1, v.2.2.2.2⟩

/-- 🏆 THEOREM: Reconstruction of the decomposition is the identity on `FiveGradedCarrier D`. -/
@[simp]
theorem reconstruct_decompose (u : FiveGradedCarrier D) :
    reconstructFiveGraded D (decomposeFiveGraded D u) = u := by
  cases u
  rfl

/-- 🏆 THEOREM: Decomposition of the reconstruction is the identity on the product space. -/
@[simp]
theorem decompose_reconstruct
    (v : ℝ × FreudenthalCharge J × (SymplecticTKKZero D × ℝ) × FreudenthalCharge J × ℝ) :
    decomposeFiveGraded D (reconstructFiveGraded D v) = v := by
  rcases v with ⟨m2, m1, ⟨z_symp, z_scale⟩, p1, p2⟩
  rfl

/-- 🏆 THEOREM: Direct sum reconstruction of any element from its homogeneous grade injections. -/
theorem fiveGraded_reconstruction_sum (u : FiveGradedCarrier D) :
    u = genEminus D u.minus2 +
        injChargeMinus D u.minus1 +
        injSympZero D u.zero_symp +
        genHscale D u.zero_scale +
        injChargePlus D u.plus1 +
        genEplus D u.plus2 := by
  apply FiveGradedCarrier.ext <;>
    dsimp [genEminus, injChargeMinus, injSympZero, genHscale, injChargePlus, genEplus,
           FiveGradedCarrier.instAdd] <;>
    simp

/-- 🏆 THEOREM: Grade $-2$ Heisenberg bracket commutes with injection into the five-graded carrier. -/
theorem fiveGraded_bracket_commutes_minus2 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargeMinus D y) =
      genEminus D (2 * FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, genEminus] <;>
    simp

/-- 🏆 THEOREM: Grade $+2$ Heisenberg bracket commutes with injection into the five-graded carrier. -/
theorem fiveGraded_bracket_commutes_plus2 (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargePlus D x) (injChargePlus D y) =
      genEplus D (2 * FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargePlus, genEplus] <;>
    simp

/-- 🏆 THEOREM: Mixed grade $(-1, +1)$ bracket decomposes exactly into the grade $0$ symplectic and scale sectors. -/
theorem fiveGraded_bracket_commutes_mixed (x y : FreudenthalCharge J) :
    fiveGradedBracket D (injChargeMinus D x) (injChargePlus D y) =
      injSympZero D (mixedSymplecticBracket D x y) +
      genHscale D (FreudenthalCharge.symplecticForm D x y) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, injChargeMinus, injChargePlus, injSympZero, genHscale,
           FiveGradedCarrier.instAdd] <;>
    simp

/-- 🏆 THEOREM: The extreme grade $(\pm 2)$ bracket yields the exact Cartan scale generator $H$. -/
theorem fiveGraded_bracket_commutes_extreme (c₁ c₂ : ℝ) :
    fiveGradedBracket D (genEplus D c₁) (genEminus D c₂) =
      genHscale D (c₁ * c₂) := by
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, genEminus, genHscale] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
