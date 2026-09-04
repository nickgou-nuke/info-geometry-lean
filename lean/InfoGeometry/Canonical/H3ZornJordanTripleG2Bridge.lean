import Mathlib
import InfoGeometry.Canonical.SplitG2AlbertJordanCompatibility
import InfoGeometry.Canonical.H3ZornAlgebraicSoldering
import InfoGeometry.Algebra.KantorTripleFiveGrading
import InfoGeometry.Algebra.BaezF4H3Zorn

noncomputable section

namespace InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering
open InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift
open InfoGeometry.Canonical.SplitG2AlbertJordanCompatibility

abbrev H3 := H3Zorn ℝ
abbrev G2Der := InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations

/-- The standard Jordan triple product associated to the installed split-Albert
Jordan product:
`{x,y,z} = (x∘y)∘z + (z∘y)∘x - (x∘z)∘y`.

This owner does not yet assert the full Freudenthal--Kantor first and second
identities required by `KantorTripleSystem`; those remain a separate capstone. -/
noncomputable def jordanTriple (x y z : H3) : H3 :=
  candidateJordanMul (candidateJordanMul x y) z +
    candidateJordanMul (candidateJordanMul z y) x -
      candidateJordanMul (candidateJordanMul x z) y

@[simp] theorem jordanTriple_add_left (x₁ x₂ y z : H3) :
    jordanTriple (x₁ + x₂) y z =
      jordanTriple x₁ y z + jordanTriple x₂ y z := by
  simp [jordanTriple, candidateJordanMul_add_left, candidateJordanMul_add_right]
  abel

@[simp] theorem jordanTriple_smul_left (r : ℝ) (x y z : H3) :
    jordanTriple (r • x) y z = r • jordanTriple x y z := by
  simp [jordanTriple, candidateJordanMul_smul_left,
    candidateJordanMul_smul_right, smul_sub]
  module

@[simp] theorem jordanTriple_add_middle (x y₁ y₂ z : H3) :
    jordanTriple x (y₁ + y₂) z =
      jordanTriple x y₁ z + jordanTriple x y₂ z := by
  simp [jordanTriple, candidateJordanMul_add_left, candidateJordanMul_add_right]
  abel

@[simp] theorem jordanTriple_smul_middle (r : ℝ) (x y z : H3) :
    jordanTriple x (r • y) z = r • jordanTriple x y z := by
  simp [jordanTriple, candidateJordanMul_smul_left,
    candidateJordanMul_smul_right, smul_sub]
  module

@[simp] theorem jordanTriple_add_right (x y z₁ z₂ : H3) :
    jordanTriple x y (z₁ + z₂) =
      jordanTriple x y z₁ + jordanTriple x y z₂ := by
  simp [jordanTriple, candidateJordanMul_add_left, candidateJordanMul_add_right]
  abel

@[simp] theorem jordanTriple_smul_right (r : ℝ) (x y z : H3) :
    jordanTriple x y (r • z) = r • jordanTriple x y z := by
  simp [jordanTriple, candidateJordanMul_smul_left,
    candidateJordanMul_smul_right, smul_sub]
  module

/-- Outer symmetry of the Jordan triple product. -/
theorem jordanTriple_outer_symm (x y z : H3) :
    jordanTriple x y z = jordanTriple z y x := by
  simp [jordanTriple, candidateJordanMul_comm]
  abel

/-- Triple operator `D(x,y) z = {x,y,z}`. -/
noncomputable def jordanTripleD (x y : H3) : Module.End ℝ H3 where
  toFun z := jordanTriple x y z
  map_add' := jordanTriple_add_right x y
  map_smul' := jordanTriple_smul_right x y

@[simp] theorem jordanTripleD_apply (x y z : H3) :
    jordanTripleD x y z = jordanTriple x y z := rfl

/-- Native Jordan left multiplication. -/
noncomputable def jordanLeft (x : H3) : Module.End ℝ H3 where
  toFun z := candidateJordanMul x z
  map_add' := candidateJordanMul_add_right x
  map_smul' := candidateJordanMul_smul_right

/-- Inner Jordan derivation `[L_x,L_y]`. -/
noncomputable def jordanInner (x y : H3) : Module.End ℝ H3 :=
  jordanLeft x * jordanLeft y - jordanLeft y * jordanLeft x

@[simp] theorem jordanInner_apply (x y z : H3) :
    jordanInner x y z =
      candidateJordanMul x (candidateJordanMul y z) -
        candidateJordanMul y (candidateJordanMul x z) := rfl

/-- The antisymmetric part of the triple operator is exactly twice the inner
Jordan derivation.  This is the direct bridge from triple geometry to the
native `F4` inner-derivation lane. -/
theorem jordanTriple_antisym_eq_two_inner (x y z : H3) :
    jordanTriple x y z - jordanTriple y x z =
      (2 : ℝ) • jordanInner x y z := by
  simp [jordanTriple, jordanInner_apply, candidateJordanMul_comm]
  module

/-- The existing Baez inner derivation is the same commutator of native left
multiplications, so it is recovered from the antisymmetric triple sector. -/
theorem jordanTriple_antisym_eq_two_baezInner (x y z : H3) :
    jordanTriple x y z - jordanTriple y x z =
      (2 : ℝ) • (h3ZornJordanInnerDerivation x y : Module.End ℝ H3) z := by
  change _ = (2 : ℝ) •
    (candidateJordanMul x (candidateJordanMul y z) -
      candidateJordanMul y (candidateJordanMul x z))
  exact jordanTriple_antisym_eq_two_inner x y z

/-- A Jordan derivation differentiates the associated triple product in all
three slots.  No additional Freudenthal calculation is required. -/
theorem jordanTriple_derivation
    (D : Module.End ℝ H3) (hD : H3ZornJordanDerivation D)
    (x y z : H3) :
    D (jordanTriple x y z) =
      jordanTriple (D x) y z +
        jordanTriple x (D y) z +
          jordanTriple x y (D z) := by
  simp only [jordanTriple, map_add, map_sub]
  rw [hD, hD, hD, hD, hD, hD]
  simp [candidateJordanMul_comm]
  abel

/-- Hence every entrywise split-`G2` derivation differentiates the Albert
Jordan triple product. -/
theorem g2_jordanTriple_derivation (D : G2Der) (x y z : H3) :
    liftG2End D (jordanTriple x y z) =
      jordanTriple (liftG2End D x) y z +
        jordanTriple x (liftG2End D y) z +
          jordanTriple x y (liftG2End D z) := by
  exact jordanTriple_derivation (liftG2End D)
    (liftG2End_isJordanDerivation D) x y z

/-- Pulled-back triple product on the six-lane soldering coordinates. -/
noncomputable def coordJordanTriple (x y z : H3Coord) : H3Coord :=
  h3Soldering.symm (jordanTriple (h3Soldering x) (h3Soldering y) (h3Soldering z))

/-- Algebraic soldering intertwines the coordinate and native triple products. -/
@[simp] theorem h3Soldering_triple_intertwines (x y z : H3Coord) :
    h3Soldering (coordJordanTriple x y z) =
      jordanTriple (h3Soldering x) (h3Soldering y) (h3Soldering z) := by
  simp [coordJordanTriple]

/-- The source-coordinate `G2` action satisfies the three-slot Leibniz rule for
the soldered triple product. -/
theorem entrywiseCoord_triple_derivation
    (D : G2Der) (x y z : H3Coord) :
    entrywiseCoordEnd D (coordJordanTriple x y z) =
      coordJordanTriple (entrywiseCoordEnd D x) y z +
        coordJordanTriple x (entrywiseCoordEnd D y) z +
          coordJordanTriple x y (entrywiseCoordEnd D z) := by
  apply h3Soldering.injective
  simp only [map_add, h3Soldering_triple_intertwines,
    h3Soldering_entrywise_intertwines]
  exact g2_jordanTriple_derivation D (h3Soldering x) (h3Soldering y) (h3Soldering z)

/-- The present Jordan triple is outer symmetric, so the associated Kantor
`K`-operator would vanish.  This theorem records the correct Jordan boundary
before any full `KantorTripleSystem` instance is installed. -/
theorem jordanTriple_K_expression_zero (x y z : H3) :
    jordanTriple x z y - jordanTriple y z x = 0 := by
  rw [jordanTriple_outer_symm x z y]
  simp

end InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
