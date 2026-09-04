import Mathlib
import InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
import InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

noncomputable section

namespace InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleG2Bridge
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation

abbrev H3 := H3Zorn ℝ
abbrev Spin10 := SplitSpacetime10

/-- The ambient Albert Jordan triple product preserves the fixed-`e1`
Peirce-zero subalgebra. -/
theorem jordanTriple_preserves_peirceZero
    {x y z : H3}
    (hx : InPeirceZero x) (hy : InPeirceZero y) (hz : InPeirceZero z) :
    InPeirceZero (jordanTriple x y z) := by
  unfold jordanTriple
  apply sub_preserves_peirceZero
  · exact add_mem
      (candidateJordanMul_preserves_peirceZero
        (candidateJordanMul_preserves_peirceZero hx hy) hz)
      (candidateJordanMul_preserves_peirceZero
        (candidateJordanMul_preserves_peirceZero hz hy) hx)
  · exact candidateJordanMul_preserves_peirceZero
      (candidateJordanMul_preserves_peirceZero hx hz) hy

/-- Jordan product induced on the ten-dimensional Peirce-zero/spin-factor
carrier. -/
def jordanMul10 (x y : Spin10) : Spin10 :=
  fromH3 (candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y))

/-- The Peirce-zero embedding strictly intertwines the induced 10D Jordan
product with the ambient split-Albert product. -/
theorem peirceZeroEmbed_jordanMul10 (x y : Spin10) :
    peirceZeroEmbed (jordanMul10 x y) =
      candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y) := by
  apply (eq_peirceZeroEmbed_of_mem
    (candidateJordanMul_preserves_peirceZero
      (peirceZeroEmbed_mem x) (peirceZeroEmbed_mem y))).symm

/-- The Jordan triple product intrinsic to the induced 10D Jordan algebra. -/
def jordanTriple10 (x y z : Spin10) : Spin10 :=
  jordanMul10 (jordanMul10 x y) z +
    jordanMul10 (jordanMul10 z y) x -
      jordanMul10 (jordanMul10 x z) y

/-- The Peirce-zero embedding is additive. -/
theorem peirceZeroEmbed_add (x y : Spin10) :
    peirceZeroEmbed (x + y) = peirceZeroEmbed x + peirceZeroEmbed y := by
  rcases x with ⟨⟨x2, x3⟩, xb⟩
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  apply H3Zorn.ext_h3 <;>
    simp [peirceZeroEmbed, H3Zorn.add_readback]

/-- The Peirce-zero embedding respects subtraction. -/
theorem peirceZeroEmbed_sub (x y : Spin10) :
    peirceZeroEmbed (x - y) = peirceZeroEmbed x - peirceZeroEmbed y := by
  rcases x with ⟨⟨x2, x3⟩, xb⟩
  rcases y with ⟨⟨y2, y3⟩, yb⟩
  apply H3Zorn.ext_h3 <;>
    simp [peirceZeroEmbed, H3Zorn.sub_readback]

/-- Main restriction theorem: the intrinsic 10D spin-factor Jordan triple is
exactly the restriction of the ambient split-Albert triple to `V₀(e₁)`. -/
theorem peirceZeroEmbed_jordanTriple10 (x y z : Spin10) :
    peirceZeroEmbed (jordanTriple10 x y z) =
      jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y) (peirceZeroEmbed z) := by
  unfold jordanTriple10 jordanTriple
  rw [peirceZeroEmbed_sub, peirceZeroEmbed_add]
  rw [peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanMul10,
    peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanMul10,
    peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanMul10]

/-- Coordinate readback form of the restriction theorem. -/
theorem jordanTriple10_eq_fromH3_ambient (x y z : Spin10) :
    jordanTriple10 x y z =
      fromH3 (jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y) (peirceZeroEmbed z)) := by
  apply peirceZeroEmbed_injective
  rw [peirceZeroEmbed_jordanTriple10]
  exact (eq_peirceZeroEmbed_of_mem
    (jordanTriple_preserves_peirceZero
      (peirceZeroEmbed_mem x) (peirceZeroEmbed_mem y)
      (peirceZeroEmbed_mem z))).symm

/-- Compact restriction packet separating the 27D Albert Kantor/Jordan triple
from the 10D split-spin-factor conformal/TKK lane. -/
theorem peirceZero_jordanTriple_restriction_packet :
    (∀ x y : Spin10,
      peirceZeroEmbed (jordanMul10 x y) =
        candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y)) ∧
    (∀ x y z : Spin10,
      peirceZeroEmbed (jordanTriple10 x y z) =
        jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y) (peirceZeroEmbed z)) := by
  exact ⟨peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanTriple10⟩

end InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestriction
