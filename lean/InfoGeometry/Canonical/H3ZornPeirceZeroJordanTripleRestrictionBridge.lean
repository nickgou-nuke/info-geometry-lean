import InfoGeometry.Canonical.SplitAlbertPeirceZeroJordanTripleRestriction
import InfoGeometry.Canonical.H3ZornJordanTripleBridge

/-! The induced Jordan product on the Peirce-zero carrier, reconstructed from
the existing ambient preservation and soldering owners. -/

noncomputable section

namespace InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestrictionBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornJordanTripleBridge
open InfoGeometry.Canonical.SplitAlbertTripotentPeirceBoundary
open InfoGeometry.Canonical.SplitAlbertPeirceZeroQuadraticRepresentation
open InfoGeometry.Canonical.SplitAlbertPeirceZeroJordanTripleRestriction

abbrev Spin10 := SplitSpacetime10

def jordanMul10 (x y : Spin10) : Spin10 :=
  fromH3 (candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y))

theorem peirceZeroEmbed_jordanMul10 (x y : Spin10) :
    peirceZeroEmbed (jordanMul10 x y) =
      candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y) := by
  apply (eq_peirceZeroEmbed_of_mem
    (candidateJordanMul_preserves_peirceZero
      (peirceZeroEmbed_mem x) (peirceZeroEmbed_mem y))).symm

def jordanTriple10 (x y z : Spin10) : Spin10 :=
  jordanMul10 (jordanMul10 x y) z +
    jordanMul10 (jordanMul10 z y) x - jordanMul10 (jordanMul10 x z) y

theorem peirceZeroEmbed_add (x y : Spin10) :
    peirceZeroEmbed (x + y) = peirceZeroEmbed x + peirceZeroEmbed y := by
  rcases x with ⟨⟨x₂, x₃⟩, xb⟩
  rcases y with ⟨⟨y₂, y₃⟩, yb⟩
  apply H3Zorn.ext_h3 <;>
    simp [peirceZeroEmbed, H3Zorn.add_readback,
      ZornVectorMatrix.zero, ZornVectorMatrix.add, ZornVectorMatrix.neg] <;>
    ring

theorem peirceZeroEmbed_sub (x y : Spin10) :
    peirceZeroEmbed (x - y) = peirceZeroEmbed x - peirceZeroEmbed y := by
  rcases x with ⟨⟨x₂, x₃⟩, xb⟩
  rcases y with ⟨⟨y₂, y₃⟩, yb⟩
  apply H3Zorn.ext_h3
  · simp [peirceZeroEmbed, H3Zorn.sub_readback,
      ZornVectorMatrix.zero, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg]
  · simp [peirceZeroEmbed, H3Zorn.sub_readback]
  · simp [peirceZeroEmbed, H3Zorn.sub_readback]
  · simp [peirceZeroEmbed, H3Zorn.sub_readback,
      ZornVectorMatrix.zero, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg]
  · change xb - yb = ZornVectorMatrix.add xb (ZornVectorMatrix.neg yb)
    rfl
  · simp [peirceZeroEmbed, H3Zorn.sub_readback,
      ZornVectorMatrix.zero, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg]

theorem peirceZeroEmbed_jordanTriple10 (x y z : Spin10) :
    peirceZeroEmbed (jordanTriple10 x y z) =
      jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y)
        (peirceZeroEmbed z) := by
  unfold jordanTriple10 jordanTriple
  rw [peirceZeroEmbed_sub, peirceZeroEmbed_add,
    peirceZeroEmbed_jordanMul10,
    peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanMul10,
    peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanMul10,
    peirceZeroEmbed_jordanMul10]
  rw [candidateJordanMul_eq_mul, candidateJordanMul_eq_mul,
    candidateJordanMul_eq_mul, candidateJordanMul_eq_mul,
    candidateJordanMul_eq_mul, candidateJordanMul_eq_mul]

theorem peirceZero_jordanTriple_restriction_packet :
    (∀ x y : Spin10,
      peirceZeroEmbed (jordanMul10 x y) =
        candidateJordanMul (peirceZeroEmbed x) (peirceZeroEmbed y)) ∧
    (∀ x y z : Spin10,
      peirceZeroEmbed (jordanTriple10 x y z) =
        jordanTriple (peirceZeroEmbed x) (peirceZeroEmbed y)
          (peirceZeroEmbed z)) := by
  exact ⟨peirceZeroEmbed_jordanMul10, peirceZeroEmbed_jordanTriple10⟩

end InfoGeometry.Canonical.H3ZornPeirceZeroJordanTripleRestrictionBridge
