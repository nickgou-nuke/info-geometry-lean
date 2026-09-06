import InfoGeometry.Algebra.SplitQuaternionAutomorphismStructure
import InfoGeometry.Algebra.IdempotentProjector
import InfoGeometry.Algebra.CPTComplexStructure
import InfoGeometry.Algebra.Zorn.NullCone
import InfoGeometry.Clifford.SplitCliffordBoundaryPacket
import InfoGeometry.Algebra.AnyonFiniteSpinBraid
import InfoGeometry.Physics.HolyTrinity

/-!
# Repo-backed split-quaternion / Zorn / triality / braid fact index

This file is intentionally a fact index over already-compiled codebase owners.
It does not introduce heuristic physics claims.  It only re-exports theorem
surfaces that already exist in the repository and compile in the live checkout:

* concrete split-quaternion `M₂(ℝ)` determinant, inner-conjugation, and
  left/right structure transformations;
* general Peirce/idempotent algebra for diagonal/off-diagonal channels;
* Zorn null representatives for the two diagonal projectors and upper/lower
  off-diagonal lightrays;
* the `Cl(1,1)` chiral projectors and Euler sheet-reversal operator;
* the split `Cl(4,4)` boundary packet with label-level `S₃` rotation;
* a concrete finite `B₃` spin Artin braid packet;
* the existing finite null-cone quark readback and order-three triality label.

Anything stronger — full Skolem-Noether/PGL classification, global
`CO(2,2)`, global Dirac equation, neutrino PMNS theorem, triality-derived
fermion generations, physical confinement, or a QCD derivation — must be a
separate owner theorem, not inferred here.
-/

noncomputable section

namespace InfoGeometry.Algebra.SplitQuaternionZornTrialityFactIndex

open InfoGeometry.Algebra.SplitQuaternionAutomorphismStructure
open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.CPT
open InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-- Split-quaternion trace-zero determinant readback: the live owner proves the
`(1,2)` form `y² - x² - z²`. -/
theorem splitQuaternion_traceZero_signature (x y z : ℝ) :
    det2 (traceZeroMatrix x y z) = y ^ 2 - x ^ 2 - z ^ 2 :=
  det2_traceZeroMatrix x y z

/-- Full split-quaternion determinant readback: the live owner proves the
`(2,2)` coordinate form. -/
theorem splitQuaternion_full_signature (w x y z : ℝ) :
    det2 (InfoGeometry.Algebra.SplitQuaternionMatrices.splitQ w x y z) =
      w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 :=
  det2_splitQuaternion_signature w x y z

/-- Inner conjugation by an invertible `2×2` matrix is a concrete multiplicative
unital determinant-preserving automorphism packet. -/
theorem splitQuaternion_inner_automorphism_packet
    (A : Mat2) (hA : det2 A ≠ 0) :
    innerConj A (1 : Mat2) = 1 ∧
      (∀ X Y : Mat2, innerConj A (X * Y) = innerConj A X * innerConj A Y) ∧
      (∀ X : Mat2, det2 (innerConj A X) = det2 X) :=
  inner_automorphism_packet A hA

/-- The concrete structure-generator packet: left/right multiplication scales
the determinant and transpose preserves it. -/
theorem splitQuaternion_structure_group_generators_packet (A B X : Mat2) :
    det2 (leftRight A B X) = (det2 A * det2 B) * det2 X ∧
      det2 X.transpose = det2 X :=
  structure_group_generators_packet A B X

/-- Generic Peirce reconstruction from an idempotent. -/
theorem peirce_reconstruction {R : Type*} [Ring R] (p x : R) :
    peirce11 p x + peirce10 p x + peirce01 p x + peirce00 p x = x :=
  peirce_decomposition_sum p x

/-- Opposing off-diagonal Peirce channels repopulate the positive diagonal
sector. -/
theorem peirce_opposing_channels_to_11
    {R : Type*} [Ring R] {p : R} (hp : IsIdempotent p) (x y : R) :
    peirce10 p x * peirce01 p y = peirce11 p (x * compIdempotent p * y) :=
  peirce10_mul_peirce01 hp x y

/-- Opposing off-diagonal Peirce channels repopulate the complementary diagonal
sector. -/
theorem peirce_opposing_channels_to_00
    {R : Type*} [Ring R] {p : R} (hp : IsIdempotent p) (x y : R) :
    peirce01 p x * peirce10 p y = peirce00 p (x * p * y) :=
  peirce01_mul_peirce10 hp x y

/-- Zorn upper Peirce projector is null. -/
theorem zorn_pPlus_null {R : Type*} [CommRing R] :
    ZornMatrix.IsNull (pPlus : ZornMatrix R) :=
  pPlus_isNull

/-- Zorn lower Peirce projector is null. -/
theorem zorn_pMinus_null {R : Type*} [CommRing R] :
    ZornMatrix.IsNull (pMinus : ZornMatrix R) :=
  pMinus_isNull

/-- Every upper off-diagonal Zorn lightray is null. -/
theorem zorn_upper_lightray_null {R : Type*} [CommRing R]
    (v : Fin 3 → R) :
    ZornMatrix.IsNull (upperLightray v) :=
  upperLightray_isNull v

/-- Every lower off-diagonal Zorn lightray is null. -/
theorem zorn_lower_lightray_null {R : Type*} [CommRing R]
    (w : Fin 3 → R) :
    ZornMatrix.IsNull (lowerLightray w) :=
  lowerLightray_isNull w

/-- The `Cl(1,1)` chiral projectors are orthogonal. -/
theorem cl11_chiral_sheets_orthogonal
    {K : Type*} [Ring K] [Algebra ℝ K] (atom : Cl11Atom K) :
    Cl11AtomLaws atom → chiralProjectorPlus atom * chiralProjectorMinus atom = 0 := by
  intro h
  exact chiral_sheets_orthogonal atom h

/-- The `Cl(1,1)` chiral projectors partition unity. -/
theorem cl11_chiral_sheets_partition_unity
    {K : Type*} [Ring K] [Algebra ℝ K] (atom : Cl11Atom K) :
    chiralProjectorPlus atom + chiralProjectorMinus atom = 1 :=
  chiral_sheets_partition_unity atom

/-- The `Cl(1,1)` Euler operator reverses the two chiral sheets. -/
theorem cl11_euler_reverses_chiral_sheets
    {K : Type*} [Ring K] [Algebra ℝ K] (atom : Cl11Atom K) :
    Cl11AtomLaws atom →
      chiralProjectorPlus atom * EulerOperator atom =
        EulerOperator atom * chiralProjectorMinus atom := by
  intro h
  exact euler_operator_reverses_chiral_sheets atom h

/-- Concrete finite `B₃` spin operators satisfy the Artin braid packet. -/
theorem finite_b3_spin_artin_packet :
    b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ = b3SpinSwap0 ∧
    b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ = b3SpinSwap1 ∧
    b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ =
      b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨0, by decide⟩ ∘
        b3SpinArtinBraidOperators.generatorOperator ⟨1, by decide⟩ :=
  b3SpinArtinBraidOperators_packet

/-- Existing finite null-cone quark readback: under the supplied zero-diagonal
and lower-zero hypotheses, the Zorn determinant is zero. -/
theorem finite_null_cone_quark_readback
    (a b : ℚ) (x y : Fin 3 → ℚ) (hq : a = 0 ∧ b = 0 ∧ y = 0) :
    InfoGeometry.HolyTrinity.is_confined (a * b - ∑ i, x i * y i) :=
  InfoGeometry.HolyTrinity.quark_confinement a b x y hq

/-- Existing three-label triality cycle has order three. -/
theorem finite_triality_order_three (rep : InfoGeometry.HolyTrinity.D4Rep) :
    InfoGeometry.HolyTrinity.triality_shift
      (InfoGeometry.HolyTrinity.triality_shift
        (InfoGeometry.HolyTrinity.triality_shift rep)) = rep :=
  InfoGeometry.HolyTrinity.triality_order_three rep

end InfoGeometry.Algebra.SplitQuaternionZornTrialityFactIndex
