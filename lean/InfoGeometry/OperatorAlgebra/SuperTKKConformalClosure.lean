/-
InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean

Super-TKK conformal closure data.

This file records the safe algebraic version of the slogan:

  TKK closure defect can be absorbed by an extended graded algebra.

It does not assert a concrete `E7(7)`, affine Kac-Moody algebra, Virasoro
extension, or physical BPS sector. Those are later instantiations. Here we
package the proof-bearing data needed to say:

* mixed chiral supercharges generate the translation grade;
* same-chirality supercharges generate a grade-two topological sector;
* a TKK closure defect can be lifted into that grade-two sector;
* the scalar BPS charge norm may be calibrated as a trace of that lifted
  defect;
* in the stationary-curvature regime, Ricci flux is pure absorbed defect.

The concrete operatorial central-charge owner remains the existing canonical
lane in `Canonical.OperatorialCentralCharge`,
`Canonical.SuperchargeOddOddDecomposition`, and
`Canonical.SuperchargeCentralChargeClosure`. This file is only the abstract
super-TKK interface over `TKKConformalClosure.TKKRicciFluxDatum`.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.TKKConformalClosure

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure



/-! ## 1. Five-grade closure -/

/--
A five-grading on a Lie algebra with explicit coordinates.

The intended picture is

`L = g_-2 + g_-1 + g_0 + g_+1 + g_+2`.

The grade pieces are submodules. The linear equivalence gives actual grade
coordinates, and `decomposition_symm_apply` says reconstruction is the sum of
the five grade components.
-/
structure FiveGrading
    (L : Type*) [LieRing L] [LieAlgebra ℝ L] where
  gNegTwo : Submodule ℝ L
  gNegOne : Submodule ℝ L
  gZero : Submodule ℝ L
  gPosOne : Submodule ℝ L
  gPosTwo : Submodule ℝ L

  /-- Explicit five-grade coordinate decomposition. -/
  decomposition :
    L ≃ₗ[ℝ]
      ((((gNegTwo × gNegOne) × gZero) × gPosOne) × gPosTwo)

  /-- The inverse decomposition reconstructs by summing the grade components. -/
  decomposition_symm_apply :
    ∀ v :
      ((((gNegTwo × gNegOne) × gZero) × gPosOne) × gPosTwo),
      decomposition.symm v =
        (((((v.1.1.1.1 : L) + (v.1.1.1.2 : L)) +
            (v.1.1.2 : L)) +
            (v.1.2 : L)) +
            (v.2 : L))

  /-- `[g_-1, g_+1] ⊆ g_0`. -/
  bracket_neg_one_pos_one :
    ∀ X Y : L, X ∈ gNegOne → Y ∈ gPosOne → ⁅X, Y⁆ ∈ gZero

  /-- `[g_0, g_0] ⊆ g_0`; the grade-zero sector is a Lie subalgebra. -/
  bracket_zero_zero :
    ∀ X Y : L, X ∈ gZero → Y ∈ gZero → ⁅X, Y⁆ ∈ gZero

  /-- `[g_+1, g_+1] ⊆ g_+2`. -/
  bracket_pos_one_pos_one :
    ∀ X Y : L, X ∈ gPosOne → Y ∈ gPosOne → ⁅X, Y⁆ ∈ gPosTwo

  /-- `[g_-1, g_-1] ⊆ g_-2`. -/
  bracket_neg_one_neg_one :
    ∀ X Y : L, X ∈ gNegOne → Y ∈ gNegOne → ⁅X, Y⁆ ∈ gNegTwo

  /-- `[g_0, g_+2] ⊆ g_+2`. -/
  bracket_zero_pos_two :
    ∀ X Y : L, X ∈ gZero → Y ∈ gPosTwo → ⁅X, Y⁆ ∈ gPosTwo

  /-- `[g_0, g_-2] ⊆ g_-2`. -/
  bracket_zero_neg_two :
    ∀ X Y : L, X ∈ gZero → Y ∈ gNegTwo → ⁅X, Y⁆ ∈ gNegTwo

  /-- `[g_+2, g_+2] = 0`; the positive extremal sector is abelian. -/
  bracket_pos_two_pos_two_zero :
    ∀ X Y : L, X ∈ gPosTwo → Y ∈ gPosTwo → ⁅X, Y⁆ = 0

namespace FiveGrading

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (G : FiveGrading L)

/-- Coordinates of an element in the five-grade decomposition. -/
def coordinates
    (X : L) :
    ((((G.gNegTwo × G.gNegOne) × G.gZero) × G.gPosOne) × G.gPosTwo) :=
  G.decomposition X

/-- Reconstructing the coordinates of `X` gives back `X`. -/
theorem recompose_coordinates
    (X : L) :
    G.decomposition.symm (G.coordinates X) = X := by
  simp [coordinates]

/-- Decomposing a reconstructed coordinate tuple gives back the tuple. -/
theorem coordinates_recompose
    (v :
      ((((G.gNegTwo × G.gNegOne) × G.gZero) × G.gPosOne) × G.gPosTwo)) :
    G.coordinates (G.decomposition.symm v) = v := by
  simp [coordinates]

/-- Reconstruction is the actual sum of the five grade components. -/
theorem decomposition_sum
    (v :
      ((((G.gNegTwo × G.gNegOne) × G.gZero) × G.gPosOne) × G.gPosTwo)) :
    G.decomposition.symm v =
      (((((v.1.1.1.1 : L) + (v.1.1.1.2 : L)) +
          (v.1.1.2 : L)) +
          (v.1.2 : L)) +
          (v.2 : L)) :=
  G.decomposition_symm_apply v

/-- Re-export: the mixed outer bracket lands in grade zero. -/
theorem neg_one_pos_one_mem_zero
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.bracket_neg_one_pos_one X Y hX hY

/-- The reversed mixed bracket lands in grade zero by Lie skew-symmetry. -/
theorem pos_one_neg_one_mem_zero
    {X Y : L}
    (hX : X ∈ G.gPosOne)
    (hY : Y ∈ G.gNegOne) :
    ⁅X, Y⁆ ∈ G.gZero := by
  rw [← lie_skew]
  exact G.gZero.neg_mem (G.bracket_neg_one_pos_one Y X hY hX)

/-- Re-export: grade zero is closed under the bracket. -/
theorem zero_zero_mem_zero
    {X Y : L}
    (hX : X ∈ G.gZero)
    (hY : Y ∈ G.gZero) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.bracket_zero_zero X Y hX hY

/-- Re-export: two positive grade-one elements bracket into grade two. -/
theorem pos_one_pos_one_mem_pos_two
    {X Y : L}
    (hX : X ∈ G.gPosOne)
    (hY : Y ∈ G.gPosOne) :
    ⁅X, Y⁆ ∈ G.gPosTwo :=
  G.bracket_pos_one_pos_one X Y hX hY

/-- Re-export: two negative grade-one elements bracket into grade negative two. -/
theorem neg_one_neg_one_mem_neg_two
    {X Y : L}
    (hX : X ∈ G.gNegOne)
    (hY : Y ∈ G.gNegOne) :
    ⁅X, Y⁆ ∈ G.gNegTwo :=
  G.bracket_neg_one_neg_one X Y hX hY

/-- Re-export: grade zero acts on the positive grade-two sector. -/
theorem zero_pos_two_mem_pos_two
    {X Y : L}
    (hX : X ∈ G.gZero)
    (hY : Y ∈ G.gPosTwo) :
    ⁅X, Y⁆ ∈ G.gPosTwo :=
  G.bracket_zero_pos_two X Y hX hY

/-- Re-export: grade zero acts on the negative grade-two sector. -/
theorem zero_neg_two_mem_neg_two
    {X Y : L}
    (hX : X ∈ G.gZero)
    (hY : Y ∈ G.gNegTwo) :
    ⁅X, Y⁆ ∈ G.gNegTwo :=
  G.bracket_zero_neg_two X Y hX hY

/-- The reversed positive extremal action follows from Lie skew-symmetry. -/
theorem pos_two_zero_mem_pos_two
    {X Y : L}
    (hX : X ∈ G.gPosTwo)
    (hY : Y ∈ G.gZero) :
    ⁅X, Y⁆ ∈ G.gPosTwo := by
  rw [← lie_skew]
  exact G.gPosTwo.neg_mem (G.bracket_zero_pos_two Y X hY hX)

/-- The reversed negative extremal action follows from Lie skew-symmetry. -/
theorem neg_two_zero_mem_neg_two
    {X Y : L}
    (hX : X ∈ G.gNegTwo)
    (hY : Y ∈ G.gZero) :
    ⁅X, Y⁆ ∈ G.gNegTwo := by
  rw [← lie_skew]
  exact G.gNegTwo.neg_mem (G.bracket_zero_neg_two Y X hY hX)

/-- The positive grade-two sector is closed under addition. -/
theorem pos_two_add_mem
    {X Y : L}
    (hX : X ∈ G.gPosTwo)
    (hY : Y ∈ G.gPosTwo) :
    X + Y ∈ G.gPosTwo :=
  G.gPosTwo.add_mem hX hY

/-- The positive grade-two sector is abelian. -/
theorem pos_two_is_abelian
    {X Y : L}
    (hX : X ∈ G.gPosTwo)
    (hY : Y ∈ G.gPosTwo) :
    ⁅X, Y⁆ = 0 :=
  G.bracket_pos_two_pos_two_zero X Y hX hY

end FiveGrading

/-! ## 2. Supercharge square-root data -/

/--
Supercharge square-root data over a five-graded even Lie algebra.

`Odd` is the odd/supercharge carrier.

`qLeft` and `qRight` are the two chiral supercharge sectors.

`superAnticommutator` is the supplied even-valued anticommutator readout. The
module does not derive a concrete Clifford/CAR representation; it records the
algebraic consequences once that representation is installed.
-/
structure SuperchargeSquareRoot
    (L Odd : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Odd] [Module ℝ Odd]
    (G : FiveGrading L) where
  qLeft : Submodule ℝ Odd
  qRight : Submodule ℝ Odd

  /-- Even-valued anticommutator of odd supercharges. -/
  superAnticommutator :
    Odd →ₗ[ℝ] Odd →ₗ[ℝ] L

  /-- The super-anticommutator is symmetric. -/
  superAnticommutator_symm :
    ∀ Q R : Odd, superAnticommutator Q R = superAnticommutator R Q

  /--
  Mixed chirality lands in the translation grade.
  -/
  mixed_chirality_mem_translation :
    ∀ Q Qbar : Odd,
      Q ∈ qLeft →
      Qbar ∈ qRight →
        superAnticommutator Q Qbar ∈ G.gNegOne

  /--
  Left-left same-chirality anticommutators land in the positive grade-two
  topological sector.
  -/
  left_left_mem_pos_two :
    ∀ Q R : Odd,
      Q ∈ qLeft →
      R ∈ qLeft →
        superAnticommutator Q R ∈ G.gPosTwo

  /--
  Right-right same-chirality anticommutators land in the negative grade-two
  topological sector.
  -/
  right_right_mem_neg_two :
    ∀ Q R : Odd,
      Q ∈ qRight →
      R ∈ qRight →
        superAnticommutator Q R ∈ G.gNegTwo

  /-- Every translation-grade element has a mixed-supercharge representative. -/
  mixed_translation_surjective :
    ∀ P : L,
      P ∈ G.gNegOne →
        ∃ Q : Odd, ∃ Qbar : Odd,
          Q ∈ qLeft ∧
          Qbar ∈ qRight ∧
          superAnticommutator Q Qbar = P

  /-- Every positive grade-two element has a left-left representative. -/
  left_left_pos_two_surjective :
    ∀ Z : L,
      Z ∈ G.gPosTwo →
        ∃ Q : Odd, ∃ R : Odd,
          Q ∈ qLeft ∧
          R ∈ qLeft ∧
          superAnticommutator Q R = Z

  /-- Every negative grade-two element has a right-right representative. -/
  right_right_neg_two_surjective :
    ∀ Z : L,
      Z ∈ G.gNegTwo →
        ∃ Q : Odd, ∃ R : Odd,
          Q ∈ qRight ∧
          R ∈ qRight ∧
          superAnticommutator Q R = Z

namespace SuperchargeSquareRoot

variable
    {L Odd : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Odd] [Module ℝ Odd]
    {G : FiveGrading L}

variable (S : SuperchargeSquareRoot L Odd G)

/-- Mixed chiral supercharges land in a translation-grade element. -/
theorem mixed_supercharges_mem_translation
    {Q Qbar : Odd}
    (hQ : Q ∈ S.qLeft)
    (hQbar : Qbar ∈ S.qRight) :
    S.superAnticommutator Q Qbar ∈ G.gNegOne :=
  S.mixed_chirality_mem_translation Q Qbar hQ hQbar

/-- Right-left mixed order also lands in the translation grade, by symmetry. -/
theorem mixed_supercharges_mem_translation_right_left
    {Qbar Q : Odd}
    (hQbar : Qbar ∈ S.qRight)
    (hQ : Q ∈ S.qLeft) :
    S.superAnticommutator Qbar Q ∈ G.gNegOne := by
  rw [S.superAnticommutator_symm Qbar Q]
  exact S.mixed_supercharges_mem_translation hQ hQbar

/-- Same left chirality lands in a positive grade-two charge. -/
theorem left_left_mem_grade_two
    {Q R : Odd}
    (hQ : Q ∈ S.qLeft)
    (hR : R ∈ S.qLeft) :
    S.superAnticommutator Q R ∈ G.gPosTwo :=
  S.left_left_mem_pos_two Q R hQ hR

/-- Same right chirality lands in a negative grade-two charge. -/
theorem right_right_mem_grade_two
    {Q R : Odd}
    (hQ : Q ∈ S.qRight)
    (hR : R ∈ S.qRight) :
    S.superAnticommutator Q R ∈ G.gNegTwo :=
  S.right_right_mem_neg_two Q R hQ hR

/-- Re-export symmetry of the super-anticommutator. -/
theorem superAnticommutator_comm
    (Q R : Odd) :
    S.superAnticommutator Q R = S.superAnticommutator R Q :=
  S.superAnticommutator_symm Q R

/-- Same left chirality maps to grade two in the reversed order as well. -/
theorem left_left_mem_grade_two_swap
    {Q R : Odd}
    (hQ : Q ∈ S.qLeft)
    (hR : R ∈ S.qLeft) :
    S.superAnticommutator R Q ∈ G.gPosTwo := by
  rw [← S.superAnticommutator_comm Q R]
  exact S.left_left_mem_grade_two hQ hR

/-- Every translation-grade element has a mixed-supercharge representative. -/
theorem exists_mixed_supercharge_for_translation
    {P : L}
    (hP : P ∈ G.gNegOne) :
    ∃ Q : Odd, ∃ Qbar : Odd,
      Q ∈ S.qLeft ∧
      Qbar ∈ S.qRight ∧
      S.superAnticommutator Q Qbar = P :=
  S.mixed_translation_surjective P hP

/-- Every positive grade-two element has a left-left supercharge representative. -/
theorem exists_left_left_supercharge_for_pos_two
    {Z : L}
    (hZ : Z ∈ G.gPosTwo) :
    ∃ Q : Odd, ∃ R : Odd,
      Q ∈ S.qLeft ∧
      R ∈ S.qLeft ∧
      S.superAnticommutator Q R = Z :=
  S.left_left_pos_two_surjective Z hZ

/-- Every negative grade-two element has a right-right supercharge representative. -/
theorem exists_right_right_supercharge_for_neg_two
    {Z : L}
    (hZ : Z ∈ G.gNegTwo) :
    ∃ Q : Odd, ∃ R : Odd,
      Q ∈ S.qRight ∧
      R ∈ S.qRight ∧
      S.superAnticommutator Q R = Z :=
  S.right_right_neg_two_surjective Z hZ

/-! ## 2A. Finite bonding-map preservation lemmas -/

/--
A finite bonding/intertwiner map preserves mixed-supercharge translation
charges, provided it preserves chirality and the super-anticommutator.

This is the local induction step for the translation lane.
-/
theorem map_mixed_supercharge_mem_translation
    {L₁ L₂ Odd₁ Odd₂ : Type*}
    [LieRing L₁] [LieAlgebra ℝ L₁]
    [LieRing L₂] [LieAlgebra ℝ L₂]
    [AddCommGroup Odd₁] [Module ℝ Odd₁]
    [AddCommGroup Odd₂] [Module ℝ Odd₂]
    {G₁ : FiveGrading L₁}
    {G₂ : FiveGrading L₂}
    (S₁ : SuperchargeSquareRoot L₁ Odd₁ G₁)
    (S₂ : SuperchargeSquareRoot L₂ Odd₂ G₂)
    (fL : L₁ →ₗ[ℝ] L₂)
    (fOdd : Odd₁ →ₗ[ℝ] Odd₂)
    (hLeft :
      ∀ Q : Odd₁, Q ∈ S₁.qLeft → fOdd Q ∈ S₂.qLeft)
    (hRight :
      ∀ Q : Odd₁, Q ∈ S₁.qRight → fOdd Q ∈ S₂.qRight)
    (hSuper :
      ∀ Q R : Odd₁,
        fL (S₁.superAnticommutator Q R) =
          S₂.superAnticommutator (fOdd Q) (fOdd R))
    {Q R : Odd₁}
    (hQ : Q ∈ S₁.qLeft)
    (hR : R ∈ S₁.qRight) :
    fL (S₁.superAnticommutator Q R) ∈ G₂.gNegOne := by
  rw [hSuper Q R]
  exact
    S₂.mixed_supercharges_mem_translation
      (hLeft Q hQ)
      (hRight R hR)

/--
A finite bonding/intertwiner map preserves same-left-chirality grade-two
central/topological charges, provided it preserves chirality and the
super-anticommutator.

This is the local induction step for the positive central lane.
-/
theorem map_left_left_supercharge_mem_pos_two
    {L₁ L₂ Odd₁ Odd₂ : Type*}
    [LieRing L₁] [LieAlgebra ℝ L₁]
    [LieRing L₂] [LieAlgebra ℝ L₂]
    [AddCommGroup Odd₁] [Module ℝ Odd₁]
    [AddCommGroup Odd₂] [Module ℝ Odd₂]
    {G₁ : FiveGrading L₁}
    {G₂ : FiveGrading L₂}
    (S₁ : SuperchargeSquareRoot L₁ Odd₁ G₁)
    (S₂ : SuperchargeSquareRoot L₂ Odd₂ G₂)
    (fL : L₁ →ₗ[ℝ] L₂)
    (fOdd : Odd₁ →ₗ[ℝ] Odd₂)
    (hLeft :
      ∀ Q : Odd₁, Q ∈ S₁.qLeft → fOdd Q ∈ S₂.qLeft)
    (hSuper :
      ∀ Q R : Odd₁,
        fL (S₁.superAnticommutator Q R) =
          S₂.superAnticommutator (fOdd Q) (fOdd R))
    {Q R : Odd₁}
    (hQ : Q ∈ S₁.qLeft)
    (hR : R ∈ S₁.qLeft) :
    fL (S₁.superAnticommutator Q R) ∈ G₂.gPosTwo := by
  rw [hSuper Q R]
  exact
    S₂.left_left_mem_grade_two
      (hLeft Q hQ)
      (hLeft R hR)

/--
Finite bonding maps preserve the abelian closure of same-left grade-two
charges.

If two source charges are represented by left-left supercharge pairs, then
their transported target charges commute because they land in the target
positive grade-two sector.
-/
theorem map_left_left_supercharge_charges_commute
    {L₁ L₂ Odd₁ Odd₂ : Type*}
    [LieRing L₁] [LieAlgebra ℝ L₁]
    [LieRing L₂] [LieAlgebra ℝ L₂]
    [AddCommGroup Odd₁] [Module ℝ Odd₁]
    [AddCommGroup Odd₂] [Module ℝ Odd₂]
    {G₁ : FiveGrading L₁}
    {G₂ : FiveGrading L₂}
    (S₁ : SuperchargeSquareRoot L₁ Odd₁ G₁)
    (S₂ : SuperchargeSquareRoot L₂ Odd₂ G₂)
    (fL : L₁ →ₗ[ℝ] L₂)
    (fOdd : Odd₁ →ₗ[ℝ] Odd₂)
    (hLeft :
      ∀ Q : Odd₁, Q ∈ S₁.qLeft → fOdd Q ∈ S₂.qLeft)
    (hSuper :
      ∀ Q R : Odd₁,
        fL (S₁.superAnticommutator Q R) =
          S₂.superAnticommutator (fOdd Q) (fOdd R))
    {Q R Q' R' : Odd₁}
    (hQ : Q ∈ S₁.qLeft)
    (hR : R ∈ S₁.qLeft)
    (hQ' : Q' ∈ S₁.qLeft)
    (hR' : R' ∈ S₁.qLeft) :
    ⁅fL (S₁.superAnticommutator Q R),
      fL (S₁.superAnticommutator Q' R')⁆ = 0 := by
  rw [hSuper Q R, hSuper Q' R']
  exact
    G₂.pos_two_is_abelian
      (S₂.left_left_mem_grade_two
        (hLeft Q hQ)
        (hLeft R hR))
      (S₂.left_left_mem_grade_two
        (hLeft Q' hQ')
        (hLeft R' hR'))

end SuperchargeSquareRoot

/-! ## 3. TKK defect absorption into grade two -/

/--
Absorption of a TKK closure defect by a five-graded super-TKK extension.

`geometryLift` maps geometric readouts into the enlarged even Lie algebra.

The lifted defect is not merely assumed to lie in `g_+2`. It is represented as
a same-left-chirality supercharge anticommutator.
-/
structure SuperTKKDefectAbsorption
    (L Odd State Geometry : Type*)
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Odd] [Module ℝ Odd]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    (R : InfoGeometry.OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum L State Geometry) where
  grading :
    FiveGrading L

  supercharges :
    SuperchargeSquareRoot L Odd grading

  /-- Lift a geometric readout into the enlarged even algebra. -/
  geometryLift :
    Geometry →ₗ[ℝ] L

  /--
  Constructive absorption property.

  For every closure defect, produce two left-chiral supercharges whose
  anticommutator is exactly the lifted defect.
  -/
  defect_as_left_left_supercharge :
    ∀ X : L, ∀ s : State,
      ∃ Q : Odd, ∃ Rq : Odd,
        Q ∈ supercharges.qLeft ∧
        Rq ∈ supercharges.qLeft ∧
        geometryLift (R.closureDefect.defect X s) =
          supercharges.superAnticommutator Q Rq

namespace SuperTKKDefectAbsorption

variable
    {L Odd State Geometry : Type*}
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Odd] [Module ℝ Odd]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {R : InfoGeometry.OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum L State Geometry}

variable (A : SuperTKKDefectAbsorption L Odd State Geometry R)

/-- The TKK closure defect has an explicit left-left supercharge square. -/
theorem closure_defect_has_left_left_square
    (X : L)
    (s : State) :
    ∃ Q : Odd, ∃ Rq : Odd,
      Q ∈ A.supercharges.qLeft ∧
      Rq ∈ A.supercharges.qLeft ∧
      A.geometryLift (R.closureDefect.defect X s) =
        A.supercharges.superAnticommutator Q Rq :=
  A.defect_as_left_left_supercharge X s

/--
The TKK closure defect lifts into the grade-two sector, derived from the
explicit same-chirality supercharge representative.
-/
theorem closure_defect_absorbed_as_grade_two
    (X : L)
    (s : State) :
    A.geometryLift (R.closureDefect.defect X s) ∈ A.grading.gPosTwo := by
  rcases A.closure_defect_has_left_left_square X s with
    ⟨Q, Rq, hQ, hR, hdef⟩
  rw [hdef]
  exact A.supercharges.left_left_mem_grade_two hQ hR

/-- Lifted closure defects commute inside the positive grade-two sector. -/
theorem closure_defect_is_abelian
    (X Y : L)
    (s t : State) :
    ⁅A.geometryLift (R.closureDefect.defect X s),
      A.geometryLift (R.closureDefect.defect Y t)⁆ = 0 :=
  A.grading.pos_two_is_abelian
    (A.closure_defect_absorbed_as_grade_two X s)
    (A.closure_defect_absorbed_as_grade_two Y t)

/-- Mixed supercharges generate a translation-grade representative. -/
theorem mixed_supercharges_generate_translation
    {P : L}
    (hP : P ∈ A.grading.gNegOne) :
    ∃ Q : Odd, ∃ Qbar : Odd,
      Q ∈ A.supercharges.qLeft ∧
      Qbar ∈ A.supercharges.qRight ∧
      A.supercharges.superAnticommutator Q Qbar = P :=
  A.supercharges.exists_mixed_supercharge_for_translation hP

/-- Same left chirality generates a positive grade-two representative. -/
theorem left_chirality_generates_grade_two_charge
    {Z : L}
    (hZ : Z ∈ A.grading.gPosTwo) :
    ∃ Q : Odd, ∃ Q' : Odd,
      Q ∈ A.supercharges.qLeft ∧
      Q' ∈ A.supercharges.qLeft ∧
      A.supercharges.superAnticommutator Q Q' = Z :=
  A.supercharges.exists_left_left_supercharge_for_pos_two hZ

/--
Lifted Ricci flux is the lifted sum of curvature variation and closure defect.
-/
theorem lifted_ricciFlux_eq_lifted_curvature_plus_defect
    (X : L)
    (s : State) :
    A.geometryLift (R.ricciFlux X s) =
      A.geometryLift
        (R.derivativeAlong.deriv R.curvatureReadout.curvature X s) +
        A.geometryLift (R.closureDefect.defect X s) := by
  rw [R.ricciFlux_def X s]
  exact A.geometryLift.map_add _ _

/--
If curvature is stationary along `X` at `s`, the lifted Ricci flux is absorbed
as a grade-two element.
-/
theorem lifted_ricciFlux_mem_grade_two_of_curvature_stationary
    (X : L)
    (s : State)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0) :
    A.geometryLift (R.ricciFlux X s) ∈ A.grading.gPosTwo := by
  have hflux :
      R.ricciFlux X s = R.closureDefect.defect X s := by
    rw [R.ricciFlux_def X s, hstat, zero_add]
  rw [hflux]
  exact A.closure_defect_absorbed_as_grade_two X s

/--
If curvature is stationary, the lifted Ricci flux has an explicit left-left
supercharge-square representative.
-/
theorem exists_left_left_square_for_lifted_ricciFlux_of_curvature_stationary
    (X : L)
    (s : State)
    (hstat :
      R.derivativeAlong.deriv R.curvatureReadout.curvature X s = 0) :
    ∃ Q : Odd, ∃ Q' : Odd,
      Q ∈ A.supercharges.qLeft ∧
      Q' ∈ A.supercharges.qLeft ∧
      A.geometryLift (R.ricciFlux X s) =
        A.supercharges.superAnticommutator Q Q' := by
  rcases A.closure_defect_has_left_left_square X s with
    ⟨Q, Q', hQ, hQ', hdef⟩
  refine ⟨Q, Q', hQ, hQ', ?_⟩
  rw [R.ricciFlux_def X s, hstat, zero_add]
  exact hdef

end SuperTKKDefectAbsorption

/-! ## 4. BPS-style charge-norm ledger -/

/--
A scalar BPS-style charge-norm ledger.

This is not a proof of supersymmetry or a physical mass formula. It records
the formal consequence of a supplied energy/charge-norm bound and a supplied
heat-as-excess law.

`chargeNorm` is nonnegative by construction, avoiding a signed central-charge
readout in the scalar BPS comparison.
-/
structure BPSCentralChargeLedger
    (State : Type*) where
  energy : State → ℝ
  chargeNorm : State → ℝ
  heat : State → ℝ

  /-- The charge norm is nonnegative. -/
  chargeNorm_nonneg :
    ∀ s : State, 0 ≤ chargeNorm s

  /-- Charge norm is bounded above by energy. -/
  chargeNorm_le_energy :
    ∀ s : State, chargeNorm s ≤ energy s

  /-- Heat is the excess over the charge norm. -/
  heat_eq_energy_sub_chargeNorm :
    ∀ s : State, heat s = energy s - chargeNorm s

namespace BPSCentralChargeLedger

variable {State : Type*}
variable (B : BPSCentralChargeLedger State)

/-- A BPS-saturated state has energy equal to charge norm. -/
def IsBPS
    (s : State) : Prop :=
  B.energy s = B.chargeNorm s

/-- Energy is nonnegative under the BPS-style bound. -/
theorem energy_nonneg
    (s : State) :
    0 ≤ B.energy s := by
  linarith [B.chargeNorm_nonneg s, B.chargeNorm_le_energy s]

/-- The BPS ledger gives nonnegative heat. -/
theorem heat_nonneg
    (s : State) :
    0 ≤ B.heat s := by
  rw [B.heat_eq_energy_sub_chargeNorm s]
  exact sub_nonneg.mpr (B.chargeNorm_le_energy s)

/-- BPS saturation kills the excess heat readout. -/
theorem heat_eq_zero_of_bps
    {s : State}
    (hBPS : B.IsBPS s) :
    B.heat s = 0 := by
  rw [B.heat_eq_energy_sub_chargeNorm s, hBPS]
  ring

/-- Zero excess heat implies BPS saturation. -/
theorem bps_of_heat_eq_zero
    {s : State}
    (hheat : B.heat s = 0) :
    B.IsBPS s := by
  unfold IsBPS
  rw [B.heat_eq_energy_sub_chargeNorm s] at hheat
  linarith

/-- Vanishing excess heat is equivalent to BPS saturation in this ledger. -/
theorem heat_eq_zero_iff_bps
    (s : State) :
    B.heat s = 0 ↔ B.IsBPS s := by
  constructor
  · intro h
    exact B.bps_of_heat_eq_zero h
  · intro h
    exact B.heat_eq_zero_of_bps h

end BPSCentralChargeLedger

/-! ## 5. BPS defect bridge -/

/--
Bridge from the absorbed TKK defect to a scalar BPS charge norm.

This is a calibration layer. It does not assert that every BPS charge is a TKK
defect trace; it records the consequences once a linear trace and equality law
are supplied.
-/
structure BPSDefectBridge
    {L Odd State Geometry : Type*}
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Odd] [Module ℝ Odd]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {R : InfoGeometry.OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum L State Geometry}
    (A : SuperTKKDefectAbsorption L Odd State Geometry R)
    (B : BPSCentralChargeLedger State) where
  /-- Linear readout evaluating the lifted defect as a scalar charge norm. -/
  chargeNormTrace : L →ₗ[ℝ] ℝ

  /-- The scalar charge norm is the trace of the lifted TKK defect. -/
  chargeNorm_eq_trace_defect :
    ∀ X : L, ∀ s : State,
      B.chargeNorm s =
        chargeNormTrace (A.geometryLift (R.closureDefect.defect X s))

namespace BPSDefectBridge

variable
    {L Odd State Geometry : Type*}
    [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Odd] [Module ℝ Odd]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Geometry] [Module ℝ Geometry]
    {R : InfoGeometry.OperatorAlgebra.TKKConformalClosure.TKKRicciFluxDatum L State Geometry}
    {A : SuperTKKDefectAbsorption L Odd State Geometry R}
    {B : BPSCentralChargeLedger State}

variable (Bridge : BPSDefectBridge A B)

/-- Re-export the charge-norm / defect trace calibration. -/
theorem chargeNorm_eq_trace_defect_readout
    (X : L)
    (s : State) :
    B.chargeNorm s =
      Bridge.chargeNormTrace (A.geometryLift (R.closureDefect.defect X s)) :=
  Bridge.chargeNorm_eq_trace_defect X s

/-- Heat is energy minus the traced absorbed TKK defect charge norm. -/
theorem heat_eq_energy_sub_trace_defect
    (X : L)
    (s : State) :
    B.heat s =
      B.energy s -
        Bridge.chargeNormTrace (A.geometryLift (R.closureDefect.defect X s)) := by
  rw [← Bridge.chargeNorm_eq_trace_defect_readout X s]
  exact B.heat_eq_energy_sub_chargeNorm s

set_option linter.unusedSectionVars false in
/-- BPS saturation still forces zero heat after defect-trace calibration. -/
theorem heat_eq_zero_of_bps
    {s : State}
    (hBPS : B.IsBPS s) :
    B.heat s = 0 :=
  B.heat_eq_zero_of_bps hBPS

end BPSDefectBridge

end InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
