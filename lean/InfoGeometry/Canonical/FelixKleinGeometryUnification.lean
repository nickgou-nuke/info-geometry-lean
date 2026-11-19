/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.KinematicCliffordAlgebra
import InfoGeometry.Core.HomogeneousSpaces
import InfoGeometry.Erlangen.InvariantGeometry
import InfoGeometry.Detector.ErlangenProgramInvariants
import InfoGeometry.Canonical.OperatorErlangenFixedPoints
import InfoGeometry.Canonical.OperatorErlangenGaloisConnection
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Projective.KleinQuadricPlucker
import InfoGeometry.Projective.DahmPluckerKleinCollineation
import InfoGeometry.Canonical.FierzKleinFoundation
import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Projective.ExteriorKleinProjective
import InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
import InfoGeometry.Projective.CrossRatioPGL2
import InfoGeometry.Projective.KleinCrossRatioInvariant
import InfoGeometry.Projective.NoncommutativeCrossRatio
import InfoGeometry.Canonical.BipolarCayleyKleinPristineChain
import InfoGeometry.Canonical.KleinFourRealizations
import InfoGeometry.Canonical.KleinDeckFiveGradeAction

/-!
# Felix Klein Geometry Unification Across Five Mathematical Corridors

This canonical bridge unifies the five Felix Klein and Erlangen geometry
corridors across `info-geometry-lean` without creating duplicate carriers or
wrapping hypotheses into opaque records:

1. **Classical Homogeneous Spaces (`G / H`) & Erlangen Invariants**:
   Connects `Core.IsHomogeneousSpace`, `Erlangen.InvariantGeometry`,
   `DetectorGeometry.ErlangenProgramInvariants.KleinGeometry`, and
   `OperatorErlangenFixedPoints.orbit_quotient_stabilizer_equiv` via the
   equivariant reconstruction `X ≃ G ⧸ stabilizer G x₀` and single-point
   constancy of invariant readouts and predicates.
2. **Operator Erlangen 2.0 & Galois Connection**:
   Equates `OperatorAlgebra.SymmetryAction G Op` with `G →* RingAut Op`,
   induces `MulSemiringAction G Op`, proves
   `(invariantSubring α).toSubsemiring = fixedPointSubsemiring ⊤`, connects to the
   subgroup–observable Galois connection, and grounds symmetry invariants in the
   noncommutative Cantor double-cylinder colimit and the Klein-bottle
   deck action on split `Cl(5,5)`.
3. **Klein Quadric (`Q ⊂ ℙ⁵`), `GL(4)`/`SL(4)` Action, & Noncommutative Defect**:
   Equates all four Plücker/Klein quadratic carriers (`Projective.KleinQuadric.Plucker6`,
   `KleinQuadricPlucker.Plucker6`, `Bivector4`, `⋀[ℝ]^2 Vec4`) and bridges polar
   bilinear forms between the two `Plucker6` owners, establishes
   Cauchy–Binet functoriality for `DahmPluckerKleinCollineation.compound`,
   proves `GL(4)` invariance of the Klein quadric and `SL(4)` invariance of
   `kleinQ`, and witnesses non-vanishing spin-algebra commutator defects.
4. **Projective Cross-Ratio & Klein Four-Group `V₄` Stabilization**:
   Aligns `CrossRatioPGL2`, `KleinCrossRatioInvariant.HomPoint2`, and
   `NoncommutativeCrossRatio`, proves the Plücker harmonic complement law,
   formalizes Klein's `V₄` double-transposition invariance and `GL(2,ℂ)`
   invariance (`IsInvariantReadout`), and separates commutative cancellation
   from noncommutative `Quaternion ℝ` affine conjugation defects.
5. **Kinematic Cayley–Klein Signatures & Master Synthesis**:
   Evaluates `kinematicGenerator` squares across elliptic (`-1`), parabolic
   (`0`), and hyperbolic (`+1`) signatures alongside the split-octonion /
   matrix eight-dimensional non-multiplicativity barrier.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization
open scoped Quaternion

namespace InfoGeometry.Canonical.FelixKleinGeometryUnification

open InfoGeometry.Algebra.FiniteSpin (J_plus J_minus j_plus_j_minus_ne)

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem felixKleinUnification_exists_noncomm_pair :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℂ, a * b ≠ b * a :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

/-- Explicit non-commutativity witness on `Matrix (Fin 4) (Fin 4) R` for any nontrivial ring `R`. -/
theorem felixKleinUnification_mat4_exists_noncomm_pair
    {R : Type*} [Ring R] [Nontrivial R] :
    ∃ a b : Matrix (Fin 4) (Fin 4) R, a * b ≠ b * a := by
  refine ⟨Matrix.single 0 1 (1 : R), Matrix.single 1 0 (1 : R), ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M 0 0) h
  simp [Matrix.mul_apply, Matrix.single_apply] at h00

/-!
## Corridor 1: Classical Homogeneous Spaces (`G / H`) and Erlangen Invariants
-/

section ClassicalHomogeneousErlangen

open InfoGeometry.Core
open InfoGeometry.Erlangen.InvariantGeometry

/-- Any standard Mathlib `MulAction G X` gives a canonical `DetectorGeometry.KleinGeometry G X`. -/
@[instance_reducible]
def mulActionKleinGeometry (G X : Type*) [Group G] [MulAction G X] :
    DetectorGeometry.ErlangenProgramInvariants.KleinGeometry G X where
  smul := (· • ·)

/-- Detector `IsKleinInvariant` coincides with Erlangen `IsInvariantReadout` for any `MulAction`. -/
theorem isKleinInvariant_iff_isInvariantReadout
    {G X β : Type*} [Group G] [MulAction G X] (f : X → β) :
    @DetectorGeometry.ErlangenProgramInvariants.IsKleinInvariant G X β
        (mulActionKleinGeometry G X) f ↔
      IsInvariantReadout G X f := by
  dsimp [DetectorGeometry.ErlangenProgramInvariants.IsKleinInvariant,
    mulActionKleinGeometry, IsInvariantReadout]
  exact Iff.rfl

/-- Every group-invariant readout on a homogeneous space is globally constant. -/
theorem invariantReadout_const_of_homogeneousSpace
    {G X β : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X)
    {f : X → β} (hf : IsInvariantReadout G X f)
    (x y : X) :
    f x = f y := by
  obtain ⟨g, hg⟩ := hHom x y
  rw [← hg]
  exact (hf g x).symm

/-- Every group-invariant predicate on a homogeneous space satisfies a global dichotomy. -/
theorem geometricInvariant_dichotomy_of_homogeneousSpace
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X)
    {P : X → Prop} (hP : IsGeometricInvariant G X P) :
    (∀ x : X, P x) ∨ (∀ x : X, ¬ P x) := by
  by_cases hne : ∃ x₀ : X, P x₀
  · left
    obtain ⟨x₀, hx₀⟩ := hne
    intro y
    obtain ⟨g, hg⟩ := hHom x₀ y
    rw [← hg]
    exact (hP g x₀).mpr hx₀
  · right
    intro y hy
    exact hne ⟨y, hy⟩

/-- Specialization to Cartan fixed-subgroup quotients `G ⧸ θ.fixedSubgroup`. -/
theorem cartan_fixedQuotient_invariantReadout_const
    {G β : Type*} [Group G] (θ : CartanInvolution G)
    {f : (G ⧸ θ.fixedSubgroup) → β}
    (hf : IsInvariantReadout G (G ⧸ θ.fixedSubgroup) f)
    (x y : G ⧸ θ.fixedSubgroup) :
    f x = f y :=
  invariantReadout_const_of_homogeneousSpace
    (cartan_fixedQuotient_isHomogeneousSpace θ) hf x y

/-- In a homogeneous space, every orbit fills the ambient carrier `Set.univ`. -/
theorem orbit_eq_univ_of_homogeneousSpace
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X) (x₀ : X) :
    InfoGeometry.Canonical.OperatorErlangenFixedPoints.orbit (G := G) x₀ = Set.univ := by
  ext y
  constructor
  · intro _
    trivial
  · intro _
    exact hHom x₀ y

/-- Klein reconstruction: every homogeneous `G`-space with basepoint `x₀` is in bijection
with the coset quotient `G ⧸ stabilizer G x₀`. -/
def homogeneousSpaceEquivQuotient
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X) (x₀ : X) :
    X ≃ G ⧸ MulAction.stabilizer G x₀ :=
  let orbEquiv : X ≃ ↥(InfoGeometry.Canonical.OperatorErlangenFixedPoints.orbit (G := G) x₀) :=
    { toFun := fun x => ⟨x, hHom x₀ x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  orbEquiv.trans
    (InfoGeometry.Canonical.OperatorErlangenFixedPoints.orbit_quotient_stabilizer_equiv x₀)

theorem homogeneousSpaceEquivQuotient_symm_mk
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X) (x₀ : X) (g : G) :
    (homogeneousSpaceEquivQuotient hHom x₀).symm (QuotientGroup.mk g) = g • x₀ := by
  dsimp [homogeneousSpaceEquivQuotient,
    InfoGeometry.Canonical.OperatorErlangenFixedPoints.orbit_quotient_stabilizer_equiv]
  exact MulAction.orbitEquivQuotientStabilizer_symm_apply G x₀ g

/-- The reconstruction sends the chosen basepoint `x₀` to `quotientBasepoint (stabilizer G x₀)`. -/
theorem homogeneousSpaceEquivQuotient_basepoint
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X) (x₀ : X) :
    homogeneousSpaceEquivQuotient hHom x₀ x₀ =
      quotientBasepoint (MulAction.stabilizer G x₀) := by
  have h1 : (homogeneousSpaceEquivQuotient hHom x₀).symm
      (quotientBasepoint (MulAction.stabilizer G x₀)) = x₀ := by
    calc
      (homogeneousSpaceEquivQuotient hHom x₀).symm
          (quotientBasepoint (MulAction.stabilizer G x₀)) = (1 : G) • x₀ :=
        homogeneousSpaceEquivQuotient_symm_mk hHom x₀ 1
      _ = x₀ := one_smul G x₀
  exact ((homogeneousSpaceEquivQuotient hHom x₀).eq_symm_apply).mp h1.symm

/-- The Klein coset reconstruction `X ≃ G ⧸ stabilizer G x₀` is `G`-equivariant. -/
theorem homogeneousSpaceEquivQuotient_equivariant
    {G X : Type*} [Group G] [MulAction G X]
    (hHom : IsHomogeneousSpace G X) (x₀ : X) :
    IsEquivariantMap G X (homogeneousSpaceEquivQuotient hHom x₀) := by
  intro g x
  let e := homogeneousSpaceEquivQuotient hHom x₀
  obtain ⟨q, hq⟩ : ∃ q, q = e x := ⟨e x, rfl⟩
  have hq' : e.symm q = x := by
    rw [hq]
    exact e.symm_apply_apply x
  have hsymm : e.symm (g • e x) = g • x := by
    rw [← hq]
    induction q using Quotient.inductionOn' with
    | h a =>
      have ha : x = a • x₀ := by
        rw [← hq']
        exact homogeneousSpaceEquivQuotient_symm_mk hHom x₀ a
      calc
        e.symm (g • (QuotientGroup.mk a : G ⧸ MulAction.stabilizer G x₀)) =
            e.symm (QuotientGroup.mk (g * a)) := by rw [smul_mk]
        _ = (g * a) • x₀ := homogeneousSpaceEquivQuotient_symm_mk hHom x₀ (g * a)
        _ = g • (a • x₀) := mul_smul g a x₀
        _ = g • x := by rw [← ha]
  exact (e.eq_symm_apply).mp hsymm.symm

end ClassicalHomogeneousErlangen

/-!
## Corridor 2: Operator Erlangen 2.0, Galois Connection, & Direct-Limit / Deck Realizations
-/

section OperatorErlangenUnification

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.OperatorErlangenFixedPoints
open InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants
open InfoGeometry.OperatorAlgebra.CantorDoubleCylinderFractalColimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary (BitWord)

/-- Convert an `OperatorAlgebra.SymmetryAction` into a group homomorphism into `RingAut Op`. -/
def symmetryActionToRingAutHom
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) :
    G →* RingAut Op where
  toFun := α.act
  map_one' := by
    ext x
    exact α.act_one x
  map_mul' := by
    intro g h
    ext x
    exact α.act_mul g h x

/-- Convert a group homomorphism `G →* RingAut Op` into an `OperatorAlgebra.SymmetryAction`. -/
def ringAutHomToSymmetryAction
    {G Op : Type*} [Group G] [Ring Op]
    (φ : G →* RingAut Op) :
    SymmetryAction G Op where
  act := φ
  act_one := by
    intro x
    rw [φ.map_one]
    rfl
  act_mul := by
    intro g h x
    rw [φ.map_mul]
    rfl

/-- `SymmetryAction G Op` is in bijection with `G →* RingAut Op`. -/
def symmetryActionEquivRingAutHom
    (G Op : Type*) [Group G] [Ring Op] :
    SymmetryAction G Op ≃ (G →* RingAut Op) where
  toFun := symmetryActionToRingAutHom
  invFun := ringAutHomToSymmetryAction
  left_inv α := by
    cases α
    rfl
  right_inv φ := by
    ext g x
    rfl

/-- Induce a `MulSemiringAction G Op` from any `SymmetryAction G Op` (kept explicit as a `def`). -/
@[instance_reducible]
def symmetryActionToMulSemiringAction
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) :
    MulSemiringAction G Op where
  smul g x := α.act g x
  one_smul x := α.act_one x
  mul_smul g h x := α.act_mul g h x
  smul_zero g := (α.act g).map_zero
  smul_add g x y := (α.act g).map_add x y
  smul_one g := (α.act g).map_one
  smul_mul g x y := (α.act g).map_mul x y

/-- The symmetry-invariant subring agrees setwise with the `⊤`-subgroup fixed semiring. -/
theorem invariantSubring_toSubsemiring_eq_fixedPointSubsemiring_top
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) :
    (invariantSubring α).toSubsemiring =
      @fixedPointSubsemiring G Op _ _ (symmetryActionToMulSemiringAction α) ⊤ := by
  let _inst : MulSemiringAction G Op := symmetryActionToMulSemiringAction α
  ext x
  constructor
  · intro hx g
    exact hx (g : G)
  · intro hx g
    exact hx ⟨g, Subgroup.mem_top g⟩

/-- Bridge connecting `SymmetryAction G Op` to the operator Erlangen Galois connection. -/
theorem symmetryAction_galois_connection
    {G Op : Type*} [Group G] [Ring Op]
    (α : SymmetryAction G Op) (H : Subgroup G) (S : Set Op) :
    H ≤ @fixingSubgroup G Op _ _ (symmetryActionToMulSemiringAction α) S ↔
      S ⊆ @fixedPointSet G Op _ _ (symmetryActionToMulSemiringAction α) H := by
  exact @subgroup_le_fixingSubgroup_iff G Op _ _ (symmetryActionToMulSemiringAction α) H S

/-- Symmetrized Cantor double-cylinder projectors inhabit the Galois fixed-point set of `⊤`,
and for `Mat2C` the invariant subring remains strictly noncommutative. -/
theorem erlangenDoubleCylinder_unified_noncomm_and_fixedPoint
    (n : ℕ) (u : BitWord (n + 1)) :
    (∀ B : Type, [Ring B] →
      (erlangenDoubleCylinderInvariantSubring B).toSubsemiring =
        @fixedPointSubsemiring G_swap (DoubleCylinderColimit B) _ _
          (symmetryActionToMulSemiringAction (erlangenDoubleCylinderSymmetryAction B)) ⊤) ∧
    (∀ B : Type, [Ring B] →
      doubleCylinderInclusion B (n + 1) (symmetrizedCylinderProj B (n + 1) u) ∈
        @fixedPointSet G_swap (DoubleCylinderColimit B) _ _
          (symmetryActionToMulSemiringAction (erlangenDoubleCylinderSymmetryAction B)) ⊤) ∧
    (∃ a b : erlangenDoubleCylinderInvariantSubring _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C,
      a * b ≠ b * a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B _
    exact invariantSubring_toSubsemiring_eq_fixedPointSubsemiring_top
      (erlangenDoubleCylinderSymmetryAction B)
  · intro B _ h
    exact colimit_symmetrizedCylinderProj_isInvariant B (n + 1) u (h : G_swap)
  · exact erlangenDoubleCylinderInvariantSubring_noncommutative
      _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C

section KleinDeckBridge

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Canonical.KleinDeckFiveGradeAction
open InfoGeometry.Clifford.ConformalLieAlgebra55

private def kleinDeckSymmetryAction :
    @SymmetryAction KleinDeckGroup (InfoGeometry.Clifford.ClNN.Alg 5)
      kleinDeckGroupStructure _ :=
  @ringAutHomToSymmetryAction KleinDeckGroup (InfoGeometry.Clifford.ClNN.Alg 5)
    kleinDeckGroupStructure _ deckGradeActionHom

/-- The Klein-bottle deck action on split `Cl(5,5)` matches the invariant subring under
`ringAutHomToSymmetryAction deckGradeActionHom`, stabilizes `u5 + v5`, and moves `u5` to `v5`. -/
theorem kleinDeck_unified_invariant_and_nontrivial :
    ((@invariantSubring KleinDeckGroup (InfoGeometry.Clifford.ClNN.Alg 5)
        kleinDeckGroupStructure _ kleinDeckSymmetryAction =
      deckInvariantSubring)) ∧
    (u5 + v5) ∈ deckInvariantSubring ∧
    u5 ∉ deckInvariantSubring ∧
    u5 * v5 + v5 * u5 = 1 := by
  refine ⟨?_, ?_, ?_, u5_v5_add_v5_u5⟩
  · ext x
    change (∀ g : KleinDeckGroup, deckGradeActionHom g x = x) ↔
      ∀ g : KleinDeckGroup, deckGradeAction g x = x
    refine ⟨fun h g => h g, fun h g => h g⟩
  · intro g
    rw [deckGradeAction_apply]
    split_ifs with h
    · rfl
    · have hgl : thetaOp (u5 + v5) = deckGradeAction ⟨0, 1⟩ (u5 + v5) :=
        (deckGradeAction_glide (u5 + v5)).symm
      rw [hgl, map_add, glide_exchanges_null_generators.1,
        glide_exchanges_null_generators.2, add_comm]
  · intro hu
    have hg0 : deckGradeAction ⟨0, 1⟩ u5 = u5 := hu ⟨0, 1⟩
    have hg := glide_exchanges_null_generators.1
    have hvu : v5 = u5 := hg.symm.trans hg0
    have hne : u5 ≠ v5 := by
      intro huv
      have hone : (1 : InfoGeometry.Clifford.ClNN.Alg 5) = 0 := by
        calc
          (1 : InfoGeometry.Clifford.ClNN.Alg 5) = u5 * v5 + v5 * u5 := u5_v5_add_v5_u5.symm
          _ = u5 * u5 + u5 * u5 := by rw [← huv]
          _ = 0 := by rw [u5_sq]; simp
      have hmat := congrArg (InfoGeometry.CliffordWeyl.SplitSpinorFierz.spinorEquiv 5) hone
      simp at hmat
    exact hne hvu.symm

end KleinDeckBridge

end OperatorErlangenUnification

/-!
## Corridor 3: Klein Quadric (`Q ⊂ ℙ⁵`), `GL(4)`/`SL(4)` Action, & Noncommutative Defect
-/

section KleinQuadricUnification

open InfoGeometry.Erlangen.InvariantGeometry

/-- Equivalence between `Projective.KleinQuadric.Plucker6 R` and `KleinQuadricPlucker.Plucker6 R`. -/
def pluckerQuadricEquivPluckerLine (R : Type*) :
    InfoGeometry.Projective.KleinQuadric.Plucker6 R ≃
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 R where
  toFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  invFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

/-- The Klein quadratic forms coincide across both `Plucker6` owners over any `[Ring R]`. -/
theorem kleinQ_pluckerQuadricEquivPluckerLine
    {R : Type*} [Ring R]
    (P : InfoGeometry.Projective.KleinQuadric.Plucker6 R) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (pluckerQuadricEquivPluckerLine R P) =
      InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ P := by
  cases P
  dsimp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ,
    pluckerQuadricEquivPluckerLine,
    InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ]

/-- The Klein polar bilinear forms coincide across both `Plucker6` owners over any `[Ring R]`. -/
theorem polar_eq_kleinPolar
    {R : Type*} [Ring R]
    (P Q : InfoGeometry.Projective.KleinQuadric.Plucker6 R) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.polar P Q =
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
        (pluckerQuadricEquivPluckerLine R P)
        (pluckerQuadricEquivPluckerLine R Q) := by
  rw [InfoGeometry.Projective.KleinQuadric.Plucker6.polar_formula]
  cases P
  cases Q
  dsimp [InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar,
    pluckerQuadricEquivPluckerLine]

/-- Equivalence between `FierzKleinFoundation.Bivector4` and `Projective.KleinQuadric.Plucker6 ℝ`. -/
def bivector4EquivPlucker6 :
    InfoGeometry.Canonical.FierzKleinFoundation.Bivector4 ≃
      InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ where
  toFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  invFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

/-- Full real exterior square equivalence `⋀[ℝ]^2 Vec4 ≃ Plucker6 ℝ`. -/
def exteriorSquareEquivPlucker6 :
    (⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4) ≃
      InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ :=
  InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorBivectorLinearEquiv.toEquiv.trans
    bivector4EquivPlucker6

/-- The real exterior Klein quadratic form equals the `Plucker6 ℝ` Klein form through `exteriorSquareEquivPlucker6`. -/
theorem kleinQ_exteriorSquareEquivPlucker6
    (X : ⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ (exteriorSquareEquivPlucker6 X) =
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm X := by
  dsimp [exteriorSquareEquivPlucker6, bivector4EquivPlucker6,
    InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ,
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm,
    InfoGeometry.Canonical.FierzKleinFoundation.kleinForm]

/-- An exterior bivector maps onto the `Plucker6 ℝ` Klein quadric iff it is a pure wedge `u ∧ v`,
matching `realTwoPlaneEquivKleinLocus : RealTwoPlane ≃ KleinLocus`. -/
theorem isKlein_exteriorSquareEquivPlucker6_iff_decomposable
    (X : ⋀[ℝ]^2 InfoGeometry.Canonical.FierzKleinFoundation.Vec4) :
    InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein (exteriorSquareEquivPlucker6 X) ↔
      ∃ u v : InfoGeometry.Canonical.FierzKleinFoundation.Vec4,
        X = exteriorPower.ιMulti ℝ 2 ![u, v] := by
  dsimp [InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein]
  rw [kleinQ_exteriorSquareEquivPlucker6]
  exact InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm_eq_zero_iff_decomposable X

/-- Pointwise bridge uniting `RealTwoPlane`, `KleinLocus`, and decomposability on `ℙ(⋀² ℝ⁴)`. -/
theorem realTwoPlane_corresponds_to_projectiveKleinLocus
    (P : InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane) :
    InfoGeometry.Projective.ExteriorKleinProjective.IsDecomposable
      (InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv.realTwoPlaneEquivKleinLocus P).1 := by
  have hk := (InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv.realTwoPlaneEquivKleinLocus P).2
  exact (InfoGeometry.Projective.ExteriorKleinProjective.isKlein_iff_isDecomposable _).mp hk

section LinearGroupCollineations

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.DahmPluckerKleinCollineation

private theorem compound_one_aux
    {R : Type*} [CommRing R] (P : Plucker6 R) :
    compound (1 : Matrix (Fin 4) (Fin 4) R) P = P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  apply InfoGeometry.Projective.KleinQuadric.Plucker6.ext <;>
    simp [compound, compoundRow, minor2]

private theorem compound_mul_aux
    {R : Type*} [CommRing R]
    (A B : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) :
    compound (A * B) P = compound A (compound B P) := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  ext <;>
    simp [compound, compoundRow, minor2, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

private theorem act_one_aux
    {R : Type*} [CommRing R] (u : Vec4 R) :
    act (1 : Matrix (Fin 4) (Fin 4) R) u = u := by
  rcases u with ⟨u0, u1, u2, u3⟩
  dsimp [act]
  congr 1 <;> simp

private theorem act_mul_entry {R : Type*} [CommRing R]
    (a0 a1 a2 a3 b00 b01 b02 b03 b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33
      u0 u1 u2 u3 : R) :
    (a0 * b00 + a1 * b10 + a2 * b20 + a3 * b30) * u0 +
        (a0 * b01 + a1 * b11 + a2 * b21 + a3 * b31) * u1 +
        (a0 * b02 + a1 * b12 + a2 * b22 + a3 * b32) * u2 +
        (a0 * b03 + a1 * b13 + a2 * b23 + a3 * b33) * u3 =
      a0 * (b00 * u0 + b01 * u1 + b02 * u2 + b03 * u3) +
        a1 * (b10 * u0 + b11 * u1 + b12 * u2 + b13 * u3) +
        a2 * (b20 * u0 + b21 * u1 + b22 * u2 + b23 * u3) +
        a3 * (b30 * u0 + b31 * u1 + b32 * u2 + b33 * u3) := by
  ring

private theorem act_mul_aux
    {R : Type*} [CommRing R]
    (A B : Matrix (Fin 4) (Fin 4) R) (u : Vec4 R) :
    act (A * B) u = act A (act B u) := by
  rcases u with ⟨u0, u1, u2, u3⟩
  dsimp [act]
  congr 1 <;> simp only [Matrix.mul_apply, Fin.sum_univ_four] <;>
    exact act_mul_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u0 u1 u2 u3

/-- The identity `4 × 4` matrix acts trivially on `Plucker6 R`. -/
theorem compound_one {R : Type*} [CommRing R] (P : Plucker6 R) :
    compound (1 : Matrix (Fin 4) (Fin 4) R) P = P :=
  compound_one_aux P

/-- Compound `2 × 2`-minor action satisfies Cauchy–Binet functoriality `Λ²(A B) = (Λ²A)(Λ²B)`. -/
theorem compound_mul {R : Type*} [CommRing R]
    (A B : Matrix (Fin 4) (Fin 4) R) (P : Plucker6 R) :
    compound (A * B) P = compound A (compound B P) :=
  compound_mul_aux A B P

@[instance_reducible]
private def gl4PluckerMulAction (R : Type*) [CommRing R] :
    MulAction (Matrix.GeneralLinearGroup (Fin 4) R) (Plucker6 R) where
  smul g P := compound (g : Matrix (Fin 4) (Fin 4) R) P
  one_smul P := compound_one P
  mul_smul g h P := compound_mul (g : Matrix (Fin 4) (Fin 4) R)
    (h : Matrix (Fin 4) (Fin 4) R) P

@[instance_reducible]
private def gl4PairMulAction (R : Type*) [CommRing R] :
    MulAction (Matrix.GeneralLinearGroup (Fin 4) R) (Vec4 R × Vec4 R) where
  smul g uv := (act (g : Matrix (Fin 4) (Fin 4) R) uv.1,
                act (g : Matrix (Fin 4) (Fin 4) R) uv.2)
  one_smul uv := by
    apply Prod.ext
    · exact act_one_aux uv.1
    · exact act_one_aux uv.2
  mul_smul g h uv := by
    apply Prod.ext
    · exact act_mul_aux (g : Matrix (Fin 4) (Fin 4) R) (h : Matrix (Fin 4) (Fin 4) R) uv.1
    · exact act_mul_aux (g : Matrix (Fin 4) (Fin 4) R) (h : Matrix (Fin 4) (Fin 4) R) uv.2

@[instance_reducible]
private def sl4PluckerMulAction (R : Type*) [CommRing R] :
    MulAction (Matrix.SpecialLinearGroup (Fin 4) R) (Plucker6 R) where
  smul g P := compound (g : Matrix (Fin 4) (Fin 4) R) P
  one_smul P := compound_one P
  mul_smul g h P := compound_mul (g : Matrix (Fin 4) (Fin 4) R)
    (h : Matrix (Fin 4) (Fin 4) R) P

/-- In the Erlangen vocabulary of `InvariantGeometry`, membership on the Klein quadric
is a `GL(4, R)`-geometric invariant for every `[CommRing R]`. -/
theorem isKlein_geometricInvariant_gl4 {R : Type*} [CommRing R] :
    @IsGeometricInvariant (Matrix.GeneralLinearGroup (Fin 4) R) (Plucker6 R)
      _ (gl4PluckerMulAction R) Plucker6.IsKlein := by
  intro g P
  change Plucker6.IsKlein (compound (g : Matrix (Fin 4) (Fin 4) R) P) ↔ Plucker6.IsKlein P
  unfold Plucker6.IsKlein
  rw [kleinQ_compound]
  have hunit : IsUnit ((g : Matrix (Fin 4) (Fin 4) R).det) :=
    (Matrix.GeneralLinearGroup.det g).isUnit
  exact hunit.mul_right_eq_zero

/-- The wedge map `(u, v) ↦ u ∧ v` is `GL(4, R)`-equivariant (`IsEquivariantMap`). -/
theorem wedge_equivariantMap_gl4 {R : Type*} [CommRing R] :
    @IsEquivariantMap (Matrix.GeneralLinearGroup (Fin 4) R) (Vec4 R × Vec4 R)
      _ (gl4PairMulAction R) (Plucker6 R) (gl4PluckerMulAction R)
      (fun uv => Vec4.wedge uv.1 uv.2) := by
  intro g uv
  exact wedge_act (g : Matrix (Fin 4) (Fin 4) R) uv.1 uv.2

/-- The Klein quadratic form `kleinQ` itself is an `SL(4, R)`-invariant readout. -/
theorem kleinQ_invariantReadout_sl4 {R : Type*} [CommRing R] :
    @IsInvariantReadout (Matrix.SpecialLinearGroup (Fin 4) R) (Plucker6 R)
      _ (sl4PluckerMulAction R) R Plucker6.kleinQ := by
  intro g P
  change Plucker6.kleinQ (compound (g : Matrix (Fin 4) (Fin 4) R) P) = Plucker6.kleinQ P
  exact kleinQ_compound_of_det_eq_one (g : Matrix (Fin 4) (Fin 4) R) g.det_coe P

/-- On the noncommutative spin algebra `Mat2C`, the split Klein senary commutator defect
is nonzero and separates the exact quadratic form from its commutative shadow. -/
theorem splitKlein_spin_commutator_defect :
    senaryDefect _root_.InfoGeometry.Algebra.FiniteSpin.J_plus
        _root_.InfoGeometry.Algebra.FiniteSpin.J_minus 0 0 0 0 ≠ 0 ∧
      Plucker6.kleinQ (splitKleinMap _root_.InfoGeometry.Algebra.FiniteSpin.J_plus
        _root_.InfoGeometry.Algebra.FiniteSpin.J_minus 0 0 0 0) ≠
        (_root_.InfoGeometry.Algebra.FiniteSpin.J_plus *
          _root_.InfoGeometry.Algebra.FiniteSpin.J_plus -
         _root_.InfoGeometry.Algebra.FiniteSpin.J_minus *
          _root_.InfoGeometry.Algebra.FiniteSpin.J_minus) := by
  have hdef : senaryDefect _root_.InfoGeometry.Algebra.FiniteSpin.J_plus
      _root_.InfoGeometry.Algebra.FiniteSpin.J_minus 0 0 0 0 ≠ 0 := by
    intro h
    dsimp [senaryDefect] at h
    simp only [mul_zero, sub_self, add_zero] at h
    rw [sub_eq_zero] at h
    exact _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne h
  refine ⟨hdef, ?_⟩
  intro hEq
  rw [kleinQ_splitKleinMap] at hEq
  simp only [mul_zero, sub_self, add_zero] at hEq
  exact hdef (sub_eq_self.mp hEq)

end LinearGroupCollineations

end KleinQuadricUnification

/-!
## Corridor 4: Projective Cross-Ratio & Klein Four-Group `V₄` Stabilization
-/

section CrossRatioUnification

open InfoGeometry.Erlangen.InvariantGeometry
open InfoGeometry.Projective.CrossRatioPGL2
open InfoGeometry.Projective.KleinCrossRatioInvariant
open InfoGeometry.Projective.NoncommutativeCrossRatio

/-- Equivalence between `CrossRatioPGL2.ProjPoint` and `KleinCrossRatioInvariant.HomPoint2 ℂ`. -/
def projPointEquivHomPoint2 : ProjPoint ≃ HomPoint2 ℂ where
  toFun P := ⟨P.1, P.2⟩
  invFun P := (P.x, P.y)
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

/-- The two `ℂP¹` determinant brackets agree under `projPointEquivHomPoint2`. -/
theorem homPoint2_bracket_eq_detBracket (P Q : ProjPoint) :
    HomPoint2.bracket (projPointEquivHomPoint2 P) (projPointEquivHomPoint2 Q) =
      detBracket P Q := by
  change P.1 * Q.2 - Q.1 * P.2 = P.1 * Q.2 - P.2 * Q.1
  ring

/-- `KleinCrossRatioInvariant`'s cross-ratio numerator/denominator fraction equals `CrossRatioPGL2.crossRatio`
after cyclic permutation of `(P₂, P₃, P₄)` and simultaneous sign cancellation. -/
theorem homPoint2_ratio_eq_pgl2_crossRatio (P₁ P₂ P₃ P₄ : ProjPoint) :
    HomPoint2.crossNum
        (projPointEquivHomPoint2 P₁) (projPointEquivHomPoint2 P₂)
        (projPointEquivHomPoint2 P₃) (projPointEquivHomPoint2 P₄) /
      HomPoint2.crossDen
        (projPointEquivHomPoint2 P₁) (projPointEquivHomPoint2 P₂)
        (projPointEquivHomPoint2 P₃) (projPointEquivHomPoint2 P₄) =
      crossRatio P₁ P₃ P₄ P₂ := by
  unfold HomPoint2.crossNum HomPoint2.crossDen crossRatio
  rw [homPoint2_bracket_eq_detBracket P₁ P₃,
      homPoint2_bracket_eq_detBracket P₂ P₄,
      homPoint2_bracket_eq_detBracket P₁ P₄,
      homPoint2_bracket_eq_detBracket P₂ P₃]
  have hswap24 : detBracket P₂ P₄ = -detBracket P₄ P₂ := by
    dsimp [detBracket]
    ring
  have hswap23 : detBracket P₂ P₃ = -detBracket P₃ P₂ := by
    dsimp [detBracket]
    ring
  rw [hswap24, hswap23, mul_neg, mul_neg, neg_div_neg_eq]

/-- Scalar specialization of `ncCrossRatio` over `ℂ` equals the affine `CrossRatioPGL2.crossRatio`. -/
theorem ncCrossRatio_complex_eq_pgl2_affine (z₁ z₂ z₃ z₄ : ℂ) :
    ncCrossRatio z₁ z₂ z₃ z₄ =
      crossRatio (affinePoint z₁) (affinePoint z₃) (affinePoint z₄) (affinePoint z₂) := by
  unfold ncCrossRatio crossRatio
  rw [detBracket_affine z₁ z₃, detBracket_affine z₄ z₂,
      detBracket_affine z₁ z₄, detBracket_affine z₃ z₂]
  simp only [div_eq_mul_inv, mul_inv]
  have h42 : z₂ - z₄ = -(z₄ - z₂) := by ring
  have h32 : z₂ - z₃ = -(z₃ - z₂) := by ring
  rw [h42, h32, inv_neg]
  ring

/-- Classical Plücker–Grassmann harmonic complement identity uniting the two cross-ratio orientations
on `ℂ`: `[z₁, z₂; z₃, z₄] + ncCrossRatio z₁ z₂ z₄ z₃ = 1`. -/
theorem pgl2_affine_add_ncCrossRatio_eq_one
    (z₁ z₂ z₃ z₄ : ℂ) (h₁₃ : z₁ - z₃ ≠ 0) (h₂₄ : z₂ - z₄ ≠ 0) :
    crossRatio (affinePoint z₁) (affinePoint z₂) (affinePoint z₃) (affinePoint z₄) +
      ncCrossRatio z₁ z₂ z₄ z₃ = 1 := by
  unfold crossRatio ncCrossRatio
  rw [detBracket_affine z₁ z₂, detBracket_affine z₃ z₄,
      detBracket_affine z₁ z₃, detBracket_affine z₂ z₄]
  have hsum : ((z₁ - z₂) * (z₃ - z₄)) / ((z₁ - z₃) * (z₂ - z₄)) +
      (z₁ - z₄) * (z₁ - z₃)⁻¹ * (z₂ - z₃) * (z₂ - z₄)⁻¹ = 1 := by
    field_simp [h₁₃, h₂₄]
    ring
  exact hsum

/-- Action of Klein's four-group `V₄` by double transpositions on ordered quadruples. -/
def v4PermuteQuadruple {α : Type*} (g : InfoGeometry.Canonical.KleinFourRealizations.V4)
    (q : α × α × α × α) : α × α × α × α :=
  match (Multiplicative.toAdd g).1.val, (Multiplicative.toAdd g).2.val with
  | 0, 0 => q
  | 1, 0 => (q.2.1, q.1, q.2.2.2, q.2.2.1)
  | 0, 1 => (q.2.2.1, q.2.2.2, q.1, q.2.1)
  | _, _ => (q.2.2.2, q.2.2.1, q.2.1, q.1)

@[instance_reducible]
private def v4QuadrupleMulAction (α : Type*) :
    MulAction InfoGeometry.Canonical.KleinFourRealizations.V4 (α × α × α × α) where
  smul := v4PermuteQuadruple
  one_smul q := rfl
  mul_smul g h q := by
    rcases g with ⟨g1, g2⟩
    rcases h with ⟨h1, h2⟩
    fin_cases g1 <;> fin_cases g2 <;> fin_cases h1 <;> fin_cases h2 <;> rfl

/-- Felix Klein theorem: the projective cross-ratio is strictly invariant under the
anharmonic Klein four-group `V₄` of double transpositions (`IsInvariantReadout`). -/
theorem crossRatio_invariantReadout_v4 :
    @IsInvariantReadout InfoGeometry.Canonical.KleinFourRealizations.V4
      (ProjPoint × ProjPoint × ProjPoint × ProjPoint) _
      (v4QuadrupleMulAction ProjPoint) ℂ
      (fun q => crossRatio q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  intro g q
  rcases q with ⟨P₁, P₂, P₃, P₄⟩
  have h21 : detBracket P₂ P₁ = -detBracket P₁ P₂ := by dsimp [detBracket]; ring
  have h43 : detBracket P₄ P₃ = -detBracket P₃ P₄ := by dsimp [detBracket]; ring
  have h31 : detBracket P₃ P₁ = -detBracket P₁ P₃ := by dsimp [detBracket]; ring
  have h42 : detBracket P₄ P₂ = -detBracket P₂ P₄ := by dsimp [detBracket]; ring
  have hg : g = Multiplicative.ofAdd ((0 : ZMod 2), (0 : ZMod 2)) ∨
      g = Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2)) ∨
      g = Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2)) ∨
      g = Multiplicative.ofAdd ((1 : ZMod 2), (1 : ZMod 2)) := by
    revert g
    decide
  rcases hg with rfl | rfl | rfl | rfl
  · change crossRatio P₁ P₂ P₃ P₄ = crossRatio P₁ P₂ P₃ P₄
    exact Eq.refl _
  · change crossRatio P₂ P₁ P₄ P₃ = crossRatio P₁ P₂ P₃ P₄
    dsimp only [crossRatio]
    rw [h21, h43, neg_mul_neg, mul_comm (detBracket P₂ P₄) (detBracket P₁ P₃)]
  · change crossRatio P₃ P₄ P₁ P₂ = crossRatio P₁ P₂ P₃ P₄
    dsimp only [crossRatio]
    rw [h31, h42, neg_mul_neg, mul_comm (detBracket P₃ P₄) (detBracket P₁ P₂)]
  · change crossRatio P₄ P₃ P₂ P₁ = crossRatio P₁ P₂ P₃ P₄
    dsimp only [crossRatio]
    rw [h43, h21, h42, h31, neg_mul_neg, neg_mul_neg,
      mul_comm (detBracket P₃ P₄) (detBracket P₁ P₂),
      mul_comm (detBracket P₂ P₄) (detBracket P₁ P₃)]

private theorem matrixAct_one_aux (P : ProjPoint) :
    matrixAct (1 : Matrix (Fin 2) (Fin 2) ℂ) P = P := by
  rcases P with ⟨p1, p2⟩
  dsimp [matrixAct]
  refine Prod.ext ?_ ?_ <;> simp

private theorem matrixAct_mul_entry (a00 a01 b00 b01 b10 b11 p1 p2 : ℂ) :
    (a00 * b00 + a01 * b10) * p1 + (a00 * b01 + a01 * b11) * p2 =
      a00 * (b00 * p1 + b01 * p2) + a01 * (b10 * p1 + b11 * p2) := by
  ring

private theorem matrixAct_mul_aux (A B : Matrix (Fin 2) (Fin 2) ℂ) (P : ProjPoint) :
    matrixAct (A * B) P = matrixAct A (matrixAct B P) := by
  rcases P with ⟨p1, p2⟩
  dsimp [matrixAct]
  refine Prod.ext ?_ ?_
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact matrixAct_mul_entry _ _ _ _ _ _ p1 p2
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact matrixAct_mul_entry _ _ _ _ _ _ p1 p2

@[instance_reducible]
private def gl2NondegenMulAction :
    MulAction (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      {q : ProjPoint × ProjPoint × ProjPoint × ProjPoint //
        detBracket q.1 q.2.2.1 ≠ 0 ∧ detBracket q.2.1 q.2.2.2 ≠ 0} where
  smul g q :=
    ⟨(matrixAct (g : Matrix (Fin 2) (Fin 2) ℂ) q.1.1,
      matrixAct (g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2.1,
      matrixAct (g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2.2.1,
      matrixAct (g : Matrix (Fin 2) (Fin 2) ℂ) q.1.2.2.2),
     by
       have hd : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
         Matrix.GeneralLinearGroup.det_ne_zero g
       refine ⟨?_, ?_⟩
       · rw [detBracket_matrix_action]; exact mul_ne_zero hd q.2.1
       · rw [detBracket_matrix_action]; exact mul_ne_zero hd q.2.2⟩
  one_smul q := by
    apply Subtype.ext
    dsimp [HSMul.hSMul]
    simp [matrixAct_one_aux]
  mul_smul g h q := by
    apply Subtype.ext
    dsimp [HSMul.hSMul]
    simp only [matrixAct_mul_aux]

/-- `GL(2, ℂ)` acts by projective invariance on nondegenerate `ℂP¹` quadruples. -/
theorem crossRatio_invariantReadout_gl2 :
    @IsInvariantReadout (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      {q : ProjPoint × ProjPoint × ProjPoint × ProjPoint //
        detBracket q.1 q.2.2.1 ≠ 0 ∧ detBracket q.2.1 q.2.2.2 ≠ 0}
      _ gl2NondegenMulAction ℂ
      (fun q => crossRatio q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2) := by
  intro g q
  have hd : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero g
  exact cross_ratio_pgl2_invariant (g : Matrix (Fin 2) (Fin 2) ℂ) hd
    q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2

/-- Noncommutative quaternionic separation: on `Quaternion ℝ`, right-affine scalings
strictly preserve `ncCrossRatio`, whereas left-affine scaling `x ↦ j * x + b` shifts
`ncCrossRatio` via the non-vanishing inner derivation `innerDerivation j (-2i) = 4k`. -/
theorem ncCrossRatio_quaternion_right_vs_left_separation (b : ℍ) :
    let qP1 : ℍ := ⟨1, 0, 0, 0⟩
    let qP2 : ℍ := ⟨-1, 1, 0, 0⟩
    let qP3 : ℍ := ⟨0, 1, 0, 0⟩
    let qP4 : ℍ := ⟨0, 0, 0, 0⟩
    let qJ  : ℍ := ⟨0, 0, 1, 0⟩
    ncCrossRatio qP1 qP2 qP3 qP4 = ⟨0, -2, 0, 0⟩ ∧
    ncCrossRatio (rightAffine qJ b qP1) (rightAffine qJ b qP2)
      (rightAffine qJ b qP3) (rightAffine qJ b qP4) =
      ncCrossRatio qP1 qP2 qP3 qP4 ∧
    innerDerivation qJ (ncCrossRatio qP1 qP2 qP3 qP4) = ⟨0, 0, 0, 4⟩ ∧
    ncCrossRatio (leftAffine qJ b qP1) (leftAffine qJ b qP2)
      (leftAffine qJ b qP3) (leftAffine qJ b qP4) ≠
      ncCrossRatio qP1 qP2 qP3 qP4 := by
  dsimp only
  let qP1 : ℍ := ⟨1, 0, 0, 0⟩
  let qP2 : ℍ := ⟨-1, 1, 0, 0⟩
  let qP3 : ℍ := ⟨0, 1, 0, 0⟩
  let qP4 : ℍ := ⟨0, 0, 0, 0⟩
  let qJ  : ℍ := ⟨0, 0, 1, 0⟩
  have h14 : qP1 - qP4 = (1 : ℍ) := by ext <;> simp [qP1, qP4]
  have h23 : qP2 - qP3 = (-1 : ℍ) := by ext <;> simp [qP2, qP3]
  have hcr : ncCrossRatio qP1 qP2 qP3 qP4 = ⟨0, -2, 0, 0⟩ := by
    unfold ncCrossRatio
    rw [h14, h23, inv_one, inv_neg, inv_one, mul_one]
    ext
    · simp [qP1, qP2, qP3, qP4]
    · simp [qP1, qP2, qP3, qP4]; norm_num
    · simp [qP1, qP2, qP3, qP4]
    · simp [qP1, qP2, qP3, qP4]
  have hJne : qJ ≠ 0 := by
    intro h
    have hj := congrArg QuaternionAlgebra.imJ h
    simp [qJ] at hj
  have hR : ncCrossRatio (rightAffine qJ b qP1) (rightAffine qJ b qP2)
      (rightAffine qJ b qP3) (rightAffine qJ b qP4) = ncCrossRatio qP1 qP2 qP3 qP4 :=
    ncCrossRatio_rightAffine qJ b qP1 qP2 qP3 qP4 hJne
  have hderiv : innerDerivation qJ (ncCrossRatio qP1 qP2 qP3 qP4) = ⟨0, 0, 0, 4⟩ := by
    rw [hcr]
    unfold innerDerivation
    ext
    · simp [qJ]
    · simp [qJ]
    · simp [qJ]
    · simp [qJ]; norm_num
  have hL : ncCrossRatio (leftAffine qJ b qP1) (leftAffine qJ b qP2)
      (leftAffine qJ b qP3) (leftAffine qJ b qP4) ≠ ncCrossRatio qP1 qP2 qP3 qP4 := by
    intro heq
    have h0 := (ncCrossRatio_leftAffine_eq_iff_innerDerivation_eq_zero
      qJ b qP1 qP2 qP3 qP4 hJne).mp heq
    rw [hderiv] at h0
    have hk := congrArg QuaternionAlgebra.imK h0
    simp at hk
  exact ⟨hcr, hR, hderiv, hL⟩

end CrossRatioUnification

/-!
## Corridor 5: Kinematic Cayley–Klein Tri-Regime & Five-Lane Master Synthesis
-/

section KinematicAndMasterSynthesis

/-- Generator square in the 1D `KinematicCliffordAlgebra 1 (fun _ => κ)` recovers the
Cayley–Klein curvature parameter `κ` across elliptic (`-1`), parabolic (`0`), and hyperbolic (`+1`) signatures. -/
theorem kinematicGenerator_tri_regime_sq (κ : ℝ) :
    InfoGeometry.Algebra.kinematicGenerator 1 (fun _ => κ) 0 *
      InfoGeometry.Algebra.kinematicGenerator 1 (fun _ => κ) 0 =
        algebraMap ℝ (InfoGeometry.Algebra.KinematicCliffordAlgebra 1 (fun _ => κ)) κ ∧
    InfoGeometry.Algebra.kinematicQuadraticForm 1 (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) = -1 ∧
    InfoGeometry.Algebra.kinematicQuadraticForm 1 (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) = 0 ∧
    InfoGeometry.Algebra.kinematicQuadraticForm 1 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold InfoGeometry.Algebra.kinematicGenerator
    rw [CliffordAlgebra.ι_sq_scalar]
    congr 1
    simp [InfoGeometry.Algebra.kinematicQuadraticForm, Matrix.toQuadraticForm',
      Matrix.toLinearMap₂'_apply', dotProduct]
  · simp [InfoGeometry.Algebra.kinematicQuadraticForm, Matrix.toQuadraticForm',
      Matrix.toLinearMap₂'_apply', dotProduct]
  · simp [InfoGeometry.Algebra.kinematicQuadraticForm, Matrix.toQuadraticForm']
  · simp [InfoGeometry.Algebra.kinematicQuadraticForm, Matrix.toQuadraticForm',
      Matrix.toLinearMap₂'_apply', dotProduct]

/-- **Five-Corridor Felix Klein Unification Theorem**:
Assembles homogeneous-space invariant constancy and equivariant `G/H` reconstruction (Corridor 1),
operator Galois fixed-point / Cantor double-cylinder noncommutativity and Klein-deck invariance on `Cl(5,5)` (Corridor 2),
`RealTwoPlane`/`KleinLocus` decomposability, `GL(4)` Klein-quadric invariance, `SL(4)` quadratic-form invariance, and `Mat2C` spin commutator defect (Corridor 3),
`V₄` and `GL(2,ℂ)` cross-ratio invariance and quaternionic right-vs-left affine separation (Corridor 4),
and Cayley–Klein kinematic signature tri-regime (`κ ∈ ℝ`) with 8D octonionic non-multiplicativity (Corridor 5). -/
theorem felix_klein_five_lane_unification
    {R : Type*} [CommRing R] (κ : ℝ) :
    ((∀ (G X β : Type*) [Group G] [MulAction G X],
      InfoGeometry.Core.IsHomogeneousSpace G X →
      ∀ (f : X → β), InfoGeometry.Erlangen.InvariantGeometry.IsInvariantReadout G X f →
        ∀ x y : X, f x = f y) ∧
     (∀ (G X : Type*) [Group G] [MulAction G X]
      (hHom : InfoGeometry.Core.IsHomogeneousSpace G X) (x₀ : X),
      InfoGeometry.Erlangen.InvariantGeometry.IsEquivariantMap G X
        (homogeneousSpaceEquivQuotient hHom x₀))) ∧
    ((∃ a b : InfoGeometry.OperatorAlgebra.ErlangenDoubleCylinderSymmetryInvariants.erlangenDoubleCylinderInvariantSubring
        _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a) ∧
     InfoGeometry.Clifford.ConformalLieAlgebra55.u5 +
       InfoGeometry.Clifford.ConformalLieAlgebra55.v5 ∈
         InfoGeometry.Canonical.KleinDeckFiveGradeAction.deckInvariantSubring ∧
     InfoGeometry.Clifford.ConformalLieAlgebra55.u5 ∉
       InfoGeometry.Canonical.KleinDeckFiveGradeAction.deckInvariantSubring ∧
     InfoGeometry.Clifford.ConformalLieAlgebra55.u5 *
       InfoGeometry.Clifford.ConformalLieAlgebra55.v5 +
       InfoGeometry.Clifford.ConformalLieAlgebra55.v5 *
         InfoGeometry.Clifford.ConformalLieAlgebra55.u5 = 1) ∧
    ((∀ P : InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient.RealTwoPlane,
      InfoGeometry.Projective.ExteriorKleinProjective.IsDecomposable
        (InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv.realTwoPlaneEquivKleinLocus P).1) ∧
     (@InfoGeometry.Erlangen.InvariantGeometry.IsGeometricInvariant
        (Matrix.GeneralLinearGroup (Fin 4) R) (InfoGeometry.Projective.KleinQuadric.Plucker6 R)
        _ (gl4PluckerMulAction R) InfoGeometry.Projective.KleinQuadric.Plucker6.IsKlein) ∧
     (@InfoGeometry.Erlangen.InvariantGeometry.IsInvariantReadout
        (Matrix.SpecialLinearGroup (Fin 4) R) (InfoGeometry.Projective.KleinQuadric.Plucker6 R)
        _ (sl4PluckerMulAction R) R InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ) ∧
     (InfoGeometry.Projective.DahmPluckerKleinCollineation.senaryDefect
        _root_.InfoGeometry.Algebra.FiniteSpin.J_plus
        _root_.InfoGeometry.Algebra.FiniteSpin.J_minus 0 0 0 0 ≠ 0)) ∧
    ((∀ g q,
      InfoGeometry.Projective.CrossRatioPGL2.crossRatio
        (v4PermuteQuadruple g q).1 (v4PermuteQuadruple g q).2.1
        (v4PermuteQuadruple g q).2.2.1 (v4PermuteQuadruple g q).2.2.2 =
      InfoGeometry.Projective.CrossRatioPGL2.crossRatio q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
     (@InfoGeometry.Erlangen.InvariantGeometry.IsInvariantReadout
        (Matrix.GeneralLinearGroup (Fin 2) ℂ)
        {q : InfoGeometry.Projective.CrossRatioPGL2.ProjPoint ×
             InfoGeometry.Projective.CrossRatioPGL2.ProjPoint ×
             InfoGeometry.Projective.CrossRatioPGL2.ProjPoint ×
             InfoGeometry.Projective.CrossRatioPGL2.ProjPoint //
          InfoGeometry.Projective.CrossRatioPGL2.detBracket q.1 q.2.2.1 ≠ 0 ∧
          InfoGeometry.Projective.CrossRatioPGL2.detBracket q.2.1 q.2.2.2 ≠ 0}
        _ gl2NondegenMulAction ℂ
        (fun q => InfoGeometry.Projective.CrossRatioPGL2.crossRatio
          q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2)) ∧
     (∀ b : ℍ,
      InfoGeometry.Projective.NoncommutativeCrossRatio.ncCrossRatio
          (InfoGeometry.Projective.NoncommutativeCrossRatio.rightAffine ⟨0, 0, 1, 0⟩ b ⟨1, 0, 0, 0⟩)
          (InfoGeometry.Projective.NoncommutativeCrossRatio.rightAffine ⟨0, 0, 1, 0⟩ b ⟨-1, 1, 0, 0⟩)
          (InfoGeometry.Projective.NoncommutativeCrossRatio.rightAffine ⟨0, 0, 1, 0⟩ b ⟨0, 1, 0, 0⟩)
          (InfoGeometry.Projective.NoncommutativeCrossRatio.rightAffine ⟨0, 0, 1, 0⟩ b ⟨0, 0, 0, 0⟩) =
        InfoGeometry.Projective.NoncommutativeCrossRatio.ncCrossRatio
          ⟨1, 0, 0, 0⟩ ⟨-1, 1, 0, 0⟩ ⟨0, 1, 0, 0⟩ ⟨0, 0, 0, 0⟩ ∧
      InfoGeometry.Projective.NoncommutativeCrossRatio.ncCrossRatio
          (InfoGeometry.Projective.NoncommutativeCrossRatio.leftAffine ⟨0, 0, 1, 0⟩ b ⟨1, 0, 0, 0⟩)
          (InfoGeometry.Projective.NoncommutativeCrossRatio.leftAffine ⟨0, 0, 1, 0⟩ b ⟨-1, 1, 0, 0⟩)
          (InfoGeometry.Projective.NoncommutativeCrossRatio.leftAffine ⟨0, 0, 1, 0⟩ b ⟨0, 1, 0, 0⟩)
          (InfoGeometry.Projective.NoncommutativeCrossRatio.leftAffine ⟨0, 0, 1, 0⟩ b ⟨0, 0, 0, 0⟩) ≠
        InfoGeometry.Projective.NoncommutativeCrossRatio.ncCrossRatio
          ⟨1, 0, 0, 0⟩ ⟨-1, 1, 0, 0⟩ ⟨0, 1, 0, 0⟩ ⟨0, 0, 0, 0⟩)) ∧
    ((InfoGeometry.Algebra.kinematicGenerator 1 (fun _ => κ) 0 *
        InfoGeometry.Algebra.kinematicGenerator 1 (fun _ => κ) 0 =
          algebraMap ℝ (InfoGeometry.Algebra.KinematicCliffordAlgebra 1 (fun _ => κ)) κ ∧
      InfoGeometry.Algebra.kinematicQuadraticForm 1 (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) = -1 ∧
      InfoGeometry.Algebra.kinematicQuadraticForm 1 (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) = 0 ∧
      InfoGeometry.Algebra.kinematicQuadraticForm 1 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1) ∧
     (Module.finrank ℝ InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation.ComplexMatrix = 8 ∧
      Module.finrank ℝ InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation.SplitCarrier = 8 ∧
      ¬ ∃ f : InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation.ComplexMatrix →
          InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation.SplitCarrier,
        Function.Surjective f ∧ ∀ A B, f (A * B) = f A * f B)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro G X β _ _ hHom f hf x y
    exact invariantReadout_const_of_homogeneousSpace hHom hf x y
  · intro G X _ _ hHom x₀
    exact homogeneousSpaceEquivQuotient_equivariant hHom x₀
  · exact (erlangenDoubleCylinder_unified_noncomm_and_fixedPoint 0 (fun _ => false)).2.2
  · exact kleinDeck_unified_invariant_and_nontrivial.2
  · exact realTwoPlane_corresponds_to_projectiveKleinLocus
  · exact isKlein_geometricInvariant_gl4
  · exact kleinQ_invariantReadout_sl4
  · exact splitKlein_spin_commutator_defect.1
  · intro g q
    exact crossRatio_invariantReadout_v4 g q
  · exact crossRatio_invariantReadout_gl2
  · intro b
    exact ⟨(ncCrossRatio_quaternion_right_vs_left_separation b).2.1,
      (ncCrossRatio_quaternion_right_vs_left_separation b).2.2.2⟩
  · exact kinematicGenerator_tri_regime_sq κ
  · exact InfoGeometry.Canonical.BipolarCayleyKleinPristineChain.pristine_eight_dimensional_separation

end KinematicAndMasterSynthesis

end InfoGeometry.Canonical.FelixKleinGeometryUnification

