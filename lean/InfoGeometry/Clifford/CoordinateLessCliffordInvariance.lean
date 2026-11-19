/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.RealQuadraticReflection
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11CliffordMapIsometryBridge
import InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Coordinate-Less Invariant Representation of Clifford Algebra Properties

This module is the canonical owner of basis-free, coordinate-less symmetry
invariance for arbitrary `CliffordAlgebra Q` over commutative rings and fields:

1. **Universal `O(Q)` Symmetry Action**: Packages `CliffordAlgebra.equivOfIsometry`
   as `SymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q)` (for any
   `[CommRing R]`) and `OperatorSymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q)`
   (over `ℝ`), reusing `InfoGeometry.Clifford.quadraticIsometryEquivGroup` without
   creating a competing `Group (Q.IsometryEquiv Q)` instance.
2. **Invariant Readouts, Pairings, and Equivariant Operators**: Packages
   `hTrace_cl` as `InvariantReadout`, `cliffordKreinPairing` as `InvariantPairing`,
   `cliffordGradeProj` equivariance, `graceOperator` as `EquivariantLinearMap`,
   and center stability.
3. **Negation Isometry `-id`**: Identifies `equivOfIsometry (negIsometryEquiv Q)`
   with `CliffordAlgebra.involuteEquiv` and characterizes its fixed subalgebra as
   `evenOdd Q 0` when `2` is invertible.
4. **Finite-Dimensional `O(Q)` and `SO(Q)` Invariant Subalgebras**: Proves the
   top-grade determinant law (`equivOfIsometry f ω = det f • ω`), characterizes
   `(CliffordAlgebra Q)^{O(Q)} = range (algebraMap K _)` and
   `(CliffordAlgebra Q)^{SO(Q)} = grade 0 ⊔ grade (finrank K M)` for any
   quadratic form `Q` over a field `K` with `Invertible (2 : K)` (no
   nondegeneracy hypothesis needed), and specializes to `ℝ` with `hTrace_cl` and
   `graceOperator`.
5. **`Cl(1,1)` `V₄`-Invariance**: Embeds `V4Group` into `q11.IsometryEquiv q11`,
   intertwines with `localCl11RootMap` via `cl11EquivMat`, characterizes
   `(CliffordAlgebra q11)^{V₄}` as scalars, and provides an explicit
   noncommutative Clifford witness.

## Felix Klein 1872 *Erlanger Programm* Alignment (`ABN7632.0001.001` / `arXiv:0807.3161v1`)
Following Felix Klein's 1872 Erlangen Programme (*Vergleichende Betrachtungen über
neuere geometrische Forschungen*, Michigan `ABN7632.0001.001`; M. W. Haskell
translation `arXiv:0807.3161v1`):
- **§4 (*Abbildung* / Transfer by Representation)**: Equivariant isomorphisms
  conjugate symmetry groups across carriers and transport invariant theory, realized
  here by `equivExterior_equivOfIsometry` (`CliffordAlgebra Q ≃ₗ ExteriorAlgebra R M`),
  internal helper `conjIsometry_equivOfIsometry` (`Q₁.IsometryEquiv Q₂` transfer), and
  `cl11EquivMat_v4_equivOfIsometry` (`CliffordAlgebra q11 ≃ₐ M₂(ℝ)`).
- **§5 & Footnotes 22–23 (Choice of Space-Element & Faithful Orbits)**: Representing
  a transformation group `G` faithfully requires avoiding space-elements stabilized
  by a nontrivial normal ("self-conjugate") subgroup. Here `{1, negIsometryEquiv Q}`
  is a normal subgroup stabilizing the entire even subalgebra `evenOdd Q 0`
  (`equivOfIsometry_neg_fixed_iff_mem_even`), so `evenOdd Q 0` carries only a
  faithful `O(Q)/{±id}` action (for `dim M ≥ 3`, `dim M = 0`, or `dim M = 1` with
  nondegenerate `Q`; when `dim M = 2`, all of `SO(Q)` stabilizes
  `evenOdd Q 0 = grade 0 ⊔ grade 2` so only `O(Q)/SO(Q)` acts faithfully, and when
  `dim M = 1` and `Q = 0`, `O(0)/{±id}` acts trivially on `evenOdd 0 0 = K`), whereas
  full `CliffordAlgebra Q` carries faithful `O(Q)` orbits, and `SO(Q)` stabilizes
  `grade 0 ⊔ grade (finrank K M)` (`isInvariant_specialIsometry_iff`).
- **Concluding Remarks + Footnote 37 (Coordinate-Independent Analytic Formalism)**:
  Formalizes Klein's call for coordinate-system-independent invariant analytic
  formalisms (1872: quaternions) on general `CliffordAlgebra Q`, in contrast with the
  concrete `M₂(ℂ)` spin-frame matrix identities in `InfoGeometry.ErlangenCoordinateless`.
-/

set_option autoImplicit false

namespace InfoGeometry.Clifford.CoordinateLessCliffordInvariance

open CliffordAlgebra
open InfoGeometry.Clifford
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Riemannian
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
open scoped Matrix

/-! ## Section 1: Universal `SymmetryAction` and `OperatorSymmetryAction` -/

section SymmetryActions

/-- Canonical coordinate-less `O(Q)` symmetry action on `CliffordAlgebra Q`,
reusing `InfoGeometry.Clifford.quadraticIsometryEquivGroup Q`. -/
noncomputable def cliffordSymmetryAction {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) :
    SymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q) where
  act g := (CliffordAlgebra.equivOfIsometry g).toRingEquiv
  act_one x := by
    change CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q) x = x
    rw [CliffordAlgebra.equivOfIsometry_refl]
    rfl
  act_mul g h x := by
    change CliffordAlgebra.equivOfIsometry (h.trans g) x =
      CliffordAlgebra.equivOfIsometry g (CliffordAlgebra.equivOfIsometry h x)
    rw [← CliffordAlgebra.equivOfIsometry_trans]
    rfl

@[simp]
theorem cliffordSymmetryAction_act_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (g : Q.IsometryEquiv Q) (x : CliffordAlgebra Q) :
    (cliffordSymmetryAction Q).act g x = CliffordAlgebra.equivOfIsometry g x :=
  rfl

/-- Canonical real operator-algebra `O(Q)` symmetry action on `CliffordAlgebra Q`.
Note that `OperatorSymmetryAction.act S g` applies `S.toFun g⁻¹`, so setting
`toFun g := CliffordAlgebra.equivOfIsometry g⁻¹` ensures `toSymmetryAction` agrees
definitionally with `cliffordSymmetryAction Q`. -/
noncomputable def cliffordOperatorSymmetryAction {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) :
    OperatorSymmetryAction (Q.IsometryEquiv Q) (CliffordAlgebra Q) where
  toFun g := CliffordAlgebra.equivOfIsometry g⁻¹
  map_one' := by
    change CliffordAlgebra.equivOfIsometry ((1 : Q.IsometryEquiv Q)⁻¹) = AlgEquiv.refl
    rw [inv_one]
    exact CliffordAlgebra.equivOfIsometry_refl
  map_mul' g₁ g₂ := by
    change CliffordAlgebra.equivOfIsometry ((g₁ * g₂)⁻¹) =
      (CliffordAlgebra.equivOfIsometry g₁⁻¹).trans (CliffordAlgebra.equivOfIsometry g₂⁻¹)
    rw [mul_inv_rev, CliffordAlgebra.equivOfIsometry_trans]
    rfl

@[simp]
theorem cliffordOperatorSymmetryAction_act_apply {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (g : Q.IsometryEquiv Q) (x : CliffordAlgebra Q) :
    (cliffordOperatorSymmetryAction Q).act g x = CliffordAlgebra.equivOfIsometry g x := by
  change CliffordAlgebra.equivOfIsometry (g⁻¹)⁻¹ x = _
  rw [inv_inv]

theorem toSymmetryAction_cliffordOperatorSymmetryAction
    {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ M) :
    toSymmetryAction (cliffordOperatorSymmetryAction Q) = cliffordSymmetryAction Q := by
  dsimp [toSymmetryAction, cliffordSymmetryAction]
  congr 1

end SymmetryActions

/-! ## Section 2: Packaged Invariant Readouts, Pairings, and Equivariant Maps -/

section InvariantStructures

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem isInvariant_algebraMap (Q : QuadraticForm R M) (r : R) :
    IsInvariant (cliffordSymmetryAction Q) (algebraMap R (CliffordAlgebra Q) r) := by
  intro g
  exact (CliffordAlgebra.equivOfIsometry g).commutes r

theorem algebraMap_mem_cliffordInvariantSubring (Q : QuadraticForm R M) (r : R) :
    algebraMap R (CliffordAlgebra Q) r ∈ invariantSubring (cliffordSymmetryAction Q) :=
  isInvariant_algebraMap Q r

theorem mem_center_equivOfIsometry_iff (Q : QuadraticForm R M) (f : Q.IsometryEquiv Q)
    (x : CliffordAlgebra Q) :
    CliffordAlgebra.equivOfIsometry f x ∈ Subalgebra.center R (CliffordAlgebra Q) ↔
      x ∈ Subalgebra.center R (CliffordAlgebra Q) := by
  simp only [Subalgebra.mem_center_iff]
  constructor
  · intro hx y
    have hy := hx (CliffordAlgebra.equivOfIsometry f y)
    rw [← map_mul, ← map_mul] at hy
    exact (CliffordAlgebra.equivOfIsometry f).injective hy
  · intro hx y
    have hy := hx (CliffordAlgebra.equivOfIsometry f.symm y)
    have hxy := congrArg (CliffordAlgebra.equivOfIsometry f) hy
    rw [map_mul, map_mul] at hxy
    have hinv : CliffordAlgebra.equivOfIsometry f (CliffordAlgebra.equivOfIsometry f.symm y) = y := by
      change CliffordAlgebra.equivOfIsometry f ((CliffordAlgebra.equivOfIsometry f).symm y) = y
      exact (CliffordAlgebra.equivOfIsometry f).apply_symm_apply y
    rwa [hinv] at hxy

section InvertibleTwoReadouts

variable [Invertible (2 : R)]

/-- `hTrace_cl Q` packaged as a coordinate-less `O(Q)`-invariant readout. -/
noncomputable def hTraceInvariantReadout (Q : QuadraticForm R M) :
    InvariantReadout (cliffordSymmetryAction Q) R :=
  InvariantReadout.mk (hTrace_cl Q) fun g x => hTrace_cl_equivOfIsometry g x

@[simp]
theorem hTraceInvariantReadout_apply (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    (hTraceInvariantReadout Q).read x = hTrace_cl Q x :=
  rfl

/-- `cliffordKreinPairing Q` packaged as a coordinate-less `O(Q)`-invariant pairing. -/
noncomputable def cliffordKreinInvariantPairing (Q : QuadraticForm R M) :
    InvariantPairing (cliffordSymmetryAction Q) R :=
  InvariantPairing.mk (cliffordKreinPairing Q) fun g u v =>
    cliffordKreinPairing_equivOfIsometry g u v

@[simp]
theorem cliffordKreinInvariantPairing_apply (Q : QuadraticForm R M)
    (u v : CliffordAlgebra Q) :
    (cliffordKreinInvariantPairing Q).pair u v = cliffordKreinPairing Q u v :=
  rfl

theorem cliffordSymmetryAction_equivariant_gradeProj (Q : QuadraticForm R M) (k : ℕ)
    {x : CliffordAlgebra Q} (hx : IsInvariant (cliffordSymmetryAction Q) x) :
    IsInvariant (cliffordSymmetryAction Q) (cliffordGradeProj Q k x) := by
  intro g
  have hxg := hx g
  change CliffordAlgebra.equivOfIsometry g x = x at hxg
  change CliffordAlgebra.equivOfIsometry g (cliffordGradeProj Q k x) = cliffordGradeProj Q k x
  rw [cliffordGradeProj_equivOfIsometry, hxg]

end InvertibleTwoReadouts

/-- The Grace operator packaged as an `O(Q)`-equivariant linear map on `CliffordAlgebra Q`. -/
noncomputable def graceOperator_equivariantLinearMap {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) :
    (cliffordOperatorSymmetryAction Q).EquivariantLinearMap (cliffordOperatorSymmetryAction Q) where
  toLinearMap := graceOperator Q
  equivariant g x := by
    rw [cliffordOperatorSymmetryAction_act_apply, cliffordOperatorSymmetryAction_act_apply]
    exact (graceOperator_equivOfIsometry g x).symm

end InvariantStructures

/-! ## Section 3: Negation Isometry `-id` and Even Subalgebra Fixed Points

Per Klein 1872 *Erlanger Programm* §5 & Footnotes 22–23 (`arXiv:0807.3161v1` /
`ABN7632.0001.001`), `{1, negIsometryEquiv Q} ≃ ℤ/2` is a central normal subgroup of
`O(Q)` stabilizing all of `evenOdd Q 0` (`equivOfIsometry_neg_fixed_iff_mem_even`).
Consequently, `evenOdd Q 0` carries only a faithful `O(Q)/{±id}` representation
(for `dim M ≥ 3`, `dim M = 0`, or `dim M = 1` with nondegenerate `Q`; when `dim M = 2`,
all of `SO(Q)` stabilizes `evenOdd Q 0 = grade 0 ⊔ grade 2` so only `O(Q)/SO(Q)` acts
faithfully, and when `dim M = 1` and `Q = 0`, `O(0)/{±id}` acts trivially on
`evenOdd 0 0 = K`), whereas full `CliffordAlgebra Q` carries faithful `O(Q)` orbits. -/

section NegationIsometry

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The central inversion / negation isometry `-id : Q.IsometryEquiv Q`. -/
def negIsometryEquiv (Q : QuadraticForm R M) : Q.IsometryEquiv Q where
  toFun := fun m => -m
  invFun := fun m => -m
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add
  map_smul' r m := by simp
  map_app' m := by
    change Q (-m) = Q m
    exact QuadraticMap.map_neg Q m

@[simp]
theorem negIsometryEquiv_apply (Q : QuadraticForm R M) (m : M) :
    negIsometryEquiv Q m = -m :=
  rfl

theorem equivOfIsometry_negIsometryEquiv (Q : QuadraticForm R M) :
    CliffordAlgebra.equivOfIsometry (negIsometryEquiv Q) = CliffordAlgebra.involuteEquiv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro m
  simp [CliffordAlgebra.involuteEquiv]

theorem isInvariant_involute_eq_self (Q : QuadraticForm R M) {x : CliffordAlgebra Q}
    (hx : IsInvariant (cliffordSymmetryAction Q) x) :
    CliffordAlgebra.involute x = x := by
  have hneg := hx (negIsometryEquiv Q)
  change CliffordAlgebra.equivOfIsometry (negIsometryEquiv Q) x = x at hneg
  rwa [equivOfIsometry_negIsometryEquiv] at hneg

section InvertibleTwoParity

variable [Invertible (2 : R)]

private theorem two_smul_eq_zero_iff {Q : QuadraticForm R M} (x : CliffordAlgebra Q) :
    (2 : R) • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun z : CliffordAlgebra Q => (⅟(2 : R)) • z) h
    simpa [smul_smul, invOf_mul_self, one_smul] using h'
  · rintro rfl
    exact smul_zero _

omit [Invertible (2 : R)] in
private theorem decompose_evenOdd_sum (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    ((DirectSum.decompose (CliffordAlgebra.evenOdd Q) x 0 : CliffordAlgebra Q) +
      (DirectSum.decompose (CliffordAlgebra.evenOdd Q) x 1 : CliffordAlgebra Q)) = x := by
  classical
  let d := DirectSum.decompose (CliffordAlgebra.evenOdd Q) x
  have hsum := DirectSum.sum_support_decompose (CliffordAlgebra.evenOdd Q) x
  have hsub :
      ∑ i ∈ d.support, (d i : CliffordAlgebra Q) =
        ∑ i ∈ (Finset.univ : Finset (ZMod 2)), (d i : CliffordAlgebra Q) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    have h0 : d i = 0 := by
      by_contra hne
      exact hi (DFinsupp.mem_support_iff.mpr hne)
    simp [h0]
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hsub, huniv, Finset.sum_pair (by decide)] at hsum
  exact hsum

theorem involute_eq_self_iff_mem_even (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute x = x ↔ x ∈ CliffordAlgebra.evenOdd Q 0 := by
  constructor
  · intro hinv
    let d := DirectSum.decompose (CliffordAlgebra.evenOdd Q) x
    have hx_sum : (d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q) = x :=
      decompose_evenOdd_sum Q x
    have h0 : CliffordAlgebra.involute (d 0 : CliffordAlgebra Q) = (d 0 : CliffordAlgebra Q) :=
      CliffordAlgebra.involute_eq_of_mem_even (SetLike.coe_mem (d 0))
    have h1 : CliffordAlgebra.involute (d 1 : CliffordAlgebra Q) = -(d 1 : CliffordAlgebra Q) :=
      CliffordAlgebra.involute_eq_of_mem_odd (SetLike.coe_mem (d 1))
    have hcomb : (d 0 : CliffordAlgebra Q) - (d 1 : CliffordAlgebra Q) =
        (d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q) := by
      calc
        (d 0 : CliffordAlgebra Q) - (d 1 : CliffordAlgebra Q)
            = CliffordAlgebra.involute ((d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q)) := by
              rw [map_add, h0, h1, ← sub_eq_add_neg]
        _ = CliffordAlgebra.involute x := by rw [hx_sum]
        _ = x := hinv
        _ = (d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q) := hx_sum.symm
    have hd1_zero : (2 : R) • (d 1 : CliffordAlgebra Q) = 0 := by
      rw [two_smul]
      have : (d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q) -
          ((d 0 : CliffordAlgebra Q) - (d 1 : CliffordAlgebra Q)) =
          (d 1 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q) := by abel
      rw [← this]
      exact sub_eq_zero.mpr hcomb.symm
    have hd1 : (d 1 : CliffordAlgebra Q) = 0 := (two_smul_eq_zero_iff _).mp hd1_zero
    rw [← hx_sum, hd1, add_zero]
    exact SetLike.coe_mem (d 0)
  · exact CliffordAlgebra.involute_eq_of_mem_even

theorem equivOfIsometry_neg_fixed_iff_mem_even (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.equivOfIsometry (negIsometryEquiv Q) x = x ↔
      x ∈ CliffordAlgebra.evenOdd Q 0 := by
  rw [equivOfIsometry_negIsometryEquiv]
  exact involute_eq_self_iff_mem_even Q x

theorem involute_eq_neg_self_iff_mem_odd (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute x = -x ↔ x ∈ CliffordAlgebra.evenOdd Q 1 := by
  constructor
  · intro hinv
    let d := DirectSum.decompose (CliffordAlgebra.evenOdd Q) x
    have hx_sum : (d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q) = x :=
      decompose_evenOdd_sum Q x
    have h0 : CliffordAlgebra.involute (d 0 : CliffordAlgebra Q) = (d 0 : CliffordAlgebra Q) :=
      CliffordAlgebra.involute_eq_of_mem_even (SetLike.coe_mem (d 0))
    have h1 : CliffordAlgebra.involute (d 1 : CliffordAlgebra Q) = -(d 1 : CliffordAlgebra Q) :=
      CliffordAlgebra.involute_eq_of_mem_odd (SetLike.coe_mem (d 1))
    have hcomb : (d 0 : CliffordAlgebra Q) - (d 1 : CliffordAlgebra Q) =
        -((d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q)) := by
      calc
        (d 0 : CliffordAlgebra Q) - (d 1 : CliffordAlgebra Q)
            = CliffordAlgebra.involute ((d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q)) := by
              rw [map_add, h0, h1, ← sub_eq_add_neg]
        _ = CliffordAlgebra.involute x := by rw [hx_sum]
        _ = -x := hinv
        _ = -((d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q)) := by rw [hx_sum]
    have hd0_zero : (2 : R) • (d 0 : CliffordAlgebra Q) = 0 := by
      rw [two_smul]
      have : (d 0 : CliffordAlgebra Q) - (d 1 : CliffordAlgebra Q) +
          ((d 0 : CliffordAlgebra Q) + (d 1 : CliffordAlgebra Q)) =
          (d 0 : CliffordAlgebra Q) + (d 0 : CliffordAlgebra Q) := by abel
      rw [← this, hcomb, neg_add_cancel]
    have hd0 : (d 0 : CliffordAlgebra Q) = 0 := (two_smul_eq_zero_iff _).mp hd0_zero
    rw [← hx_sum, hd0, zero_add]
    exact SetLike.coe_mem (d 1)
  · exact CliffordAlgebra.involute_eq_of_mem_odd

end InvertibleTwoParity

end NegationIsometry

/-! ## Section 4: Top-Grade Determinant Law, `SO(Q)`, and `O(Q)` Invariants

Under Klein 1872 §4 (*Abbildung*, internal helper `conjIsometry_equivOfIsometry`) and §5 &
Footnotes 22–23 (`arXiv:0807.3161v1` / `ABN7632.0001.001`), restricting from `O(Q)`
to the normal subgroup `SO(Q) = ker (detHom Q)` enlarges the invariant subalgebra from
`grade 0 = range (algebraMap K _)` (`isInvariant_cliffordSymmetryAction_iff_mem_range`)
to `grade 0 ⊔ grade (finrank K M)` (`isInvariant_specialIsometry_iff`). -/

section FiniteDimInvariants

section DetAndTopGrade

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Group homomorphism `Q.IsometryEquiv Q →* R` (`O(Q) →* R`) given by `LinearMap.det`. -/
noncomputable def detHom (Q : QuadraticForm R M) : Q.IsometryEquiv Q →* R where
  toFun f := LinearMap.det (f : M →ₗ[R] M)
  map_one' := by
    change LinearMap.det (LinearMap.id : M →ₗ[R] M) = 1
    exact LinearMap.det_id
  map_mul' f g := by
    change LinearMap.det ((f : M →ₗ[R] M).comp (g : M →ₗ[R] M)) =
      LinearMap.det (f : M →ₗ[R] M) * LinearMap.det (g : M →ₗ[R] M)
    exact LinearMap.det_comp _ _

@[simp]
theorem detHom_apply (Q : QuadraticForm R M) (f : Q.IsometryEquiv Q) :
    detHom Q f = LinearMap.det (f : M →ₗ[R] M) :=
  rfl

/-- Special orthogonal / special isometry subgroup `SO(Q) = ker (detHom Q)`. -/
noncomputable def specialIsometrySubgroup (Q : QuadraticForm R M) :
    Subgroup (Q.IsometryEquiv Q) :=
  MonoidHom.ker (detHom Q)

theorem mem_specialIsometrySubgroup_iff (Q : QuadraticForm R M) (f : Q.IsometryEquiv Q) :
    f ∈ specialIsometrySubgroup Q ↔ LinearMap.det (f : M →ₗ[R] M) = 1 :=
  Iff.rfl

private theorem fin_orderEmb_eq_id {n : ℕ} (σ : Fin n ↪o Fin n) (j : Fin n) : σ j = j := by
  have hle : j ≤ σ j := σ.strictMono.id_le j
  have hle_set : Finset.image σ (Finset.Ici j) ≤ Finset.Ici (σ j) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
    exact Finset.mem_Ici.mpr (σ.monotone (Finset.mem_Ici.mp hk))
  have hcard := Finset.card_le_card hle_set
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Ici, Fin.card_Ici] at hcard
  have hj_lt : j.val < n := j.isLt
  have hσ_lt : (σ j).val < n := (σ j).isLt
  have hle_val : j.val ≤ (σ j).val := hle
  exact Fin.ext (by omega)

section TopGradeModule

variable [Invertible (2 : R)] [Module.Finite R M] [Module.Free R M] [StrongRankCondition R]

omit [Invertible (2 : R)] in
theorem exteriorPower_top_map_eq_det_smul (g : M →ₗ[R] M)
    {y : ExteriorAlgebra R M} (hy : y ∈ ⋀[R]^(Module.finrank R M) M) :
    ExteriorAlgebra.map g y = (LinearMap.det g) • y := by
  let n : ℕ := Module.finrank R M
  let b : Module.Basis (Fin n) R M := Module.finBasis R M
  let s₀ : Set.powersetCard (Fin n) n := ⟨Finset.univ, Finset.card_fin n⟩
  let eb := b.exteriorPower n
  have hsub : ∀ s : Set.powersetCard (Fin n) n, s = s₀ := by
    intro s
    apply Subtype.ext
    exact Finset.eq_univ_of_card s.1 (by simp [n])
  have heq : ∀ s : Set.powersetCard (Fin n) n,
      ExteriorAlgebra.map g (eb s : ExteriorAlgebra R M) =
        (LinearMap.det g) • (eb s : ExteriorAlgebra R M) := by
    intro s
    rw [hsub s]
    have hmem : ExteriorAlgebra.map g (eb s₀ : ExteriorAlgebra R M) ∈ ⋀[R]^n M :=
      exteriorPower_map_le g n (Submodule.mem_map_of_mem (SetLike.coe_mem (eb s₀)))
    let z : ⋀[R]^n M := ⟨ExteriorAlgebra.map g (eb s₀ : ExteriorAlgebra R M), hmem⟩
    have hz_repr : z = (eb.repr z s₀) • eb s₀ := by
      have hs := (eb.sum_repr z).symm
      rw [Finset.sum_eq_single s₀] at hs
      · exact hs
      · intro t _ hts
        exact (hts (hsub t)).elim
      · intro hnot
        exact (hnot (Finset.mem_univ s₀)).elim
    have hcoord : eb.repr z s₀ = LinearMap.det g := by
      change eb.coord s₀ z = LinearMap.det g
      rw [exteriorPower.basis_coord R n b s₀]
      have hfam : (eb s₀ : ExteriorAlgebra R M) =
          ExteriorAlgebra.ιMulti R n (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm s₀ i)) := by
        change ((b.exteriorPower n s₀ : ⋀[R]^n M) : ExteriorAlgebra R M) = _
        rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe]
        rfl
      have hz_val : (z : ExteriorAlgebra R M) =
          ExteriorAlgebra.ιMulti R n (fun i => g (b (Set.powersetCard.ofFinEmbEquiv.symm s₀ i))) := by
        change ExteriorAlgebra.map g (eb s₀ : ExteriorAlgebra R M) = _
        rw [hfam, ExteriorAlgebra.map_apply_ιMulti]
        rfl
      have hdual :
          exteriorPower.ιMultiDual R n b s₀ z =
            (Matrix.of fun i j =>
              b.coord (Set.powersetCard.ofFinEmbEquiv.symm s₀ j)
                (g (b (Set.powersetCard.ofFinEmbEquiv.symm s₀ i)))).det := by
        have hsub_eq :
            z = ⟨ExteriorAlgebra.ιMulti R n
                (fun i => g (b (Set.powersetCard.ofFinEmbEquiv.symm s₀ i))),
              by rw [← hz_val]; exact z.2⟩ :=
          Subtype.ext hz_val
        rw [hsub_eq]
        exact exteriorPower.ιMultiDual_apply_ιMulti R n b s₀ _
      rw [hdual]
      have hmat :
          (Matrix.of fun i j =>
              b.coord (Set.powersetCard.ofFinEmbEquiv.symm s₀ j)
                (g (b (Set.powersetCard.ofFinEmbEquiv.symm s₀ i)))) =
            (LinearMap.toMatrix b b g)ᵀ := by
        ext i j
        simp only [Matrix.of_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
          fin_orderEmb_eq_id]
        rfl
      rw [hmat, Matrix.det_transpose, LinearMap.det_toMatrix]
    have hval := congrArg (Subtype.val : ⋀[R]^n M → ExteriorAlgebra R M) hz_repr
    simpa [z, hcoord] using hval
  let y_sub : ⋀[R]^n M := ⟨y, hy⟩
  have hy_repr : y_sub = (eb.repr y_sub s₀) • eb s₀ := by
    have hs := (eb.sum_repr y_sub).symm
    rw [Finset.sum_eq_single s₀] at hs
    · exact hs
    · intro t _ hts
      exact (hts (hsub t)).elim
    · intro hnot
      exact (hnot (Finset.mem_univ s₀)).elim
  have hy_val : y = (eb.repr y_sub s₀) • (eb s₀ : ExteriorAlgebra R M) :=
    congrArg Subtype.val hy_repr
  conv_lhs => rw [hy_val]
  rw [map_smul, heq s₀, smul_comm, ← hy_val]

theorem equivOfIsometry_top_grade_eq_det_smul (Q : QuadraticForm R M)
    (f : Q.IsometryEquiv Q) {ω : CliffordAlgebra Q}
    (hω : ω ∈ cliffordGradeSubmodule Q (Module.finrank R M)) :
    CliffordAlgebra.equivOfIsometry f ω = (LinearMap.det (f : M →ₗ[R] M)) • ω := by
  have hproj : cliffordGradeProj Q (Module.finrank R M) ω = ω :=
    (mem_cliffordGradeSubmodule_iff (Module.finrank R M) ω).mp hω
  have hmem : CliffordAlgebra.equivExterior Q ω ∈ ⋀[R]^(Module.finrank R M) M := by
    have hproj_ext :
        CliffordAlgebra.equivExterior Q (cliffordGradeProj Q (Module.finrank R M) ω) =
          exteriorGradeProj R M (Module.finrank R M) (CliffordAlgebra.equivExterior Q ω) := by
      dsimp [cliffordGradeProj]
      exact LinearEquiv.apply_symm_apply _ _
    rw [hproj] at hproj_ext
    rw [hproj_ext]
    exact exteriorGradeProj_mem R M (Module.finrank R M) _
  apply (CliffordAlgebra.equivExterior Q).injective
  rw [equivExterior_equivOfIsometry, map_smul,
    exteriorPower_top_map_eq_det_smul (f : M →ₗ[R] M) hmem]

theorem equivOfIsometry_top_grade_fixed_of_mem_SO (Q : QuadraticForm R M)
    {f : Q.IsometryEquiv Q} (hf : f ∈ specialIsometrySubgroup Q)
    {ω : CliffordAlgebra Q} (hω : ω ∈ cliffordGradeSubmodule Q (Module.finrank R M)) :
    CliffordAlgebra.equivOfIsometry f ω = ω := by
  rw [equivOfIsometry_top_grade_eq_det_smul Q f hω,
    (mem_specialIsometrySubgroup_iff Q f).mp hf, one_smul]

end TopGradeModule

end DetAndTopGrade

section FieldInvariants

variable {K M : Type*} [Field K] [Invertible (2 : K)]
variable [AddCommGroup M] [Module K M] [Module.Finite K M]

/-- Canonical exterior-algebra blade basis of `ExteriorAlgebra K (Fin n → K)`
over any field (or ring) `K`. -/
noncomputable def exteriorBladeBasisK (K : Type*) [CommRing K] (n : ℕ) :
    Module.Basis (Finset (Fin n)) K (ExteriorAlgebra K (Fin n → K)) :=
  (Pi.basisFun K (Fin n)).ExteriorAlgebra

/-- Coordinate sign-flip isometry on `weightedSumSquares K w`, negating coordinate `i`. -/
def coordFlipIsometry {n : ℕ} (w : Fin n → K) (i : Fin n) :
    (QuadraticMap.weightedSumSquares K w).IsometryEquiv
      (QuadraticMap.weightedSumSquares K w) where
  toFun v j := if j = i then -v j else v j
  invFun v j := if j = i then -v j else v j
  left_inv v := by
    ext j
    dsimp
    split_ifs <;> simp
  right_inv v := by
    ext j
    dsimp
    split_ifs <;> simp
  map_add' u v := by
    ext j
    simp only [Pi.add_apply]
    split_ifs with h
    · exact neg_add (u j) (v j)
    · rfl
  map_smul' c v := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs with h
    · exact (mul_neg c (v j)).symm
    · rfl
  map_app' v := by
    simp only [QuadraticMap.weightedSumSquares_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring

omit [Invertible (2 : K)] in
@[simp]
theorem coordFlipIsometry_apply {n : ℕ} (w : Fin n → K) (i j : Fin n) (v : Fin n → K) :
    coordFlipIsometry w i v j = if j = i then -v j else v j :=
  rfl

omit [Invertible (2 : K)] in
theorem det_coordFlipIsometry {n : ℕ} (w : Fin n → K) (i : Fin n) :
    LinearMap.det ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap) = -1 := by
  let b := Pi.basisFun K (Fin n)
  rw [← LinearMap.det_toMatrix b]
  have hmat :
      LinearMap.toMatrix b b
          ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap) =
        Matrix.diagonal (fun j : Fin n => if j = i then (-1 : K) else 1) := by
    ext j k
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    change (b.repr (coordFlipIsometry w i (Pi.basisFun K (Fin n) k))) j = _
    rw [Pi.basisFun_apply, Pi.basisFun_repr, coordFlipIsometry_apply]
    by_cases hjk : j = k
    · subst hjk
      simp
    · simp [hjk]
  rw [hmat, Matrix.det_diagonal, Finset.prod_ite_eq']
  simp

omit [Invertible (2 : K)] in
theorem coordFlipIsometry_mul_mem_SO {n : ℕ} (w : Fin n → K) (i j : Fin n) :
    coordFlipIsometry w i * coordFlipIsometry w j ∈
      specialIsometrySubgroup (QuadraticMap.weightedSumSquares K w) := by
  rw [mem_specialIsometrySubgroup_iff, ← detHom_apply, map_mul, detHom_apply, detHom_apply,
    det_coordFlipIsometry, det_coordFlipIsometry]
  ring

omit [Invertible (2 : K)] in
private theorem exteriorBladeBasisK_empty (n : ℕ) :
    exteriorBladeBasisK K n ∅ = (1 : ExteriorAlgebra K (Fin n → K)) := by
  dsimp [exteriorBladeBasisK]
  let s0 : Set.powersetCard (Fin n) 0 := ⟨∅, Finset.card_empty⟩
  change (Pi.basisFun K (Fin n)).ExteriorAlgebra s0 = 1
  rw [ExteriorAlgebra.basis_apply_powersetCard, ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply _

omit [Invertible (2 : K)] in
private theorem exteriorBladeBasisK_mem_grade (n : ℕ) (S : Finset (Fin n)) :
    exteriorBladeBasisK K n S ∈ ⋀[K]^S.card (Fin n → K) := by
  dsimp [exteriorBladeBasisK]
  let s : Set.powersetCard (Fin n) S.card := ⟨S, rfl⟩
  change (Pi.basisFun K (Fin n)).ExteriorAlgebra s ∈ ⋀[K]^S.card (Fin n → K)
  rw [ExteriorAlgebra.basis_eq_coe_basis]
  exact SetLike.coe_mem _

omit [Invertible (2 : K)] in
private theorem exteriorMap_coordFlip_bladeBasis {n : ℕ} (w : Fin n → K) (i : Fin n)
    (S : Finset (Fin n)) :
    ExteriorAlgebra.map ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap)
        (exteriorBladeBasisK K n S) =
      (if i ∈ S then (-1 : K) else 1) • exteriorBladeBasisK K n S := by
  dsimp [exteriorBladeBasisK]
  let s : Set.powersetCard (Fin n) S.card := ⟨S, rfl⟩
  change ExteriorAlgebra.map ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap)
      ((Pi.basisFun K (Fin n)).ExteriorAlgebra s) =
    (if i ∈ S then (-1 : K) else 1) • (Pi.basisFun K (Fin n)).ExteriorAlgebra s
  rw [ExteriorAlgebra.basis_apply_powersetCard, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.map_apply_ιMulti]
  have hvec :
      ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap ∘
          ⇑(Pi.basisFun K (Fin n)) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) =
        (fun m : Fin S.card =>
          (if (Set.powersetCard.ofFinEmbEquiv.symm s m : Fin n) = i then (-1 : K) else 1) •
            Pi.basisFun K (Fin n) (Set.powersetCard.ofFinEmbEquiv.symm s m)) := by
    funext m
    ext j
    simp only [Function.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, Pi.smul_apply,
      smul_eq_mul]
    change coordFlipIsometry w i (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s m) (1 : K)) j = _
    rw [coordFlipIsometry_apply]
    simp only [Pi.single_apply]
    split_ifs <;> simp_all
  rw [hvec, AlternatingMap.map_smul_univ]
  congr 1
  have hinj : Function.Injective (Set.powersetCard.ofFinEmbEquiv.symm s) :=
    (Set.powersetCard.ofFinEmbEquiv.symm s).injective
  by_cases hiS : i ∈ S
  · simp only [hiS, ↓reduceIte]
    have him : i ∈ s.1 := hiS
    obtain ⟨m₀, hm₀⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr him
    rw [Finset.prod_eq_single m₀]
    · simp [hm₀]
    · intro m _ hmm₀
      have hne : Set.powersetCard.ofFinEmbEquiv.symm s m ≠ i := by
        intro h
        exact hmm₀ (hinj (h.trans hm₀.symm))
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_univ m₀)).elim
  · simp only [hiS, ↓reduceIte]
    refine Finset.prod_eq_one fun m _ => ?_
    have hne : Set.powersetCard.ofFinEmbEquiv.symm s m ≠ i := by
      intro h
      apply hiS
      change i ∈ s.1
      rw [← h]
      exact Finset.orderEmbOfFin_mem s.1 s.2 m
    simp [hne]

private theorem two_mul_field_eq_zero_iff (c : K) : (2 : K) * c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun z : K => (⅟(2 : K)) * z) h
    rw [← mul_assoc, invOf_mul_self, one_mul, mul_zero] at h'
    exact h'
  · rintro rfl
    exact mul_zero _

private theorem weightedSumSquares_O_invariant_iff {n : ℕ} (w : Fin n → K)
    (x : CliffordAlgebra (QuadraticMap.weightedSumSquares K w)) :
    IsInvariant (cliffordSymmetryAction (QuadraticMap.weightedSumSquares K w)) x ↔
      ∃ c : K, x = algebraMap K _ c := by
  let Q' := QuadraticMap.weightedSumSquares K w
  constructor
  · intro hx
    let y : ExteriorAlgebra K (Fin n → K) := CliffordAlgebra.equivExterior Q' x
    have hy_fix : ∀ i : Fin n,
        ExteriorAlgebra.map
            ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap) y = y := by
      intro i
      have hxi := hx (coordFlipIsometry w i)
      change CliffordAlgebra.equivOfIsometry (coordFlipIsometry w i) x = x at hxi
      change ExteriorAlgebra.map _ (CliffordAlgebra.equivExterior Q' x) =
        CliffordAlgebra.equivExterior Q' x
      rw [← equivExterior_equivOfIsometry, hxi]
    let eb := exteriorBladeBasisK K n
    have hy_coord : ∀ S : Finset (Fin n), S.Nonempty → eb.repr y S = 0 := by
      intro S ⟨i, hiS⟩
      have hmap :
          eb.repr (ExteriorAlgebra.map
              ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap) y) S =
            eb.repr y S :=
        congrArg (fun z => eb.repr z S) (hy_fix i)
      conv_lhs at hmap => rw [← eb.sum_repr y]
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at hmap
      dsimp only [eb] at hmap
      simp_rw [exteriorMap_coordFlip_bladeBasis, map_smul, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, Module.Basis.repr_self] at hmap
      rw [Finset.sum_eq_single S] at hmap
      · rw [Finsupp.single_eq_same, mul_one] at hmap
        simp only [hiS, ↓reduceIte] at hmap
        have h2 : (2 : K) * eb.repr y S = 0 := by
          linear_combination -hmap
        exact (two_mul_field_eq_zero_iff (K := K) _).mp h2
      · intro T _ hTS
        rw [Finsupp.single_eq_of_ne hTS.symm, mul_zero, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ S)).elim
    have hy_eq : y = algebraMap K (ExteriorAlgebra K (Fin n → K)) (eb.repr y ∅) := by
      have hs := (eb.sum_repr y).symm
      rw [Finset.sum_eq_single ∅] at hs
      · rw [exteriorBladeBasisK_empty, ← Algebra.algebraMap_eq_smul_one] at hs
        exact hs
      · intro S _ hSne
        rw [hy_coord S (Finset.nonempty_iff_ne_empty.mpr hSne), zero_smul]
      · intro hnot
        exact (hnot (Finset.mem_univ ∅)).elim
    refine ⟨eb.repr y ∅, ?_⟩
    apply (CliffordAlgebra.equivExterior Q').injective
    rw [equivExterior_algebraMap]
    exact hy_eq
  · rintro ⟨c, rfl⟩
    exact isInvariant_algebraMap Q' c

private theorem weightedSumSquares_SO_invariant_iff {n : ℕ} (w : Fin n → K)
    (x : CliffordAlgebra (QuadraticMap.weightedSumSquares K w)) :
    (∀ f ∈ specialIsometrySubgroup (QuadraticMap.weightedSumSquares K w),
        CliffordAlgebra.equivOfIsometry f x = x) ↔
      x ∈ cliffordGradeSubmodule (QuadraticMap.weightedSumSquares K w) 0 ⊔
        cliffordGradeSubmodule (QuadraticMap.weightedSumSquares K w) n := by
  let Q' := QuadraticMap.weightedSumSquares K w
  have hfin : Module.finrank K (Fin n → K) = n := by
    simp
  constructor
  · intro hx
    let y : ExteriorAlgebra K (Fin n → K) := CliffordAlgebra.equivExterior Q' x
    let eb := exteriorBladeBasisK K n
    have hy_coord : ∀ S : Finset (Fin n), S ≠ ∅ → S ≠ Finset.univ → eb.repr y S = 0 := by
      intro S hne huniv
      obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hnot_univ : ¬ ∀ j : Fin n, j ∈ S := by
        intro h
        apply huniv
        exact Finset.eq_univ_iff_forall.mpr h
      push Not at hnot_univ
      obtain ⟨j, hjS⟩ := hnot_univ
      let g := coordFlipIsometry w i * coordFlipIsometry w j
      have hg_SO : g ∈ specialIsometrySubgroup Q' := coordFlipIsometry_mul_mem_SO w i j
      have hxg := hx g hg_SO
      have hy_fix :
          ExteriorAlgebra.map ((g : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap) y = y := by
        change ExteriorAlgebra.map _ (CliffordAlgebra.equivExterior Q' x) =
          CliffordAlgebra.equivExterior Q' x
        rw [← equivExterior_equivOfIsometry, hxg]
      have hmap_comp :
          ExteriorAlgebra.map ((g : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap) =
            (ExteriorAlgebra.map
                ((coordFlipIsometry w i : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap)).comp
              (ExteriorAlgebra.map
                ((coordFlipIsometry w j : (Fin n → K) ≃ₗ[K] (Fin n → K)).toLinearMap)) := by
        rw [ExteriorAlgebra.map_comp_map]
        rfl
      have hmap := congrArg (fun z => eb.repr z S) hy_fix
      conv_lhs at hmap => rw [hmap_comp, AlgHom.comp_apply, ← eb.sum_repr y]
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at hmap
      dsimp only [eb] at hmap
      simp_rw [exteriorMap_coordFlip_bladeBasis, map_smul,
        exteriorMap_coordFlip_bladeBasis, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Module.Basis.repr_self] at hmap
      rw [Finset.sum_eq_single S] at hmap
      · rw [Finsupp.single_eq_same, mul_one] at hmap
        simp only [hiS, hjS, ↓reduceIte, one_mul] at hmap
        have h2 : (2 : K) * eb.repr y S = 0 := by
          linear_combination -hmap
        exact (two_mul_field_eq_zero_iff (K := K) _).mp h2
      · intro T _ hTS
        rw [Finsupp.single_eq_of_ne hTS.symm, mul_zero, mul_zero, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ S)).elim
    have hmem_grade : ∀ {k : ℕ} {z : ExteriorAlgebra K (Fin n → K)},
        z ∈ ⋀[K]^k (Fin n → K) →
        (CliffordAlgebra.equivExterior Q').symm z ∈ cliffordGradeSubmodule Q' k := by
      intro k z hz
      rw [mem_cliffordGradeSubmodule_iff]
      dsimp [cliffordGradeProj]
      rw [LinearEquiv.apply_symm_apply, exteriorGradeProj_of_mem hz]
    have hx_sum :
        x = ∑ S : Finset (Fin n),
          (CliffordAlgebra.equivExterior Q').symm ((eb.repr y S) • eb S) := by
      have h := congrArg (CliffordAlgebra.equivExterior Q').symm (eb.sum_repr y).symm
      rw [LinearEquiv.symm_apply_apply, map_sum] at h
      exact h
    rw [hx_sum]
    refine Submodule.sum_mem _ fun S _ => ?_
    by_cases hS0 : S = ∅
    · subst hS0
      refine Submodule.mem_sup_left (hmem_grade ?_)
      have hmem : eb ∅ ∈ ⋀[K]^0 (Fin n → K) := by
        simpa [Finset.card_empty] using exteriorBladeBasisK_mem_grade (K := K) n ∅
      exact Submodule.smul_mem _ _ hmem
    · by_cases hSn : S = Finset.univ
      · subst hSn
        refine Submodule.mem_sup_right (hmem_grade ?_)
        have hmem : eb Finset.univ ∈ ⋀[K]^n (Fin n → K) := by
          simpa [Finset.card_univ, Fintype.card_fin] using
            exteriorBladeBasisK_mem_grade (K := K) n Finset.univ
        exact Submodule.smul_mem _ _ hmem
      · rw [hy_coord S hS0 hSn, zero_smul, map_zero]
        exact Submodule.zero_mem _
  · intro hx f hf
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨x₀, hx₀, xₙ, hxₙ, rfl⟩
    rw [map_add]
    have hx₀_fix : CliffordAlgebra.equivOfIsometry f x₀ = x₀ := by
      have hx₀' := (mem_cliffordGradeSubmodule_iff 0 x₀).mp hx₀
      rw [← hx₀', cliffordGradeProj_zero_eq_algebraMap_hTrace]
      exact isInvariant_algebraMap Q' _ f
    have hxₙ_fix : CliffordAlgebra.equivOfIsometry f xₙ = xₙ := by
      have hxₙ' : xₙ ∈ cliffordGradeSubmodule Q' (Module.finrank K (Fin n → K)) := by
        simpa [hfin] using hxₙ
      exact equivOfIsometry_top_grade_fixed_of_mem_SO Q' hf hxₙ'
    rw [hx₀_fix, hxₙ_fix]

private def conjIsometry {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁]
    [AddCommGroup M₂] [Module K M₂] {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}
    (e : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₂) : Q₁.IsometryEquiv Q₁ :=
  (e.trans g).trans e.symm

omit [Invertible (2 : K)] in
private theorem conjIsometry_equivOfIsometry {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁]
    [AddCommGroup M₂] [Module K M₂] {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}
    (e : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₂) (x : CliffordAlgebra Q₁) :
    CliffordAlgebra.equivOfIsometry (conjIsometry e g) x =
      CliffordAlgebra.equivOfIsometry e.symm
        (CliffordAlgebra.equivOfIsometry g (CliffordAlgebra.equivOfIsometry e x)) := by
  dsimp [conjIsometry]
  rw [← CliffordAlgebra.equivOfIsometry_trans, ← CliffordAlgebra.equivOfIsometry_trans]
  rfl

omit [Invertible (2 : K)] in
private theorem det_conjIsometry {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁]
    [AddCommGroup M₂] [Module K M₂] {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}
    (e : Q₁.IsometryEquiv Q₂) (g : Q₂.IsometryEquiv Q₂) :
    LinearMap.det ((conjIsometry e g : Q₁.IsometryEquiv Q₁) : M₁ →ₗ[K] M₁) =
      LinearMap.det ((g : Q₂.IsometryEquiv Q₂) : M₂ →ₗ[K] M₂) := by
  change LinearMap.det
      ((e.symm.toLinearEquiv : M₂ →ₗ[K] M₁) ∘ₗ (g : M₂ →ₗ[K] M₂) ∘ₗ
        (e.symm.toLinearEquiv.symm : M₁ →ₗ[K] M₂)) =
    LinearMap.det (g : M₂ →ₗ[K] M₂)
  exact LinearMap.det_conj (g : M₂ →ₗ[K] M₂) e.symm.toLinearEquiv

/-- Coordinate-less `O(Q)` invariant characterization for ANY finite-dimensional quadratic
space `(M, Q)` over a field `K` with `Invertible (2 : K)` (no nondegeneracy needed). -/
theorem isInvariant_cliffordSymmetryAction_iff_mem_range (Q : QuadraticForm K M)
    (x : CliffordAlgebra Q) :
    IsInvariant (cliffordSymmetryAction Q) x ↔
      ∃ c : K, x = algebraMap K (CliffordAlgebra Q) c := by
  constructor
  · intro hx
    obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares Q
    have hinv_e :
        IsInvariant (cliffordSymmetryAction (QuadraticMap.weightedSumSquares K w))
          (CliffordAlgebra.equivOfIsometry e x) := by
      intro g
      change CliffordAlgebra.equivOfIsometry g (CliffordAlgebra.equivOfIsometry e x) =
        CliffordAlgebra.equivOfIsometry e x
      have hconj := hx (conjIsometry e g)
      change CliffordAlgebra.equivOfIsometry (conjIsometry e g) x = x at hconj
      rw [conjIsometry_equivOfIsometry] at hconj
      have happ := congrArg (CliffordAlgebra.equivOfIsometry e) hconj
      have hcancel :
          ∀ z : CliffordAlgebra (QuadraticMap.weightedSumSquares K w),
            CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.equivOfIsometry e.symm z) = z := by
        intro z
        change CliffordAlgebra.equivOfIsometry e ((CliffordAlgebra.equivOfIsometry e).symm z) = z
        exact (CliffordAlgebra.equivOfIsometry e).apply_symm_apply z
      rwa [hcancel] at happ
    obtain ⟨c, hc⟩ := (weightedSumSquares_O_invariant_iff w _).mp hinv_e
    refine ⟨c, ?_⟩
    apply (CliffordAlgebra.equivOfIsometry e).injective
    rw [hc, AlgEquiv.commutes]
  · rintro ⟨c, rfl⟩
    exact isInvariant_algebraMap Q c

/-- The coordinate-less `O(Q)`-invariant subring of `CliffordAlgebra Q` is precisely the
scalar subring `range (algebraMap K _)`. -/
theorem invariantSubring_cliffordSymmetryAction (Q : QuadraticForm K M) :
    invariantSubring (cliffordSymmetryAction Q) =
      (algebraMap K (CliffordAlgebra Q)).range := by
  ext x
  simp only [mem_invariantSubring_iff, RingHom.mem_range]
  simpa only [eq_comm] using isInvariant_cliffordSymmetryAction_iff_mem_range Q x

/-- Coordinate-less `SO(Q)` invariant characterization for ANY finite-dimensional quadratic
space `(M, Q)` over a field `K` with `Invertible (2 : K)`:
`(CliffordAlgebra Q)^{SO(Q)} = grade 0 ⊔ grade (finrank K M)`. -/
theorem isInvariant_specialIsometry_iff (Q : QuadraticForm K M) (x : CliffordAlgebra Q) :
    (∀ f ∈ specialIsometrySubgroup Q, CliffordAlgebra.equivOfIsometry f x = x) ↔
      x ∈ cliffordGradeSubmodule Q 0 ⊔ cliffordGradeSubmodule Q (Module.finrank K M) := by
  constructor
  · intro hx
    obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares Q
    have hSO :
        ∀ g ∈ specialIsometrySubgroup (QuadraticMap.weightedSumSquares K w),
          CliffordAlgebra.equivOfIsometry g (CliffordAlgebra.equivOfIsometry e x) =
            CliffordAlgebra.equivOfIsometry e x := by
      intro g hg
      have hconj_SO : conjIsometry e g ∈ specialIsometrySubgroup Q := by
        rw [mem_specialIsometrySubgroup_iff, det_conjIsometry]
        exact (mem_specialIsometrySubgroup_iff _ g).mp hg
      have hconj := hx (conjIsometry e g) hconj_SO
      rw [conjIsometry_equivOfIsometry] at hconj
      have happ := congrArg (CliffordAlgebra.equivOfIsometry e) hconj
      have hcancel :
          ∀ z : CliffordAlgebra (QuadraticMap.weightedSumSquares K w),
            CliffordAlgebra.equivOfIsometry e (CliffordAlgebra.equivOfIsometry e.symm z) = z := by
        intro z
        change CliffordAlgebra.equivOfIsometry e ((CliffordAlgebra.equivOfIsometry e).symm z) = z
        exact (CliffordAlgebra.equivOfIsometry e).apply_symm_apply z
      rwa [hcancel] at happ
    have hmem := (weightedSumSquares_SO_invariant_iff w (CliffordAlgebra.equivOfIsometry e x)).mp hSO
    rw [Submodule.mem_sup] at hmem ⊢
    rcases hmem with ⟨y₀, hy₀, yₙ, hyₙ, hy_eq⟩
    refine ⟨CliffordAlgebra.equivOfIsometry e.symm y₀,
      (mem_cliffordGradeSubmodule_equivOfIsometry_iff e.symm 0 y₀).mpr hy₀,
      CliffordAlgebra.equivOfIsometry e.symm yₙ,
      (mem_cliffordGradeSubmodule_equivOfIsometry_iff e.symm (Module.finrank K M) yₙ).mpr hyₙ, ?_⟩
    rw [← map_add, hy_eq]
    change (CliffordAlgebra.equivOfIsometry e).symm ((CliffordAlgebra.equivOfIsometry e) x) = x
    exact (CliffordAlgebra.equivOfIsometry e).symm_apply_apply x
  · intro hx f hf
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨x₀, hx₀, xₙ, hxₙ, rfl⟩
    rw [map_add]
    have hx₀_fix : CliffordAlgebra.equivOfIsometry f x₀ = x₀ := by
      have hx₀' := (mem_cliffordGradeSubmodule_iff 0 x₀).mp hx₀
      rw [← hx₀', cliffordGradeProj_zero_eq_algebraMap_hTrace]
      exact isInvariant_algebraMap Q _ f
    have hxₙ_fix : CliffordAlgebra.equivOfIsometry f xₙ = xₙ :=
      equivOfIsometry_top_grade_fixed_of_mem_SO Q hf hxₙ
    rw [hx₀_fix, hxₙ_fix]

end FieldInvariants

section RealSpecialization

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [Module.Finite ℝ M]

theorem isInvariant_real_iff_hTrace_eq (Q : QuadraticForm ℝ M) (x : CliffordAlgebra Q) :
    IsInvariant (cliffordSymmetryAction Q) x ↔
      x = algebraMap ℝ (CliffordAlgebra Q) (hTrace_cl Q x) := by
  rw [isInvariant_cliffordSymmetryAction_iff_mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    simp [hTrace_cl]
  · intro h
    exact ⟨hTrace_cl Q x, h⟩

theorem isInvariant_real_iff_grace_fixed (Q : QuadraticForm ℝ M) (x : CliffordAlgebra Q) :
    IsInvariant (cliffordSymmetryAction Q) x ↔ graceOperator Q x = x := by
  rw [isInvariant_real_iff_hTrace_eq, graceOperator_fixed_iff_scalar]

end RealSpecialization

end FiniteDimInvariants

/-! ## Section 5: `Cl(1,1)` `V₄`-Invariance, Adjoint Compatibility, and Noncommutativity

Realizes Klein 1872 §4 (*Abbildung*, `cl11EquivMat_v4_equivOfIsometry`) by
transferring `V₄ ≤ O(q11)` onto `localCl11RootMap` on `M₂(ℝ)` and characterizing its
invariant scalars (`v4_invariant_cl11_iff_scalar`), fulfilling Klein's Concluding
Remarks + Footnote 37 (`arXiv:0807.3161v1` / `ABN7632.0001.001`) on a noncommutative
Clifford algebra (`cl11_noncommutative_witness`). -/

section Cl11V4Invariance

private noncomputable def v4ToQ11Fun : V4Group → (q11.IsometryEquiv q11)
  | .I => 1
  | .W1 => splitReflectionIsometryEquiv
  | .W2 => negIsometryEquiv q11
  | .W12 => splitReflectionFirstCoordinateIsometryEquiv

/-- Group homomorphism embedding the Klein four group `V4Group` into `q11.IsometryEquiv q11`,
matching `Cl11KleinFourAdjointRepresentation.rootUnit`:
- `I ↦ 1`
- `W1 ↦ splitReflectionIsometryEquiv` (`(x, -y)`)
- `W2 ↦ negIsometryEquiv q11` (`(-x, -y)`)
- `W12 ↦ splitReflectionFirstCoordinateIsometryEquiv` (`(-x, y)`). -/
noncomputable def v4ToQ11IsometryHom : V4Group →* (q11.IsometryEquiv q11) where
  toFun := v4ToQ11Fun
  map_one' := rfl
  map_mul' g h := by
    apply DFunLike.ext
    intro v
    rcases v with ⟨x, y⟩
    have hmul : g * h = v4_mul g h := rfl
    have hI : ∀ a b : ℝ, (1 : q11.IsometryEquiv q11) (a, b) = (a, b) := fun _ _ => rfl
    have h1 : ∀ a b : ℝ, splitReflectionIsometryEquiv (a, b) = (a, -b) := fun _ _ => rfl
    have h2 : ∀ a b : ℝ, negIsometryEquiv q11 (a, b) = (-a, -b) := fun _ _ => rfl
    have h12 : ∀ a b : ℝ, splitReflectionFirstCoordinateIsometryEquiv (a, b) = (-a, b) :=
      fun _ _ => rfl
    have htrans : ∀ (a b : q11.IsometryEquiv q11) (u : ℝ × ℝ), (a * b) u = a (b u) :=
      fun _ _ _ => rfl
    rw [hmul]
    change v4ToQ11Fun (v4_mul g h) (x, y) = (v4ToQ11Fun g * v4ToQ11Fun h) (x, y)
    rw [htrans]
    cases g <;> cases h <;>
      simp only [v4_mul, v4ToQ11Fun, hI, h1, h2, h12, neg_neg]

@[simp]
theorem v4ToQ11IsometryHom_I :
    v4ToQ11IsometryHom V4Group.I = 1 :=
  rfl

@[simp]
theorem v4ToQ11IsometryHom_W1 :
    v4ToQ11IsometryHom V4Group.W1 = splitReflectionIsometryEquiv :=
  rfl

@[simp]
theorem v4ToQ11IsometryHom_W2 :
    v4ToQ11IsometryHom V4Group.W2 = negIsometryEquiv q11 :=
  rfl

@[simp]
theorem v4ToQ11IsometryHom_W12 :
    v4ToQ11IsometryHom V4Group.W12 = splitReflectionFirstCoordinateIsometryEquiv :=
  rfl

/-- `equivOfIsometry ∘ v4ToQ11IsometryHom` intertwines `cl11EquivMat` with
`Cl11KleinFourAdjointRepresentation.localCl11RootMap` for every element of `V4Group`. -/
theorem cl11EquivMat_v4_equivOfIsometry (g : V4Group) (a : CliffordAlgebra q11) :
    cl11EquivMat (CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g) a) =
      localCl11RootMap g (cl11EquivMat a) := by
  have hmaps :
      cl11EquivMat.toAlgHom.comp
          (CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g)).toAlgHom =
        (localCl11RootMap g).toAlgHom.comp cl11EquivMat.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨x, y⟩
    dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply]
    change cl11EquivMat (CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g)
        (CliffordAlgebra.ι q11 (x, y))) =
      localCl11RootMap g (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
    have hι :
        CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g) (CliffordAlgebra.ι q11 (x, y)) =
          CliffordAlgebra.ι q11 (v4ToQ11IsometryHom g (x, y)) := by
      change CliffordAlgebra.map (v4ToQ11IsometryHom g).toIsometry (CliffordAlgebra.ι q11 (x, y)) = _
      rw [CliffordAlgebra.map_apply_ι]
      rfl
    rw [hι]
    cases g
    · change cl11EquivMat (CliffordAlgebra.ι q11 (x, y)) =
        adjointAlgHom (1 : Cl11Matrix.Mat2ˣ) (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      rw [adjointAlgHom_one]
      rfl
    · simp only [v4ToQ11IsometryHom_W1, localCl11RootMap, rootUnit]
      change cl11EquivMat (CliffordAlgebra.ι q11 (x, -y)) =
        adjointAlgHom gammaUnit (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      rw [adjointAlgHom_apply, adjointAlgEquiv_apply]
      have hginv : (↑(gammaUnit⁻¹) : Cl11Matrix.Mat2) = Eplus := rfl
      rw [gammaUnit_value, hginv]
      simp only [cl11EquivMat, cl11ToMat, gen]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [v4ToQ11IsometryHom_W2, localCl11RootMap, rootUnit]
      change cl11EquivMat (CliffordAlgebra.ι q11 (-x, -y)) =
        adjointAlgHom bivectorUnit (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      rw [adjointAlgHom_apply, adjointAlgEquiv_apply]
      have hbinv : (↑(bivectorUnit⁻¹) : Cl11Matrix.Mat2) = J1 := rfl
      rw [bivectorUnit_value, hbinv]
      simp only [cl11EquivMat, cl11ToMat, gen]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [v4ToQ11IsometryHom_W12, localCl11RootMap, rootUnit]
      change cl11EquivMat (CliffordAlgebra.ι q11 (-x, y)) =
        adjointAlgHom causalUnit (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      rw [adjointAlgHom_apply, adjointAlgEquiv_apply]
      have hcinv : (↑(causalUnit⁻¹) : Cl11Matrix.Mat2) = -Eminus := rfl
      rw [causalUnit_value, hcinv]
      simp only [cl11EquivMat, cl11ToMat, gen]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]
  exact DFunLike.congr_fun hmaps a

theorem v4_invariant_cl11_iff_scalar (a : CliffordAlgebra q11) :
    (splitReflectionCliffordAuto a = a ∧ splitReflectionFirstCoordinateCliffordAuto a = a) ↔
      ∃ r : ℝ, a = algebraMap ℝ (CliffordAlgebra q11) r := by
  constructor
  · rintro ⟨h1, h2⟩
    let M : Cl11Matrix.Mat2 := cl11EquivMat a
    have hM1 : adjointAlgEquiv gammaUnit M = M := by
      have h := congrArg cl11EquivMat h1
      rwa [cl11EquivMat_splitReflectionCliffordAuto] at h
    have hM2 : adjointAlgEquiv causalUnit M = M := by
      have h := congrArg cl11EquivMat h2
      have h2' :
          cl11EquivMat (splitReflectionFirstCoordinateCliffordAuto a) =
            localCl11RootMap V4Group.W12 (cl11EquivMat a) :=
        cl11EquivMat_v4_equivOfIsometry V4Group.W12 a
      rw [h2'] at h
      simpa [localCl11RootMap, rootUnit] using h
    have h01 : M 0 1 = 0 := by
      have h := congrArg (fun X : Cl11Matrix.Mat2 => X 0 1) hM1
      have hginv : (↑(gammaUnit⁻¹) : Cl11Matrix.Mat2) = Eplus := rfl
      rw [adjointAlgEquiv_apply, gammaUnit_value, hginv] at h
      simp [Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead,
        Matrix.vecTail] at h
      linarith
    have h10 : M 1 0 = 0 := by
      have h := congrArg (fun X : Cl11Matrix.Mat2 => X 1 0) hM1
      have hginv : (↑(gammaUnit⁻¹) : Cl11Matrix.Mat2) = Eplus := rfl
      rw [adjointAlgEquiv_apply, gammaUnit_value, hginv] at h
      simp [Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead,
        Matrix.vecTail] at h
      linarith
    have hdiag : M 0 0 = M 1 1 := by
      have h := congrArg (fun X : Cl11Matrix.Mat2 => X 0 0) hM2
      have hcinv : (↑(causalUnit⁻¹) : Cl11Matrix.Mat2) = -Eminus := rfl
      rw [adjointAlgEquiv_apply, causalUnit_value, hcinv] at h
      simp [Eminus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead,
        Matrix.vecTail] at h
      linarith
    have hM_eq : M = (M 0 0) • (1 : Cl11Matrix.Mat2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hdiag, h01, h10]
    refine ⟨M 0 0, ?_⟩
    apply cl11EquivMat.injective
    rw [AlgEquiv.commutes]
    simpa [Algebra.algebraMap_eq_smul_one] using hM_eq
  · rintro ⟨r, rfl⟩
    exact ⟨AlgEquiv.commutes _ r, AlgEquiv.commutes _ r⟩

theorem v4ToQ11IsometryHom_invariant_iff_scalar (a : CliffordAlgebra q11) :
    (∀ g : V4Group, CliffordAlgebra.equivOfIsometry (v4ToQ11IsometryHom g) a = a) ↔
      ∃ r : ℝ, a = algebraMap ℝ (CliffordAlgebra q11) r := by
  constructor
  · intro hg
    exact (v4_invariant_cl11_iff_scalar a).mp ⟨hg V4Group.W1, hg V4Group.W12⟩
  · rintro ⟨r, rfl⟩ g
    exact AlgEquiv.commutes _ r

/-- Explicit noncommutativity witness in `CliffordAlgebra q11`: the canonical
generators `ι q11 (1, 0)` and `ι q11 (0, 1)` do not commute. -/
theorem cl11_noncommutative_witness :
    CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1) ≠
      CliffordAlgebra.ι q11 (0, 1) * CliffordAlgebra.ι q11 (1, 0) := by
  intro h
  have hm := congrArg (fun x => (cl11EquivMat x) 0 1) h
  simp only [map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg] at hm
  simp only [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at hm
  norm_num at hm

end Cl11V4Invariance

end InfoGeometry.Clifford.CoordinateLessCliffordInvariance