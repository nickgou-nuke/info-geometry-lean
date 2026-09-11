import InfoGeometry.RootSystem.D4RootLattice
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The rational dual carrier of the integral `D₄` lattice

This file proves the first dual-lattice facts only.  The discriminant quotient
and its triality action are intentionally separate: they require a quotient
construction, not merely a list of four labels.
-/

namespace InfoGeometry.RootSystem.D4

abbrev RationalAmbient := InfoGeometry.Algebra.FiniteSpin.Vec4Q

def integerEmbedding (x : Ambient) : RationalAmbient := fun i => x i

def rationalDot (x y : RationalAmbient) : ℚ := ∑ i, x i * y i

def IsDual (x : RationalAmbient) : Prop :=
  ∀ y : Lattice, ∃ n : ℤ, rationalDot x (integerEmbedding y.1) = n

abbrev DualLattice := {x : RationalAmbient // IsDual x}

theorem zero_mem_dual : IsDual (0 : RationalAmbient) := by
  intro y
  refine ⟨0, ?_⟩
  simp [rationalDot]

theorem add_mem_dual {x y : RationalAmbient}
    (hx : IsDual x) (hy : IsDual y) : IsDual (x + y) := by
  intro z
  obtain ⟨m, hm⟩ := hx z
  obtain ⟨n, hn⟩ := hy z
  refine ⟨m + n, ?_⟩
  rw [show rationalDot (x + y) (integerEmbedding z.1) =
      rationalDot x (integerEmbedding z.1) +
    rationalDot y (integerEmbedding z.1) by
    simp [rationalDot, Finset.sum_add_distrib, add_mul]]
  simp [hm, hn]

theorem neg_mem_dual {x : RationalAmbient}
    (hx : IsDual x) : IsDual (-x) := by
  intro z
  obtain ⟨m, hm⟩ := hx z
  refine ⟨-m, ?_⟩
  simpa [rationalDot, neg_mul, Finset.sum_neg_distrib, hm]

theorem rationalDot_integerEmbedding (x y : Ambient) :
    rationalDot (integerEmbedding x) (integerEmbedding y) = dot x y := by
  calc
    rationalDot (integerEmbedding x) (integerEmbedding y) =
        ∑ i, (x i : ℚ) * (y i : ℚ) := by
      simp [rationalDot, integerEmbedding]
    _ = dot x y := by
      simp [dot, Fin.sum_univ_four]

theorem integerEmbedding_mem_dual (x : Lattice) :
    IsDual (integerEmbedding x.1) := by
  intro y
  refine ⟨dot x.1 y.1, ?_⟩
  exact rationalDot_integerEmbedding x.1 y.1

def dualEmbedding (x : Lattice) : DualLattice :=
  ⟨integerEmbedding x.1, integerEmbedding_mem_dual x⟩

theorem integerEmbedding_injective : Function.Injective integerEmbedding := by
  intro x y h
  funext i
  have h' : (x i : ℚ) = y i := by
    simpa [integerEmbedding] using congrFun h i
  exact_mod_cast h'

theorem dualEmbedding_injective : Function.Injective dualEmbedding := by
  intro x y h
  apply Subtype.ext
  exact integerEmbedding_injective (congrArg Subtype.val h)

def dualSubgroup : AddSubgroup RationalAmbient where
  carrier := IsDual
  zero_mem' := zero_mem_dual
  add_mem' := add_mem_dual
  neg_mem' := neg_mem_dual

theorem mem_dualSubgroup_iff (x : RationalAmbient) :
    x ∈ dualSubgroup ↔ IsDual x := Iff.rfl

def dualSubgroupEmbedding (x : Lattice) : dualSubgroup :=
  ⟨integerEmbedding x.1, integerEmbedding_mem_dual x⟩

theorem dualSubgroupEmbedding_injective :
    Function.Injective dualSubgroupEmbedding := by
  intro x y h
  apply Subtype.ext
  exact integerEmbedding_injective (congrArg Subtype.val h)

def latticeToDualSubgroup : latticeSubgroup →+ dualSubgroup where
  toFun x := dualSubgroupEmbedding ⟨x.1, x.2⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' := by
    intro x y
    apply Subtype.ext
    change integerEmbedding (x.1 + y.1) =
      integerEmbedding x.1 + integerEmbedding y.1
    funext i
    change ((x.1 i + y.1 i : ℤ) : ℚ) =
      (x.1 i : ℚ) + (y.1 i : ℚ)
    simp

def integralSubgroup : AddSubgroup dualSubgroup :=
  AddSubgroup.map latticeToDualSubgroup ⊤

theorem integerEmbedding_mem_integralSubgroup_iff (x : Ambient)
    (hx : IsDual (integerEmbedding x)) :
    (⟨integerEmbedding x, hx⟩ : dualSubgroup) ∈ integralSubgroup ↔ IsD4 x := by
  constructor
  · intro h
    rcases AddSubgroup.mem_map.mp h with ⟨y, -, hy⟩
    have hxy : integerEmbedding x = integerEmbedding y.1 := by
      simpa [latticeToDualSubgroup, dualSubgroupEmbedding] using
        (congrArg Subtype.val hy).symm
    have hxy' : x = y.1 := integerEmbedding_injective hxy
    have hyD : IsD4 y.1 := by exact y.2
    simpa [← hxy'] using hyD
  · intro hx
    apply AddSubgroup.mem_map.mpr
    refine ⟨⟨x, hx⟩, Set.mem_univ _, ?_⟩
    rfl

theorem integerEmbedding_mem_dual_ambient (x : Ambient) :
    IsDual (integerEmbedding x) := by
  intro y
  refine ⟨dot x y.1, ?_⟩
  exact rationalDot_integerEmbedding x y.1

theorem integralSubgroup_mem (x : Lattice) :
    dualSubgroupEmbedding x ∈ integralSubgroup := by
  apply AddSubgroup.mem_map.mpr
  refine ⟨⟨x.1, x.2⟩, Set.mem_univ _, ?_⟩
  rfl

theorem two_integerEmbedding_mem_integralSubgroup (y : Ambient) :
    (⟨integerEmbedding (2 • y), integerEmbedding_mem_dual_ambient (2 • y)⟩ :
      dualSubgroup) ∈ integralSubgroup := by
  apply (integerEmbedding_mem_integralSubgroup_iff (2 • y)
    (integerEmbedding_mem_dual_ambient (2 • y))).2
  change coordinateSum (2 • y) % 2 = 0
  apply Int.emod_eq_zero_of_dvd
  have hsum : coordinateSum (2 • y) = 2 * coordinateSum y := by
    have h0 : (2 • y) 0 = y 0 + y 0 := by rw [two_smul]; rfl
    have h1 : (2 • y) 1 = y 1 + y 1 := by rw [two_smul]; rfl
    have h2 : (2 • y) 2 = y 2 + y 2 := by rw [two_smul]; rfl
    have h3 : (2 • y) 3 = y 3 + y 3 := by rw [two_smul]; rfl
    simp only [coordinateSum, Fin.sum_univ_four]
    rw [h0, h1, h2, h3]
    ring
  rw [hsum]
  simp

abbrev discriminantCarrier := dualSubgroup ⧸ integralSubgroup

def discriminantMap : dualSubgroup →+ discriminantCarrier :=
  QuotientAddGroup.mk' integralSubgroup

theorem discriminantMap_surjective :
    Function.Surjective discriminantMap := by
  exact QuotientAddGroup.mk'_surjective integralSubgroup

theorem discriminantMap_integral (x : Lattice) :
    discriminantMap (dualSubgroupEmbedding x) = 0 := by
  change QuotientAddGroup.mk' integralSubgroup (dualSubgroupEmbedding x) =
    QuotientAddGroup.mk' integralSubgroup 0
  rw [QuotientAddGroup.mk'_eq_mk']
  refine ⟨-(dualSubgroupEmbedding x), ?_, ?_⟩
  · exact AddSubgroup.neg_mem _ (integralSubgroup_mem x)
  · simp

theorem discriminantMap_eq_of_sub_mem {u v : dualSubgroup}
    (h : u - v ∈ integralSubgroup) :
    discriminantMap u = discriminantMap v := by
  have hz : discriminantMap (u - v) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 h
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

def firstCoordinate : RationalAmbient := ![1, 0, 0, 0]

def halfCoordinate : RationalAmbient := fun _ => (1 / 2 : ℚ)

theorem halfCoordinate_mem_dual : IsDual halfCoordinate := by
  intro y
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero y.2
  refine ⟨k, ?_⟩
  have hkQ := congrArg (fun z : ℤ => (z : ℚ)) hk
  simp [coordinateSum, Fin.sum_univ_four] at hkQ
  simp only [halfCoordinate, rationalDot, integerEmbedding,
    Fin.sum_univ_four]
  norm_num at hkQ ⊢
  linarith

def halfCoordinateSubgroup : dualSubgroup :=
  ⟨halfCoordinate, halfCoordinate_mem_dual⟩

/-! The second half-integral discriminant representative. -/

def signedHalfCoordinate : RationalAmbient := fun i =>
  if i = 3 then -(1 / 2 : ℚ) else 1 / 2

theorem signedHalfCoordinate_mem_dual : IsDual signedHalfCoordinate := by
  intro y
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero y.2
  refine ⟨k - y.1 3, ?_⟩
  have hkQ := congrArg (fun z : ℤ => (z : ℚ)) hk
  simp [coordinateSum, Fin.sum_univ_four] at hkQ
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp [signedHalfCoordinate, rationalDot, integerEmbedding,
    Fin.sum_univ_four, h03, h13, h23]
  norm_num at ⊢
  linarith

def signedHalfCoordinateSubgroup : dualSubgroup :=
  ⟨signedHalfCoordinate, signedHalfCoordinate_mem_dual⟩

theorem signedHalfCoordinate_not_mem_integralSubgroup :
    signedHalfCoordinateSubgroup ∉ integralSubgroup := by
  intro h
  rcases AddSubgroup.mem_map.mp h with ⟨y, -, hy⟩
  have hy' : integerEmbedding y.1 = signedHalfCoordinate :=
    congrArg Subtype.val hy
  have h0 := congrFun hy' 0
  have hmulQ : (2 : ℚ) * (y.1 0 : ℚ) = 1 := by
    have h0' : (y.1 0 : ℚ) = 1 / 2 := by
      simpa [integerEmbedding, signedHalfCoordinate,
        Matrix.cons_val_zero] using h0
    linarith
  have hmulZ : (2 : ℤ) * y.1 0 = 1 := by
    exact_mod_cast hmulQ
  omega

def negativeThirdBasis : Ambient := fun i =>
  if i = 3 then -1 else 0

theorem coordinateSum_sub (x y : Ambient) :
    coordinateSum (x - y) = coordinateSum x - coordinateSum y := by
  change (∑ i : Fin 4, (x i - y i)) = _
  rw [Finset.sum_sub_distrib]
  rfl

theorem coordinateSum_basisVector_zero :
    coordinateSum (basisVector 0) = 1 := by
  simp [coordinateSum, basisVector, Fin.sum_univ_four]

theorem coordinateSum_negativeThirdBasis :
    coordinateSum negativeThirdBasis = -1 := by
  simp [coordinateSum, negativeThirdBasis, Fin.sum_univ_four]

theorem basisVector_zero_add_sub (y : Ambient) :
    basisVector 0 + (y - basisVector 0) = y := by
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [basisVector]
  · simp [basisVector, h0]

theorem negativeThirdBasis_add_sub (y : Ambient) :
    negativeThirdBasis + (y - negativeThirdBasis) = y := by
  funext i
  by_cases h3 : i = 3
  · subst i
    simp [negativeThirdBasis]
  · simp [negativeThirdBasis, h3]

theorem integerEmbedding_sub_basisVector_zero (y : Ambient) :
    integerEmbedding (y - basisVector 0) =
      integerEmbedding y - firstCoordinate := by
  funext i
  fin_cases i
  · simp [Ambient, integerEmbedding, basisVector, firstCoordinate, Pi.sub_apply]
  · simp only [integerEmbedding, Pi.sub_apply]
    change ((y 1 - (basisVector 0) 1 : ℤ) : ℚ) =
      (y 1 : ℚ) - firstCoordinate 1
    simp [basisVector, firstCoordinate]
  · simp only [integerEmbedding, Pi.sub_apply]
    change ((y 2 - (basisVector 0) 2 : ℤ) : ℚ) =
      (y 2 : ℚ) - firstCoordinate 2
    simp [basisVector, firstCoordinate]
  · simp only [integerEmbedding, Pi.sub_apply]
    change ((y 3 - (basisVector 0) 3 : ℤ) : ℚ) =
      (y 3 : ℚ) - firstCoordinate 3
    simp [basisVector, firstCoordinate]

theorem signedHalf_sub_half_eq_integerEmbedding :
    signedHalfCoordinate - halfCoordinate = integerEmbedding negativeThirdBasis := by
  funext i
  by_cases hi : i = 3
  · subst hi
    norm_num [signedHalfCoordinate, halfCoordinate, negativeThirdBasis,
      integerEmbedding]
  · simp [signedHalfCoordinate, halfCoordinate, negativeThirdBasis,
      integerEmbedding, hi]

theorem negativeThirdBasis_not_D4 : ¬ IsD4 negativeThirdBasis := by
  norm_num [negativeThirdBasis, IsD4, coordinateSum, Fin.sum_univ_four]

theorem discriminantMap_signedHalf_half_distinct :
    discriminantMap signedHalfCoordinateSubgroup ≠
      discriminantMap halfCoordinateSubgroup := by
  intro h
  have hzero : discriminantMap
      (signedHalfCoordinateSubgroup - halfCoordinateSubgroup) = 0 := by
    rw [map_sub, h, sub_self]
  have hmem : signedHalfCoordinateSubgroup - halfCoordinateSubgroup ∈
      integralSubgroup := by
    exact (QuotientAddGroup.eq_zero_iff _).mp hzero
  have hdiff : (signedHalfCoordinateSubgroup - halfCoordinateSubgroup).1 =
      integerEmbedding negativeThirdBasis := by
    change signedHalfCoordinate - halfCoordinate = integerEmbedding negativeThirdBasis
    exact signedHalf_sub_half_eq_integerEmbedding
  have hmem' :
      (⟨integerEmbedding negativeThirdBasis,
        integerEmbedding_mem_dual_ambient negativeThirdBasis⟩ : dualSubgroup) ∈
      integralSubgroup := by
    have heq : signedHalfCoordinateSubgroup - halfCoordinateSubgroup =
        (⟨integerEmbedding negativeThirdBasis,
          integerEmbedding_mem_dual_ambient negativeThirdBasis⟩ : dualSubgroup) :=
      Subtype.ext hdiff
    exact heq ▸ hmem
  have hfalse := (integerEmbedding_mem_integralSubgroup_iff
    negativeThirdBasis (integerEmbedding_mem_dual_ambient negativeThirdBasis)).mp hmem'
  exact negativeThirdBasis_not_D4 hfalse

theorem two_signedHalfCoordinate_mem_integralSubgroup :
    signedHalfCoordinateSubgroup + signedHalfCoordinateSubgroup ∈
      integralSubgroup := by
  apply AddSubgroup.mem_map.mpr
  let y : Lattice :=
    ⟨![1, 1, 1, -1], by native_decide⟩
  refine ⟨y, Set.mem_univ _, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [signedHalfCoordinateSubgroup, signedHalfCoordinate, y,
      dualSubgroupEmbedding, latticeToDualSubgroup, integerEmbedding] <;>
      norm_num

theorem discriminantMap_signedHalfCoordinate_two_eq_zero :
    discriminantMap signedHalfCoordinateSubgroup +
        discriminantMap signedHalfCoordinateSubgroup = 0 := by
  rw [← map_add]
  change discriminantMap
    (signedHalfCoordinateSubgroup + signedHalfCoordinateSubgroup) = 0
  exact (QuotientAddGroup.eq_zero_iff _).2
    two_signedHalfCoordinate_mem_integralSubgroup

theorem halfCoordinate_not_mem_integralSubgroup :
    halfCoordinateSubgroup ∉ integralSubgroup := by
  intro h
  rcases AddSubgroup.mem_map.mp h with ⟨y, -, hy⟩
  have hcoord : integerEmbedding y.1 = halfCoordinate :=
    congrArg Subtype.val hy
  have hzero := congrFun hcoord 0
  norm_num [integerEmbedding, halfCoordinate, Matrix.cons_val_zero] at hzero
  have hmulQ : (2 : ℚ) * (y.1 0 : ℚ) = 1 := by
    linarith
  have hmulZ : (2 : ℤ) * y.1 0 = 1 := by
    exact_mod_cast hmulQ
  omega

theorem firstCoordinate_mem_dual : IsDual firstCoordinate := by
  intro y
  refine ⟨y.1 0, ?_⟩
  change rationalDot firstCoordinate (integerEmbedding y.1) = (y.1 0 : ℚ)
  simp [firstCoordinate, rationalDot, integerEmbedding, Fin.sum_univ_four]

def firstCoordinateDual : DualLattice :=
  ⟨firstCoordinate, firstCoordinate_mem_dual⟩

theorem firstCoordinate_not_in_D4 :
    ¬ IsD4 (fun i => if i = 0 then 1 else 0) := by
  intro h
  norm_num [IsD4, coordinateSum] at h

theorem dual_strictly_contains_integral_carrier :
    ∃ x : DualLattice, x.1 ∉ Set.range (fun y : Lattice => (dualEmbedding y).1) := by
  refine ⟨firstCoordinateDual, ?_⟩
  rintro ⟨y, hy⟩
  have hcoord : y.1 = (fun i => if i = 0 then 1 else 0) := by
    funext i
    have hy' : integerEmbedding y.1 = firstCoordinate := by
      simpa [dualEmbedding, firstCoordinate] using hy
    fin_cases i
    · have h := congrFun hy' 0
      have h' : (y.1 0 : ℚ) = 1 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_zero] using h
      exact_mod_cast h'
    · have h := congrFun hy' 1
      have h' : (y.1 1 : ℚ) = 0 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_one] using h
      exact_mod_cast h'
    · have h := congrFun hy' 2
      have h' : (y.1 2 : ℚ) = 0 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_two] using h
      exact_mod_cast h'
    · have h := congrFun hy' 3
      have h' : (y.1 3 : ℚ) = 0 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_three] using h
      exact_mod_cast h'
  exact firstCoordinate_not_in_D4 (by simpa [hcoord] using y.2)

def firstCoordinateSubgroup : dualSubgroup :=
  ⟨firstCoordinate, firstCoordinate_mem_dual⟩

theorem discriminantMap_signedHalf_first_distinct :
    discriminantMap signedHalfCoordinateSubgroup ≠
      discriminantMap firstCoordinateSubgroup := by
  intro h
  have hzero : discriminantMap
      (signedHalfCoordinateSubgroup - firstCoordinateSubgroup) = 0 := by
    rw [map_sub, h, sub_self]
  have hmem : signedHalfCoordinateSubgroup - firstCoordinateSubgroup ∈
      integralSubgroup := (QuotientAddGroup.eq_zero_iff _).mp hzero
  rcases AddSubgroup.mem_map.mp hmem with ⟨y, -, hy⟩
  have hcoord := congrArg (fun v : dualSubgroup => v.1 0) hy
  have hmulQ : (2 : ℚ) * (y.1 0 : ℚ) = -1 := by
    have hcoord' : (y.1 0 : ℚ) = -(1 / 2) := by
      have hcoord'' : integerEmbedding y.1 0 = (1 / 2 : ℚ) - 1 := by
        simpa [latticeToDualSubgroup, dualSubgroupEmbedding,
          signedHalfCoordinateSubgroup, firstCoordinateSubgroup,
          signedHalfCoordinate, firstCoordinate] using hcoord
      change (y.1 0 : ℚ) = (1 / 2 : ℚ) - 1 at hcoord''
      norm_num at hcoord''
      exact hcoord''
    linarith
  have hmulZ : (2 : ℤ) * y.1 0 = -1 := by
    exact_mod_cast hmulQ
  omega

theorem two_halfCoordinate_mem_integralSubgroup :
    halfCoordinateSubgroup + halfCoordinateSubgroup ∈ integralSubgroup := by
  apply AddSubgroup.mem_map.mpr
  let y : Ambient := fun _ => 1
  have hy : IsD4 y := by
    norm_num [IsD4, coordinateSum, y, Fin.sum_univ_four]
  let ly : Lattice := ⟨y, hy⟩
  refine ⟨ly, Set.mem_univ _, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;>
    norm_num [halfCoordinateSubgroup, halfCoordinate, y,
      dualSubgroupEmbedding, latticeToDualSubgroup, integerEmbedding]

theorem discriminantMap_halfCoordinate_add_self_eq_zero :
    discriminantMap halfCoordinateSubgroup +
        discriminantMap halfCoordinateSubgroup = 0 := by
  rw [← map_add]
  exact (QuotientAddGroup.eq_zero_iff _).2
    two_halfCoordinate_mem_integralSubgroup

theorem two_firstCoordinate_mem_integralSubgroup :
    firstCoordinateSubgroup + firstCoordinateSubgroup ∈ integralSubgroup := by
  apply AddSubgroup.mem_map.mpr
  let y : Lattice :=
    ⟨fun i => if i = 0 then 2 else 0, by
      norm_num [IsD4, coordinateSum, Fin.sum_univ_four]⟩
  refine ⟨y, Set.mem_univ _, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;>
    norm_num [firstCoordinateSubgroup, firstCoordinate, y,
      dualSubgroupEmbedding, latticeToDualSubgroup, integerEmbedding,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem discriminantMap_firstCoordinate_add_self_eq_zero :
    discriminantMap firstCoordinateSubgroup +
        discriminantMap firstCoordinateSubgroup = 0 := by
  rw [← map_add]
  exact (QuotientAddGroup.eq_zero_iff _).2
    two_firstCoordinate_mem_integralSubgroup

theorem firstCoordinate_not_mem_integralSubgroup :
    firstCoordinateSubgroup ∉ integralSubgroup := by
  intro h
  rcases AddSubgroup.mem_map.mp h with ⟨y, -, hy⟩
  have hcoord : y.1 = (fun i => if i = 0 then 1 else 0) := by
    have hy' : integerEmbedding y.1 = firstCoordinate := by
      exact congrArg Subtype.val hy
    funext i
    fin_cases i
    · have h := congrFun hy' 0
      have h' : (y.1 0 : ℚ) = 1 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_zero] using h
      exact_mod_cast h'
    · have h := congrFun hy' 1
      have h' : (y.1 1 : ℚ) = 0 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_one] using h
      exact_mod_cast h'
    · have h := congrFun hy' 2
      have h' : (y.1 2 : ℚ) = 0 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_two] using h
      exact_mod_cast h'
    · have h := congrFun hy' 3
      have h' : (y.1 3 : ℚ) = 0 := by
        simpa [integerEmbedding, firstCoordinate, Matrix.cons_val_three] using h
      exact_mod_cast h'
  exact firstCoordinate_not_in_D4 (by simpa [hcoord] using y.2)

theorem discriminantMap_firstCoordinate_ne_zero :
    discriminantMap firstCoordinateSubgroup ≠ 0 := by
  intro h
  have h' : QuotientAddGroup.mk' integralSubgroup firstCoordinateSubgroup =
      QuotientAddGroup.mk' integralSubgroup 0 := h
  rw [QuotientAddGroup.mk'_eq_mk'] at h'
  rcases h' with ⟨z, hz, hsum⟩
  have hneg : firstCoordinateSubgroup = -z :=
    eq_neg_of_add_eq_zero_left hsum
  have hm : firstCoordinateSubgroup ∈ integralSubgroup := by
    rw [hneg]
    exact integralSubgroup.neg_mem hz
  exact firstCoordinate_not_mem_integralSubgroup hm

theorem discriminantMap_ne_zero_of_not_mem
    {x : dualSubgroup} (hx : x ∉ integralSubgroup) :
    discriminantMap x ≠ 0 := by
  intro h
  exact hx ((QuotientAddGroup.eq_zero_iff _).mp h)

theorem discriminantMap_halfCoordinate_ne_zero :
    discriminantMap halfCoordinateSubgroup ≠ 0 :=
  discriminantMap_ne_zero_of_not_mem halfCoordinate_not_mem_integralSubgroup

theorem discriminantMap_signedHalfCoordinate_ne_zero :
    discriminantMap signedHalfCoordinateSubgroup ≠ 0 :=
  discriminantMap_ne_zero_of_not_mem signedHalfCoordinate_not_mem_integralSubgroup

theorem discriminantMap_first_half_distinct :
    discriminantMap firstCoordinateSubgroup ≠
      discriminantMap halfCoordinateSubgroup := by
  intro h
  have h' : QuotientAddGroup.mk' integralSubgroup firstCoordinateSubgroup =
      QuotientAddGroup.mk' integralSubgroup halfCoordinateSubgroup := h
  rw [QuotientAddGroup.mk'_eq_mk'] at h'
  rcases h' with ⟨z, hz, hsum⟩
  rcases AddSubgroup.mem_map.mp hz with ⟨y, -, hy⟩
  have hsum' := congrArg (fun v : dualSubgroup => v.1 0) hsum
  have hy' : integerEmbedding y.1 = (z : RationalAmbient) :=
    congrArg Subtype.val hy
  have hzero : (1 : ℚ) + (y.1 0 : ℚ) = 1 / 2 := by
    have hsum'' := hsum'
    simp [firstCoordinateSubgroup, halfCoordinateSubgroup, firstCoordinate,
      halfCoordinate] at hsum''
    rw [← hy'] at hsum''
    have hcoord : integerEmbedding y.1 0 = (y.1 0 : ℚ) := rfl
    rw [hcoord] at hsum''
    norm_num at hsum''
    exact hsum''
  have hmulQ : (2 : ℚ) * (y.1 0 : ℚ) = -1 := by
    linarith
  have hmulZ : (2 : ℤ) * y.1 0 = -1 := by
    exact_mod_cast hmulQ
  omega

theorem discriminantMap_first_signedHalf_distinct :
    discriminantMap firstCoordinateSubgroup ≠
      discriminantMap signedHalfCoordinateSubgroup := by
  intro h
  have h' : QuotientAddGroup.mk' integralSubgroup firstCoordinateSubgroup =
      QuotientAddGroup.mk' integralSubgroup signedHalfCoordinateSubgroup := h
  rw [QuotientAddGroup.mk'_eq_mk'] at h'
  rcases h' with ⟨z, hz, hsum⟩
  rcases AddSubgroup.mem_map.mp hz with ⟨y, -, hy⟩
  have hsum' := congrArg (fun v : dualSubgroup => v.1 0) hsum
  have hy' : integerEmbedding y.1 = (z : RationalAmbient) :=
    congrArg Subtype.val hy
  have hzero : (1 : ℚ) + (y.1 0 : ℚ) = 1 / 2 := by
    have hsum'' := hsum'
    simp [firstCoordinateSubgroup, signedHalfCoordinateSubgroup,
      firstCoordinate, signedHalfCoordinate] at hsum''
    rw [← hy'] at hsum''
    have hcoord : integerEmbedding y.1 0 = (y.1 0 : ℚ) := rfl
    rw [hcoord] at hsum''
    norm_num at hsum''
    exact hsum''
  have hmulQ : (2 : ℚ) * (y.1 0 : ℚ) = -1 := by
    linarith
  have hmulZ : (2 : ℤ) * y.1 0 = -1 := by
    exact_mod_cast hmulQ
  omega

def discriminantRepresentatives : Fin 4 → discriminantCarrier :=
  ![0, discriminantMap firstCoordinateSubgroup,
    discriminantMap halfCoordinateSubgroup,
    discriminantMap signedHalfCoordinateSubgroup]

theorem discriminantRepresentatives_injective :
    Function.Injective discriminantRepresentatives := by
  intro i j h
  fin_cases i
  · fin_cases j
    · rfl
    · exfalso
      exact discriminantMap_firstCoordinate_ne_zero h.symm
    · exfalso
      exact discriminantMap_halfCoordinate_ne_zero h.symm
    · exfalso
      exact discriminantMap_signedHalfCoordinate_ne_zero h.symm
  · fin_cases j
    · exfalso
      exact discriminantMap_firstCoordinate_ne_zero h
    · rfl
    · exfalso
      exact discriminantMap_first_half_distinct h
    · exfalso
      exact discriminantMap_first_signedHalf_distinct h
  · fin_cases j
    · exfalso
      exact discriminantMap_halfCoordinate_ne_zero h
    · exfalso
      exact discriminantMap_first_half_distinct h.symm
    · rfl
    · exfalso
      apply discriminantMap_signedHalf_half_distinct
      simpa [discriminantRepresentatives] using h.symm
  · fin_cases j
    · exfalso
      exact discriminantMap_signedHalfCoordinate_ne_zero h
    · exfalso
      exact discriminantMap_first_signedHalf_distinct h.symm
    · exfalso
      apply discriminantMap_signedHalf_half_distinct
      simpa [discriminantRepresentatives] using h
    · rfl

theorem discriminantCarrier_nontrivial :
    Nontrivial discriminantCarrier := by
  refine ⟨0, discriminantMap firstCoordinateSubgroup, ?_⟩
  exact discriminantMap_firstCoordinate_ne_zero.symm

theorem dual_two_coordinate_integral (x : DualLattice) (i : Fin 4) :
    ∃ n : ℤ, 2 * x.1 i = n := by
  fin_cases i
  · let ym : Lattice := ⟨![1, -1, 0, 0], by native_decide⟩
    let yp : Lattice := ⟨![1, 1, 0, 0], by native_decide⟩
    obtain ⟨m, hm⟩ := x.2 ym
    obtain ⟨p, hp⟩ := x.2 yp
    refine ⟨m + p, ?_⟩
    have hm' : x.1 0 - x.1 1 = (m : ℚ) := by
      simpa [sub_eq_add_neg, rationalDot, integerEmbedding, ym,
        Fin.sum_univ_four] using hm
    have hp' : x.1 0 + x.1 1 = (p : ℚ) := by
      simpa [rationalDot, integerEmbedding, yp, Fin.sum_univ_four] using hp
    change 2 * x.1 0 = (m + p : ℤ)
    exact_mod_cast (by linarith : 2 * x.1 0 = (m : ℚ) + p)
  · let ym : Lattice := ⟨![1, -1, 0, 0], by native_decide⟩
    let yp : Lattice := ⟨![1, 1, 0, 0], by native_decide⟩
    obtain ⟨m, hm⟩ := x.2 ym
    obtain ⟨p, hp⟩ := x.2 yp
    refine ⟨p - m, ?_⟩
    have hm' : x.1 0 - x.1 1 = (m : ℚ) := by
      simpa [sub_eq_add_neg, rationalDot, integerEmbedding, ym,
        Fin.sum_univ_four] using hm
    have hp' : x.1 0 + x.1 1 = (p : ℚ) := by
      simpa [rationalDot, integerEmbedding, yp, Fin.sum_univ_four] using hp
    change 2 * x.1 1 = (p - m : ℤ)
    exact_mod_cast (by linarith : 2 * x.1 1 = (p : ℚ) - m)
  · let ym : Lattice := ⟨![0, 0, 1, -1], by native_decide⟩
    let yp : Lattice := ⟨![0, 0, 1, 1], by native_decide⟩
    obtain ⟨m, hm⟩ := x.2 ym
    obtain ⟨p, hp⟩ := x.2 yp
    refine ⟨m + p, ?_⟩
    change 2 * (x.1 2 : ℚ) = _
    have hm' : x.1 2 - x.1 3 = (m : ℚ) := by
      simpa [sub_eq_add_neg, rationalDot, integerEmbedding, ym,
        Fin.sum_univ_four] using hm
    have hp' : x.1 2 + x.1 3 = (p : ℚ) := by
      simpa [rationalDot, integerEmbedding, yp, Fin.sum_univ_four] using hp
    exact_mod_cast (by linarith : 2 * x.1 2 = (m : ℚ) + p)
  · let ym : Lattice := ⟨![0, 0, 1, -1], by native_decide⟩
    let yp : Lattice := ⟨![0, 0, 1, 1], by native_decide⟩
    obtain ⟨m, hm⟩ := x.2 ym
    obtain ⟨p, hp⟩ := x.2 yp
    refine ⟨p - m, ?_⟩
    change 2 * (x.1 3 : ℚ) = _
    have hm' : x.1 2 - x.1 3 = (m : ℚ) := by
      simpa [sub_eq_add_neg, rationalDot, integerEmbedding, ym,
        Fin.sum_univ_four] using hm
    have hp' : x.1 2 + x.1 3 = (p : ℚ) := by
      simpa [rationalDot, integerEmbedding, yp, Fin.sum_univ_four] using hp
    exact_mod_cast (by linarith : 2 * x.1 3 = (p : ℚ) - m)

theorem dual_coordinate_half_integral (x : DualLattice) (i : Fin 4) :
    ∃ n : ℤ, x.1 i = (n : ℚ) / 2 := by
  obtain ⟨n, hn⟩ := dual_two_coordinate_integral x i
  refine ⟨n, ?_⟩
  linarith

theorem dual_simpleRoot_pairings_integral (x : DualLattice) :
    (∃ a : ℤ, x.1 0 - x.1 1 = a) ∧
    (∃ b : ℤ, x.1 1 - x.1 2 = b) ∧
    (∃ c : ℤ, x.1 2 - x.1 3 = c) ∧
    (∃ d : ℤ, x.1 2 + x.1 3 = d) := by
  let r01 : Lattice := ⟨![1, -1, 0, 0], by native_decide⟩
  let r12 : Lattice := ⟨![0, 1, -1, 0], by native_decide⟩
  let r23 : Lattice := ⟨![0, 0, 1, -1], by native_decide⟩
  let r2p3 : Lattice := ⟨![0, 0, 1, 1], by native_decide⟩
  obtain ⟨a, ha⟩ := x.2 r01
  obtain ⟨b, hb⟩ := x.2 r12
  obtain ⟨c, hc⟩ := x.2 r23
  obtain ⟨d, hd⟩ := x.2 r2p3
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨a, ?_⟩
    simpa [rationalDot, integerEmbedding, r01, Fin.sum_univ_four,
      sub_eq_add_neg] using ha
  · refine ⟨b, ?_⟩
    simpa [rationalDot, integerEmbedding, r12, Fin.sum_univ_four,
      sub_eq_add_neg] using hb
  · refine ⟨c, ?_⟩
    simpa [rationalDot, integerEmbedding, r23, Fin.sum_univ_four,
      sub_eq_add_neg] using hc
  · refine ⟨d, ?_⟩
    simpa [rationalDot, integerEmbedding, r2p3, Fin.sum_univ_four] using hd

theorem dual_coordinate_numerators_same_parity (x : DualLattice) :
    ∃ n : Fin 4 → ℤ,
      (∀ i, x.1 i = (n i : ℚ) / 2) ∧
      (∀ i j, n i % 2 = n j % 2) := by
  obtain ⟨n0, h0⟩ := dual_coordinate_half_integral x 0
  obtain ⟨n1, h1⟩ := dual_coordinate_half_integral x 1
  obtain ⟨n2, h2⟩ := dual_coordinate_half_integral x 2
  obtain ⟨n3, h3⟩ := dual_coordinate_half_integral x 3
  obtain ⟨a, ha⟩ := (dual_simpleRoot_pairings_integral x).1
  obtain ⟨b, hb⟩ := (dual_simpleRoot_pairings_integral x).2.1
  obtain ⟨c, hc⟩ := (dual_simpleRoot_pairings_integral x).2.2.1
  obtain ⟨d, hd⟩ := (dual_simpleRoot_pairings_integral x).2.2.2
  have h01 : n0 - n1 = 2 * a := by
    have h := congrArg (fun z : ℚ => 2 * z) ha
    have hq : (n0 : ℚ) - n1 = 2 * a := by linarith [h, h0, h1]
    exact_mod_cast hq
  have h12 : n1 - n2 = 2 * b := by
    have h := congrArg (fun z : ℚ => 2 * z) hb
    have hq : (n1 : ℚ) - n2 = 2 * b := by linarith [h, h1, h2]
    exact_mod_cast hq
  have h23 : n2 - n3 = 2 * c := by
    have h := congrArg (fun z : ℚ => 2 * z) hc
    have hq : (n2 : ℚ) - n3 = 2 * c := by linarith [h, h2, h3]
    exact_mod_cast hq
  have h23' : n2 + n3 = 2 * d := by
    have h := congrArg (fun z : ℚ => 2 * z) hd
    have hq : (n2 : ℚ) + n3 = 2 * d := by linarith [h, h2, h3]
    exact_mod_cast hq
  let n : Fin 4 → ℤ := ![n0, n1, n2, n3]
  refine ⟨n, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [n] <;> omega

theorem dual_coordinate_numerators_parity_cases (x : DualLattice) :
    ∃ n : Fin 4 → ℤ,
      (∀ i, x.1 i = (n i : ℚ) / 2) ∧
      ((∀ i, n i % 2 = 0) ∨ (∀ i, n i % 2 = 1)) := by
  obtain ⟨n, hn, hpar⟩ := dual_coordinate_numerators_same_parity x
  have hcases : n 0 % 2 = 0 ∨ n 0 % 2 = 1 := by omega
  refine ⟨n, hn, ?_⟩
  rcases hcases with h0 | h0
  · left
    intro i
    have hi := hpar i 0
    omega
  · right
    intro i
    have hi := hpar i 0
    omega

theorem dual_integer_or_half_integer_normal_form (x : DualLattice) :
    (∃ y : Ambient, ∀ i, x.1 i = (y i : ℚ)) ∨
    (∃ y : Ambient, ∀ i, x.1 i = (1 / 2 : ℚ) + (y i : ℚ)) := by
  obtain ⟨n, hn, hcases⟩ := dual_coordinate_numerators_parity_cases x
  rcases hcases with heven | hodd
  · left
    let y : Ambient := fun i => n i / 2
    refine ⟨y, ?_⟩
    intro i
    have hi : n i = 2 * (n i / 2) := by
      have := heven i
      omega
    calc
      x.1 i = (n i : ℚ) / 2 := hn i
      _ = (y i : ℚ) := by
        change (n i : ℚ) / 2 = ((n i / 2 : ℤ) : ℚ)
        have hq : (n i : ℚ) = 2 * ((n i / 2 : ℤ) : ℚ) := by
          exact_mod_cast hi
        linarith
  · right
    let y : Ambient := fun i => (n i - 1) / 2
    refine ⟨y, ?_⟩
    intro i
    have hi : n i = 2 * ((n i - 1) / 2) + 1 := by
      have := hodd i
      omega
    calc
      x.1 i = (n i : ℚ) / 2 := hn i
      _ = (1 / 2 : ℚ) + (y i : ℚ) := by
        change (n i : ℚ) / 2 =
          (1 / 2 : ℚ) + (((n i - 1) / 2 : ℤ) : ℚ)
        have hq : (n i : ℚ) =
            2 * (((n i - 1) / 2 : ℤ) : ℚ) + 1 := by
          exact_mod_cast hi
        linarith

end InfoGeometry.RootSystem.D4
