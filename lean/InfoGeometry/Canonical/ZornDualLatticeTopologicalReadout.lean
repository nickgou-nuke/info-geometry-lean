import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.Rat
import InfoGeometry.Canonical.ZornVectorMatrixRationalTopCatReadout

/-!
# Topological readout for the rational Zorn dual lattice

The algebraic owner `ZornDualLattice` defines `dualLattice` as an
`AddSubgroup`.  This file only supplies the inherited subtype topology and
continuous evaluation maps.  It does not assert that the dual lattice is
closed, self-dual, unimodular, or an `E₈` lattice.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

abbrev ZornDualLatticePoint (L : AddSubgroup (ZornVectorMatrix ℚ)) :=
  {X : ZornVectorMatrix ℚ // X ∈ dualLattice L}

def zornDualLatticeInclusionTopCat
    (L : AddSubgroup (ZornVectorMatrix ℚ)) :
    TopCat.of (ZornDualLatticePoint L) ⟶
      TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem continuous_zornDualLattice_polar_left
    (Y : ZornVectorMatrix ℚ) :
    Continuous (fun X : ZornVectorMatrix ℚ => polar X Y) := by
  exact continuous_zornVectorMatrix_rational_polar.comp
    (continuous_id.prodMk continuous_const)

def zornDualLatticePolarTopCat
    (L : AddSubgroup (ZornVectorMatrix ℚ))
    (Y : ZornVectorMatrix ℚ) :
    TopCat.of (ZornDualLatticePoint L) ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun X => polar X.1 Y
      continuous_toFun :=
        (continuous_zornDualLattice_polar_left Y).comp continuous_subtype_val }

@[simp] theorem zornDualLatticePolarTopCat_apply
    (L : AddSubgroup (ZornVectorMatrix ℚ))
    (Y : ZornVectorMatrix ℚ)
    (X : ZornDualLatticePoint L) :
    zornDualLatticePolarTopCat L Y X = polar X.1 Y :=
  rfl

theorem zornDualLatticePolarTopCat_is_integer
    (L : AddSubgroup (ZornVectorMatrix ℚ))
    (Y : ZornVectorMatrix ℚ)
    (hY : Y ∈ L)
    (X : ZornDualLatticePoint L) :
    ∃ n : ℤ, zornDualLatticePolarTopCat L Y X = (n : ℚ) := by
  exact X.property Y hY

abbrev ZornIntegralLatticePoint :=
  {X : ZornVectorMatrix ℚ // X ∈ integralLattice}

def zornIntegralLatticeInclusionTopCat :
    TopCat.of ZornIntegralLatticePoint ⟶
      TopCat.of (ZornVectorMatrix ℚ) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def zornIntegralLatticePolarTopCat
    (Y : ZornVectorMatrix ℚ) :
    TopCat.of ZornIntegralLatticePoint ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun X => polar X.1 Y
      continuous_toFun :=
        (continuous_zornDualLattice_polar_left Y).comp continuous_subtype_val }

@[simp] theorem zornIntegralLatticePolarTopCat_apply
    (Y : ZornVectorMatrix ℚ)
    (X : ZornIntegralLatticePoint) :
    zornIntegralLatticePolarTopCat Y X = polar X.1 Y :=
  rfl

theorem zornIntegralLatticePolarTopCat_is_integer
    (Y : ZornVectorMatrix ℚ)
    (hY : Y ∈ integralLattice)
    (X : ZornIntegralLatticePoint) :
    ∃ n : ℤ, zornIntegralLatticePolarTopCat Y X = (n : ℚ) := by
  have h_integral := integralLattice_is_integral X.property Y hY
  simpa using h_integral

def zornIntegralLatticeTraceTopCat :
    TopCat.of ZornIntegralLatticePoint ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun X => ZornVectorMatrix.trace X.1
      continuous_toFun :=
        continuous_zornVectorMatrix_rational_trace.comp continuous_subtype_val }

def zornIntegralLatticeNormTopCat :
    TopCat.of ZornIntegralLatticePoint ⟶ TopCat.of ℚ :=
  TopCat.ofHom
    { toFun := fun X => ZornVectorMatrix.norm X.1
      continuous_toFun :=
        continuous_zornVectorMatrix_rational_norm.comp continuous_subtype_val }

@[simp] theorem zornIntegralLatticeTraceTopCat_apply
    (X : ZornIntegralLatticePoint) :
    zornIntegralLatticeTraceTopCat X = ZornVectorMatrix.trace X.1 :=
  rfl

@[simp] theorem zornIntegralLatticeNormTopCat_apply
    (X : ZornIntegralLatticePoint) :
    zornIntegralLatticeNormTopCat X = ZornVectorMatrix.norm X.1 :=
  rfl

theorem zornIntegralLatticeTraceTopCat_is_integer
    (X : ZornIntegralLatticePoint) :
    ∃ n : ℤ, zornIntegralLatticeTraceTopCat X = (n : ℚ) := by
  rcases X.property with ⟨_, ⟨n, hn⟩, _, _⟩
  exact ⟨n, by simpa using hn⟩

theorem zornIntegralLatticeNormTopCat_is_integer
    (X : ZornIntegralLatticePoint) :
    ∃ n : ℤ, zornIntegralLatticeNormTopCat X = (n : ℚ) := by
  rcases X.property with ⟨_, _, ⟨n, hn⟩, _⟩
  refine ⟨n, ?_⟩
  change ZornVectorMatrix.norm X.1 = (n : ℚ)
  simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using hn

theorem isClosed_zornDualLattice
    (L : AddSubgroup (ZornVectorMatrix ℚ)) :
    IsClosed (dualLattice L : Set (ZornVectorMatrix ℚ)) := by
  classical
  let S : ZornVectorMatrix ℚ → Set (ZornVectorMatrix ℚ) := fun Y =>
    if Y ∈ L then
      (fun X : ZornVectorMatrix ℚ => polar X Y) ⁻¹'
        Set.range ((↑) : ℤ → ℚ)
    else Set.univ
  have hS : ∀ Y, IsClosed (S Y) := by
    intro Y
    by_cases hY : Y ∈ L
    · simp [S, hY]
      exact Int.isClosedEmbedding_coe_rat.isClosed_range.preimage
        (continuous_zornDualLattice_polar_left Y)
    · simp [S, hY]
  have hEq : (dualLattice L : Set (ZornVectorMatrix ℚ)) = ⋂ Y, S Y := by
    ext X
    change (∀ Y ∈ L, ∃ n : ℤ, polar X Y = (n : ℚ)) ↔ X ∈ ⋂ Y, S Y
    simp only [Set.mem_iInter]
    constructor
    · intro h Y
      by_cases hY : Y ∈ L
      · simp only [S, if_pos hY, Set.mem_preimage, Set.mem_range]
        rcases h Y hY with ⟨n, hn⟩
        exact ⟨n, hn.symm⟩
      · simp [S, hY]
    · intro h Y hY
      have hY' := h Y
      simp only [S, if_pos hY, Set.mem_preimage, Set.mem_range] at hY'
      rcases hY' with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
  rw [hEq]
  exact isClosed_iInter hS

theorem isClosedEmbedding_zornDualLattice
    (L : AddSubgroup (ZornVectorMatrix ℚ)) :
    Topology.IsClosedEmbedding
      (Subtype.val : ZornDualLatticePoint L → ZornVectorMatrix ℚ) :=
  (isClosed_zornDualLattice L).isClosedEmbedding_subtypeVal

def rationalHalfIntegerSet : Set ℚ :=
  (fun q : ℚ => 2 * q) ⁻¹' Set.range ((↑) : ℤ → ℚ)

theorem isClosed_rationalHalfIntegerSet :
    IsClosed rationalHalfIntegerSet := by
  exact Int.isClosedEmbedding_coe_rat.isClosed_range.preimage
    (continuous_const.mul continuous_id)

theorem rationalHalfIntegerSet_mem_iff (q : ℚ) :
    q ∈ rationalHalfIntegerSet ↔
      ∃ n : ℤ, q = (n : ℚ) / 2 := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (n : ℚ) = 2 * q at hn
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (n : ℚ) = 2 * q
    rw [hn]
    ring

def rationalHalfIntegerZornSet : Set (ZornVectorMatrix ℚ) :=
  {X | X.a ∈ rationalHalfIntegerSet ∧
    X.b ∈ rationalHalfIntegerSet ∧
    (∀ i, X.v i ∈ rationalHalfIntegerSet) ∧
    ∀ i, X.w i ∈ rationalHalfIntegerSet}

theorem isClosed_rationalHalfIntegerZornSet :
    IsClosed rationalHalfIntegerZornSet := by
  have ha : IsClosed {X : ZornVectorMatrix ℚ |
      X.a ∈ rationalHalfIntegerSet} :=
    isClosed_rationalHalfIntegerSet.preimage
      continuous_zornVectorMatrix_rational_a
  have hb : IsClosed {X : ZornVectorMatrix ℚ |
      X.b ∈ rationalHalfIntegerSet} :=
    isClosed_rationalHalfIntegerSet.preimage
      continuous_zornVectorMatrix_rational_b
  have hv : IsClosed {X : ZornVectorMatrix ℚ |
      ∀ i, X.v i ∈ rationalHalfIntegerSet} := by
    rw [show {X : ZornVectorMatrix ℚ |
        ∀ i, X.v i ∈ rationalHalfIntegerSet} =
        ⋂ i, (fun X : ZornVectorMatrix ℚ => X.v i) ⁻¹'
          rationalHalfIntegerSet by
      ext X
      simp]
    exact isClosed_iInter fun i =>
      isClosed_rationalHalfIntegerSet.preimage
        (continuous_zornVectorMatrix_rational_v i)
  have hw : IsClosed {X : ZornVectorMatrix ℚ |
      ∀ i, X.w i ∈ rationalHalfIntegerSet} := by
    rw [show {X : ZornVectorMatrix ℚ |
        ∀ i, X.w i ∈ rationalHalfIntegerSet} =
        ⋂ i, (fun X : ZornVectorMatrix ℚ => X.w i) ⁻¹'
          rationalHalfIntegerSet by
      ext X
      simp]
    exact isClosed_iInter fun i =>
      isClosed_rationalHalfIntegerSet.preimage
        (continuous_zornVectorMatrix_rational_w i)
  exact ha.inter (hb.inter (hv.inter hw))

theorem isMaximalSplitOrder_half_mem_iff (X : ZornVectorMatrix ℚ) :
    (∃ (za zb : ℤ) (zv zw : Fin 3 → ℤ),
      X.a = (za : ℚ) / 2 ∧ X.b = (zb : ℚ) / 2 ∧
      (∀ i, X.v i = (zv i : ℚ) / 2) ∧
      (∀ i, X.w i = (zw i : ℚ) / 2)) ↔
      X ∈ rationalHalfIntegerZornSet := by
  classical
  constructor
  · rintro ⟨za, zb, zv, zw, ha, hb, hv, hw⟩
    refine ⟨(rationalHalfIntegerSet_mem_iff _).2 ⟨za, ha⟩,
      (rationalHalfIntegerSet_mem_iff _).2 ⟨zb, hb⟩, ?_, ?_⟩
    · intro i
      exact (rationalHalfIntegerSet_mem_iff _).2 ⟨zv i, hv i⟩
    · intro i
      exact (rationalHalfIntegerSet_mem_iff _).2 ⟨zw i, hw i⟩
  · intro h
    have ha := (rationalHalfIntegerSet_mem_iff X.a).1 h.1
    have hb := (rationalHalfIntegerSet_mem_iff X.b).1 h.2.1
    choose zv hv using fun i => (rationalHalfIntegerSet_mem_iff (X.v i)).1 (h.2.2.1 i)
    choose zw hw using fun i => (rationalHalfIntegerSet_mem_iff (X.w i)).1 (h.2.2.2 i)
    exact ⟨ha.choose, hb.choose, zv, zw, ha.choose_spec, hb.choose_spec, hv, hw⟩

def rationalIntegerSet : Set ℚ := Set.range ((↑) : ℤ → ℚ)

theorem isClosed_rationalIntegerSet : IsClosed rationalIntegerSet :=
  Int.isClosedEmbedding_coe_rat.isClosed_range

def rationalIntegralZornBaseSet : Set (ZornVectorMatrix ℚ) :=
  rationalHalfIntegerZornSet ∩
    ({X | ZornVectorMatrix.trace X ∈ rationalIntegerSet} ∩
      {X | ZornVectorMatrix.norm X ∈ rationalIntegerSet})

theorem isClosed_rationalIntegralZornBaseSet :
    IsClosed rationalIntegralZornBaseSet := by
  have htrace : IsClosed {X : ZornVectorMatrix ℚ |
      ZornVectorMatrix.trace X ∈ rationalIntegerSet} :=
    isClosed_rationalIntegerSet.preimage
      continuous_zornVectorMatrix_rational_trace
  have hnorm : IsClosed {X : ZornVectorMatrix ℚ |
      ZornVectorMatrix.norm X ∈ rationalIntegerSet} :=
    isClosed_rationalIntegerSet.preimage
      continuous_zornVectorMatrix_rational_norm
  exact isClosed_rationalHalfIntegerZornSet.inter (htrace.inter hnorm)

def rationalIntegralZornBilinearSet : Set (ZornVectorMatrix ℚ) :=
  {X | ∀ Y, Y ∈ rationalIntegralZornBaseSet →
    polar X Y ∈ rationalIntegerSet}

theorem isClosed_rationalIntegralZornBilinearSet :
    IsClosed rationalIntegralZornBilinearSet := by
  classical
  let S : ZornVectorMatrix ℚ → Set (ZornVectorMatrix ℚ) := fun Y =>
    if Y ∈ rationalIntegralZornBaseSet then
      (fun X : ZornVectorMatrix ℚ => polar X Y) ⁻¹' rationalIntegerSet
    else Set.univ
  have hS : ∀ Y, IsClosed (S Y) := by
    intro Y
    by_cases hY : Y ∈ rationalIntegralZornBaseSet
    · simp [S, hY]
      exact isClosed_rationalIntegerSet.preimage
        (continuous_zornDualLattice_polar_left Y)
    · simp [S, hY]
  have hEq : rationalIntegralZornBilinearSet = ⋂ Y, S Y := by
    ext X
    change (∀ Y, Y ∈ rationalIntegralZornBaseSet →
      polar X Y ∈ rationalIntegerSet) ↔ X ∈ ⋂ Y, S Y
    simp only [Set.mem_iInter]
    constructor
    · intro h Y
      by_cases hY : Y ∈ rationalIntegralZornBaseSet
      · simp only [S, if_pos hY, Set.mem_preimage]
        exact h Y hY
      · simp [S, hY]
    · intro h Y hY
      have hY' := h Y
      simp only [S, if_pos hY, Set.mem_preimage] at hY'
      exact hY'
  rw [hEq]
  exact isClosed_iInter hS

theorem isMaximalSplitOrder_mem_iff_integralZorn
    (X : ZornVectorMatrix ℚ) :
    isMaximalSplitOrder X ↔
      X ∈ rationalIntegralZornBaseSet ∩ rationalIntegralZornBilinearSet := by
  constructor
  · rintro ⟨hhalf, ⟨t, ht⟩, ⟨n, hn⟩, hbilin⟩
    refine ⟨?_, ?_⟩
    · refine ⟨(isMaximalSplitOrder_half_mem_iff X).1 hhalf, ?_⟩
      refine ⟨⟨t, ht.symm⟩, ?_⟩
      exact ⟨n, by
        simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using hn.symm⟩
    · intro Y hY
      have hYhalf :
          (∃ (ya yb : ℤ) (yv yw : Fin 3 → ℤ),
            Y.a = (ya : ℚ) / 2 ∧ Y.b = (yb : ℚ) / 2 ∧
            (∀ i, Y.v i = (yv i : ℚ) / 2) ∧
            (∀ i, Y.w i = (yw i : ℚ) / 2)) :=
        (isMaximalSplitOrder_half_mem_iff Y).2 hY.1
      rcases hY.2.1 with ⟨ty, hty⟩
      have hYtrace : ∃ ty : ℤ, Y.a + Y.b = (ty : ℚ) :=
        ⟨ty, hty.symm⟩
      rcases hY.2.2 with ⟨ny, hny⟩
      have hYnorm : ∃ ny : ℤ,
          Y.a * Y.b - (Y.v 0 * Y.w 0 + Y.v 1 * Y.w 1 + Y.v 2 * Y.w 2) =
            (ny : ℚ) :=
        ⟨ny, by
          simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using hny.symm⟩
      rcases hbilin Y hYhalf hYtrace hYnorm with ⟨m, hm⟩
      exact ⟨m, by simpa [polar, mul_comm] using hm.symm⟩
  · rintro ⟨hbase, hbilin⟩
    refine ⟨(isMaximalSplitOrder_half_mem_iff X).2 hbase.1, ?_, ?_, ?_⟩
    · rcases hbase.2.1 with ⟨t, ht⟩
      exact ⟨t, ht.symm⟩
    · rcases hbase.2.2 with ⟨n, hn⟩
      exact ⟨n, by
        simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using hn.symm⟩
    · intro Y hYhalf hYtrace hYnorm
      have hYhalf' := (isMaximalSplitOrder_half_mem_iff Y).1 hYhalf
      rcases hYtrace with ⟨ty, hty⟩
      have hYtrace' : Y ∈ {X | ZornVectorMatrix.trace X ∈ rationalIntegerSet} :=
        ⟨ty, hty.symm⟩
      rcases hYnorm with ⟨ny, hny⟩
      have hYnorm' : Y ∈ {X | ZornVectorMatrix.norm X ∈ rationalIntegerSet} :=
        ⟨ny, by
          simpa [ZornVectorMatrix.norm, ZornVec3.dot_eq_sum_coords] using hny.symm⟩
      rcases hbilin Y ⟨hYhalf', hYtrace', hYnorm'⟩ with ⟨m, hm⟩
      exact ⟨m, by simpa [polar, mul_comm] using hm.symm⟩

theorem isClosed_integralLattice :
    IsClosed (integralLattice : Set (ZornVectorMatrix ℚ)) := by
  have hEq : (integralLattice : Set (ZornVectorMatrix ℚ)) =
      rationalIntegralZornBaseSet ∩ rationalIntegralZornBilinearSet := by
    ext X
    exact isMaximalSplitOrder_mem_iff_integralZorn X
  rw [hEq]
  exact isClosed_rationalIntegralZornBaseSet.inter
    isClosed_rationalIntegralZornBilinearSet

end InfoGeometry.Canonical
