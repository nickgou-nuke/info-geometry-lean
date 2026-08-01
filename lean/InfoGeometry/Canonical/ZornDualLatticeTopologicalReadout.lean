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

end InfoGeometry.Canonical
