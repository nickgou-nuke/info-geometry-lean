/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl55ExteriorContractionGrading
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient homology of the five-mode Clifford contraction complex

This file packages the existing degreewise exactness theorem for the actual
five-mode exterior-algebra contraction into quotient homology.  The result is
conditional on a nonzero covector; it does not identify this Koszul complex
with a gravitational BRST quartet or assert a Hilbert-space completion.
-/

noncomputable section

namespace InfoGeometry.Quantum.BRSTKoszulCohomology

open InfoGeometry.Clifford.Cl55ExteriorContractionGrading

/-- Cycles in exterior degree `n + 1`, for the Clifford contraction. -/
def cycles (φ : Module.Dual ℝ V) (n : ℕ) : Submodule ℝ (⋀[ℝ]^(n + 1) V) :=
  LinearMap.ker (differentialComponent φ n)

/-- Boundaries in exterior degree `n + 1`, coming from degree `n + 2`. -/
def boundaries (φ : Module.Dual ℝ V) (n : ℕ) : Submodule ℝ (⋀[ℝ]^(n + 1) V) :=
  LinearMap.range (differentialComponent φ (n + 1))

instance cyclesAddCommGroup (φ : Module.Dual ℝ V) (n : ℕ) :
    AddCommGroup (cycles φ n) := inferInstance

instance cyclesModule (φ : Module.Dual ℝ V) (n : ℕ) :
    Module ℝ (cycles φ n) := inferInstance

/-- The degree-`n + 1` homology quotient of the five-mode Koszul complex. -/
def homology (φ : Module.Dual ℝ V) (n : ℕ) : Type :=
  cycles φ n ⧸ (boundaries φ n).comap (cycles φ n).subtype

/-- Degree-zero homology of the augmented contraction complex: the scalar
exterior degree modulo contractions from degree one. -/
def degreeZeroHomology (φ : Module.Dual ℝ V) : Type :=
  (⋀[ℝ]^0 V) ⧸ LinearMap.range (differentialComponent φ 0)

instance (φ : Module.Dual ℝ V) (n : ℕ) : AddCommGroup (homology φ n) :=
  Submodule.Quotient.addCommGroup _

instance (φ : Module.Dual ℝ V) (n : ℕ) : Module ℝ (homology φ n) :=
  Submodule.Quotient.module _

instance (φ : Module.Dual ℝ V) : AddCommGroup (degreeZeroHomology φ) :=
  Submodule.Quotient.addCommGroup _

instance (φ : Module.Dual ℝ V) : Module ℝ (degreeZeroHomology φ) :=
  Submodule.Quotient.module _

/-- The contraction complex's boundary submodule is contained in its cycle
submodule, by square-zero of Clifford contraction. -/
theorem boundaries_le_cycles (φ : Module.Dual ℝ V) (n : ℕ) :
    boundaries φ n ≤ cycles φ n := by
  change LinearMap.range (differentialComponent φ (n + 1)) ≤
    LinearMap.ker (differentialComponent φ n)
  rw [LinearMap.range_le_ker_iff]
  exact differentialComponent_comp_zero φ n

/-- A nonzero covector makes each positive-degree cycle a boundary.  This is
the quotient-level input, not merely the operator identity `d² = 0`. -/
theorem cycles_eq_boundaries (φ : Module.Dual ℝ V) (hφ : φ ≠ 0) (n : ℕ) :
    cycles φ n = boundaries φ n :=
  differentialComponent_exact_of_ne_zero φ hφ n

/-- Every homology class in positive exterior degree vanishes for the
five-mode Koszul contraction associated with a nonzero covector. -/
theorem homology_subsingleton (φ : Module.Dual ℝ V) (hφ : φ ≠ 0) (n : ℕ) :
    Subsingleton (homology φ n) := by
  change Subsingleton
    ((cycles φ n) ⧸ (boundaries φ n).comap (cycles φ n).subtype)
  rw [Submodule.Quotient.subsingleton_iff]
  apply le_antisymm
  · exact le_top
  · intro x hx
    change (x : ⋀[ℝ]^(n + 1) V) ∈ boundaries φ n
    rw [← cycles_eq_boundaries φ hφ n]
    exact x.2

/-- The degree-zero endpoint of the augmented five-mode Koszul complex is
also exact: a nonzero covector makes contraction from degree one onto degree
zero surjective. -/
theorem differentialComponent_zero_surjective
    (φ : Module.Dual ℝ V) (hφ : φ ≠ 0) :
    Function.Surjective (differentialComponent φ 0) := by
  have htop : LinearMap.range φ = ⊤ := Module.Dual.range_eq_top_of_ne_zero hφ
  have hone : 1 ∈ LinearMap.range φ := by rw [htop]; exact Submodule.mem_top
  obtain ⟨v, hv⟩ := hone
  have hunit : (⟨1, SetLike.GradedOne.one_mem⟩ : ⋀[ℝ]^0 V) ∈
      LinearMap.range (differentialComponent φ 0) := by
    refine ⟨wedgeComponent v 0 ⟨1, SetLike.GradedOne.one_mem⟩, ?_⟩
    apply Subtype.ext
    change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm ℝ V)) φ (ExteriorAlgebra.ι ℝ v * 1) = 1
    rw [mul_one, CliffordAlgebra.contractLeft_ι, hv]
    simp [Algebra.algebraMap_eq_smul_one]
  have hmapUnit : (1 : Spinor) ∈
      (LinearMap.range (differentialComponent φ 0)).map
        (⋀[ℝ]^0 V).subtype := by
    exact ⟨⟨1, SetLike.GradedOne.one_mem⟩, hunit, rfl⟩
  have hrange : LinearMap.range (differentialComponent φ 0) = ⊤ := by
    apply Submodule.eq_top_iff'.2
    intro x
    let image : Submodule ℝ Spinor :=
      Submodule.map (⋀[ℝ]^0 V).subtype
        (LinearMap.range (differentialComponent φ 0))
    have hspan :
        Submodule.span ℝ
          (Set.range (ExteriorAlgebra.ιMulti ℝ 0 : (Fin 0 → V) → Spinor)) ≤ image := by
      apply Submodule.span_le.2
      rintro y ⟨v, rfl⟩
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact hmapUnit
    have hxspan : (x : Spinor) ∈
        Submodule.span ℝ (Set.range (ExteriorAlgebra.ιMulti ℝ 0 : (Fin 0 → V) → Spinor)) := by
      rw [ExteriorAlgebra.ιMulti_span_fixedDegree (R := ℝ) (M := V) 0]
      exact x.property
    have hxmap : (x : Spinor) ∈ image := hspan hxspan
    obtain ⟨y, hy, hxy⟩ := hxmap
    have hval : y = x := Subtype.ext hxy
    rw [← hval]
    exact hy
  rw [← LinearMap.range_eq_top]
  exact hrange

/-- The augmented degree-zero homology quotient vanishes for every nonzero
covector. -/
theorem degreeZeroHomology_subsingleton
    (φ : Module.Dual ℝ V) (hφ : φ ≠ 0) :
    Subsingleton (degreeZeroHomology φ) := by
  change Subsingleton
    ((⋀[ℝ]^0 V) ⧸ LinearMap.range (differentialComponent φ 0))
  rw [Submodule.Quotient.subsingleton_iff]
  have hrange : LinearMap.range (differentialComponent φ 0) = ⊤ :=
    LinearMap.range_eq_top.mpr (differentialComponent_zero_surjective φ hφ)
  apply le_antisymm le_top
  rw [← hrange]

end InfoGeometry.Quantum.BRSTKoszulCohomology
