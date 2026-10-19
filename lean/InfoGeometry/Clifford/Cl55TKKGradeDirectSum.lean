/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import Mathlib.LinearAlgebra.Eigenspace.Basic
import InfoGeometry.Clifford.Cl55SuperTKK

/-!
# Directness of the concrete Cl(5,5) TKK eigenspace decomposition

The five subspaces are eigenspaces of the concrete adjoint grading operator.
Distinct-eigenvalue independence therefore upgrades the established spanning
decomposition to uniqueness of its five components.
-/

set_option maxRecDepth 10000

noncomputable section

namespace InfoGeometry.Clifford.Cl55SuperTKK

open scoped BigOperators

/-- The five grading labels, indexed in increasing order. -/
def tkkFiveGradeValue (i : Fin 5) : ℤ := (i.val : ℤ) - 2

/-- The corresponding family of concrete TKK eigenspaces. -/
def tkkFiveGradeSubmodule (i : Fin 5) : Submodule ℝ EndV :=
  Module.End.eigenspace (R := ℝ) (M := EndV) (f := tkkAdjointLinear)
    (μ := (tkkFiveGradeValue i : ℝ))

private theorem tkkFiveGradeValue_real_injective :
    Function.Injective (fun i : Fin 5 => (tkkFiveGradeValue i : ℝ)) := by
  intro i j hij
  change (tkkFiveGradeValue i : ℝ) = (tkkFiveGradeValue j : ℝ) at hij
  have hint : tkkFiveGradeValue i = tkkFiveGradeValue j := by
    exact_mod_cast hij
  dsimp [tkkFiveGradeValue] at hint
  have hval : (i.val : ℤ) = (j.val : ℤ) := by omega
  have hval' : i.val = j.val := by exact_mod_cast hval
  exact Fin.ext hval'

private theorem tkkFiveGradeSubmodule_eq_grade (i : Fin 5) :
    tkkFiveGradeSubmodule i = tkkGrade (tkkFiveGradeValue i) := by
  ext X
  simp only [tkkFiveGradeSubmodule, tkkGrade, Module.End.mem_eigenspace_iff]
  rfl

private def tkkMatrixUnitWeight (p : Fin 32 × Fin 32) : ℤ :=
  coordinateWeightInt p.1 - coordinateWeightInt p.2

private theorem tkkAdjointLinear_matrixUnit (i j : Fin 32) :
    tkkAdjointLinear (matrixUnit i j) =
      (coordinateWeight i - coordinateWeight j) • matrixUnit i j := by
  change tkkAdjoint (matrixUnit i j) = _
  exact tkkAdjoint_matrixUnit i j

private theorem tkkAdjointLinear_basis (p : Fin 32 × Fin 32) :
    tkkAdjointLinear (tkkMatrixUnitBasis p) =
      (tkkMatrixUnitWeight p : ℝ) • tkkMatrixUnitBasis p := by
  rcases p with ⟨i, j⟩
  rw [tkkMatrixUnitBasis_apply, tkkAdjointLinear_matrixUnit,
    tkkMatrixUnitWeight]
  simp [coordinateWeight_eq_int, Int.cast_sub]

private def tkkMatrixUnitCoefficient (p : Fin 32 × Fin 32) :
    EndV →ₗ[ℝ] ℝ where
  toFun X := (tkkMatrixUnitBasis.repr X) p
  map_add' X Y := by simp
  map_smul' c X := by simp

private theorem tkkMatrixUnitBasis_apply_pair (p : Fin 32 × Fin 32) :
    tkkMatrixUnitBasis p = matrixUnit p.1 p.2 := by
  rcases p with ⟨i, j⟩
  exact tkkMatrixUnitBasis_apply i j

/-- The adjoint grading operator acts diagonally on each matrix-unit
coefficient of the owner basis. -/
private theorem tkkMatrixUnitCoefficient_adjoint
    (X : EndV) (p : Fin 32 × Fin 32) :
    tkkMatrixUnitCoefficient p (tkkAdjoint X) =
      (tkkMatrixUnitWeight p : ℝ) * tkkMatrixUnitCoefficient p X := by
  change (tkkMatrixUnitBasis.repr (tkkAdjointLinear X)) p = _
  have hdecomp :
      (∑ q, tkkMatrixUnitBasis.repr X q •
        tkkAdjointLinear (tkkMatrixUnitBasis q)) =
        tkkAdjointLinear X := by
    simpa only [map_sum, map_smul] using
      congrArg tkkAdjointLinear (tkkMatrixUnitBasis.sum_repr X)
  have hcoeff :
      (tkkMatrixUnitBasis.repr (tkkAdjointLinear X)) p =
        ∑ q, tkkMatrixUnitBasis.repr X q *
          (tkkMatrixUnitBasis.repr
            (tkkAdjointLinear (tkkMatrixUnitBasis q)) p) := by
    have h := congrArg (fun Y => (tkkMatrixUnitBasis.repr Y) p) hdecomp
    rw [map_sum] at h
    rw [Finset.sum_apply'] at h
    have hterms :
        (∑ q, (tkkMatrixUnitBasis.repr
          (tkkMatrixUnitBasis.repr X q •
            tkkAdjointLinear (tkkMatrixUnitBasis q))) p) =
        ∑ q, tkkMatrixUnitBasis.repr X q *
          (tkkMatrixUnitBasis.repr
            (tkkAdjointLinear (tkkMatrixUnitBasis q)) p) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hm := tkkMatrixUnitBasis.repr.map_smul
        (tkkMatrixUnitBasis.repr X q)
        (tkkAdjointLinear (tkkMatrixUnitBasis q))
      have hmp := congrArg (fun z : (Fin 32 × Fin 32 →₀ ℝ) => z p) hm
      simpa only [Finsupp.smul_apply, smul_eq_mul] using hmp
    rw [hterms] at h
    exact h.symm
  have hbasis (q : Fin 32 × Fin 32) :
      (tkkMatrixUnitBasis.repr
        (tkkAdjointLinear (tkkMatrixUnitBasis q)) p) =
        if q = p then (tkkMatrixUnitWeight p : ℝ) else 0 := by
    rw [tkkAdjointLinear_basis]
    rw [map_smul]
    rw [Finsupp.smul_apply, tkkMatrixUnitBasis.repr_self_apply q p]
    by_cases hqp : q = p
    · subst q
      simp [tkkMatrixUnitWeight]
    · simp [hqp]
  rw [hcoeff]
  simp_rw [hbasis]
  change (∑ q, tkkMatrixUnitBasis.repr X q *
    (if q = p then (tkkMatrixUnitWeight p : ℝ) else 0)) = _
  calc
    (∑ q, tkkMatrixUnitBasis.repr X q *
        (if q = p then (tkkMatrixUnitWeight p : ℝ) else 0)) =
        tkkMatrixUnitBasis.repr X p * (tkkMatrixUnitWeight p : ℝ) := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    _ = (tkkMatrixUnitWeight p : ℝ) * tkkMatrixUnitBasis.repr X p :=
      mul_comm _ _

/-- A grade-k element has zero matrix-unit coefficients at every other
adjoint weight. -/
private theorem tkkGrade_coefficient_eq_zero_of_weight_ne
    {k : ℤ} {X : EndV} (hX : X ∈ tkkGrade k)
    (p : Fin 32 × Fin 32) (hweight : tkkMatrixUnitWeight p ≠ k) :
    tkkMatrixUnitCoefficient p X = 0 := by
  have heigen : tkkAdjoint X = (k : ℝ) • X := hX
  have hcoeff := congrArg (tkkMatrixUnitCoefficient p) heigen
  rw [tkkMatrixUnitCoefficient_adjoint] at hcoeff
  rw [map_smul] at hcoeff
  have hscalar : (tkkMatrixUnitWeight p : ℝ) - (k : ℝ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hweight)
  have hmul : ((tkkMatrixUnitWeight p : ℝ) - (k : ℝ)) *
      tkkMatrixUnitCoefficient p X = 0 := by
    linear_combination hcoeff
  exact (mul_eq_zero.mp hmul).resolve_left hscalar

/-- Equal sums of five grade components have equal components. -/
theorem tkkFiveGrade_sum_injective
    (xNeg2 xNeg1 x0 x1 x2 yNeg2 yNeg1 y0 y1 y2 : EndV)
    (hxNeg2 : xNeg2 ∈ tkkGrade (-2))
    (hxNeg1 : xNeg1 ∈ tkkGrade (-1))
    (hx0 : x0 ∈ tkkGrade 0)
    (hx1 : x1 ∈ tkkGrade 1)
    (hx2 : x2 ∈ tkkGrade 2)
    (hyNeg2 : yNeg2 ∈ tkkGrade (-2))
    (hyNeg1 : yNeg1 ∈ tkkGrade (-1))
    (hy0 : y0 ∈ tkkGrade 0)
    (hy1 : y1 ∈ tkkGrade 1)
    (hy2 : y2 ∈ tkkGrade 2)
    (hsum : xNeg2 + xNeg1 + x0 + x1 + x2 =
      yNeg2 + yNeg1 + y0 + y1 + y2) :
    xNeg2 = yNeg2 ∧ xNeg1 = yNeg1 ∧ x0 = y0 ∧
      x1 = y1 ∧ x2 = y2 := by
  let xs : Fin 5 → EndV := ![xNeg2, xNeg1, x0, x1, x2]
  let ys : Fin 5 → EndV := ![yNeg2, yNeg1, y0, y1, y2]
  have hx : ∀ i, xs i ∈ tkkFiveGradeSubmodule i := by
    intro i
    fin_cases i
    · change xNeg2 ∈ tkkFiveGradeSubmodule 0
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hxNeg2
    · change xNeg1 ∈ tkkFiveGradeSubmodule 1
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hxNeg1
    · change x0 ∈ tkkFiveGradeSubmodule 2
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hx0
    · change x1 ∈ tkkFiveGradeSubmodule 3
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hx1
    · change x2 ∈ tkkFiveGradeSubmodule 4
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hx2
  have hy : ∀ i, ys i ∈ tkkFiveGradeSubmodule i := by
    intro i
    fin_cases i
    · change yNeg2 ∈ tkkFiveGradeSubmodule 0
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hyNeg2
    · change yNeg1 ∈ tkkFiveGradeSubmodule 1
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hyNeg1
    · change y0 ∈ tkkFiveGradeSubmodule 2
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hy0
    · change y1 ∈ tkkFiveGradeSubmodule 3
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hy1
    · change y2 ∈ tkkFiveGradeSubmodule 4
      rw [tkkFiveGradeSubmodule_eq_grade]
      simpa [tkkFiveGradeValue] using hy2
  have hxGrade (i : Fin 5) : xs i ∈ tkkGrade (tkkFiveGradeValue i) := by
    rw [← tkkFiveGradeSubmodule_eq_grade i]
    exact hx i
  have hyGrade (i : Fin 5) : ys i ∈ tkkGrade (tkkFiveGradeValue i) := by
    rw [← tkkFiveGradeSubmodule_eq_grade i]
    exact hy i
  have hsum' : (∑ i : Fin 5, xs i) = ∑ i : Fin 5, ys i := by
    simpa [xs, ys, Fin.sum_univ_succ, ← add_assoc] using hsum
  have hcoeffSum (p : Fin 32 × Fin 32) :
      (∑ i : Fin 5, tkkMatrixUnitCoefficient p (xs i)) =
      (∑ i : Fin 5, tkkMatrixUnitCoefficient p (ys i)) := by
    have h := congrArg (tkkMatrixUnitCoefficient p) hsum'
    simpa only [map_sum] using h
  have hparts (r : Fin 5) : ∀ p,
      tkkMatrixUnitCoefficient p (xs r) =
        tkkMatrixUnitCoefficient p (ys r) := by
    intro p
    by_cases hweight : tkkMatrixUnitWeight p = tkkFiveGradeValue r
    · have hleft : (∑ i : Fin 5, tkkMatrixUnitCoefficient p (xs i)) =
          tkkMatrixUnitCoefficient p (xs r) := by
        rw [Finset.sum_eq_single r]
        · intro i hi hir
          have hne : tkkMatrixUnitWeight p ≠ tkkFiveGradeValue i := by
            intro hEq
            apply hir
            apply tkkFiveGradeValue_real_injective
            change (tkkFiveGradeValue i : ℝ) = (tkkFiveGradeValue r : ℝ)
            exact_mod_cast hEq.symm.trans hweight
          exact tkkGrade_coefficient_eq_zero_of_weight_ne (hxGrade i) p hne
        · simp
      have hright : (∑ i : Fin 5, tkkMatrixUnitCoefficient p (ys i)) =
          tkkMatrixUnitCoefficient p (ys r) := by
        rw [Finset.sum_eq_single r]
        · intro i hi hir
          have hne : tkkMatrixUnitWeight p ≠ tkkFiveGradeValue i := by
            intro hEq
            apply hir
            apply tkkFiveGradeValue_real_injective
            change (tkkFiveGradeValue i : ℝ) = (tkkFiveGradeValue r : ℝ)
            exact_mod_cast hEq.symm.trans hweight
          exact tkkGrade_coefficient_eq_zero_of_weight_ne (hyGrade i) p hne
        · simp
      have h := hcoeffSum p
      rw [hleft, hright] at h
      exact h
    · have hxzero := tkkGrade_coefficient_eq_zero_of_weight_ne (hxGrade r) p hweight
      have hyzero := tkkGrade_coefficient_eq_zero_of_weight_ne (hyGrade r) p hweight
      rw [hxzero, hyzero]
  have hcomponent (r : Fin 5) : xs r = ys r := by
    apply tkkMatrixUnitBasis.repr.injective
    ext p
    exact hparts r p
  have h0 := hcomponent 0
  have h1 := hcomponent 1
  have h2 := hcomponent 2
  have h3 := hcomponent 3
  have h4 := hcomponent 4
  simpa [xs, ys] using And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 h4)))

/-- The existential five-grade decomposition of an endomorphism is unique. -/
theorem tkkFiveGrade_decomposition_unique
    (X : EndV)
    (xNeg2 xNeg1 x0 x1 x2 : EndV)
    (hxNeg2 : xNeg2 ∈ tkkGrade (-2))
    (hxNeg1 : xNeg1 ∈ tkkGrade (-1))
    (hx0 : x0 ∈ tkkGrade 0)
    (hx1 : x1 ∈ tkkGrade 1)
    (hx2 : x2 ∈ tkkGrade 2)
    (hX : X = xNeg2 + xNeg1 + x0 + x1 + x2)
    (yNeg2 yNeg1 y0 y1 y2 : EndV)
    (hyNeg2 : yNeg2 ∈ tkkGrade (-2))
    (hyNeg1 : yNeg1 ∈ tkkGrade (-1))
    (hy0 : y0 ∈ tkkGrade 0)
    (hy1 : y1 ∈ tkkGrade 1)
    (hy2 : y2 ∈ tkkGrade 2)
    (hY : X = yNeg2 + yNeg1 + y0 + y1 + y2) :
    xNeg2 = yNeg2 ∧ xNeg1 = yNeg1 ∧ x0 = y0 ∧
      x1 = y1 ∧ x2 = y2 := by
  apply tkkFiveGrade_sum_injective xNeg2 xNeg1 x0 x1 x2
    yNeg2 yNeg1 y0 y1 y2 hxNeg2 hxNeg1 hx0 hx1 hx2
    hyNeg2 hyNeg1 hy0 hy1 hy2
  exact hX.symm.trans hY

/-- The concrete TKK adjoint eigenspaces vanish at every integer grade outside
the five weights `-2, -1, 0, 1, 2`. This uses the transported matrix-unit
basis of the endomorphism algebra, whose row-minus-column weights all lie in
that interval. -/
theorem tkkGrade_eq_bot_of_outside_range {k : ℤ}
    (hk : k < -2 ∨ 2 < k) : tkkGrade k = ⊥ := by
  apply Submodule.ext
  intro X
  simp only [Submodule.mem_bot]
  constructor
  · intro hX
    apply tkkMatrixUnitBasis.repr.injective
    ext p
    rcases p with ⟨i, j⟩
    have hweight : tkkMatrixUnitWeight (i, j) ≠ k := by
      change coordinateWeightInt i - coordinateWeightInt j ≠ k
      rcases coordinateWeightInt_sub_range i j with h | h | h | h | h <;>
        rcases hk with hkLow | hkHigh <;> omega
    have hcoeff := tkkGrade_coefficient_eq_zero_of_weight_ne hX (i, j) hweight
    simpa [tkkMatrixUnitCoefficient] using hcoeff
  · intro hX
    simpa [hX]

/-- A bracket of homogeneous elements vanishes when its summed grade is
outside the concrete five-grade range. -/
theorem tkkBracket_eq_zero_of_grade_sum_outside
    {i j : ℤ} {X Y : EndV}
    (hX : X ∈ tkkGrade i) (hY : Y ∈ tkkGrade j)
    (hOut : i + j < -2 ∨ 2 < i + j) : tkkBracket X Y = 0 := by
  have hbracket : tkkBracket X Y ∈ tkkGrade (i + j) :=
    tkk_bracket_grade_add rfl hX hY
  rw [tkkGrade_eq_bot_of_outside_range hOut] at hbracket
  simpa only [Submodule.mem_bot] using hbracket

end InfoGeometry.Clifford.Cl55SuperTKK

end noncomputable section

set_option maxRecDepth 1000
