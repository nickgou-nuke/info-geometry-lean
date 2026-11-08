import InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzModularAutomorphism
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.OperatorAlgebra.GradeActionInterface
import InfoGeometry.OperatorAlgebra.FiveGradeActionPreservation

/-! Integer weights in the Cuntz matrix-unit lane agree with the native
real-valued `HasOperatorGrade` predicate after scalar coercion. -/

namespace InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Algebra.CuntzModularAutomorphism

theorem isGradedComponent_int_iff_hasOperatorGrade
    (k : ℤ) (x : Cuntz3) :
    IsGradedComponent gradingOp (k : ℂ) x ↔
      HasOperatorGrade gradingOp x k := by
  change commutator gradingOp x = (k : ℂ) • x ↔
    commutator gradingOp x = (k : ℝ) • x
  rw [Algebra.smul_def, Algebra.smul_def]
  norm_cast

theorem hop_mem_hasOperatorGrade (i j : Fin 3) :
    HasOperatorGrade gradingOp (hop i j)
      (colourWeight i - colourWeight j) := by
  exact (isGradedComponent_int_iff_hasOperatorGrade
    (colourWeight i - colourWeight j) (hop i j)).mp (hop_mem_grade i j)

theorem commutator_mem_hasOperatorGrade_add
    {k l : ℤ} {x y : Cuntz3}
    (hx : HasOperatorGrade gradingOp x k)
    (hy : HasOperatorGrade gradingOp y l) :
    HasOperatorGrade gradingOp (commutator x y) (k + l) := by
  apply (isGradedComponent_int_iff_hasOperatorGrade (k + l)
    (commutator x y)).mp
  simpa only [Int.cast_add] using
    (commutator_mem_grade_add
      (p := (k : ℂ)) (q := (l : ℂ))
      ((isGradedComponent_int_iff_hasOperatorGrade k x).mpr hx)
      ((isGradedComponent_int_iff_hasOperatorGrade l y).mpr hy))

theorem gradingOp_mem_hasOperatorGrade_zero :
    HasOperatorGrade gradingOp gradingOp 0 := by
  apply (isGradedComponent_int_iff_hasOperatorGrade 0 gradingOp).mp
  unfold IsGradedComponent
  simp [commutator]

theorem sigmaEquiv_fixes_gradingOp (primes : Fin 3 → ℕ) (t : ℝ) :
    sigmaEquiv 3 primes t gradingOp = gradingOp := by
  unfold gradingOp hop InfoGeometry.Algebra.CuntzMatrixUnits.E
  rw [sub_eq_add_neg, map_add, map_neg]
  rw [sigmaEquiv_fixes_projector, sigmaEquiv_fixes_projector]

theorem sigmaEquiv_preserves_isGradedComponent
    (primes : Fin 3 → ℕ) (t : ℝ) {p : ℂ} {x : Cuntz3}
    (hx : IsGradedComponent gradingOp p x) :
    IsGradedComponent gradingOp p (sigmaEquiv 3 primes t x) := by
  unfold IsGradedComponent at hx ⊢
  have h := congrArg (sigmaEquiv 3 primes t) hx
  change (sigmaEquiv 3 primes t) (gradingOp * x - x * gradingOp) =
      (sigmaEquiv 3 primes t) (p • x) at h
  rw [map_sub, map_mul, map_mul, map_smul] at h
  rw [sigmaEquiv_fixes_gradingOp] at h
  exact h

theorem sigmaEquiv_preserves_hasOperatorGrade
    (primes : Fin 3 → ℕ) (t : ℝ) {k : ℤ} {x : Cuntz3}
    (hx : HasOperatorGrade gradingOp x k) :
    HasOperatorGrade gradingOp (sigmaEquiv 3 primes t x) k := by
  apply (isGradedComponent_int_iff_hasOperatorGrade k _).mp
  apply sigmaEquiv_preserves_isGradedComponent primes t
  exact (isGradedComponent_int_iff_hasOperatorGrade k x).mpr hx

theorem sigmaEquiv_maps_operatorGrade_family
    (primes : Fin 3 → ℕ) (t : ℝ) :
    MapsToGrade
      (fun k : ℤ => {x : Cuntz3 | HasOperatorGrade gradingOp x k})
      (fun _ : ℝ => sigmaEquiv 3 primes t)
      (fun _ k => k) := by
  intro _ k x hx
  exact sigmaEquiv_preserves_hasOperatorGrade primes t hx

theorem sigmaEquiv_maps_gradeSubmodule_family
    (primes : Fin 3 → ℕ) (t : ℝ) :
    MapsToGrade
      (fun k : ℤ => (gradeSubmodule gradingOp k : Set Cuntz3))
      (fun _ : ℝ => sigmaEquiv 3 primes t)
      (fun _ k => k) := by
  intro _ k x hx
  change HasOperatorGrade gradingOp x k at hx
  change HasOperatorGrade gradingOp (sigmaEquiv 3 primes t x) k
  exact sigmaEquiv_preserves_hasOperatorGrade primes t hx

noncomputable def sigmaEquivReal (primes : Fin 3 → ℕ) (t : ℝ) :
    Cuntz3 ≃ₐ[ℝ] Cuntz3 :=
  (sigmaEquiv 3 primes t).restrictScalars ℝ

@[simp] theorem sigmaEquivReal_apply
    (primes : Fin 3 → ℕ) (t : ℝ) (x : Cuntz3) :
    sigmaEquivReal primes t x = sigmaEquiv 3 primes t x :=
  rfl

theorem sigmaEquivReal_symm (primes : Fin 3 → ℕ) (t : ℝ) :
    (sigmaEquivReal primes t).symm = sigmaEquivReal primes (-t) := by
  apply AlgEquiv.ext
  intro x
  apply (sigmaEquivReal primes t).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := sigmaEquiv_add_apply 3 primes t (-t) x
  simpa [sigmaEquivReal_apply] using h

theorem sigmaEquivReal_fixes_gradingOp
    (primes : Fin 3 → ℕ) (t : ℝ) :
    sigmaEquivReal primes t gradingOp = gradingOp := by
  exact sigmaEquiv_fixes_gradingOp primes t

theorem sigmaEquivReal_maps_gradeSubmodule_family
    (primes : Fin 3 → ℕ) (t : ℝ) :
    MapsToGrade
      (fun k : ℤ => (gradeSubmodule gradingOp k : Set Cuntz3))
      (fun _ : Unit => sigmaEquivReal primes t)
      (fun _ k => k) := by
  have h := algEquiv_mapsToGradeSubmoduleBetween
    (sigmaEquivReal primes t) gradingOp
  rw [sigmaEquivReal_fixes_gradingOp primes t] at h
  exact h

theorem sigmaEquivReal_preserves_gradeSubmodule
    (primes : Fin 3 → ℕ) (t : ℝ) :
    PreservesGrade
      (fun k : ℤ => (gradeSubmodule gradingOp k : Set Cuntz3))
      (fun _ : Unit => fun x => sigmaEquivReal primes t x) := by
  exact algEquiv_preserves_gradeSubmodule
    (sigmaEquivReal primes t) gradingOp
    (sigmaEquivReal_fixes_gradingOp primes t)

theorem sigmaEquivReal_gradeSubmodule_map
    (primes : Fin 3 → ℕ) (t : ℝ) (k : ℤ) :
    Submodule.map (sigmaEquivReal primes t).toLinearMap
        (gradeSubmodule gradingOp k) = gradeSubmodule gradingOp k := by
    exact algEquiv_map_gradeSubmodule
      (sigmaEquivReal primes t) gradingOp k
      (sigmaEquivReal_fixes_gradingOp primes t)

theorem sigmaEquivReal_gradeSubmodule_image_eq
    (primes : Fin 3 → ℕ) (t : ℝ) (k : ℤ) :
    sigmaEquivReal primes t ''
        (gradeSubmodule gradingOp k : Set Cuntz3) =
      (gradeSubmodule gradingOp k : Set Cuntz3) := by
  apply linearEquiv_preservesGrade_image_eq
    (sigmaEquivReal primes t).toLinearEquiv
    (fun k : ℤ => (gradeSubmodule gradingOp k : Set Cuntz3))
  · exact sigmaEquivReal_preserves_gradeSubmodule primes t
  · simpa [sigmaEquivReal_symm primes t] using
      sigmaEquivReal_preserves_gradeSubmodule primes (-t)

end InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge
