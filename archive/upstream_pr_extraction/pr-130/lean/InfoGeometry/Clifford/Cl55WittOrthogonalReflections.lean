import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import InfoGeometry.Clifford.Clifford55

/-!
# Native orthogonal reflections for the `Cl(5,5)` Witt carrier

This owner deliberately stops at the native quadratic-space and Clifford
automorphism layers.  It does not claim that the chosen isometry is a member
of Mathlib's `pinGroup`: that predicate includes a convention-dependent
unitarity condition which is separate from orthogonality of the carrier.
-/

namespace InfoGeometry.Clifford.Clifford55

open BigOperators

def negativeReflection (i : Fin 5) (x : V55) : V55 :=
  (x.1, fun j => if j = i then -x.2 j else x.2 j)

private theorem negativeReflection_add (i : Fin 5) (x y : V55) :
    negativeReflection i (x + y) =
      negativeReflection i x + negativeReflection i y := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases h : j = i
    · simp [negativeReflection, h]
      ring
    · simp [negativeReflection, h]

private theorem negativeReflection_smul (i : Fin 5) (r : ℝ) (x : V55) :
    negativeReflection i (r • x) = r • negativeReflection i x := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases h : j = i <;> simp [negativeReflection, h]

noncomputable def negativeReflectionLinearEquiv (i : Fin 5) :
    V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofLinear
    { toFun := negativeReflection i
      map_add' := negativeReflection_add i
      map_smul' := negativeReflection_smul i }
    { toFun := negativeReflection i
      map_add' := negativeReflection_add i
      map_smul' := negativeReflection_smul i }
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · rfl
      · funext j
        by_cases h : j = i <;> simp [negativeReflection, h])
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · rfl
      · funext j
        by_cases h : j = i <;> simp [negativeReflection, h])

@[simp] theorem negativeReflectionLinearEquiv_apply (i : Fin 5) (x : V55) :
    negativeReflectionLinearEquiv i x = negativeReflection i x := rfl

theorem negativeReflection_preserves_Q55 (i : Fin 5) (x : V55) :
    Q55 (negativeReflection i x) = Q55 x := by
  classical
  simp only [Q55_apply, negativeReflection]
  apply congrArg id
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j = i
  · simp [h]
  · simp [h]

noncomputable def negativeReflectionIsometry (i : Fin 5) :
    Q55.IsometryEquiv Q55 where
  __ := negativeReflectionLinearEquiv i
  map_app' := negativeReflection_preserves_Q55 i

@[simp] theorem negativeReflectionIsometry_apply (i : Fin 5) (x : V55) :
    negativeReflectionIsometry i x = negativeReflection i x := rfl

noncomputable def negativeReflectionAlg (i : Fin 5) :
    Cl55 ≃ₐ[ℝ] Cl55 :=
  CliffordAlgebra.equivOfIsometry (negativeReflectionIsometry i)

theorem negativeReflectionAlg_apply_ι (i : Fin 5) (x : V55) :
    negativeReflectionAlg i (ι55 x) =
      ι55 (negativeReflection i x) := by
  simp [negativeReflectionAlg]

@[simp] theorem negativeReflection_apply_e_pos (i : Fin 5) :
    negativeReflection i (e_pos i) = e_pos i := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases h : j = i <;> simp [negativeReflection, e_pos, h]

@[simp] theorem negativeReflection_apply_f_neg (i : Fin 5) :
    negativeReflection i (f_neg i) = -f_neg i := by
  apply Prod.ext
  · simp [negativeReflection, f_neg]
  · funext j
    by_cases h : j = i <;> simp [negativeReflection, f_neg, h]

@[simp] theorem negativeReflectionAlg_apply_e_pos (i : Fin 5) :
    negativeReflectionAlg i (ι55 (e_pos i)) = ι55 (e_pos i) := by
  rw [negativeReflectionAlg_apply_ι, negativeReflection_apply_e_pos]

@[simp] theorem negativeReflectionAlg_apply_f_neg (i : Fin 5) :
    negativeReflectionAlg i (ι55 (f_neg i)) = -ι55 (f_neg i) := by
  rw [negativeReflectionAlg_apply_ι, negativeReflection_apply_f_neg]
  simp

theorem negativeReflection_involutive (i : Fin 5) (x : V55) :
    negativeReflection i (negativeReflection i x) = x := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases h : j = i <;> simp [negativeReflection, h]

theorem negativeReflection_commute (i j : Fin 5) (x : V55) :
    negativeReflection i (negativeReflection j x) =
      negativeReflection j (negativeReflection i x) := by
  by_cases hij : i = j
  · subst j
    rfl
  apply Prod.ext
  · rfl
  · funext k
    by_cases hki : k = i
    · subst k
      simp [negativeReflection, hij]
    · by_cases hkj : k = j
      · subst k
        simp [negativeReflection, Ne.symm hij]
      · simp [negativeReflection, hki, hkj]

theorem negativeReflectionIsometry_involutive (i : Fin 5) (x : V55) :
    negativeReflectionIsometry i (negativeReflectionIsometry i x) = x := by
  simpa only [negativeReflectionIsometry_apply] using
    negativeReflection_involutive i x

/-! The positive-norm coordinate reflection is kept at the quadratic-space
level even though the current native `pinGroup Q55` convention excludes its
Clifford vector. -/

def positiveReflection (i : Fin 5) (x : V55) : V55 :=
  (fun j => if j = i then -x.1 j else x.1 j, x.2)

private theorem positiveReflection_add (i : Fin 5) (x y : V55) :
    positiveReflection i (x + y) =
      positiveReflection i x + positiveReflection i y := by
  apply Prod.ext
  · funext j
    by_cases h : j = i
    · simp [positiveReflection, h]
      ring
    · simp [positiveReflection, h]
  · rfl

private theorem positiveReflection_smul (i : Fin 5) (r : ℝ) (x : V55) :
    positiveReflection i (r • x) = r • positiveReflection i x := by
  apply Prod.ext
  · funext j
    by_cases h : j = i <;> simp [positiveReflection, h]
  · rfl

noncomputable def positiveReflectionLinearEquiv (i : Fin 5) :
    V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofLinear
    { toFun := positiveReflection i
      map_add' := positiveReflection_add i
      map_smul' := positiveReflection_smul i }
    { toFun := positiveReflection i
      map_add' := positiveReflection_add i
      map_smul' := positiveReflection_smul i }
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · funext j
        by_cases h : j = i <;> simp [positiveReflection, h]
      · rfl)
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · funext j
        by_cases h : j = i <;> simp [positiveReflection, h]
      · rfl)

@[simp] theorem positiveReflectionLinearEquiv_apply (i : Fin 5) (x : V55) :
    positiveReflectionLinearEquiv i x = positiveReflection i x := rfl

theorem positiveReflection_preserves_Q55 (i : Fin 5) (x : V55) :
    Q55 (positiveReflection i x) = Q55 x := by
  classical
  simp only [Q55_apply, positiveReflection]
  apply congrArg id
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j = i
  · simp [h]
  · simp [h]

noncomputable def positiveReflectionIsometry (i : Fin 5) :
    Q55.IsometryEquiv Q55 where
  __ := positiveReflectionLinearEquiv i
  map_app' := positiveReflection_preserves_Q55 i

@[simp] theorem positiveReflectionIsometry_apply (i : Fin 5) (x : V55) :
    positiveReflectionIsometry i x = positiveReflection i x := rfl

noncomputable def positiveReflectionAlg (i : Fin 5) :
    Cl55 ≃ₐ[ℝ] Cl55 :=
  CliffordAlgebra.equivOfIsometry (positiveReflectionIsometry i)

theorem positiveReflectionAlg_apply_ι (i : Fin 5) (x : V55) :
    positiveReflectionAlg i (ι55 x) =
      ι55 (positiveReflection i x) := by
  simp [positiveReflectionAlg]

theorem positiveReflection_involutive (i : Fin 5) (x : V55) :
    positiveReflection i (positiveReflection i x) = x := by
  apply Prod.ext
  · funext j
    by_cases h : j = i <;> simp [positiveReflection, h]
  · rfl

theorem positiveReflectionIsometry_involutive (i : Fin 5) (x : V55) :
    positiveReflectionIsometry i (positiveReflectionIsometry i x) = x := by
  simpa only [positiveReflectionIsometry_apply] using
    positiveReflection_involutive i x

def globalSheetReflection (x : V55) : V55 :=
  (x.1, -x.2)

private theorem globalSheetReflection_add (x y : V55) :
    globalSheetReflection (x + y) =
      globalSheetReflection x + globalSheetReflection y := by
  apply Prod.ext
  · rfl
  · simp [globalSheetReflection]
    ring

private theorem globalSheetReflection_smul (r : ℝ) (x : V55) :
    globalSheetReflection (r • x) = r • globalSheetReflection x := by
  apply Prod.ext
  · rfl
  · simp [globalSheetReflection]

noncomputable def globalSheetReflectionLinearEquiv :
    V55 ≃ₗ[ℝ] V55 :=
  LinearEquiv.ofLinear
    { toFun := globalSheetReflection
      map_add' := globalSheetReflection_add
      map_smul' := globalSheetReflection_smul }
    { toFun := globalSheetReflection
      map_add' := globalSheetReflection_add
      map_smul' := globalSheetReflection_smul }
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> simp [globalSheetReflection])
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> simp [globalSheetReflection])

theorem globalSheetReflection_preserves_Q55 (x : V55) :
    Q55 (globalSheetReflection x) = Q55 x := by
  classical
  simp [Q55_apply, globalSheetReflection]

noncomputable def globalSheetReflectionIsometry :
    Q55.IsometryEquiv Q55 where
  __ := globalSheetReflectionLinearEquiv
  map_app' := globalSheetReflection_preserves_Q55

@[simp] theorem globalSheetReflectionIsometry_apply (x : V55) :
    globalSheetReflectionIsometry x = globalSheetReflection x := rfl

noncomputable def globalSheetReflectionAlg : Cl55 ≃ₐ[ℝ] Cl55 :=
  CliffordAlgebra.equivOfIsometry globalSheetReflectionIsometry

theorem globalSheetReflectionAlg_apply_ι (x : V55) :
    globalSheetReflectionAlg (ι55 x) = ι55 (globalSheetReflection x) := by
  simp [globalSheetReflectionAlg]

@[simp] theorem globalSheetReflection_apply_e_pos (i : Fin 5) :
    globalSheetReflection (e_pos i) = e_pos i := by
  apply Prod.ext
  · rfl
  · simp [globalSheetReflection, e_pos]

@[simp] theorem globalSheetReflection_apply_f_neg (i : Fin 5) :
    globalSheetReflection (f_neg i) = -f_neg i := by
  apply Prod.ext
  · simp [globalSheetReflection, f_neg]
  · simp [globalSheetReflection, f_neg]

theorem globalSheetReflection_involutive (x : V55) :
    globalSheetReflection (globalSheetReflection x) = x := by
  apply Prod.ext <;> simp [globalSheetReflection]

theorem globalSheetReflection_commute_negativeReflection
    (i : Fin 5) (x : V55) :
    globalSheetReflection (negativeReflection i x) =
      negativeReflection i (globalSheetReflection x) := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases h : j = i <;> simp [globalSheetReflection, negativeReflection, h]

theorem globalSheetReflectionIsometry_involutive (x : V55) :
    globalSheetReflectionIsometry (globalSheetReflectionIsometry x) = x := by
  simpa only [globalSheetReflectionIsometry_apply] using
    globalSheetReflection_involutive x

end InfoGeometry.Clifford.Clifford55
