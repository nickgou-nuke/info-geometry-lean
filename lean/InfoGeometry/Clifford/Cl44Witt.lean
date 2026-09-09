import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import InfoGeometry.Clifford.SplitQ44

namespace InfoGeometry.Clifford.Cl44Witt

open InfoGeometry.Clifford
open CliffordAlgebra

noncomputable def eVec : Fin 4 → Fin 8 → ℝ
  | 0 => Pi.single 0 1
  | 1 => Pi.single 1 1
  | 2 => Pi.single 2 1
  | 3 => Pi.single 3 1

noncomputable def fVec : Fin 4 → Fin 8 → ℝ
  | 0 => Pi.single 4 1
  | 1 => Pi.single 5 1
  | 2 => Pi.single 6 1
  | 3 => Pi.single 7 1

noncomputable def aVec (i : Fin 4) : Fin 8 → ℝ :=
  (1 / 2 : ℝ) • (eVec i + fVec i)

noncomputable def adagVec (i : Fin 4) : Fin 8 → ℝ :=
  (1 / 2 : ℝ) • (eVec i - fVec i)

/--
Positive Clifford generator.

-/
noncomputable def e (i : Fin 4) : Cl44 := by
  exact CliffordAlgebra.ι splitQ44 (eVec i)

/--
Negative Clifford generator.

-/
noncomputable def f (i : Fin 4) : Cl44 := by
  exact CliffordAlgebra.ι splitQ44 (fVec i)

/-- Split annihilation/null generator. -/
noncomputable def a (i : Fin 4) : Cl44 :=
  CliffordAlgebra.ι splitQ44 (aVec i)

/-- Split creation/null generator. -/
noncomputable def adag (i : Fin 4) : Cl44 :=
  CliffordAlgebra.ι splitQ44 (adagVec i)

private lemma eVec_sq (i : Fin 4) :
    splitQ44 (eVec i) = 1 := by
  fin_cases i <;>
    simp [eVec, splitQ44_apply]

private lemma fVec_sq (i : Fin 4) :
    splitQ44 (fVec i) = -(1 : ℝ) := by
  fin_cases i <;>
    simp [fVec, splitQ44_apply]

private lemma eVec_fVec_ortho (i j : Fin 4) :
    QuadraticMap.IsOrtho splitQ44 (eVec i) (fVec j) := by
  unfold QuadraticMap.IsOrtho
  fin_cases i <;> fin_cases j <;>
    simp [eVec, fVec, splitQ44_apply]

private lemma aVec_null (i : Fin 4) :
    splitQ44 (aVec i) = 0 := by
  fin_cases i <;>
    simp [aVec, eVec, fVec, splitQ44_apply]

private lemma adagVec_null (i : Fin 4) :
    splitQ44 (adagVec i) = 0 := by
  fin_cases i <;>
    simp [adagVec, eVec, fVec, splitQ44_apply]

private lemma aVec_adagVec_polar (i j : Fin 4) :
    QuadraticMap.polar splitQ44 (aVec i) (adagVec j) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [QuadraticMap.polar, aVec, adagVec, eVec, fVec, splitQ44_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne, Fin.ext_iff] <;> norm_num

private lemma aVec_aVec_polar (i j : Fin 4) :
    QuadraticMap.polar splitQ44 (aVec i) (aVec j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [QuadraticMap.polar, aVec, eVec, fVec, splitQ44_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne, Fin.ext_iff] <;> norm_num

private lemma adagVec_adagVec_polar (i j : Fin 4) :
    QuadraticMap.polar splitQ44 (adagVec i) (adagVec j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [QuadraticMap.polar, adagVec, eVec, fVec, splitQ44_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne, Fin.ext_iff] <;> norm_num

/-- Positive basis generator squares to `+1`. -/
theorem e_sq (i : Fin 4) :
    e i * e i = 1 := by
  rw [e, CliffordAlgebra.ι_sq_scalar, eVec_sq i]
  simp

/-- Negative basis generator squares to `-1`. -/
theorem f_sq (i : Fin 4) :
    f i * f i = -(1 : Cl44) := by
  rw [f, CliffordAlgebra.ι_sq_scalar, fVec_sq i]
  simp

/-- Positive/negative basis generators anticommute. -/
theorem e_mul_f_add_swap (i j : Fin 4) :
    e i * f j + f j * e i = 0 := by
  simpa [e, f] using
    (CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho
      (Q := splitQ44) (a := eVec i) (b := fVec j) (eVec_fVec_ortho i j))

/-- Nilpotency of split annihilation generators.
-/
theorem a_sq_zero (i : Fin 4) :
    a i * a i = 0 := by
  rw [a, CliffordAlgebra.ι_sq_scalar, aVec_null i]
  simp

/-- Nilpotency of split creation generators.
-/
theorem adag_sq_zero (i : Fin 4) :
    adag i * adag i = 0 := by
  rw [adag, CliffordAlgebra.ι_sq_scalar, adagVec_null i]
  simp

/-- CAR relation for the split Witt basis.
-/
theorem witt_CAR (i j : Fin 4) :
    a i * adag j + adag j * a i =
      if i = j then 1 else 0 := by
  simpa [a, adag, aVec_adagVec_polar i j] using
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := splitQ44) (aVec i) (adagVec j))

/-- Off-diagonal split CAR is zero. -/
theorem witt_CAR_ne (i j : Fin 4) (hij : i ≠ j) :
    a i * adag j + adag j * a i = 0 := by
  simp [witt_CAR, hij]

/-- Diagonal split CAR equals identity. -/
theorem witt_CAR_eq (i : Fin 4) :
    a i * adag i + adag i * a i = 1 := by
  simp [witt_CAR]

theorem witt_annihilation_anticomm (i j : Fin 4) :
    a i * a j + a j * a i = 0 := by
  simpa [a, aVec_aVec_polar i j] using
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := splitQ44) (aVec i) (aVec j))

theorem witt_creation_anticomm (i j : Fin 4) :
    adag i * adag j + adag j * adag i = 0 := by
  simpa [adag, adagVec_adagVec_polar i j] using
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := splitQ44) (adagVec i) (adagVec j))

end InfoGeometry.Clifford.Cl44Witt

/-! ## Split `Cl(1,1)` finite seed

The first Witt pair `(a 0, adag 0)` is the standard split-`(1,1)` CAR seed.
The three lemmas below package this explicitly for downstream finite-atom users.
-/

namespace InfoGeometry.Clifford.Cl44Witt

/-- Split annihilation generator for the finite `Cl(1,1)` seed. -/
noncomputable abbrev a11 : InfoGeometry.Clifford.Cl44 := a 0

/-- Split creation generator for the finite `Cl(1,1)` seed. -/
noncomputable abbrev adag11 : InfoGeometry.Clifford.Cl44 := adag 0

/-- Finite split `Cl(1,1)` nilpotency: `a11^2 = 0`. -/
theorem cl11_a_sq_zero : a11 * a11 = 0 := by
  simpa [a11] using (a_sq_zero (i := 0))

/-- Finite split `Cl(1,1)` nilpotency: `adag11^2 = 0`. -/
theorem cl11_adag_sq_zero : adag11 * adag11 = 0 := by
  simpa [adag11] using (adag_sq_zero (i := 0))

/-- Finite split `Cl(1,1)` CAR relation: `{a11, adag11} = 1`. -/
theorem cl11_witt_CAR_eq : a11 * adag11 + adag11 * a11 = 1 := by
  simpa [a11, adag11] using (witt_CAR_eq (i := 0))

end InfoGeometry.Clifford.Cl44Witt
