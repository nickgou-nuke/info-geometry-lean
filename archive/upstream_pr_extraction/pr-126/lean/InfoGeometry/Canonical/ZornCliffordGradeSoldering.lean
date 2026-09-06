import Mathlib.Tactic
import InfoGeometry.Quantum.CircularPauliCausalCone

noncomputable section

namespace InfoGeometry.Canonical.ZornCliffordGradeSoldering

open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.Quantum.CircularPauliCausalCone
open InfoGeometry.Quantum.PauliSoldering

abbrev ZornReal := ZornCell ℝ

/-- The real scalar grade in the `1+3+3+1` Hestenes decomposition. -/
def scalarGrade (X : ZornReal) : ℝ := (X.r + X.s) / 2

/-- The vector grade in the `1+3+3+1` Hestenes decomposition. -/
def vectorGrade (X : ZornReal) : Fin 3 → ℝ := ![X.x1, X.x2, X.x3]

/-- The bivector, equivalently axial-vector, grade. -/
def bivectorGrade (X : ZornReal) : Fin 3 → ℝ := ![X.y1, X.y2, X.y3]

/-- The pseudoscalar grade in the `1+3+3+1` Hestenes decomposition. -/
def pseudoscalarGrade (X : ZornReal) : ℝ := (X.r - X.s) / 2

theorem grades_reconstruct (X : ZornReal) :
    X.r = scalarGrade X + pseudoscalarGrade X ∧
    X.s = scalarGrade X - pseudoscalarGrade X ∧
    vectorGrade X = ![X.x1, X.x2, X.x3] ∧
    bivectorGrade X = ![X.y1, X.y2, X.y3] := by
  constructor
  · simp [scalarGrade, pseudoscalarGrade]
    ring
  constructor
  · simp [scalarGrade, pseudoscalarGrade]
    ring
  constructor <;> rfl

theorem grades_eq_iff (X Y : ZornReal) :
    (scalarGrade X = scalarGrade Y ∧
      vectorGrade X = vectorGrade Y ∧
      bivectorGrade X = bivectorGrade Y ∧
      pseudoscalarGrade X = pseudoscalarGrade Y) ↔ X = Y := by
  constructor
  · rintro ⟨hr, hx, hy, hp⟩
    cases X with
    | mk xr xs xx1 xx2 xx3 xy1 xy2 xy3 =>
      cases Y with
      | mk yr ys yx1 yx2 yx3 yy1 yy2 yy3 =>
        simp only [scalarGrade, vectorGrade, bivectorGrade, pseudoscalarGrade,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hr hx hy hp
        have hxr : xr = yr := by linarith
        have hxs : xs = ys := by linarith
        have hxx1 := congrFun hx 0
        have hxx2 := congrFun hx 1
        have hxx3 := congrFun hx 2
        have hxy1 := congrFun hy 0
        have hxy2 := congrFun hy 1
        have hxy3 := congrFun hy 2
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hxx1 hxx2 hxx3 hxy1 hxy2 hxy3
        cases hxr
        cases hxs
        cases hxx1
        cases hxx2
        cases hxx3
        cases hxy1
        cases hxy2
        cases hxy3
        rfl
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The real `1+3+3+1` Zorn carrier soldered into the Pauli operator algebra. -/
def hestenesSolder (X : ZornReal) : Mat2 :=
  ((X.r : ℂ) + Complex.I * X.s) • σ0 +
    pauliVector (fun k : Fin 3 =>
      (match k with
      | 0 => (X.x1 : ℂ) + Complex.I * X.y1
      | 1 => (X.x2 : ℂ) + Complex.I * X.y2
      | 2 => (X.x3 : ℂ) + Complex.I * X.y3))

@[simp] theorem scalarReadout_hestenesSolder (X : ZornReal) :
    scalarReadout (hestenesSolder X) = (X.r : ℂ) + Complex.I * X.s := by
  unfold hestenesSolder scalarReadout pauliVector
  simp [Matrix.add_apply, Matrix.smul_apply, σ0, Complex.I_sq]
  ring

@[simp] theorem vectorReadout_hestenesSolder (X : ZornReal) :
    vectorReadout (hestenesSolder X) = fun k : Fin 3 =>
      (match k with
      | 0 => (X.x1 : ℂ) + Complex.I * X.y1
      | 1 => (X.x2 : ℂ) + Complex.I * X.y2
      | 2 => (X.x3 : ℂ) + Complex.I * X.y3) := by
  unfold hestenesSolder vectorReadout pauliVector
  funext k
  fin_cases k <;>
    simp [Matrix.add_apply, Matrix.smul_apply, σ0, σ1, σ2, σ3,
      Complex.I_sq]
    <;> field_simp
    <;> ring

theorem hestenesSolder_injective : Function.Injective hestenesSolder := by
  intro X Y hXY
  have hs := congrArg scalarReadout hXY
  have hv := congrArg vectorReadout hXY
  rw [scalarReadout_hestenesSolder, scalarReadout_hestenesSolder] at hs
  rw [vectorReadout_hestenesSolder, vectorReadout_hestenesSolder] at hv
  rcases X with ⟨xr, xs, xx1, xx2, xx3, xy1, xy2, xy3⟩
  rcases Y with ⟨yr, ys, yx1, yx2, yx3, yy1, yy2, yy3⟩
  simp only at hs hv
  have hrs : xr = yr := by
    have h := congrArg Complex.re hs
    simpa using h
  have hss : xs = ys := by
    have h := congrArg Complex.im hs
    simpa using h
  have hvec :
      (fun k : Fin 3 =>
        (match k with
        | 0 => (xx1 : ℂ) + Complex.I * xy1
        | 1 => (xx2 : ℂ) + Complex.I * xy2
        | 2 => (xx3 : ℂ) + Complex.I * xy3)) =
      (fun k : Fin 3 =>
        (match k with
        | 0 => (yx1 : ℂ) + Complex.I * yy1
        | 1 => (yx2 : ℂ) + Complex.I * yy2
        | 2 => (yx3 : ℂ) + Complex.I * yy3)) := hv
  have h1 := congrFun hvec 0
  have h2 := congrFun hvec 1
  have h3 := congrFun hvec 2
  have hxx1 : xx1 = yx1 := by simpa using congrArg Complex.re h1
  have hxy1 : xy1 = yy1 := by simpa using congrArg Complex.im h1
  have hxx2 : xx2 = yx2 := by simpa using congrArg Complex.re h2
  have hxy2 : xy2 = yy2 := by simpa using congrArg Complex.im h2
  have hxx3 : xx3 = yx3 := by simpa using congrArg Complex.re h3
  have hxy3 : xy3 = yy3 := by simpa using congrArg Complex.im h3
  cases hrs
  cases hss
  cases hxx1
  cases hxx2
  cases hxx3
  cases hxy1
  cases hxy2
  cases hxy3
  rfl

theorem hestenesSolder_eq_iff (X Y : ZornReal) :
    hestenesSolder X = hestenesSolder Y ↔ X = Y := by
  constructor
  · intro h
    exact hestenesSolder_injective h
  · intro h
    simpa [h]

theorem scalar_pseudoscalar_from_scalarReadout (X : ZornReal) :
    scalarGrade X =
        (Complex.re (scalarReadout (hestenesSolder X)) +
          Complex.im (scalarReadout (hestenesSolder X))) / 2 ∧
      pseudoscalarGrade X =
        (Complex.re (scalarReadout (hestenesSolder X)) -
          Complex.im (scalarReadout (hestenesSolder X))) / 2 := by
  rw [scalarReadout_hestenesSolder]
  simp [scalarGrade, pseudoscalarGrade]

theorem vector_bivector_from_vectorReadout (X : ZornReal) :
    vectorGrade X = (fun k => Complex.re (vectorReadout (hestenesSolder X) k)) ∧
      bivectorGrade X = (fun k => Complex.im (vectorReadout (hestenesSolder X) k)) := by
  rw [vectorReadout_hestenesSolder]
  constructor
  · funext k
    fin_cases k <;> simp [vectorGrade]
  · funext k
    fin_cases k <;> simp [bivectorGrade]

end InfoGeometry.Canonical.ZornCliffordGradeSoldering

end noncomputable section
