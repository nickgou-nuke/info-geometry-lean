import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# A concrete Newman--Penrose null tetrad

This file formalizes the finite algebraic substrate of the Newman--Penrose
notation.  It uses the complexification of a four-dimensional vector space,
the bilinear Lorentz form of signature `(-,+,+,+)`, and one normalized null
tetrad.  No connection, curvature tensor, or field equation is introduced.
-/

namespace InfoGeometry.Geometry.NewmanPenrose

noncomputable section

abbrev Carrier := Fin 4 → ℂ

def lorentzBilinear (x y : Carrier) : ℂ :=
  2 * (-(x 0) * (y 0) + (x 1) * (y 1) + (x 2) * (y 2) + (x 3) * (y 3))

noncomputable def lorentzBilinearForm : LinearMap.BilinForm ℂ Carrier :=
  LinearMap.mk₂ ℂ (fun x y => lorentzBilinear x y)
    (by intro x₁ x₂ y; simp [lorentzBilinear, Pi.add_apply]; ring)
    (by intro a x y; simp [lorentzBilinear, Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y₁ y₂; simp [lorentzBilinear, Pi.add_apply]; ring)
    (by intro a x y; simp [lorentzBilinear, Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem lorentzBilinearForm_apply (x y : Carrier) :
    lorentzBilinearForm x y = lorentzBilinear x y := rfl

theorem lorentzBilinearForm_isSymm : lorentzBilinearForm.IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [lorentzBilinearForm_apply, lorentzBilinearForm_apply]
  simp [lorentzBilinear]
  ring

def ell : Carrier := ![1, 0, 0, 1]

def n : Carrier := ![(1 / 4 : ℂ), 0, 0, -(1 / 4 : ℂ)]

def m : Carrier := ![0, (1 / 2 : ℂ), Complex.I / 2, 0]

def mbar : Carrier := ![0, (1 / 2 : ℂ), -(Complex.I / 2), 0]

theorem complex_I_half_mul :
    Complex.I / 2 * (Complex.I / 2) = -(1 / 4 : ℂ) := by
  calc
    Complex.I / 2 * (Complex.I / 2) =
        (Complex.I * Complex.I) / 4 := by ring
    _ = -(1 / 4 : ℂ) := by rw [Complex.I_mul_I]; ring

theorem complex_I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  rw [pow_two, Complex.I_mul_I]

theorem lorentzBilinear_self_ell :
    lorentzBilinear ell ell = 0 := by
  simp [lorentzBilinear, ell]

theorem lorentzBilinear_self_n :
    lorentzBilinear n n = 0 := by
  simp [lorentzBilinear, n]

theorem lorentzBilinear_self_m :
    lorentzBilinear m m = 0 := by
  simp [lorentzBilinear, m, complex_I_half_mul]
  norm_num

theorem lorentzBilinear_self_mbar :
    lorentzBilinear mbar mbar = 0 := by
  simp [lorentzBilinear, mbar, complex_I_half_mul]
  norm_num

theorem lorentzBilinear_ell_n :
    lorentzBilinear ell n = -1 := by
  simp [lorentzBilinear, ell, n]
  ring

theorem lorentzBilinear_n_ell :
    lorentzBilinear n ell = -1 := by
  simp [lorentzBilinear, ell, n]
  ring

theorem lorentzBilinear_m_mbar :
    lorentzBilinear m mbar = 1 := by
  simp [lorentzBilinear, m, mbar, complex_I_half_mul]
  norm_num

theorem lorentzBilinear_mbar_m :
    lorentzBilinear mbar m = 1 := by
  simp [lorentzBilinear, m, mbar, complex_I_half_mul]
  norm_num

theorem lorentzBilinear_ell_m :
    lorentzBilinear ell m = 0 := by
  simp [lorentzBilinear, ell, m]

theorem lorentzBilinear_ell_mbar :
    lorentzBilinear ell mbar = 0 := by
  simp [lorentzBilinear, ell, mbar]

theorem lorentzBilinear_n_m :
    lorentzBilinear n m = 0 := by
  simp [lorentzBilinear, n, m]

theorem lorentzBilinear_n_mbar :
    lorentzBilinear n mbar = 0 := by
  simp [lorentzBilinear, n, mbar]

theorem lorentzBilinear_m_ell :
    lorentzBilinear m ell = 0 := by
  simp [lorentzBilinear, ell, m]

theorem lorentzBilinear_mbar_ell :
    lorentzBilinear mbar ell = 0 := by
  simp [lorentzBilinear, ell, mbar]

theorem lorentzBilinear_m_n :
    lorentzBilinear m n = 0 := by
  simp [lorentzBilinear, n, m]

theorem lorentzBilinear_mbar_n :
    lorentzBilinear mbar n = 0 := by
  simp [lorentzBilinear, n, mbar]

theorem np_null_tetrad_normalization :
    lorentzBilinear ell ell = 0 ∧
      lorentzBilinear n n = 0 ∧
      lorentzBilinear m m = 0 ∧
      lorentzBilinear mbar mbar = 0 ∧
      lorentzBilinear ell n = -1 ∧
      lorentzBilinear m mbar = 1 ∧
      lorentzBilinear ell m = 0 ∧
      lorentzBilinear ell mbar = 0 ∧
      lorentzBilinear n m = 0 ∧
      lorentzBilinear n mbar = 0 := by
  exact ⟨lorentzBilinear_self_ell, lorentzBilinear_self_n,
    lorentzBilinear_self_m, lorentzBilinear_self_mbar,
    lorentzBilinear_ell_n, lorentzBilinear_m_mbar,
    lorentzBilinear_ell_m, lorentzBilinear_ell_mbar,
    lorentzBilinear_n_m, lorentzBilinear_n_mbar⟩

def npTetrad : Fin 4 → Carrier := ![ell, n, m, mbar]

def npGram : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => lorentzBilinear (npTetrad i) (npTetrad j)

theorem npGram_eq :
    npGram = !![
      (0 : ℂ), -1, 0, 0;
      -1, 0, 0, 0;
      0, 0, 0, 1;
      0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [npGram, npTetrad, lorentzBilinear, ell, n, m, mbar,
      complex_I_half_mul] <;> norm_num <;> ring

theorem npGram_det : Matrix.det npGram = (1 : ℂ) := by
  rw [npGram_eq]
  simp [Matrix.det_succ_row_zero, Matrix.det_fin_two,
    Matrix.det_fin_one, Fin.sum_univ_succ, Fin.succAbove]

theorem npGram_mul_self : npGram * npGram = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [npGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

theorem npGram_nonsing_inv : npGram⁻¹ = npGram := by
  apply Matrix.inv_eq_right_inv
  exact npGram_mul_self

def npCoordinates (x : Carrier) : Fin 4 → ℂ :=
  ![(x 0 + x 3) / 2, 2 * (x 0 - x 3),
    (x 1 : ℂ) - Complex.I * x 2,
    (x 1 : ℂ) + Complex.I * x 2]

def npTetradCombination (a : Fin 4 → ℂ) : Carrier :=
  a 0 • ell + a 1 • n + a 2 • m + a 3 • mbar

theorem npCoordinates_combination (a : Fin 4 → ℂ) :
    npCoordinates (npTetradCombination a) = a := by
  funext i
  fin_cases i <;>
    simp [npCoordinates, npTetradCombination, ell, n, m, mbar,
      Pi.add_apply, Pi.smul_apply] <;>
    ring_nf <;> try rw [complex_I_sq] <;> ring

theorem npTetradCombination_coordinates (x : Carrier) :
    npTetradCombination (npCoordinates x) = x := by
  funext i
  fin_cases i <;>
    simp [npCoordinates, npTetradCombination, ell, n, m, mbar,
      Pi.add_apply, Pi.smul_apply] <;>
    ring_nf <;> try rw [complex_I_sq] <;> ring

def npTetradCoordinateEquiv : Carrier ≃ₗ[ℂ] (Fin 4 → ℂ) :=
  { toFun := npCoordinates
    invFun := npTetradCombination
    left_inv := npTetradCombination_coordinates
    right_inv := npCoordinates_combination
    map_add' := by
      intro x y
      funext i
      fin_cases i <;> simp [npCoordinates] <;> ring
    map_smul' := by
      intro a x
      funext i
      fin_cases i <;> simp [npCoordinates] <;> ring }

theorem np_tetrad_basis :
    Function.Bijective npTetradCoordinateEquiv :=
  npTetradCoordinateEquiv.bijective

/-! The coordinate equivalence also exposes the null tetrad as a genuine
`Module.Basis`, rather than only as a bijective coordinate readout. -/

noncomputable def npTetradBasis : Module.Basis (Fin 4) ℂ Carrier :=
  (Pi.basisFun ℂ (Fin 4)).map npTetradCoordinateEquiv.symm

@[simp] theorem npTetradBasis_apply (i : Fin 4) :
    npTetradBasis i = npTetrad i := by
  rw [npTetradBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change npTetradCombination (Pi.single i 1) = npTetrad i
  fin_cases i <;>
    ext j <;>
    simp [npTetradCombination, npTetrad, ell, n, m, mbar,
      Pi.single_apply] <;> ring

/- The coordinates supplied by the genuine null-tetrad basis are the
   previously defined concrete Newman--Penrose coordinate readout. -/
theorem npTetradBasis_repr (x : Carrier) :
    npTetradBasis.repr x = npCoordinates x := by
  rw [npTetradBasis, Module.Basis.map_repr]
  ext i
  simp [npTetradCoordinateEquiv]

theorem npTetradBasis_repr_apply (x : Carrier) (i : Fin 4) :
    npTetradBasis.repr x i = npCoordinates x i := by
  rw [npTetradBasis_repr]

theorem lorentzBilinearForm_toMatrix_npTetradBasis :
    LinearMap.BilinForm.toMatrix npTetradBasis lorentzBilinearForm = npGram := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, npTetradBasis_apply, npGram,
    npTetrad]

/-! The coordinate equivalence is the dual null-tetrad pairing readout. -/

theorem npCoordinates_eq_pairing (x : Carrier) :
    npCoordinates x =
      ![-(lorentzBilinear x n),
        -(lorentzBilinear x ell),
        lorentzBilinear x mbar,
        lorentzBilinear x m] := by
  funext i
  fin_cases i <;>
    simp [npCoordinates, lorentzBilinear, ell, n, m, mbar,
      Pi.add_apply, Pi.smul_apply] <;>
    ring_nf <;> try rw [complex_I_sq] <;> ring

theorem lorentzBilinear_npCoordinates (x y : Carrier) :
    lorentzBilinear x y =
      -(npCoordinates x 0) * npCoordinates y 1 -
        (npCoordinates x 1) * npCoordinates y 0 +
        (npCoordinates x 2) * npCoordinates y 3 +
        (npCoordinates x 3) * npCoordinates y 2 := by
  simp [lorentzBilinear, npCoordinates] <;>
    ring_nf <;> try rw [complex_I_sq] <;> ring

theorem lorentzBilinear_self_npCoordinates (x : Carrier) :
    lorentzBilinear x x =
      -2 * (npCoordinates x 0) * npCoordinates x 1 +
        2 * (npCoordinates x 2) * npCoordinates x 3 := by
  rw [lorentzBilinear_npCoordinates]
  ring

theorem np_null_iff_coordinates (x : Carrier) :
    lorentzBilinear x x = 0 ↔
      (npCoordinates x 0) * npCoordinates x 1 =
        (npCoordinates x 2) * npCoordinates x 3 := by
  rw [lorentzBilinear_self_npCoordinates]
  constructor
  · intro h
    linear_combination (-1 / 2 : ℂ) * h
  · intro h
    linear_combination (-2 : ℂ) * h

/-- The complex-bilinear Lorentz form is nondegenerate on the concrete
    carrier.  The proof uses the already established dual tetrad readout. -/
theorem lorentzBilinear_left_nondegenerate (x : Carrier)
    (h : ∀ y : Carrier, lorentzBilinear x y = 0) : x = 0 := by
  have hc : npCoordinates x = 0 := by
    rw [npCoordinates_eq_pairing]
    funext i
    fin_cases i <;> simp [h]
  rw [← npTetradCombination_coordinates x, hc]
  simp [npTetradCombination]

theorem lorentzBilinear_symm (x y : Carrier) :
    lorentzBilinear x y = lorentzBilinear y x := by
  simp [lorentzBilinear]
  ring

theorem lorentzBilinear_right_nondegenerate (y : Carrier)
    (h : ∀ x : Carrier, lorentzBilinear x y = 0) : y = 0 := by
  apply lorentzBilinear_left_nondegenerate y
  intro x
  rw [lorentzBilinear_symm]
  exact h x

theorem lorentzBilinear_nondegenerate :
    (∀ x : Carrier, (∀ y : Carrier, lorentzBilinear x y = 0) → x = 0) ∧
      (∀ y : Carrier, (∀ x : Carrier, lorentzBilinear x y = 0) → y = 0) := by
  exact ⟨lorentzBilinear_left_nondegenerate,
    lorentzBilinear_right_nondegenerate⟩

theorem lorentzBilinearForm_nondegenerate :
    lorentzBilinearForm.Nondegenerate := by
  constructor
  · intro x hx
    apply lorentzBilinear_left_nondegenerate x
    intro y
    rw [← lorentzBilinearForm_apply]
    exact hx y
  · intro y hy
    apply lorentzBilinear_right_nondegenerate y
    intro x
    rw [← lorentzBilinearForm_apply]
    exact hy x

theorem np_tetrad_reconstruction (x : Carrier) :
    npTetradCombination (npTetradCoordinateEquiv x) = x := by
  exact npTetradCombination_coordinates x

@[simp] theorem np_conj_ell : star ell = ell := by
  funext i
  fin_cases i <;> simp [ell]

@[simp] theorem np_conj_n : star n = n := by
  funext i
  fin_cases i <;> simp [n]

@[simp] theorem np_conj_m : star m = mbar := by
  funext i
  fin_cases i <;> simp [m, mbar] <;> ring_nf

@[simp] theorem np_conj_mbar : star mbar = m := by
  funext i
  fin_cases i <;> simp [m, mbar] <;> ring_nf

theorem np_pairing_reconstruction (x : Carrier) :
    x =
      (-(lorentzBilinear x n)) • ell +
        (-(lorentzBilinear x ell)) • n +
        (lorentzBilinear x mbar) • m +
        (lorentzBilinear x m) • mbar := by
  funext i
  fin_cases i <;>
    simp [lorentzBilinear, ell, n, m, mbar, complex_I_sq,
      Pi.add_apply, Pi.smul_apply] <;>
    ring_nf <;> try rw [complex_I_sq] <;> ring

end

end InfoGeometry.Geometry.NewmanPenrose
