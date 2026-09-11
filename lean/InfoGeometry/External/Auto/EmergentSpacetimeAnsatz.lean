import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.PauliZornTrifactor

noncomputable section

/-- Hermitian matrices are the concrete finite spacetime carrier. -/
def is_hermitian (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  X = X.conjTranspose

/-- Pauli coordinates extracted from a Hermitian `2 x 2` matrix. -/
def hermitian_minkowski_iso (X : Matrix (Fin 2) (Fin 2) ℂ) (_ : is_hermitian X) :
    ℝ × ℝ × ℝ × ℝ :=
  (((X 0 0).re + (X 1 1).re) / 2,
    (X 0 1).re,
    -(X 0 1).im,
    ((X 0 0).re - (X 1 1).re) / 2)

/-- Every Hermitian `2 x 2` matrix is its Pauli/Zorn owner representative. -/
theorem hermitian_minkowski_iso_recompose
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : is_hermitian X) :
    X = PauliZornTrifactor.pauliHermitian
      (hermitian_minkowski_iso X hX).1
      (hermitian_minkowski_iso X hX).2.1
      (hermitian_minkowski_iso X hX).2.2.1
      (hermitian_minkowski_iso X hX).2.2.2 := by
  have h00 : X 0 0 = star (X 0 0) := by
    simpa [is_hermitian, Matrix.conjTranspose_apply] using
      congrFun (congrFun hX 0) 0
  have h10 : X 1 0 = star (X 0 1) := by
    simpa [is_hermitian, Matrix.conjTranspose_apply] using
      congrFun (congrFun hX 1) 0
  have h11 : X 1 1 = star (X 1 1) := by
    simpa [is_hermitian, Matrix.conjTranspose_apply] using
      congrFun (congrFun hX 1) 1
  have h00im : (X 0 0).im = 0 := by
    have h := congrArg Complex.im h00
    simp at h
    linarith [h]
  have h11im : (X 1 1).im = 0 := by
    have h := congrArg Complex.im h11
    simp at h
    linarith [h]
  have h10re : (X 1 0).re = (X 0 1).re := by
    have h := congrArg Complex.re h10
    simpa using h
  have h10im : (X 1 0).im = -(X 0 1).im := by
    have h := congrArg Complex.im h10
    simpa using h
  ext i j <;> fin_cases i <;> fin_cases j
  · simp [hermitian_minkowski_iso, PauliZornTrifactor.pauliHermitian]
    apply Complex.ext
    · simp
      ring
    · simp [h00im]
  · simp [hermitian_minkowski_iso, PauliZornTrifactor.pauliHermitian]
    apply Complex.ext <;> norm_num
  · simp [hermitian_minkowski_iso, PauliZornTrifactor.pauliHermitian]
    apply Complex.ext
    · simpa using h10re
    · simpa using h10im
  · simp [hermitian_minkowski_iso, PauliZornTrifactor.pauliHermitian]
    apply Complex.ext
    · simp
      ring
    · simp [h11im]

/-- The determinant is the owner Minkowski quadratic form in Pauli coordinates. -/
def determinant_is_minkowski_norm (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : is_hermitian X) : Prop :=
  X.det = (PauliZornTrifactor.minkowskiNorm
    (hermitian_minkowski_iso X hx).1
    (hermitian_minkowski_iso X hx).2.1
    (hermitian_minkowski_iso X hx).2.2.1
    (hermitian_minkowski_iso X hx).2.2.2 : ℂ)

theorem determinant_is_minkowski_norm_proved
  (X : Matrix (Fin 2) (Fin 2) ℂ) (hx : is_hermitian X) :
    determinant_is_minkowski_norm X hx := by
  let t := (hermitian_minkowski_iso X hx).1
  let x := (hermitian_minkowski_iso X hx).2.1
  let y := (hermitian_minkowski_iso X hx).2.2.1
  let z := (hermitian_minkowski_iso X hx).2.2.2
  change X.det = (PauliZornTrifactor.minkowskiNorm t x y z : ℂ)
  calc
    X.det = (PauliZornTrifactor.pauliHermitian t x y z).det := by
      congr 1
      exact hermitian_minkowski_iso_recompose X hx
    _ = (PauliZornTrifactor.minkowskiNorm t x y z : ℂ) :=
      PauliZornTrifactor.pauliHermitian_det _ _ _ _

/-- The null cone is the determinant-zero locus in the Hermitian carrier. -/
def null_cone_locus (X : Matrix (Fin 2) (Fin 2) ℂ) (_hx : is_hermitian X) : Prop :=
  X.det = 0

theorem null_cone_locus_iff_minkowski_null
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hx : is_hermitian X) :
    null_cone_locus X hx ↔
      PauliZornTrifactor.minkowskiNorm
        (hermitian_minkowski_iso X hx).1
        (hermitian_minkowski_iso X hx).2.1
        (hermitian_minkowski_iso X hx).2.2.1
        (hermitian_minkowski_iso X hx).2.2.2 = 0 := by
  rw [null_cone_locus, determinant_is_minkowski_norm_proved X hx]
  norm_cast

/-- The finite spacetime ansatz is witnessed by the owner Pauli representative. -/
def emergent_spacetime_ansatz : Prop :=
  ∃ t x y z : ℝ,
    is_hermitian (PauliZornTrifactor.pauliHermitian t x y z) ∧
      (PauliZornTrifactor.pauliHermitian t x y z).det =
        (PauliZornTrifactor.minkowskiNorm t x y z : ℂ)

theorem emergent_spacetime_ansatz_witness : emergent_spacetime_ansatz := by
  refine ⟨1, 0, 0, 0, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [PauliZornTrifactor.pauliHermitian]
  · exact PauliZornTrifactor.pauliHermitian_det _ _ _ _

end noncomputable section
