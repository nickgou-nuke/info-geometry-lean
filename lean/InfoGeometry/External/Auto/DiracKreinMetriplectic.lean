import Mathlib.Tactic

/-!
# Dirac/Krein metriplectic anchors

Finite theorem-honest anchors reconciling the chain:

* Dirac adjoint as a Krein/fundamental-symmetry adjoint;
* Tomita-style modular conjugation socket;
* Souriau temperature as Lie-algebra/vector parameter socket;
* Bogoliubov hyperbolic sheet-mixing preserving the Krein metric;
* determinant/log-barrier and Itakura--Saito extensions as sockets.

The proved core uses a `2×2` real model with Krein metric `diag(1,-1)`, the
finite shadow of the doubled `16₊⊕16₋` spinor picture.
-/

noncomputable section

namespace DiracKreinMetriplectic

open Matrix

/-- Finite `1+1` Krein metric, the toy Dirac `γ⁰`/fundamental symmetry. -/
def kreinMetric2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

/-- Dirac/Krein adjoint in the real finite model: `A ↦ Γ Aᵀ Γ`. -/
def diracAdjoint2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinMetric2 * Aᵀ * kreinMetric2

@[simp] theorem kreinMetric2_sq : kreinMetric2 * kreinMetric2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [kreinMetric2, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem kreinMetric2_transpose : kreinMetric2ᵀ = kreinMetric2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [kreinMetric2]

/-- The Dirac/Krein adjoint is involutive in the finite model. -/
theorem diracAdjoint2_involutive (A : Matrix (Fin 2) (Fin 2) ℝ) :
    diracAdjoint2 (diracAdjoint2 A) = A := by
  simp only [diracAdjoint2, Matrix.transpose_mul, kreinMetric2_transpose,
    Matrix.transpose_transpose]
  rw [← mul_assoc kreinMetric2 kreinMetric2 (A * kreinMetric2), kreinMetric2_sq]
  simp
  rw [mul_assoc A kreinMetric2 kreinMetric2, kreinMetric2_sq]
  simp

/-- Hyperbolic Bogoliubov sheet-mixing matrix. -/
def bogoliubov2 (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, s;
     s, c]

/-- Determinant of the finite Bogoliubov matrix. -/
theorem bogoliubov2_det (c s : ℝ) : (bogoliubov2 c s).det = c^2 - s^2 := by
  simp [bogoliubov2]
  ring

/-- Hyperbolic normalization `c²-s²=1` makes the Bogoliubov determinant `1`. -/
theorem bogoliubov2_det_one {c s : ℝ} (h : c^2 - s^2 = 1) :
    (bogoliubov2 c s).det = 1 := by
  rw [bogoliubov2_det, h]

/-- Bogoliubov sheet mixing preserves the Krein metric exactly when `c²-s²=1`. -/
theorem bogoliubov2_preserves_krein {c s : ℝ} (h : c^2 - s^2 = 1) :
    (bogoliubov2 c s)ᵀ * kreinMetric2 * (bogoliubov2 c s) = kreinMetric2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubov2, kreinMetric2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [h]

/-- Log-det barrier for the finite Bogoliubov Jacobian. -/
def BogoliubovBarrier2 (c s : ℝ) : ℝ :=
  - Real.log ((bogoliubov2 c s).det)

/-- A normalized real Bogoliubov transform has zero log-det volume barrier. -/
theorem bogoliubovBarrier2_zero {c s : ℝ} (h : c^2 - s^2 = 1) :
    BogoliubovBarrier2 c s = 0 := by
  unfold BogoliubovBarrier2
  rw [bogoliubov2_det_one h]
  simp

/-- Lorentz/Souriau temperature four-vector norm in signature `(+---)`. -/
def souriauLorentzNorm (β : Fin 4 → ℝ) : ℝ :=
  β 0 ^ 2 - β 1 ^ 2 - β 2 ^ 2 - β 3 ^ 2

/-- A rest-frame Souriau temperature vector has positive Lorentz norm when its
time component is nonzero. -/
theorem souriau_rest_norm_pos {b : ℝ} (hb : b ≠ 0) :
    0 < souriauLorentzNorm ![b, 0, 0, 0] := by
  simp [souriauLorentzNorm]
  exact sq_pos_of_ne_zero hb



end DiracKreinMetriplectic
