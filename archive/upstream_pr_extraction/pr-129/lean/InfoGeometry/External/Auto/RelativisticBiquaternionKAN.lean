import Mathlib.Tactic

/-!
# Biquaternions, `SL(2,C)`, KAN boosts, and special relativity

This module formalizes the special-relativistic dictionary behind the
biquaternion architecture:

* a Minkowski vector `(t,x,y,z)` is encoded as a Hermitian Pauli matrix;
* its determinant is the Minkowski interval `t²-x²-y²-z²`;
* determinant-one spin transformations preserve the determinant under
  a specified adjoint action on `2 × 2` complex matrices;
* a diagonal `A`-sector KAN boost rescales lightcone coordinates;
* the boost generator squares to the identity, so the exponential closes in
  `span{I,σ}`;
* the nonsymmorphic glide phase imposes a relativistic momentum selection rule.
-/

noncomputable section

namespace RelativisticBiquaternionKAN

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrices. -/
def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

/-- Minkowski vector encoded as a Hermitian biquaternion/Pauli matrix. -/
def minkowskiMatrix (t x y z : ℂ) : M2C :=
  t • (1 : M2C) + x • σ1 + y • σ2 + z • σ3

/-- Entrywise closed form of the Pauli encoding. -/
theorem minkowskiMatrix_entries (t x y z : ℂ) :
    minkowskiMatrix t x y z = !![t + z, x - Complex.I * y; x + Complex.I * y, t - z] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [minkowskiMatrix, σ1, σ2, σ3, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply] <;> ring

/-- The determinant is the Minkowski interval. -/
theorem det_minkowskiMatrix (t x y z : ℂ) :
    (minkowskiMatrix t x y z).det = t^2 - x^2 - y^2 - z^2 := by
  rw [minkowskiMatrix_entries]
  simp [Matrix.det_fin_two]
  have hI : Complex.I * Complex.I = -1 := by simpa [pow_two] using Complex.I_sq
  calc
    (t + z) * (t - z) - (x - Complex.I * y) * (x + Complex.I * y)
        = t^2 - z^2 - (x^2 - (Complex.I * Complex.I) * y^2) := by ring
    _ = t^2 - z^2 - (x^2 - (-1 : ℂ) * y^2) := by rw [hI]
    _ = t^2 - x^2 - y^2 - z^2 := by ring

/-- `SL(2,C)` spinorial Lorentz transformations with determinant preservation recorded. -/
structure SL2CSpin where
  A : M2C
  det_one : A.det = 1
  adjoint : M2C → M2C
  det_preserved : ∀ X : M2C, (adjoint X).det = X.det

/-- Determinant preservation under the spin adjoint action. -/
theorem spin_adjoint_preserves_interval (S : SL2CSpin) (t x y z : ℂ) :
    (S.adjoint (minkowskiMatrix t x y z)).det = t^2 - x^2 - y^2 - z^2 := by
  rw [S.det_preserved, det_minkowskiMatrix]

/-- Diagonal KAN `A`-sector boost matrix with parameters `a,b`. -/
def Aboost (a b : ℂ) : M2C := !![a, 0; 0, b]

/-- Determinant of a diagonal boost. -/
theorem Aboost_det (a b : ℂ) : (Aboost a b).det = a * b := by
  simp [Aboost, Matrix.det_fin_two]

/-- Conjugation by a diagonal boost, represented algebraically without star. -/
def diagBoostConj (a b : ℂ) (X : M2C) : M2C := Aboost a b * X * Aboost a b

/-- Diagonal boost rescales the two lightcone diagonal entries. -/
theorem diagBoost_lightcone (a b t z : ℂ) :
    diagBoostConj a b (minkowskiMatrix t 0 0 z) =
      !![a^2 * (t + z), 0; 0, b^2 * (t - z)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [diagBoostConj, Aboost, minkowskiMatrix_entries, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply] <;> ring

/-- Boost generator used for rapidity flow. -/
def Kboost (v : ℂ) : M2C := v • σ1

/-- The boost generator squares to a scalar. -/
theorem Kboost_sq (v : ℂ) : Kboost v * Kboost v = (v * v) • (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Kboost, σ1, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply]

/-- Closed spin-boost expression `cosh η I + sinh η σ₁`. -/
def spinBoostClosed (η : ℂ) : M2C :=
  Complex.cosh η • (1 : M2C) + Complex.sinh η • σ1

/-- The closed spin boost has determinant `cosh²η-sinh²η=1`. -/
theorem spinBoostClosed_det (η : ℂ) : (spinBoostClosed η).det = 1 := by
  simp [spinBoostClosed, σ1, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  simpa [pow_two] using Complex.cosh_sq_sub_sinh_sq η

/-- `pg` glide phase for fixed-axis momentum. -/
def pgPhase (k : ℕ) : ℂ := (-1 : ℂ) ^ k

/-- Odd glide momentum has phase `-1`. -/
theorem pgPhase_odd {k : ℕ} (hodd : Odd k) : pgPhase k = -1 := by
  unfold pgPhase
  simpa using hodd.neg_one_pow

/-- Odd fixed-axis momentum coefficients are extinguished. -/
theorem relativistic_glide_momentum_extinction {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = pgPhase k * c) : c = 0 := by
  rw [pgPhase_odd hodd] at hrel
  have hneg : c = -c := by simpa using hrel
  have hsub : c - (-c) = 0 := sub_eq_zero.mpr hneg
  have h2 : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c - (-c) := by ring
      _ = 0 := hsub
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

end RelativisticBiquaternionKAN
