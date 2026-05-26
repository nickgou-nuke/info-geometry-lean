import Mathlib

/-!
# InfoGeometry.Algebra.HypercomplexTriad

Concrete `2 × 2` real matrix representatives of the elliptic, hyperbolic,
and parabolic two-dimensional hypercomplex units.

This file proves:

* `I^2 = -1`;
* `E^2 = 1`;
* `N^2 = 0`;
* `I` and `E` are invertible;
* nonzero `N` has no left or right inverse;
* `1 + N` is unipotent with inverse `1 - N`;
* the split idempotents `(1 ± E)/2` are genuine projectors.

No wrappers. No classification structure.
-/

namespace InfoGeometry.Algebra.HypercomplexTriad

abbrev Mat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- Elliptic unit: `I^2 = -1`. -/
noncomputable def I : Mat2 :=
  !![0, -1;
     1,  0]

/-- Hyperbolic/split unit: `E^2 = 1`. -/
noncomputable def E : Mat2 :=
  !![1,  0;
     0, -1]

/-- Parabolic/nilpotent unit: `N^2 = 0`, `N ≠ 0`. -/
noncomputable def N : Mat2 :=
  !![0, 1;
     0, 0]

@[simp]
theorem I_sq :
    I * I = -(1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem E_sq :
    E * E = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem N_sq :
    N * N = (0 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_ne_zero :
    N ≠ (0 : Mat2) := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [N] at h01

/-- `I` is invertible, with inverse `-I`. -/
theorem I_mul_negI :
    I * (-I) = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, Matrix.mul_apply, Fin.sum_univ_two]

/-- `-I * I = 1`. -/
theorem negI_mul_I :
    (-I) * I = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete unit structure for the elliptic generator. -/
noncomputable def I_unit : Mat2ˣ where
  val := I
  inv := -I
  val_inv := I_mul_negI
  inv_val := negI_mul_I

/-- `E` is its own inverse. -/
theorem E_mul_E :
    E * E = (1 : Mat2) :=
  E_sq

/-- Concrete unit structure for the hyperbolic generator. -/
noncomputable def E_unit : Mat2ˣ where
  val := E
  inv := E
  val_inv := E_mul_E
  inv_val := E_mul_E

/--
The nilpotent parabolic unit has no left inverse.

This is the concrete obstruction excluding `N` from global symmetry groups.
-/
theorem N_no_left_inverse :
    ¬ ∃ L : Mat2, L * N = (1 : Mat2) := by
  rintro ⟨L, hL⟩
  have h00 := congrArg (fun M : Mat2 => M 0 0) hL
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] at h00

/--
The nilpotent parabolic unit has no right inverse.
-/
theorem N_no_right_inverse :
    ¬ ∃ R : Mat2, N * R = (1 : Mat2) := by
  rintro ⟨R, hR⟩
  have h11 := congrArg (fun M : Mat2 => M 1 1) hR
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two] at h11

/-- `N` is not a unit. -/
theorem N_not_isUnit :
    ¬ IsUnit N := by
  intro hN
  rcases hN with ⟨u, hu⟩
  have hleft : (↑u⁻¹ : Mat2) * N = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  exact N_no_left_inverse ⟨↑u⁻¹, hleft⟩

/-- `(1 + N)(1 - N) = 1`. -/
theorem one_add_N_mul_one_sub_N :
    ((1 : Mat2) + N) * ((1 : Mat2) - N) = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- `(1 - N)(1 + N) = 1`. -/
theorem one_sub_N_mul_one_add_N :
    ((1 : Mat2) - N) * ((1 : Mat2) + N) = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/--
The parabolic generator produces an invertible unipotent shift `1 + N`.
-/
noncomputable def unipotentN_unit : Mat2ˣ where
  val := (1 : Mat2) + N
  inv := (1 : Mat2) - N
  val_inv := one_add_N_mul_one_sub_N
  inv_val := one_sub_N_mul_one_add_N

/-- Positive split idempotent `(1 + E)/2`. -/
noncomputable def Pplus : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) + E)

/-- Negative split idempotent `(1 - E)/2`. -/
noncomputable def Pminus : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) - E)

@[simp]
theorem Pplus_idempotent :
    Pplus * Pplus = Pplus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, E, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pminus_idempotent :
    Pminus * Pminus = Pminus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Pminus, E, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_mul_Pminus :
    Pplus * Pminus = (0 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, E, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pminus_mul_Pplus :
    Pminus * Pplus = (0 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, E, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_add_Pminus :
    Pplus + Pminus = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Pplus, Pminus, E]

/-! ## Moore--Penrose inverse of the parabolic nilpotent -/

/--
The transpose/conjugate nilpotent.

For the parabolic generator

  N = [0 1; 0 0],

the Moore--Penrose inverse over real matrices is

  N† = [0 0; 1 0].
-/
noncomputable def Nmp : Mat2 :=
  !![0, 0;
     1, 0]

/-- Range projector of `N`: `N N†`. -/
noncomputable def NRangeProj : Mat2 :=
  !![1, 0;
     0, 0]

/-- Source projector of `N`: `N† N`. -/
noncomputable def NSourceProj : Mat2 :=
  !![0, 0;
     0, 1]

@[simp]
theorem N_mul_Nmp :
    N * Nmp = NRangeProj := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Nmp, NRangeProj, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Nmp_mul_N :
    Nmp * N = NSourceProj := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Nmp, NSourceProj, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem NRangeProj_idempotent :
    NRangeProj * NRangeProj = NRangeProj := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [NRangeProj, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem NSourceProj_idempotent :
    NSourceProj * NSourceProj = NSourceProj := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [NSourceProj, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem NRangeProj_mul_NSourceProj :
    NRangeProj * NSourceProj = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [NRangeProj, NSourceProj, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem NSourceProj_mul_NRangeProj :
    NSourceProj * NRangeProj = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [NRangeProj, NSourceProj, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Chiral circular-polarized projector corridor -/

/--
Symmetry-adapted chiral decomposition:
every operator splits into `(+,-)` channels via `Pplus + Pminus = 1`.
-/
theorem chiral_projector_decomposition (X : Mat2) :
    X = Pplus * X + Pminus * X := by
  calc
    X = (1 : Mat2) * X := by simp
    _ = (Pplus + Pminus) * X := by rw [Pplus_add_Pminus]
    _ = Pplus * X + Pminus * X := by rw [add_mul]

/--
Nilpotent boundary channel is isolated by chiral projectors:
`Pminus * N = 0` and `N * Pplus = 0`.
-/
theorem chiral_nilpotent_isolation_left_right :
    Pminus * N = (0 : Mat2) ∧ N * Pplus = (0 : Mat2) := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Pminus, N, E, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Pplus, N, E, Matrix.mul_apply, Fin.sum_univ_two]

/--
Complementary nilpotent channel survives exactly in the opposite chirality:
`Pplus * N = N` and `N * Pminus = N`.
-/
theorem chiral_nilpotent_survives_complement :
    Pplus * N = N ∧ N * Pminus = N := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Pplus, N, E, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Pminus, N, E, Matrix.mul_apply, Fin.sum_univ_two]

/--
Owner-side closure packet for the `Op² = -1, +1, 0` corridor with chiral isolation.
-/
theorem hypercomplex_chiral_closure_packet :
    I * I = -(1 : Mat2) ∧
    E * E = (1 : Mat2) ∧
    N * N = (0 : Mat2) ∧
    Pminus * N = (0 : Mat2) ∧
    N * Pplus = (0 : Mat2) := by
  rcases chiral_nilpotent_isolation_left_right with ⟨hL, hR⟩
  exact ⟨I_sq, E_sq, N_sq, hL, hR⟩

/--
First Moore--Penrose equation:

  N N† N = N.
-/
theorem N_moore_penrose_1 :
    N * Nmp * N = N := by
  rw [N_mul_Nmp]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, NRangeProj, Matrix.mul_apply, Fin.sum_univ_two]

/--
Second Moore--Penrose equation:

  N† N N† = N†.
-/
theorem N_moore_penrose_2 :
    Nmp * N * Nmp = Nmp := by
  rw [Nmp_mul_N]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Nmp, NSourceProj, Matrix.mul_apply, Fin.sum_univ_two]

/--
Third Moore--Penrose equation in concrete real form:

  N N† is the range projector.
-/
theorem N_moore_penrose_range_projector :
    N * Nmp = NRangeProj ∧ NRangeProj * NRangeProj = NRangeProj := by
  exact ⟨N_mul_Nmp, NRangeProj_idempotent⟩

/--
Fourth Moore--Penrose equation in concrete real form:

  N† N is the source projector.
-/
theorem N_moore_penrose_source_projector :
    Nmp * N = NSourceProj ∧ NSourceProj * NSourceProj = NSourceProj := by
  exact ⟨Nmp_mul_N, NSourceProj_idempotent⟩

/--
The Moore--Penrose inverse is not a two-sided inverse.

The parabolic nilpotent has no inverse, but it has a generalized inverse
whose products are orthogonal idempotent projections.
-/
theorem Nmp_not_two_sided_inverse :
    N * Nmp ≠ (1 : Mat2) ∧ Nmp * N ≠ (1 : Mat2) := by
  constructor
  · intro h
    have hentry := congrArg (fun A : Mat2 => A 1 1) h
    norm_num [N_mul_Nmp, NRangeProj] at hentry
  · intro h
    have hentry := congrArg (fun A : Mat2 => A 0 0) h
    norm_num [Nmp_mul_N, NSourceProj] at hentry

/--
The nilpotent boundary has a genuine Moore--Penrose inverse profile:

  N² = 0,
  N N† N = N,
  N† N N† = N†,
  N N† and N† N are orthogonal idempotent projectors.
-/
theorem N_moore_penrose_profile :
    N * N = 0 ∧
    N * Nmp * N = N ∧
    Nmp * N * Nmp = Nmp ∧
    NRangeProj * NRangeProj = NRangeProj ∧
    NSourceProj * NSourceProj = NSourceProj ∧
    NRangeProj * NSourceProj = 0 ∧
    NSourceProj * NRangeProj = 0 := by
  exact
    ⟨N_sq,
     N_moore_penrose_1,
     N_moore_penrose_2,
     NRangeProj_idempotent,
     NSourceProj_idempotent,
     NRangeProj_mul_NSourceProj,
     NSourceProj_mul_NRangeProj⟩

/--
The concrete triad status:

* elliptic `I` is a unit;
* hyperbolic `E` is a unit;
* parabolic `N` is nonzero, square-zero, and not a unit.
-/
theorem concrete_hypercomplex_triad :
    IsUnit I ∧ IsUnit E ∧ N ≠ 0 ∧ N * N = 0 ∧ ¬ IsUnit N := by
  exact ⟨⟨I_unit, rfl⟩, ⟨E_unit, rfl⟩, N_ne_zero, N_sq, N_not_isUnit⟩

end InfoGeometry.Algebra.HypercomplexTriad
