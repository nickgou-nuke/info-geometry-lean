import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.LieOrbitInfinitesimal

Infinitesimal corridor for the adjoint orbit on matrix Lie algebra:
`ad_A(X) = X*A - A*X`.

This file proves:
1. `ad_A` is a linear map,
2. `ker(ad_A)` is exactly the commutant of `A` (stabilizer Lie algebra at `A`).

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.LieOrbitInfinitesimal

open Matrix

section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Infinitesimal adjoint action at `A`: `X ↦ [X,A]`. -/
def adMap (A : Matrix n n R) : Matrix n n R →ₗ[R] Matrix n n R where
  toFun X := X * A - A * X
  map_add' X Y := by
    simp [Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c X := by
    simp [sub_eq_add_neg, smul_add, smul_neg]

theorem adMap_apply (A X : Matrix n n R) :
    adMap (n := n) A X = X * A - A * X := rfl

@[simp] theorem adMap_zero :
    adMap (n := n) (0 : Matrix n n R) = 0 := by
  ext X
  simp [adMap_apply]

theorem adMap_add (A B : Matrix n n R) :
    adMap (n := n) (A + B) =
      adMap (n := n) A + adMap (n := n) B := by
  ext X
  simp [adMap_apply, Matrix.mul_add, Matrix.add_mul, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

theorem adMap_neg (A : Matrix n n R) :
    adMap (n := n) (-A) = -adMap (n := n) A := by
  ext X
  simp [adMap_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The infinitesimal adjoint maps form the right-adjoint Lie representation.

The order `B * A - A * B` reflects the convention
`adMap A X = [X, A]` used in this file. -/
theorem adMap_commutator (A B : Matrix n n R) :
    (adMap (n := n) A).comp (adMap (n := n) B) -
        (adMap (n := n) B).comp (adMap (n := n) A) =
      adMap (n := n) (B * A - A * B) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, adMap_apply,
    Matrix.mul_sub, Matrix.sub_mul]
  noncomm_ring

theorem mem_ker_adMap_iff_commute (A X : Matrix n n R) :
    X ∈ LinearMap.ker (adMap (n := n) A) ↔ X * A = A * X := by
  constructor
  · intro hX
    have h0 : adMap (n := n) A X = 0 := by
      exact LinearMap.mem_ker.mp hX
    have hsub : X * A - A * X = 0 := by simpa [adMap_apply] using h0
    exact sub_eq_zero.mp hsub
  · intro hcomm
    refine LinearMap.mem_ker.mpr ?_
    simp [adMap_apply, hcomm]

theorem mem_ker_adMap_iff_lieBracket_zero (A X : Matrix n n R) :
    X ∈ LinearMap.ker (adMap (n := n) A) ↔ (X * A - A * X) = 0 := by
  constructor
  · intro hX
    exact LinearMap.mem_ker.mp hX
  · intro hbr
    exact LinearMap.mem_ker.mpr hbr

/-- Tangent submodule to the adjoint orbit at `A`, represented algebraically as `range(ad_A)`. -/
def orbitTangent (A : Matrix n n R) : Submodule R (Matrix n n R) :=
  LinearMap.range (adMap (n := n) A)

theorem mem_orbitTangent_iff (A Y : Matrix n n R) :
    Y ∈ orbitTangent (n := n) (R := R) A ↔ ∃ X : Matrix n n R, X * A - A * X = Y := by
  constructor
  · intro hY
    rcases LinearMap.mem_range.mp hY with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    simpa [adMap_apply] using hX
  · rintro ⟨X, hX⟩
    refine LinearMap.mem_range.mpr ?_
    exact ⟨X, by simpa [adMap_apply] using hX⟩

theorem lieBracket_mem_orbitTangent (A X : Matrix n n R) :
    X * A - A * X ∈ orbitTangent (n := n) (R := R) A := by
  exact (mem_orbitTangent_iff (n := n) (R := R) A (X * A - A * X)).2 ⟨X, rfl⟩

/-- Stabilizer Lie submodule at `A`: infinitesimal symmetries fixing `A`. -/
def stabilizerLie (A : Matrix n n R) : Submodule R (Matrix n n R) :=
  LinearMap.ker (adMap (n := n) A)

theorem mem_stabilizerLie_iff_commute (A X : Matrix n n R) :
    X ∈ stabilizerLie (n := n) (R := R) A ↔ X * A = A * X := by
  simpa [stabilizerLie] using mem_ker_adMap_iff_commute (n := n) (R := R) A X

/-- The stabilizer of a matrix is closed under the matrix commutator. -/
theorem stabilizerLie_closed_commutator (A X Y : Matrix n n R)
    (hX : X ∈ stabilizerLie (n := n) (R := R) A)
    (hY : Y ∈ stabilizerLie (n := n) (R := R) A) :
    X * Y - Y * X ∈ stabilizerLie (n := n) (R := R) A := by
  apply (mem_stabilizerLie_iff_commute (n := n) (R := R) A
    (X * Y - Y * X)).2
  have hX' := (mem_stabilizerLie_iff_commute (n := n) (R := R) A X).1 hX
  have hY' := (mem_stabilizerLie_iff_commute (n := n) (R := R) A Y).1 hY
  calc
    (X * Y - Y * X) * A = X * (Y * A) - Y * (X * A) := by
      simp [sub_mul, mul_assoc]
    _ = X * (A * Y) - Y * (A * X) := by rw [hY', hX']
    _ = (X * A) * Y - (Y * A) * X := by simp [mul_assoc]
    _ = (A * X) * Y - (A * Y) * X := by rw [hX', hY']
    _ = A * (X * Y - Y * X) := by simp only [mul_sub, mul_assoc]

/-- The adjoint-orbit tangent is stable under the stabilizer action. -/
theorem stabilizerLie_commutator_mem_orbitTangent
    (A X Y : Matrix n n R)
    (hX : X ∈ stabilizerLie (n := n) (R := R) A)
    (hY : Y ∈ orbitTangent (n := n) (R := R) A) :
    X * Y - Y * X ∈ orbitTangent (n := n) (R := R) A := by
  rcases (mem_orbitTangent_iff (n := n) (R := R) A Y).1 hY with ⟨Z, hZ⟩
  have hX' := (mem_stabilizerLie_iff_commute (n := n) (R := R) A X).1 hX
  apply (mem_orbitTangent_iff (n := n) (R := R) A
    (X * Y - Y * X)).2
  refine ⟨X * Z - Z * X, ?_⟩
  calc
    (X * Z - Z * X) * A - A * (X * Z - Z * X) =
        X * (Z * A - A * Z) - (Z * A - A * Z) * X := by
          have hXZ : X * (A * Z) = A * (X * Z) := by
            rw [← mul_assoc, hX', mul_assoc]
          simp only [sub_mul, mul_sub]
          rw [hXZ]
          simp only [hX', mul_assoc]
          abel_nf
    _ = X * Y - Y * X := by rw [hZ]

theorem adMap_scalar (a : R) :
    adMap (n := n) ((a : R) • (1 : Matrix n n R)) = 0 := by
  ext X i j
  simp [adMap_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_eq_add_neg]

theorem orbitTangent_scalar_eq_bot (a : R) :
    orbitTangent (n := n) (R := R) ((a : R) • (1 : Matrix n n R)) = ⊥ := by
  unfold orbitTangent
  rw [adMap_scalar (n := n) (R := R) a]
  simp

theorem orbitTangent_zero :
    orbitTangent (n := n) (R := R) (0 : Matrix n n R) = ⊥ := by
  unfold orbitTangent
  rw [adMap_zero (n := n) (R := R)]
  simp

end

end InfoGeometry.Canonical.LieOrbitInfinitesimal
