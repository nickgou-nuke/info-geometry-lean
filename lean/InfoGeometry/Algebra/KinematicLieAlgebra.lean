import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.KinematicCliffordAlgebra

/-!
# Kinematic Lie Algebras from Clifford Algebras

By equipping the N-dimensional Kinematic Clifford Algebra with the standard
commutator bracket $[a, b] = ab - ba$, we naturally obtain the Lie algebra
of the associated kinematic group.

This file proves the coordinate Clifford commutator identity for pairwise
orthogonal generators.  It does not construct the full grade-2 Lie subalgebra;
that requires an additional closure theorem for arbitrary finite linear
combinations of bivectors.

This generalizes all Euclidean, Lorentzian, Galilean, and conformal Lie algebras into
a single uniform framework.
-/

namespace InfoGeometry.Algebra

open CliffordAlgebra

/-- Move the scalar factor `2` across a real algebra scalar action. -/
lemma two_mul_smul_eq_smul_two_mul {A : Type*} [Ring A] [Algebra ℝ A] (r : ℝ) (x : A) :
    ((2 : ℝ) * r) • x = r • ((2 : A) * x) := by
  calc
    ((2 : ℝ) * r) • x = (r + r) • x := by rw [two_mul]
    _ = r • x + r • x := by rw [add_smul]
    _ = r • (x + x) := by rw [smul_add]
    _ = r • ((2 : A) * x) := by rw [two_mul]

/-- The basic Clifford bivector commutator for three pairwise-orthogonal vectors. -/
lemma clifford_bivector_bracket_identity
    {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ M)
    {a b c : M} (hab : Q.IsOrtho a b) (hbc : Q.IsOrtho b c) (hac : Q.IsOrtho a c) :
    ⁅ι Q a * ι Q b, ι Q b * ι Q c⁆ = ((2 : ℝ) * Q b) • (ι Q a * ι Q c) := by
  rw [Ring.lie_def]
  have hleft : (ι Q a * ι Q b) * (ι Q b * ι Q c) = Q b • (ι Q a * ι Q c) := by
    calc
      (ι Q a * ι Q b) * (ι Q b * ι Q c) =
          ι Q a * (ι Q b * ι Q b) * ι Q c := by
        noncomm_ring
      _ = ι Q a * algebraMap ℝ (CliffordAlgebra Q) (Q b) * ι Q c := by
        rw [ι_sq_scalar]
      _ = Q b • (ι Q a * ι Q c) := by
        rw [Algebra.smul_def]
        simp only [← mul_assoc]
        rw [Algebra.commutes]
  have hsq : ι Q a * ι Q b * ι Q b * ι Q c = Q b • (ι Q a * ι Q c) := by
    calc
      ι Q a * ι Q b * ι Q b * ι Q c =
          ι Q a * (ι Q b * ι Q b) * ι Q c := by
        noncomm_ring
      _ = ι Q a * algebraMap ℝ (CliffordAlgebra Q) (Q b) * ι Q c := by
        rw [ι_sq_scalar]
      _ = Q b • (ι Q a * ι Q c) := by
        rw [Algebra.smul_def]
        simp only [← mul_assoc]
        rw [Algebra.commutes]
  have hright : (ι Q b * ι Q c) * (ι Q a * ι Q b) = -(Q b • (ι Q a * ι Q c)) := by
    calc
      (ι Q b * ι Q c) * (ι Q a * ι Q b) =
          ι Q b * (ι Q c * ι Q a) * ι Q b := by
        noncomm_ring
      _ = ι Q b * (-(ι Q a * ι Q c)) * ι Q b := by
        rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hac.symm]
      _ = -(ι Q b * ι Q a * ι Q c * ι Q b) := by
        noncomm_ring
      _ = ι Q a * ι Q b * ι Q c * ι Q b := by
        rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hab.symm]
        noncomm_ring
      _ = ι Q a * ι Q b * (ι Q c * ι Q b) := by
        noncomm_ring
      _ = -(ι Q a * ι Q b * ι Q b * ι Q c) := by
        rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hbc.symm]
        noncomm_ring
      _ = -(Q b • (ι Q a * ι Q c)) := by
        rw [hsq]
  rw [hleft, hright]
  rw [sub_neg_eq_add, ← two_smul ℝ (Q b • (ι Q a * ι Q c))]
  rw [← mul_smul]

variable {n : ℕ} (kappa : Fin n → ℝ)

/--
The generator of the Lie algebra corresponding to the rotation/boost/shear
in the $(i, j)$ plane. Defined as the Clifford product $e_i e_j$.
-/
def kinematicBivector (i j : Fin n) : KinematicCliffordAlgebra n kappa :=
  kinematicGenerator n kappa i * kinematicGenerator n kappa j

/-- The explicit kinematic generator is the Clifford image of a coordinate basis vector. -/
lemma kinematicGenerator_eq_single (i : Fin n) :
    kinematicGenerator n kappa i =
      ι (kinematicQuadraticForm n kappa) (Pi.single i (1 : ℝ)) := by
  dsimp [kinematicGenerator]
  congr 1
  funext j
  by_cases h : i = j
  · subst j
    simp [Pi.single]
  · have hji : j ≠ i := fun hji => h hji.symm
    simp [Pi.single, h, hji]

/-- The diagonal kinematic quadratic form evaluates to the selected signature entry. -/
lemma kinematicQuadraticForm_single (i : Fin n) :
    kinematicQuadraticForm n kappa (Pi.single i (1 : ℝ)) = kappa i := by
  change
    (Matrix.toLinearMap₂' ℝ (Matrix.diagonal kappa)) (Pi.single i (1 : ℝ))
      (Pi.single i (1 : ℝ)) = kappa i
  simp [Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single]
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _hx hxi
    simp [hxi]
  · intro hi
    simp at hi

/-- Distinct coordinate basis vectors are orthogonal for the diagonal kinematic form. -/
lemma kinematicQuadraticForm_single_isOrtho (i j : Fin n) (hij : i ≠ j) :
    (kinematicQuadraticForm n kappa).IsOrtho (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) := by
  let B : LinearMap.BilinMap ℝ (Fin n → ℝ) ℝ :=
    Matrix.toLinearMap₂' ℝ (Matrix.diagonal kappa)
  have h_symm : B.IsSymm := by
    refine ⟨?_⟩
    intro x y
    simp [B, Matrix.toLinearMap₂'_apply, Matrix.diagonal, mul_comm, mul_left_comm]
  have hB : B (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) = 0 := by
    change
      (Matrix.toLinearMap₂' ℝ (Matrix.diagonal kappa)) (Pi.single i (1 : ℝ))
        (Pi.single j (1 : ℝ)) = 0
    simp [Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single]
    refine Finset.sum_eq_zero ?_
    intro x _hx
    by_cases hxi : x = i
    · subst x
      simp [hij]
    · simp [hxi]
  have hQ : B.toQuadraticMap.IsOrtho (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) :=
    (LinearMap.BilinForm.toQuadraticMap_isOrtho (R := ℝ) (M := Fin n → ℝ) (B := B)
      h_symm).2 hB
  simpa [B, kinematicQuadraticForm] using hQ

/--
The structural Lie bracket identity between two bivectors.
This governs the Wigner-Inönü contractions natively.
For example, $[e_i e_j, e_j e_k] = \kappa_j e_i e_k$.
-/
theorem kinematicBivector_bracket_identity (i j k : Fin n)
  (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
  ⁅kinematicBivector kappa i j, kinematicBivector kappa j k⁆ =
    2 * kappa j • kinematicBivector kappa i k := by
  have h_ij : (kinematicQuadraticForm n kappa).IsOrtho (Pi.single i 1) (Pi.single j 1) := by
    exact kinematicQuadraticForm_single_isOrtho kappa i j hij
  have h_jk : (kinematicQuadraticForm n kappa).IsOrtho (Pi.single j 1) (Pi.single k 1) := by
    exact kinematicQuadraticForm_single_isOrtho kappa j k hjk
  have h_ik : (kinematicQuadraticForm n kappa).IsOrtho (Pi.single i 1) (Pi.single k 1) := by
    exact kinematicQuadraticForm_single_isOrtho kappa i k hik
  have h :=
    clifford_bivector_bracket_identity (kinematicQuadraticForm n kappa) h_ij h_jk h_ik
  rw [kinematicQuadraticForm_single] at h
  simpa [kinematicBivector, kinematicGenerator_eq_single, two_mul_smul_eq_smul_two_mul] using h

end InfoGeometry.Algebra
