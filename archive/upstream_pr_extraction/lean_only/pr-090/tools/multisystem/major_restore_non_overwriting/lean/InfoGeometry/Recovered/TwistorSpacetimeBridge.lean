import Mathlib
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered
import InfoGeometry.Twistor.Incidence

/-!
# Twistor Spacetime Bridge

This module formally connects the exact $2 \times 2$ real matrix recovery of the split-quaternions
(`SpacetimeLorentzTransformations`) with the native `Twistor` incidence geometry already
present in the codebase (`InfoGeometry.Twistor.Incidence`).

It demonstrates two crucial bridges:
1. **Basis Alignment**: Our recovered `spacetimeMatrix` is an exact coordinate permutation 
   of the existing `soldering` map.
2. **Conformal/Twistor Symmetry**: The algebraic Lorentz sandwich $x' = q \cdot x \cdot q^{-1}$
   induces a natural symmetry on the twistor space $Z' = (\omega', \pi') = (q \omega, q \pi)$,
   proving that the incidence relation is strictly Lorentz-invariant.
-/

namespace InfoGeometry.Recovered

open InfoGeometry.SplitQuaternion
open InfoGeometry.Spacetime
open InfoGeometry.Twistor.Incidence
open InfoGeometry.Clifford.Soldering

/--
A helper to apply a $2 \times 2$ real matrix natively to a spinor `ℝ × ℝ`.
-/
def matrixAction (M : Matrix (Fin 2) (Fin 2) ℝ) (π : ℝ × ℝ) : ℝ × ℝ :=
  (M 0 0 * π.1 + M 0 1 * π.2, M 1 0 * π.1 + M 1 1 * π.2)

/--
The structural bridge: Our algebraically recovered `spacetimeMatrix` perfectly maps
to the codebase's existing `soldering` map under coordinate permutation.
-/
theorem bridge_soldering_eq (t x y z : ℝ) :
    spacetimeMatrix t x y z = soldering (t, z, y, x) := by
  -- Evaluate both explicitly to show structural equivalence
  ext i j
  fin_cases i <;> fin_cases j <;> 
    (simp [spacetimeMatrix, splitOne, splitI, splitJ, splitK,
           soldering, sigma0, sigma3, sigma1, epsilon])

/--
The matrix action evaluates identically to the Soldering `pointAction`.
-/
theorem pointAction_eq_matrixAction (t x y z : ℝ) (π : ℝ × ℝ) :
    pointAction (t, z, y, x) π = matrixAction (spacetimeMatrix t x y z) π := by
  rw [bridge_soldering_eq]
  rfl

/--
If `q` is a unit determinant Lorentz transformation, `splitConj q` acts as its exact inverse.
-/
lemma splitConj_is_inv_of_unit (q : Matrix (Fin 2) (Fin 2) ℝ) (h_unit : q.det = 1) :
    q * splitConj q = 1 ∧ splitConj q * q = 1 := by
  have h1 : q * splitConj q = q.det • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> 
      (simp [splitConj, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring)
  have h2 : splitConj q * q = q.det • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> 
      (simp [splitConj, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring)
  rw [h_unit] at h1 h2
  simp at h1 h2
  exact ⟨h1, h2⟩

/--
Composition of matrix actions.
-/
lemma matrixAction_mul (M N : Matrix (Fin 2) (Fin 2) ℝ) (π : ℝ × ℝ) :
    matrixAction M (matrixAction N π) = matrixAction (M * N) π := by
  ext
  · simp [matrixAction, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [matrixAction, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/--
The identity matrix leaves spinors invariant.
-/
lemma matrixAction_one (π : ℝ × ℝ) :
    matrixAction 1 π = π := by
  ext
  · simp [matrixAction]
  · simp [matrixAction]

/--
**The Twistor Lorentz Symmetry Theorem**

If a spacetime point `X` is incident with a twistor `(ω, π)`, and we apply a Lorentz 
transformation `q` (where `det q = 1`), then the transformed spacetime point `X' = q X q^{-1}`
is perfectly incident with the transformed twistor `(q ω, q π)`.

This structurally proves that the geometric transformations generated algebraically
are exact projective conformal symmetries of the Twistor space!
-/
theorem lorentz_twistor_symmetry
    (X q : Matrix (Fin 2) (Fin 2) ℝ) (ω π : ℝ × ℝ)
    (h_unit : q.det = 1)
    (h_incident : ω = matrixAction X π) :
    matrixAction q ω = matrixAction (lorentzTransform q X) (matrixAction q π) := by
  calc
    matrixAction q ω = matrixAction q (matrixAction X π) := by rw [h_incident]
    _ = matrixAction (q * X) π := by rw [matrixAction_mul]
    _ = matrixAction (q * X * 1) π := by simp
    _ = matrixAction (q * X * (splitConj q * q)) π := by 
          have hinv := (splitConj_is_inv_of_unit q h_unit).2
          rw [← hinv]
    _ = matrixAction ((q * X * splitConj q) * q) π := by
          have hassoc : q * X * (splitConj q * q) = (q * X * splitConj q) * q := by
            simp [Matrix.mul_assoc]
          rw [hassoc]
    _ = matrixAction (lorentzTransform q X * q) π := rfl
    _ = matrixAction (lorentzTransform q X) (matrixAction q π) := by rw [← matrixAction_mul]

end InfoGeometry.Recovered
