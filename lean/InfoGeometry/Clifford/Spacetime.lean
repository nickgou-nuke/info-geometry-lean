import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Clifford.Biquaternion
import InfoGeometry.Quantum.HestenesKahler
import Mathlib.Tactic

/-!
# Spacetime Soldering: 4-Vectors, Quaternions, and Matrices

This module formalizes the "soldering form" which identifies spacetime 4-vectors
with elements of a quaternionic matrix algebra or the operatorial Biquaternion 
representation.

For Minkowski signature (1,3), we typically use:
* V = ℝ⁴ with q(t,x,y,z) = t² - x² - y² - z²
* This space is soldered to Biquaternionic operators on the doubled carrier.
* The determinant (refl. operator trace/norm) gives the Minkowski norm.
-/

open scoped Matrix
open scoped Quaternion

namespace InfoGeometry.Clifford.Spacetime

open InfoGeometry.Krein

/-- 
Standard Minkowski 4-vector space. 
-/
@[rep_depth projective]
abbrev Vec13 := ℝ × (ℝ × ℝ × ℝ)

/-- The Minkowski quadratic form: Q(t, x, y, z) = t² - x² - y² - z². -/
@[rep_depth projective]
noncomputable def minkiQ : QuadraticForm ℝ Vec13 :=
  QuadraticMap.ofPolar (fun v => v.1^2 - v.2.1^2 - v.2.2.1^2 - v.2.2.2^2)
    (fun a v => by dsimp; ring)
    (fun x x' y => by dsimp [QuadraticMap.polar]; ring)
    (fun a x y => by dsimp [QuadraticMap.polar]; ring)

@[simp] lemma minkiQ_apply (t x y z : ℝ) : 
    minkiQ (t, x, y, z) = t^2 - x^2 - y^2 - z^2 := rfl

/-- The algebra of 2x2 complex matrices. 
In STA (Space-Time Algebra), Cl(1,3) is represented by M₂(ℍ).
Here we use M₂(ℂ) for the vector soldering (Weyl representation).
-/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Real Pauli Matrices (used for the (1,1) slice or split-signature soldering). -/
def sigma0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
def sigma1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def sigma2_i : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0] -- iσ₂
def sigma3 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- 
Biquaternionic Soldering Form: v ↦ Σ(v)
This map solders a 4-vector to an operatorial Biquaternion.
For Minkowski signature (1,3), we use the phase-axis K = Jε to manage the 
imaginary component of the biquaternion.
-/
@[rep_depth operator]
noncomputable def biquaternionSoldering (E : Type*) 
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : 
    Vec13 → InfoGeometry.Clifford.Biquaternion E := fun v =>
    let t := v.1
    let x := v.2.1
    let y := v.2.2.1
    let z := v.2.2.2
    let raw : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
      t • (ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E))
        + x • (InfoGeometry.Krein.modular_j (E := E))
        + y • (InfoGeometry.Krein.clockAxis (E := E))
        + z • (InfoGeometry.Krein.spectral_epsilon (E := E))
    let op : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E :=
      InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart (E := E) raw
    { op := op
    , is_k_linear := by
        simpa [op] using
          (InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart_isPhaseLinear
            (E := E) raw)
    , is_biquaternionic := by
        refine ⟨op, 0, ?_⟩
        simp [op] }

/-- 
Standard soldering map to real matrices for the signature (2,2) representation.
-/
noncomputable def soldering : Vec13 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := v.1 • sigma0 + v.2.1 • sigma1 + v.2.2.1 • sigma2_i + v.2.2.2 • sigma3
  map_add' u v := by 
    ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma0, sigma1, sigma2_i, sigma3, Matrix.add_apply]; try ring)
  map_smul' a v := by 
    ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma0, sigma1, sigma2_i, sigma3, Matrix.smul_apply]; try ring)

/-- 
The fundamental property of the soldering form:
The determinant of the soldered matrix is the quadratic form.
det(σ(v)) = t² - x² + y² - z² (for this specific real representation).
-/
lemma det_soldering (v : Vec13) : 
    (soldering v).det = v.1^2 - v.2.1^2 + v.2.2.1^2 - v.2.2.2^2 := by
  rcases v with ⟨t, x, y, z⟩
  simp [soldering, sigma0, sigma1, sigma2_i, sigma3, Matrix.det_fin_two]
  ring

/-- 
The connection to Quaternions:
The space of 2x2 real matrices is isomorphic to the algebra of split-quaternions.
-/
def splitQuatBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) 1 0 (-1) where
  i := sigma3   -- σ₃² = 1
  j := sigma2_i -- (iσ₂)² = -1
  k := sigma1   -- σ₃(iσ₂) = σ₁
  i_mul_i := by ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma3, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  j_mul_j := by ext i j; fin_cases i <;> fin_cases j <;> (simp [sigma2_i, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]; try ring)
  i_mul_j := by 
    ext i j; fin_cases i <;> fin_cases j <;> 
      (simp [sigma3, sigma2_i, sigma1, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  j_mul_i := by 
    ext i j; fin_cases i <;> fin_cases j <;> 
      (simp [sigma3, sigma2_i, sigma1, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

end InfoGeometry.Clifford.Spacetime
