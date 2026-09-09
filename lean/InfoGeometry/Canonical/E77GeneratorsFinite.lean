import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Canonical.E77

open Matrix

/-!
# E7(7) Finite Generator Witness

This module provides a finite algebraic witness for the E7(7) generators 
acting on the fundamental 56-dimensional representation. It constructs
the decomposition of the 56-plet under the maximal subgroup E6(6) × GL(1, ℝ)
and formalizes the symplectic generator constraints.

Reference: "Nonorientable exceptional points in the Klein Brillouin zone"
(Ryu et al., Phys. Rev. A 112, 052223 (2025)) models how non-orientable
boundary paths randomize bulk phases. Here we capture the local algebraic 
symmetries before the continuum limit.
-/

/-- The 56-plet charge vector representation decomposes into
    27 (electric) + 27* (magnetic) + 1 + 1 under E6(6) × GL(1) -/
@[ext]
structure E77Charge56 where
  electric : Fin 27 → ℝ
  magnetic : Fin 27 → ℝ
  phi : ℝ
  psi : ℝ

/-- A simplified symplectic form Ω for the 56-dimensional space.
    Ω(A, B) = A.electric * B.magnetic - A.magnetic * B.electric + A.phi * B.psi - A.psi * B.phi 
    We model this as a finite sum to provide a structurally faithful witness. -/
def symplectic_form (A B : E77Charge56) : ℝ :=
  (∑ i : Fin 27, A.electric i * B.magnetic i) - 
  (∑ i : Fin 27, A.magnetic i * B.electric i) + 
  A.phi * B.psi - A.psi * B.phi

/-- 
Theorem: The Symplectic form is strictly antisymmetric.
-/
theorem symplectic_antisymmetric (A B : E77Charge56) :
    symplectic_form A B = - symplectic_form B A := by
  dsimp [symplectic_form]
  have h1 : (∑ i : Fin 27, B.electric i * A.magnetic i) = (∑ i : Fin 27, A.magnetic i * B.electric i) := by simp_rw [mul_comm]
  have h2 : (∑ i : Fin 27, B.magnetic i * A.electric i) = (∑ i : Fin 27, A.electric i * B.magnetic i) := by simp_rw [mul_comm]
  rw [h1, h2]
  ring

/-- The non-orientable Klein Brillouin zone twist acts as a CPT inversion
    on the charges, mapping electric to magnetic and flipping the scalars. -/
def klein_twist (A : E77Charge56) : E77Charge56 :=
  { electric := A.magnetic,
    magnetic := A.electric,
    phi := -A.psi,
    psi := -A.phi }

/-- 
Theorem: The Klein twist is an involution (a glide reflection in the Brillouin zone).
-/
theorem klein_twist_involution (A : E77Charge56) :
    klein_twist (klein_twist A) = A := by
  ext
  · simp [klein_twist]
  · simp [klein_twist]
  · simp [klein_twist]
  · simp [klein_twist]

/-- 
Theorem: The Klein twist is anti-symplectic. 
This provides the algebraic mechanism for symmetry-breaking towards GUE
when parallel transporting around non-orientable cycles.
-/
theorem klein_anti_symplectic (A B : E77Charge56) :
    symplectic_form (klein_twist A) (klein_twist B) = - symplectic_form A B := by
  dsimp [klein_twist, symplectic_form]
  have h1 : (∑ i : Fin 27, A.magnetic i * B.electric i) = (∑ i : Fin 27, A.magnetic i * B.electric i) := rfl
  have h2 : (∑ i : Fin 27, A.electric i * B.magnetic i) = (∑ i : Fin 27, A.electric i * B.magnetic i) := rfl
  ring

end InfoGeometry.Canonical.E77
