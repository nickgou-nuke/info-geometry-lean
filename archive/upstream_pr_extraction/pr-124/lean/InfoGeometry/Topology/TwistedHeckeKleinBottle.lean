import Mathlib.Tactic

/-!
# Finite Twisted Matrix Relations and a Klein-Type Involution

Formalizes a finite algebraic shadow of twisted Hecke relations together with the
displayed involution on a complex parameter pair.  The file does not construct a
quotient topology, a Klein-bottle fundamental group, a complete Hecke algebra, or
any classification/temperedness theorem for representations.
-/

noncomputable section

namespace InfoGeometry.Topology.TwistedHeckeKleinBottle

open Complex

/-- The displayed parameter involution `tau (w,z) = (-w,z⁻¹)`. -/
def tau_involution (w z : ℂ) : ℂ × ℂ :=
  (-w, z⁻¹)

/-- Algebraic involution/freeness predicate, restricted to nonzero parameters.

This predicate records pointwise identities only; it is not a quotient-space
or topological Klein-bottle construction.
-/
def tau_involution_prop : Prop :=
  (∀ w z : ℂ, w ≠ 0 → z ≠ 0 → tau_involution (tau_involution w z).1 (tau_involution w z).2 = (w, z)) ∧
  (∀ w z : ℂ, w ≠ 0 → z ≠ 0 → tau_involution w z ≠ (w, z))

/-- The displayed parameter involution is free on nonzero points. -/
theorem tau_involution_prop_proved : tau_involution_prop := by
  constructor
  · intro w z hw hz
    simp [tau_involution, inv_inv]
  · intro w z hw hz hfix
    have hfirst : -w = w := by
      simpa [tau_involution] using congrArg Prod.fst hfix
    have hzero : w + w = 0 := neg_eq_iff_add_eq_zero.mp hfirst
    have htwo : (2 : ℂ) * w = 0 := by
      simpa [two_mul] using hzero
    exact hw ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

/-- Two-by-two matrices used for the finite twisted-relation calculation. -/
def Y_matrix (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![w, 0], ![0, -w]]

def s_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![1, 0]]

def X_matrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![z, 0], ![0, z⁻¹]]

/-- Predicate collecting the displayed finite matrix relations:
1. s^2 = I
2. sX = X^{-1}s
3. sY = -Ys
4. XY = YX

No completeness claim about a Hecke algebra or its representations is made.
-/
def twisted_hecke_relations_prop (w z : ℂ) : Prop :=
  s_matrix * s_matrix = 1 ∧
  s_matrix * X_matrix z = (X_matrix z)⁻¹ * s_matrix ∧
  s_matrix * Y_matrix w = - (Y_matrix w) * s_matrix ∧
  X_matrix z * Y_matrix w = Y_matrix w * X_matrix z

/-- The displayed two-by-two matrices satisfy the twisted Hecke relations. -/
theorem twisted_hecke_relations (w z : ℂ) (hz : z ≠ 0) :
    twisted_hecke_relations_prop w z := by
  have hXinverse : (X_matrix z)⁻¹ = X_matrix z⁻¹ := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X_matrix, Matrix.mul_apply, Fin.sum_univ_two, hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hXinverse]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s_matrix, X_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s_matrix, Y_matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X_matrix, Y_matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end InfoGeometry.Topology.TwistedHeckeKleinBottle
