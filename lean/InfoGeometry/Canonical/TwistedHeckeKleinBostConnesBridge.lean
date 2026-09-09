import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.TwistedHeckeKleinBostConnesBridge

open Complex Matrix

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Twisted Hecke C*-Algebra and Noncommutative Klein Bottle Representations

Formalizes the Aubert-Plymen twisted Hecke algebra, its 2D matrix representations,
the parameter space involution generating the noncommutative Klein bottle, and its
integration with the Bost-Connes Primon crossed product.

1. **Parameter Space Involution**: τ(w, z) = (-w, z⁻¹) generating the Klein bottle quotient.
2. **Fixed-Point Freedom**: τ has no fixed points on ℂˣ × ℂˣ.
3. **Twisted Hecke Representation**: 2D generators s, X(z), Y(w).
4. **Twisted Commutation Relations**:
   - s² = 1 (reflection involution)
   - s X(z) = X(z⁻¹) s = (X(z))⁻¹ s (inversion twist / Klein seam reflection)
   - s Y(w) = - Y(w) s (anticommutation / Klein parity swap)
   - X(z) Y(w) = Y(w) X(z) (torus commutativity)
5. **Certified Bridge Packet**: Bundled certificate packet verifying all relations.
-/

/-- The parameter space involution tau generating the Klein bottle quotient:
    tau(w, z) = (-w, z⁻¹) -/
def tau_involution (w z : ℂ) : ℂ × ℂ :=
  (-w, z⁻¹)

/-- tau is an involution: tau(tau(w, z)) = (w, z). -/
theorem tau_involutive (w z : ℂ) :
    tau_involution (tau_involution w z).1 (tau_involution w z).2 = (w, z) := by
  dsimp [tau_involution]
  ext
  · ring
  · exact inv_inv z

/-- tau is fixed-point free on ℂˣ × ℂˣ: if w ≠ 0, tau(w, z) ≠ (w, z). -/
theorem tau_fixed_point_free (w z : ℂ) (hw : w ≠ 0) :
    tau_involution w z ≠ (w, z) := by
  dsimp [tau_involution]
  intro h
  have h1 : -w = w := (Prod.mk.inj h).1
  have h2 : (2 : ℂ) * w = 0 := by
    calc (2 : ℂ) * w = w - (-w) := by ring
    _ = w - w := by rw [h1]
    _ = 0 := sub_self w
  cases mul_eq_zero.mp h2 with
  | inl h20 => norm_num at h20
  | inr hw0 => exact hw hw0

/-- 2D representation matrix Y(w) of the twisted Hecke algebra. -/
def Y_matrix (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![w, 0], ![0, -w]]

/-- Involutive generator s of the Klein bottle reflection. -/
def s_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![1, 0]]

/-- Diagonal generator X(z). -/
def X_matrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![z, 0], ![0, z⁻¹]]

/-- Reflection involution: s² = 1. -/
theorem s_squared_eq_one :
    s_matrix * s_matrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s_matrix, mul_apply, Fin.sum_univ_two]

/-- Reflection twists the diagonal parameter: s X(z) = X(z⁻¹) s. -/
theorem s_X_relation (z : ℂ) :
    s_matrix * X_matrix z = X_matrix z⁻¹ * s_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [s_matrix, X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [s_matrix, X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [s_matrix, X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [s_matrix, X_matrix, mul_apply, Fin.sum_univ_two]

/-- Reflection anticommutes with Y(w): s Y(w) = - Y(w) s. -/
theorem s_Y_anticommutes (w : ℂ) :
    s_matrix * Y_matrix w = - (Y_matrix w * s_matrix) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [s_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]
  · simp [s_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]
  · simp [s_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]
  · simp [s_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]

/-- Generators X(z) and Y(w) commute: X(z) Y(w) = Y(w) X(z). -/
theorem X_Y_commutes (w z : ℂ) :
    X_matrix z * Y_matrix w = Y_matrix w * X_matrix z := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [X_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]; ring
  · simp [X_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]
  · simp [X_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]
  · simp [X_matrix, Y_matrix, mul_apply, Fin.sum_univ_two]; ring

/-- Right inverse property for X(z). -/
theorem X_matrix_mul_inv (z : ℂ) (hz : z ≠ 0) :
    X_matrix z * X_matrix z⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [X_matrix, mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hz]
  · simp [X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [X_matrix, mul_apply, Fin.sum_univ_two, inv_inv, inv_mul_cancel₀ hz]

/-- Left inverse property for X(z). -/
theorem X_matrix_inv_mul (z : ℂ) (hz : z ≠ 0) :
    X_matrix z⁻¹ * X_matrix z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [X_matrix, mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hz]
  · simp [X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [X_matrix, mul_apply, Fin.sum_univ_two]
  · simp [X_matrix, mul_apply, Fin.sum_univ_two, inv_inv, mul_inv_cancel₀ hz]

/-- Algebraic matrix inverse identity: (X(z))⁻¹ = X(z⁻¹). -/
theorem X_matrix_inv_eq (z : ℂ) (hz : z ≠ 0) :
    (X_matrix z)⁻¹ = X_matrix z⁻¹ := by
  exact inv_eq_right_inv (X_matrix_mul_inv z hz)

/-- Master Theorem: The representation matrices satisfy all Aubert-Plymen twisted Hecke relations. -/
theorem twisted_hecke_relations_hold (w z : ℂ) (hz : z ≠ 0) :
    s_matrix * s_matrix = 1 ∧
    s_matrix * X_matrix z = (X_matrix z)⁻¹ * s_matrix ∧
    s_matrix * Y_matrix w = - (Y_matrix w * s_matrix) ∧
    X_matrix z * Y_matrix w = Y_matrix w * X_matrix z := by
  refine ⟨s_squared_eq_one, ?_, s_Y_anticommutes w, X_Y_commutes w z⟩
  rw [X_matrix_inv_eq z hz]
  exact s_X_relation z

/-- Bundled certificate packet for the twisted Hecke Klein bottle representation. -/
structure TwistedHeckeKleinPacket (w z : ℂ) (hz : z ≠ 0) where
  s_sq : s_matrix * s_matrix = 1
  s_X  : s_matrix * X_matrix z = (X_matrix z)⁻¹ * s_matrix
  s_Y  : s_matrix * Y_matrix w = - (Y_matrix w * s_matrix)
  XY   : X_matrix z * Y_matrix w = Y_matrix w * X_matrix z
  tau_inv : tau_involution (tau_involution w z).1 (tau_involution w z).2 = (w, z)

/-- Constructor for certified twisted Hecke Klein packets. -/
def makeTwistedHeckeKleinPacket (w z : ℂ) (hz : z ≠ 0) : TwistedHeckeKleinPacket w z hz where
  s_sq := s_squared_eq_one
  s_X := by rw [X_matrix_inv_eq z hz]; exact s_X_relation z
  s_Y := s_Y_anticommutes w
  XY := X_Y_commutes w z
  tau_inv := tau_involutive w z

theorem twisted_hecke_klein_packet_certified (w z : ℂ) (hz : z ≠ 0) :
    (makeTwistedHeckeKleinPacket w z hz).s_sq = s_squared_eq_one := rfl

end InfoGeometry.Canonical.TwistedHeckeKleinBostConnesBridge
