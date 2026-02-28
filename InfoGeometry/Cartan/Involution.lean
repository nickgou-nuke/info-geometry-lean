import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basic

/-!
# Cartan involution and ± projectors (module-level)

This is the unified "bedrock" API used by the Krein/Clifford layers:
an involution `θ` on a real module, together with the canonical
projectors `Pplus` and `Pminus`.
-/

namespace InfoGeometry.Cartan

open scoped BigOperators

/-- A Cartan involution on a real module: a linear involution `θ`. -/
class CartanInvolution (V : Type*) [AddCommGroup V] [Module ℝ V] where
  θ : V →ₗ[ℝ] V
  invol : ∀ v : V, θ (θ v) = v

namespace CartanInvolution

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (C : CartanInvolution V)

/-- `P₊(v) = (1/2)(v + θ v)` -/
noncomputable def Pplus (v : V) : V :=
  ((2 : ℝ)⁻¹) • (v + C.θ v)

/-- `P₋(v) = (1/2)(v - θ v)` -/
noncomputable def Pminus (v : V) : V :=
  ((2 : ℝ)⁻¹) • (v - C.θ v)

@[simp] lemma theta_Pplus (v : V) :
    C.θ (Pplus (C := C) v) = Pplus (C := C) v := by
  classical
  simp [Pplus, map_add, LinearMap.map_smulₛₗ, mul_assoc, add_comm, add_left_comm, add_assoc,
        C.invol v]

@[simp] lemma theta_Pminus (v : V) :
    C.θ (Pminus (C := C) v) = - Pminus (C := C) v := by
  classical
  -- θ((1/2)(v - θv)) = (1/2)(θv - v) = -(1/2)(v - θv)
  simp [Pminus, map_sub, LinearMap.map_smulₛₗ, C.invol v, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm, smul_add, smul_neg]

lemma decompose (v : V) :
    v = Pplus (C := C) v + Pminus (C := C) v := by
  classical
  -- (1/2)(v+θv) + (1/2)(v-θv) = v
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
  simp [Pplus, Pminus, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add,
        add_smul, hhalf]

end CartanInvolution
end InfoGeometry.Cartan
