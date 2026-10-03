import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

open scoped TensorProduct

namespace InfoGeometry.Canonical.DoubledDiracKrein

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-!
# Stage 1: Microscopic Algebra (Clifford Doubled Spin Network)

We formally define the doubled Dirac operator and its SPT Krein involution,
demonstrating that their anticommutation leads exactly to the annihilation of
cross-terms, localizing the dynamics into independent Left and Right sectors.
-/

/-- The total doubled Dirac operator on the tensor product network. -/
def D_tot (D_L D_R β_R : Module.End R V) : Module.End R (V ⊗[R] V) :=
  TensorProduct.map D_L β_R + TensorProduct.map 1 D_R

/-- The total SPT Krein Involution on the network. -/
def beta_tot (β_L β_R : Module.End R V) : Module.End R (V ⊗[R] V) :=
  TensorProduct.map β_L β_R

/-- Bipartite Cross-Term Annihilation -/
lemma D_tot_sq_cross_terms_vanish
    (D_L D_R β_R : Module.End R V)
    (h_anticommute : D_R * β_R + β_R * D_R = 0)
    (h_beta_sq : β_R * β_R = 1) :
    (D_tot D_L D_R β_R) * (D_tot D_L D_R β_R) =
      TensorProduct.map (D_L * D_L) 1 + TensorProduct.map 1 (D_R * D_R) := by
  dsimp [D_tot]
  rw [mul_add, add_mul, add_mul]
  have h_map_mul : ∀ (A B C D : Module.End R V),
    (TensorProduct.map A B) * (TensorProduct.map C D) = TensorProduct.map (A * C) (B * D) := by
    intro A B C D
    exact (TensorProduct.map_comp A B C D).symm
  rw [h_map_mul, h_map_mul, h_map_mul, h_map_mul]
  rw [mul_one, one_mul, h_beta_sq, mul_one]
  have h_cross : TensorProduct.map D_L (D_R * β_R) + TensorProduct.map D_L (β_R * D_R) = 0 := by
    apply TensorProduct.ext'
    intro v w
    change (TensorProduct.map D_L (D_R * β_R) + TensorProduct.map D_L (β_R * D_R)) (v ⊗ₜ[R] w) = 0
    rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
    rw [← TensorProduct.tmul_add]
    have hz : (D_R * β_R + β_R * D_R) w = 0 := by rw [h_anticommute, LinearMap.zero_apply]
    have hz2 : (D_R * β_R) w + (β_R * D_R) w = 0 := hz
    rw [hz2, TensorProduct.tmul_zero]
  rw [add_assoc, ← add_assoc (TensorProduct.map D_L (D_R * β_R)), h_cross, zero_add]

end InfoGeometry.Canonical.DoubledDiracKrein
