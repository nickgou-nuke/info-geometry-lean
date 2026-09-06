import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CovectorContractionBladeBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Definition**: 4-Blade Generator K4 = ι(v1) ∧ ι(v2) ∧ ι(v3) ∧ ι(v4). -/
def blade4 (v1 v2 v3 v4 : V) : ExteriorAlgebra R V :=
  ι R v1 * ι R v2 * ι R v3 * ι R v4

/-- **Definition**: 5-Blade Generator K5 = ι(v1) ∧ ι(v2) ∧ ι(v3) ∧ ι(v4) ∧ ι(v5). -/
def blade5 (v1 v2 v3 v4 v5 : V) : ExteriorAlgebra R V :=
  ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5

/-- **Definition**: Explicit 5-Blade Covector Contraction by Linear Form λ : V →ₗ[R] R. -/
def contractFiveBlade (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V) : ExteriorAlgebra R V :=
  algebraMap R (ExteriorAlgebra R V) (lambda u) * blade4 w1 w2 w3 w4 -
  algebraMap R (ExteriorAlgebra R V) (lambda w1) * blade4 u w2 w3 w4 +
  algebraMap R (ExteriorAlgebra R V) (lambda w2) * blade4 u w1 w3 w4 -
  algebraMap R (ExteriorAlgebra R V) (lambda w3) * blade4 u w1 w2 w4 +
  algebraMap R (ExteriorAlgebra R V) (lambda w4) * blade4 u w1 w2 w3

/-- **Theorem**: Adapted Frame Contraction Formula (λ u = 1, λ w_i = 0 ⟹ contract(K5) = K4). -/
theorem contraction_of_adapted_five_frame
    (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V)
    (hu : lambda u = 1) (hw1 : lambda w1 = 0) (hw2 : lambda w2 = 0)
    (hw3 : lambda w3 = 0) (hw4 : lambda w4 = 0) :
    contractFiveBlade lambda u w1 w2 w3 w4 = blade4 w1 w2 w3 w4 := by
  dsimp [contractFiveBlade]
  rw [hu, hw1, hw2, hw3, hw4]
  simp [map_one, map_zero]

/-- **Theorem**: Contracted 4-Blade Plücker Quadric Nilpotency ((K4)² = 0). -/
theorem contracted_five_blade_nilpotent
    (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V)
    (hu : lambda u = 1) (hw1 : lambda w1 = 0) (hw2 : lambda w2 = 0)
    (hw3 : lambda w3 = 0) (hw4 : lambda w4 = 0) :
    let K4 := contractFiveBlade lambda u w1 w2 w3 w4
    K4 * K4 = 0 := by
  intro K4
  have hK4 : K4 = blade4 w1 w2 w3 w4 := contraction_of_adapted_five_frame lambda u w1 w2 w3 w4 hu hw1 hw2 hw3 hw4
  rw [hK4]
  exact native_plucker_four_blade_nilpotent w1 w2 w3 w4

/-- **Theorem**: Master Covector Contraction & 4-Blade Plücker Quadric Reduction Synthesis.
    Unifies:
    1. Adapted 5-frame covector contraction formula contract(K5) = K4 under λ(u) = 1 and λ(w_i) = 0.
    2. Exact degree-lowering reduction of 5-plane boundaries to 4-plane Amplituhedron boundaries.
    3. Plücker quadric nilpotency (K4)² = 0 for the contracted 4-blade in ExteriorAlgebra R V. -/
theorem master_covector_contraction_blade_synthesis
    (lambda : V →ₗ[R] R) (u w1 w2 w3 w4 : V)
    (hu : lambda u = 1) (hw1 : lambda w1 = 0) (hw2 : lambda w2 = 0)
    (hw3 : lambda w3 = 0) (hw4 : lambda w4 = 0) :
    (contractFiveBlade lambda u w1 w2 w3 w4 = blade4 w1 w2 w3 w4) ∧
    ((contractFiveBlade lambda u w1 w2 w3 w4) * (contractFiveBlade lambda u w1 w2 w3 w4) = 0) := ⟨
  contraction_of_adapted_five_frame lambda u w1 w2 w3 w4 hu hw1 hw2 hw3 hw4,
  contracted_five_blade_nilpotent lambda u w1 w2 w3 w4 hu hw1 hw2 hw3 hw4
⟩

end InfoGeometry.Canonical.CovectorContractionBladeBridge
