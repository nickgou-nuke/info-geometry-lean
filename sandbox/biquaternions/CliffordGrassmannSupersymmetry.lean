import Mathlib

namespace InfoGeometry.Canonical.SuperSymmetry

open scoped TensorProduct

variable (R : Type*) [CommRing R] 
variable (V : Type*) [AddCommGroup V] [Module R V]
variable (W : Type*) [AddCommGroup W] [Module R W]
variable (Q : QuadraticForm R V)

/--
The Supersymmetric Algebra structurally unites the Clifford algebra (providing the bosonic/spinorial
spacetime structure) with the Grassmann/Exterior algebra (providing the fermionic anti-commuting
variables).
-/
abbrev SuperSymmetryAlgebra :=
  CliffordAlgebra Q ⊗[R] ExteriorAlgebra R W

/--
Embedding the bosonic degrees of freedom (Clifford generators) into the Superalgebra.
-/
def bosonicEmbedding : V →ₗ[R] SuperSymmetryAlgebra R V W Q where
  toFun v := CliffordAlgebra.ι Q v ⊗ₜ[R] (1 : ExteriorAlgebra R W)
  map_add' x y := by simp [TensorProduct.add_tmul]
  map_smul' c x := by 
    simp only [map_smul, RingHom.id_apply]
    exact TensorProduct.smul_tmul c (CliffordAlgebra.ι Q x) 1

/--
Embedding the fermionic degrees of freedom (Grassmann generators) into the Superalgebra.
-/
def fermionicEmbedding : W →ₗ[R] SuperSymmetryAlgebra R V W Q where
  toFun w := (1 : CliffordAlgebra Q) ⊗ₜ[R] ExteriorAlgebra.ι R w
  map_add' x y := by simp [TensorProduct.tmul_add]
  map_smul' c x := by 
    simp only [map_smul, RingHom.id_apply]
    exact TensorProduct.tmul_smul c 1 (ExteriorAlgebra.ι R x)

/--
Bosonic generators satisfy the Clifford metric condition:
{B_x, B_x} = 2 Q(x)
Since we are using the Mathlib definition, B_x * B_x = Q(x).
-/
theorem bosonic_sq (x : V) :
    bosonicEmbedding R V W Q x * bosonicEmbedding R V W Q x = algebraMap R (SuperSymmetryAlgebra R V W Q) (Q x) := by
  have h_eq : (bosonicEmbedding R V W Q x) * (bosonicEmbedding R V W Q x) = (CliffordAlgebra.ι Q x ⊗ₜ[R] (1 : ExteriorAlgebra R W)) * (CliffordAlgebra.ι Q x ⊗ₜ[R] (1 : ExteriorAlgebra R W)) := rfl
  rw [h_eq]
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  have h_one : (1 : ExteriorAlgebra R W) * 1 = 1 := mul_one 1
  rw [h_one]
  have h_cliff : CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q x = algebraMap R (CliffordAlgebra Q) (Q x) :=
    CliffordAlgebra.ι_sq_scalar Q x
  rw [h_cliff]
  exact TensorProduct.algebraMap_apply R R (CliffordAlgebra Q) (ExteriorAlgebra R W) (Q x) |>.symm

/--
Fermionic generators strictly anti-commute and square to 0 (the Grassmann condition).
F_y * F_y = 0
-/
theorem fermionic_sq (y : W) :
    fermionicEmbedding R V W Q y * fermionicEmbedding R V W Q y = 0 := by
  have h_eq : (fermionicEmbedding R V W Q y) * (fermionicEmbedding R V W Q y) = ((1 : CliffordAlgebra Q) ⊗ₜ[R] ExteriorAlgebra.ι R y) * ((1 : CliffordAlgebra Q) ⊗ₜ[R] ExteriorAlgebra.ι R y) := rfl
  rw [h_eq]
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  have h_grassmann : ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R y = 0 :=
    ExteriorAlgebra.ι_sq_zero y
  rw [h_grassmann]
  exact TensorProduct.tmul_zero _ _

/--
Bosonic and Fermionic generators strictly commute across the tensor product boundary.
-/
theorem bosonic_fermionic_commute (x : V) (y : W) :
    bosonicEmbedding R V W Q x * fermionicEmbedding R V W Q y = fermionicEmbedding R V W Q y * bosonicEmbedding R V W Q x := by
  have h_lhs : (bosonicEmbedding R V W Q x) * (fermionicEmbedding R V W Q y) = (CliffordAlgebra.ι Q x ⊗ₜ[R] 1) * (1 ⊗ₜ[R] ExteriorAlgebra.ι R y) := rfl
  have h_rhs : (fermionicEmbedding R V W Q y) * (bosonicEmbedding R V W Q x) = (1 ⊗ₜ[R] ExteriorAlgebra.ι R y) * (CliffordAlgebra.ι Q x ⊗ₜ[R] 1) := rfl
  rw [h_lhs, h_rhs]
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [mul_one, one_mul, one_mul, mul_one]

end InfoGeometry.Canonical.SuperSymmetry
