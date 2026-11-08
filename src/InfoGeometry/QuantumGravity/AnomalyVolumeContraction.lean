import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.QuantumGravity.AnomalyVolumeContraction

open Matrix

/-!
# A finite nilpotent matrix and a trace calculation
This section defines one explicit real matrix depending on a parameter and
computes a trace. It does not define Moore-Penrose or Drazin inverses, a
physical axial anomaly, or a chiral volume operator.
-/

section NilpotentAxialTrace

/-- An explicit parameterized nilpotent matrix used in a finite calculation. -/
def nilpotent_matrix_example (ε : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -- A block 4x4 matrix capturing the nilpotent Jordan structure
  !![0, ε, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, ε;
     0, 0, 0, 0]

/-- A diagonal sign matrix used as a trace weight in this example. -/
def diagonal_sign_weight : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,  0,  0,  0;
     0,  1,  0,  0;
     0,  0, -1,  0;
     0,  0,  0, -1]

/-- The trace of the specified matrix product. -/
def weighted_defect_trace (ε : ℝ) : ℝ :=
  Matrix.trace (diagonal_sign_weight * (nilpotent_matrix_example ε)ᵀ *
    (nilpotent_matrix_example ε))

/-- For this explicit matrix, the diagonal trace of the displayed product is zero. -/
theorem weighted_defect_trace_eq_zero (ε : ℝ) :
    weighted_defect_trace ε = 0 := by
  dsimp [weighted_defect_trace, diagonal_sign_weight, nilpotent_matrix_example,
    Matrix.trace, Matrix.transpose_apply, Matrix.mul_apply]
  simp [Fin.sum_univ_succ]

end NilpotentAxialTrace


/-!
# Levi-Civita contraction and the scalar triple product
This section proves a coordinate identity for three vectors in `Fin 3 → ℝ`.
It does not connect that identity to the preceding trace calculation or to
physical nuclear currents.
-/

section VolumeContraction

abbrev Vec3 := Fin 3 → ℝ

/-- The totally antisymmetric Levi-Civita symbol ε_ijk. -/
def levi_civita (i j k : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then 1
  else if i = 1 ∧ j = 2 ∧ k = 0 then 1
  else if i = 2 ∧ j = 0 ∧ k = 1 then 1
  else if i = 2 ∧ j = 1 ∧ k = 0 then -1
  else if i = 1 ∧ j = 0 ∧ k = 2 then -1
  else if i = 0 ∧ j = 2 ∧ k = 1 then -1
  else 0

/-- The full contraction of the Levi-Civita tensor with three arbitrary 3-vectors.
    Σ_{i,j,k} ε_ijk * A^i * B^j * C^k. -/
def tensor_contraction (A B C : Vec3) : ℝ :=
  (A 0 * B 1 * C 2) + (A 1 * B 2 * C 0) + (A 2 * B 0 * C 1) -
  (A 2 * B 1 * C 0) - (A 1 * B 0 * C 2) - (A 0 * B 2 * C 1)

/-- The standard scalar triple product: A · (B × C). -/
def scalar_triple_product (A B C : Vec3) : ℝ :=
  A 0 * (B 1 * C 2 - B 2 * C 1) +
  A 1 * (B 2 * C 0 - B 0 * C 2) +
  A 2 * (B 0 * C 1 - B 1 * C 0)

/-- The coordinate Levi-Civita contraction equals the scalar triple product. -/
theorem levi_civita_is_scalar_triple_product (A B C : Vec3) :
    tensor_contraction A B C = scalar_triple_product A B C := by
  dsimp [tensor_contraction, scalar_triple_product]
  ring

end VolumeContraction


/-!
# Scalar triple-product readout
This section packages the scalar triple product for a record of three real
vectors and proves its vanishing under a collinearity hypothesis. The record
does not encode a spacetime or a physical mass gap.
-/

section EmergentChiralVolume

/-- The physical state of the rotating triaxial nucleus. -/
structure NuclearDroplet where
  omega_coll : Vec3
  j_proton : Vec3
  j_neutron : Vec3

/-- Scalar triple-product readout of the three vector fields. -/
def scalar_triple_readout (N : NuclearDroplet) : ℝ :=
  scalar_triple_product N.omega_coll N.j_proton N.j_neutron

/-- The scalar triple-product readout equals its Levi-Civita contraction. -/
theorem scalar_triple_readout_eq_contraction (N : NuclearDroplet) :
    scalar_triple_readout N = tensor_contraction N.omega_coll N.j_proton N.j_neutron := by
  rw [levi_civita_is_scalar_triple_product]
  rfl

/-- Collinear second and third vectors make the scalar triple contraction zero. -/
theorem scalar_triple_contraction_eq_zero_of_collinear
    (N : NuclearDroplet) (c : ℝ)
    (h_collinear : ∀ i, N.j_neutron i = c * N.j_proton i) :
    tensor_contraction N.omega_coll N.j_proton N.j_neutron = 0 := by
  dsimp [tensor_contraction]
  have h0 : N.j_neutron 0 = c * N.j_proton 0 := h_collinear 0
  have h1 : N.j_neutron 1 = c * N.j_proton 1 := h_collinear 1
  have h2 : N.j_neutron 2 = c * N.j_proton 2 := h_collinear 2
  rw [h0, h1, h2]
  ring

end EmergentChiralVolume

end InfoGeometry.QuantumGravity.AnomalyVolumeContraction
