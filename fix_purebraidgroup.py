import subprocess

lean_code = """
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

namespace ArtinPureBraid

variable {G : Type*} [Group G]

/-! ### 1. Universal Group Inversion & Conjugation Lemmas -/

/-- Core Group Identity:
    (Y * Z)⁻¹ * Y * (Y * Z) collapses identically to Z⁻¹ * Y * Z. -/
theorem conj_by_mul_self (Y Z : G) :
    (Y * Z)⁻¹ * Y * (Y * Z) = Z⁻¹ * Y * Z := by
  group

/-- Commutative inversion lemma:
    If a and b commute, then b and a⁻¹ commute. -/
lemma comm_inv_of_comm {a b : G} (h : a * b = b * a) :
    b * a⁻¹ = a⁻¹ * b := by
  have h1 : a⁻¹ * (a * b) * a⁻¹ = a⁻¹ * (b * a) * a⁻¹ := by rw [h]
  calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
  _ = a⁻¹ * (b * a) * a⁻¹ := h1
  _ = a⁻¹ * b := by group

/-! ### 2. The Artin Pure Braid Triple Structure -/

/-- An Artin Pure Braid Triple (A_{i, j}, A_{i, k}, A_{j, k}) in a group G,
    representing three strands i < j < k. -/
structure PureBraidTriple (G : Type*) [Group G] where
  A_ij : G
  A_ik : G
  A_jk : G
  cyclic_one : A_ij * A_ik * A_jk = A_ik * A_jk * A_ij
  cyclic_two : A_ik * A_jk * A_ij = A_jk * A_ij * A_ik

namespace PureBraidTriple

variable (t : PureBraidTriple G)

/-- Third cyclic branch: Z * X * Y = X * Y * Z. -/
theorem cyclic_three :
    t.A_jk * t.A_ij * t.A_ik = t.A_ij * t.A_ik * t.A_jk := by
  rw [t.cyclic_one, t.cyclic_two]

/-- Commutation of A_{i, j} with the product (A_{i, k} * A_{j, k}). -/
theorem comm_ij_ik_jk :
    t.A_ij * (t.A_ik * t.A_jk) = (t.A_ik * t.A_jk) * t.A_ij := by
  have h := t.cyclic_one
  calc t.A_ij * (t.A_ik * t.A_jk) = t.A_ij * t.A_ik * t.A_jk := by group
  _ = t.A_ik * t.A_jk * t.A_ij := h
  _ = (t.A_ik * t.A_jk) * t.A_ij := by group

/-- Commutation of A_{j, k} with the product (A_{i, j} * A_{i, k}). -/
theorem comm_jk_ij_ik :
    t.A_jk * (t.A_ij * t.A_ik) = (t.A_ij * t.A_ik) * t.A_jk := by
  have h := t.cyclic_three
  calc t.A_jk * (t.A_ij * t.A_ik) = t.A_jk * t.A_ij * t.A_ik := by group
  _ = t.A_ij * t.A_ik * t.A_jk := h
  _ = (t.A_ij * t.A_ik) * t.A_jk := by group

/-- Commutation of A_{i, k} with the product (t.A_jk * t.A_ij). -/
theorem comm_ik_jk_ij :
    t.A_ik * (t.A_jk * t.A_ij) = (t.A_jk * t.A_ij) * t.A_ik := by
  have h := t.cyclic_two
  calc t.A_ik * (t.A_jk * t.A_ij) = t.A_ik * t.A_jk * t.A_ij := by group
  _ = t.A_jk * t.A_ij * t.A_ik := h
  _ = (t.A_jk * t.A_ij) * t.A_ik := by group

/-! ### 3. The Non-Linear Artin Crossing Relations -/

/-- Primary Non-Linear Crossing Relation (Artin Form):
    A_{i, j} * A_{i, k} * A_{i, j}⁻¹ = A_{j, k}⁻¹ * A_{i, k} * A_{j, k}. -/
theorem artin_crossing_Y :
    t.A_ij * t.A_ik * t.A_ij⁻¹ = t.A_jk⁻¹ * t.A_ik * t.A_jk := by
  have h_comm := t.comm_ik_jk_ij
  calc t.A_ij * t.A_ik * t.A_ij⁻¹
      = t.A_jk⁻¹ * ((t.A_jk * t.A_ij) * t.A_ik) * t.A_ij⁻¹ := by group
    _ = t.A_jk⁻¹ * (t.A_ik * (t.A_jk * t.A_ij)) * t.A_ij⁻¹ := by rw [← h_comm]
    _ = t.A_jk⁻¹ * t.A_ik * t.A_jk := by group

/-- Factored Associator Form (Birman Form):
    A_{i, j} * A_{i, k} * A_{i, j}⁻¹ = (A_{i, k} * A_{j, k})⁻¹ * A_{i, k} * (A_{i, k} * A_{j, k}). -/
theorem artin_crossing_Y_factored :
    t.A_ij * t.A_ik * t.A_ij⁻¹ =
      (t.A_ik * t.A_jk)⁻¹ * t.A_ik * (t.A_ik * t.A_jk) := by
  rw [conj_by_mul_self]
  exact t.artin_crossing_Y

/-- Inverted Conjugation Form:
    A_{i, j}⁻¹ * A_{i, k} * A_{i, j} = (A_{i, k} * A_{j, k}) * A_{i, k} * (A_{i, k} * A_{j, k})⁻¹. -/
theorem artin_crossing_Y_inv :
    t.A_ij⁻¹ * t.A_ik * t.A_ij =
      (t.A_ik * t.A_jk) * t.A_ik * (t.A_ik * t.A_jk)⁻¹ := by
  set W := t.A_ik * t.A_jk
  have h_comm : t.A_ij * W = W * t.A_ij := t.comm_ij_ik_jk
  have h_inv : W * t.A_ij⁻¹ = t.A_ij⁻¹ * W := comm_inv_of_comm h_comm
  have h_inv2 : t.A_ij * W⁻¹ = W⁻¹ * t.A_ij := comm_inv_of_comm h_comm.symm
  have h_cross : t.A_ij * t.A_ik * t.A_ij⁻¹ = W⁻¹ * t.A_ik * W := t.artin_crossing_Y_factored
  calc t.A_ij⁻¹ * t.A_ik * t.A_ij
      = t.A_ij⁻¹ * W * W⁻¹ * t.A_ik * W * W⁻¹ * t.A_ij := by group
    _ = W * t.A_ij⁻¹ * W⁻¹ * t.A_ik * W * W⁻¹ * t.A_ij := by rw [← h_inv]
    _ = W * t.A_ij⁻¹ * (W⁻¹ * t.A_ik * W) * (W⁻¹ * t.A_ij) := by group
    _ = W * t.A_ij⁻¹ * (W⁻¹ * t.A_ik * W) * (t.A_ij * W⁻¹) := by rw [← h_inv2]
    _ = W * (t.A_ij⁻¹ * (W⁻¹ * t.A_ik * W) * t.A_ij) * W⁻¹ := by group
    _ = W * (t.A_ij⁻¹ * (t.A_ij * t.A_ik * t.A_ij⁻¹) * t.A_ij) * W⁻¹ := by rw [← h_cross]
    _ = W * t.A_ik * W⁻¹ := by group

/-- Complementary Crossing Relation on A_{j, k}:
    A_{i, j}⁻¹ * A_{j, k} * A_{i, j} = A_{i, k} * A_{j, k} * A_{i, k}⁻¹. -/
theorem artin_crossing_Z :
    t.A_ij⁻¹ * t.A_jk * t.A_ij = t.A_ik * t.A_jk * t.A_ik⁻¹ := by
  have h_comm := t.comm_jk_ij_ik
  calc t.A_ij⁻¹ * t.A_jk * t.A_ij
      = t.A_ij⁻¹ * (t.A_jk * (t.A_ij * t.A_ik)) * t.A_ik⁻¹ := by group
    _ = t.A_ij⁻¹ * ((t.A_ij * t.A_ik) * t.A_jk) * t.A_ik⁻¹ := by rw [h_comm]
    _ = t.A_ik * t.A_jk * t.A_ik⁻¹ := by group

/-- Complementary Crossing Relation on A_{i, j}:
    A_{i, k}⁻¹ * A_{i, j} * A_{i, k} = A_{j, k} * A_{i, j} * A_{j, k}⁻¹. -/
theorem artin_crossing_X :
    t.A_ik⁻¹ * t.A_ij * t.A_ik = t.A_jk * t.A_ij * t.A_jk⁻¹ := by
  have h_comm := t.comm_ij_ik_jk
  calc t.A_ik⁻¹ * t.A_ij * t.A_ik
      = t.A_ik⁻¹ * (t.A_ij * (t.A_ik * t.A_jk)) * t.A_jk⁻¹ := by group
    _ = t.A_ik⁻¹ * ((t.A_ik * t.A_jk) * t.A_ij) * t.A_jk⁻¹ := by rw [h_comm]
    _ = t.A_jk * t.A_ij * t.A_jk⁻¹ := by group

end PureBraidTriple

/-! ### 4. Specialization to Matrix Representations GL(d, R) -/

variable {d : ℕ} {R : Type*} [CommRing R]

/-- Any representation ρ : PB_n → GL(d, R) satisfies the non-linear crossing relations. -/
theorem matrix_pure_braid_crossing
    (M_ij M_ik M_jk : Matrix.GeneralLinearGroup (Fin d) R)
    (h1 : M_ij * M_ik * M_jk = M_ik * M_jk * M_ij)
    (h2 : M_ik * M_jk * M_ij = M_jk * M_ij * M_ik) :
    M_ij * M_ik * M_ij⁻¹ = M_jk⁻¹ * M_ik * M_jk := by
  let t : PureBraidTriple (Matrix.GeneralLinearGroup (Fin d) R) :=
    { A_ij := M_ij
      A_ik := M_ik
      A_jk := M_jk
      cyclic_one := h1
      cyclic_two := h2 }
  exact t.artin_crossing_Y

end ArtinPureBraid
"""
with open("lean/InfoGeometry/Topology/PureBraidGroup.lean", "w") as f:
    f.write(lean_code)

res = subprocess.run(["lake", "env", "lean", "lean/InfoGeometry/Topology/PureBraidGroup.lean"], capture_output=True, text=True)
if res.returncode == 0:
    subprocess.run(["sed", "-i", "2iimport InfoGeometry.Topology.PureBraidGroup", "lean/InfoGeometry/Topology/All.lean"])
    subprocess.run(["git", "add", "lean/InfoGeometry/Topology/PureBraidGroup.lean", "lean/InfoGeometry/Topology/All.lean"])
    subprocess.run(["git", "commit", "-m", "feat(Topology): Formalize Artin Pure Braid Group Crossing Relations"])
print(res.stdout)
