/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CanonicalNormalOrdering
import InfoGeometry.Projective.ExteriorBladeIncidence
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Faithful exterior operators and geometric incidence

The existing `create` and `annih` act on the whole native exterior algebra.
An independent frame defines a nonzero regular operator, and composition with
creation detects precisely the span of that frame. Native matrix transport
represents the full endomorphism algebra. The two ordered creation/contraction
products are separated on the vacuum, including in characteristic two.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ExteriorOperatorGeometry

open InfoGeometry.Canonical.CanonicalNormalOrdering
open InfoGeometry.Projective.ExteriorBladeIncidence

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Left exterior multiplication by the blade of an ordered finite frame. -/
def bladeOperator {n : ℕ} (v : Fin n → V) : Module.End K (ExteriorAlgebra K V) :=
  Algebra.lmul K (ExteriorAlgebra K V) (ExteriorAlgebra.ιMulti K n v)

@[simp] theorem bladeOperator_apply {n : ℕ} (v : Fin n → V)
    (ω : ExteriorAlgebra K V) :
    bladeOperator v ω = ExteriorAlgebra.ιMulti K n v * ω := rfl

/-- An operator made from a frame vanishes exactly when the frame is dependent. -/
theorem bladeOperator_eq_zero_iff {n : ℕ} (v : Fin n → V) :
    bladeOperator (K := K) v = 0 ↔ ¬LinearIndependent K v := by
  constructor
  · intro h
    apply (ιMulti_eq_zero_iff v).1
    have h1 := LinearMap.congr_fun h (1 : ExteriorAlgebra K V)
    simpa only [bladeOperator_apply, mul_one, LinearMap.zero_apply] using h1
  · intro h
    simp only [bladeOperator, (ιMulti_eq_zero_iff v).2 h, map_zero]

/-- The ordered composition is the regular action of the ordered exterior blade. -/
theorem bladeOperator_eq_prod {n : ℕ} (v : Fin n → V) :
    bladeOperator v = (List.ofFn fun i => create (R := K) (v i)).prod := by
  induction n with
  | zero =>
    simp only [bladeOperator, ExteriorAlgebra.ιMulti_zero_apply, map_one,
      List.ofFn_zero, List.prod_nil]
  | succ n ih =>
    rw [bladeOperator, ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    change create (R := K) (v 0) * bladeOperator (Matrix.vecTail v) = _
    rw [ih]
    simp only [List.ofFn_succ, List.prod_cons]
    rfl

/-- Exact incidence as composition-zero in the full endomorphism algebra. -/
theorem create_mul_bladeOperator_eq_zero_iff {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent K v) (x : V) :
    create (R := K) x * bladeOperator (K := K) v = 0 ↔
      x ∈ Submodule.span K (Set.range v) := by
  rw [← ι_mul_ιMulti_eq_zero_iff v hv x]
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h (1 : ExteriorAlgebra K V)
    change ExteriorAlgebra.ι K x * (ExteriorAlgebra.ιMulti K n v * 1) = 0 at h1
    simpa only [mul_one] using h1
  · intro h
    change Algebra.lmul K (ExteriorAlgebra K V) (ExteriorAlgebra.ι K x) *
      Algebra.lmul K (ExteriorAlgebra K V) (ExteriorAlgebra.ιMulti K n v) = 0
    rw [← map_mul, h, map_zero]

/-- Simultaneous operator annihilation computes the native geometric intersection. -/
theorem mem_span_inf_iff_operator {m n : ℕ} (v : Fin m → V) (w : Fin n → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) (x : V) :
    x ∈ Submodule.span K (Set.range v) ⊓ Submodule.span K (Set.range w) ↔
      create (R := K) x * bladeOperator v = 0 ∧
        create (R := K) x * bladeOperator w = 0 := by
  rw [Submodule.mem_inf, create_mul_bladeOperator_eq_zero_iff v hv,
    create_mul_bladeOperator_eq_zero_iff w hw]

/-- Two independent frame operators have zero product exactly for incident subspaces. -/
theorem bladeOperator_mul_eq_zero_iff {m n : ℕ}
    (v : Fin m → V) (w : Fin n → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    bladeOperator (K := K) v * bladeOperator w = 0 ↔
      ¬Disjoint (Submodule.span K (Set.range v))
        (Submodule.span K (Set.range w)) := by
  have hmul : bladeOperator (K := K) v * bladeOperator w = bladeOperator (Fin.append v w) := by
    simp only [bladeOperator, ← map_mul, ExteriorAlgebra.ιMulti_mul_ιMulti]
  rw [hmul, bladeOperator_eq_zero_iff, linearIndependent_append_iff_disjoint v w hv hw]

/-- Noncommutativity is witnessed on the vacuum, not inferred from a sign rule. -/
theorem annih_mul_create_ne_create_mul_annih
    (d : Module.Dual K V) (v : V) (hd : d v ≠ 0) :
    annih d * create v ≠ create v * annih d := by
  intro h
  have h1 := LinearMap.congr_fun h (1 : ExteriorAlgebra K V)
  change annih d (create v 1) = create v (annih d 1) at h1
  rw [annih_create_vacuum, annih_vacuum, map_zero] at h1
  exact hd ((ExteriorAlgebra.algebraMap_eq_zero_iff V (d v)).1 h1)

/-- Every nonzero mode has a covector giving genuinely noncommuting operators. -/
theorem exists_noncommuting_annihilator {v : V} (hv : v ≠ 0) :
    ∃ d : Module.Dual K V,
      annih d * create v ≠ create v * annih d := by
  obtain ⟨d, hd⟩ := Module.Projective.exists_dual_eq_one K hv
  exact ⟨d, annih_mul_create_ne_create_mul_annih d v (by rw [hd]; exact one_ne_zero)⟩

section Matrices

variable {I : Type*} [Fintype I] [LinearOrder I] (b : Module.Basis I K V)

/-- Finite-basis matrices preserve the existing, constructed CAR relation. -/
theorem matrix_annih_create_CAR (d : Module.Dual K V) (v : V) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (annih d) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create v) +
      LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create v) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (annih d) =
      d v • (1 : Matrix (Finset I) (Finset I) K) := by
  have h := congrArg (LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra)
    (annih_create_anticomm d v)
  simpa only [map_add, map_mul, map_smul, map_one] using h

/-- The full matrix model retains a certified noncommuting pair. -/
theorem matrix_annih_mul_create_ne_create_mul_annih
    (d : Module.Dual K V) (v : V) (hd : d v ≠ 0) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (annih d) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create v) ≠
      LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create v) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (annih d) := by
  intro h
  apply annih_mul_create_ne_create_mul_annih d v hd
  apply (LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra).injective
  simpa only [map_mul] using h

/-- Matrix multiplication-zero is equivalent to actual frame-span membership. -/
theorem matrix_create_mul_blade_eq_zero_iff {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent K v) (x : V) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create x) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (bladeOperator v) = 0 ↔
      x ∈ Submodule.span K (Set.range v) := by
  rw [← create_mul_bladeOperator_eq_zero_iff v hv x, ← map_mul]
  exact (LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra).map_eq_zero_iff

/-- Matrix products detect nontrivial intersection of arbitrary finite frame spans. -/
theorem matrix_blade_mul_eq_zero_iff {m n : ℕ}
    (v : Fin m → V) (w : Fin n → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (bladeOperator v) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (bladeOperator w) = 0 ↔
      ¬Disjoint (Submodule.span K (Set.range v))
        (Submodule.span K (Set.range w)) := by
  rw [← bladeOperator_mul_eq_zero_iff v w hv hw, ← map_mul]
  exact (LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra).map_eq_zero_iff

/-- Arbitrary exterior elements, including inhomogeneous ones, are retained faithfully. -/
theorem regularMatrix_eq_iff (ω η : ExteriorAlgebra K V) :
    Algebra.leftMulMatrix b.ExteriorAlgebra ω =
      Algebra.leftMulMatrix b.ExteriorAlgebra η ↔ ω = η :=
  (Algebra.leftMulMatrix_injective b.ExteriorAlgebra).eq_iff

/-- The frame operator's matrix is precisely native left exterior multiplication. -/
theorem matrix_bladeOperator {n : ℕ} (v : Fin n → V) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (bladeOperator v) =
      Algebra.leftMulMatrix b.ExteriorAlgebra (ExteriorAlgebra.ιMulti K n v) := rfl

/-- The vacuum criterion also proves noncommutativity for each basis mode. -/
theorem matrix_basis_mode_noncommuting (i : I) :
    LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (annih (b.coord i)) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create (b i)) ≠
      LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (create (b i)) *
        LinearMap.toMatrixAlgEquiv b.ExteriorAlgebra (annih (b.coord i)) := by
  apply matrix_annih_mul_create_ne_create_mul_annih b
  simp

end Matrices

end InfoGeometry.OperatorAlgebra.ExteriorOperatorGeometry
