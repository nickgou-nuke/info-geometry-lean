/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.IndexedArnoldKZComplex
import InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

/-!
# Indexed Arnold--Kohno cancellation in the native exterior algebra

The logarithmic coefficients belong to the base field, the one-forms belong
to Mathlib's exterior algebra, and the residues belong to an independent Lie
algebra. In particular the residue bracket need not vanish.

The coefficient carrier and partial-fraction theorem come from
`IndexedArnoldKZComplex`. The tensor-valued three-channel cancellation comes
from `ArnoldKohnoParaKahlerConnection`. Here the intervening Arnold identity
is proved for actual degree-one exterior elements, without imposing an
alternating multiplication on the entire exterior algebra.

The finite sums below are the ordered triangle and disjoint-pair
contributions. Their identification with the square of a connection, an
exterior-derivative theorem, integration, and monodromy are separate targets.
All statements specialize to real vector spaces and real operator algebras.
-/

noncomputable section

namespace InfoGeometry.Canonical.IndexedArnoldKohnoExterior

open scoped BigOperators TensorProduct
open InfoGeometry.Canonical.IndexedArnoldKZComplex
open InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

section Exterior

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The cyclic products of three degree-one differences agree. This only
uses exterior-algebra multiplication on images of `ExteriorAlgebra.ι`. -/
theorem exterior_difference_products (u v w : M) :
    ExteriorAlgebra.ι K (v - w) * ExteriorAlgebra.ι K (w - u) =
        ExteriorAlgebra.ι K (u - v) * ExteriorAlgebra.ι K (v - w) ∧
      ExteriorAlgebra.ι K (w - u) * ExteriorAlgebra.ι K (u - v) =
        ExteriorAlgebra.ι K (u - v) * ExteriorAlgebra.ι K (v - w) := by
  have hsum : ExteriorAlgebra.ι K (w - u) =
      -(ExteriorAlgebra.ι K (u - v) + ExteriorAlgebra.ι K (v - w)) := by
    rw [← map_add, ← map_neg]
    congr 1
    abel
  have hswap : ExteriorAlgebra.ι K (v - w) * ExteriorAlgebra.ι K (u - v) =
      -(ExteriorAlgebra.ι K (u - v) * ExteriorAlgebra.ι K (v - w)) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (v - w) (u - v))
  constructor
  · rw [hsum, mul_neg, mul_add, ExteriorAlgebra.ι_sq_zero, add_zero,
      hswap, neg_neg]
  · rw [hsum, neg_mul, add_mul, ExteriorAlgebra.ι_sq_zero, zero_add,
      hswap, neg_neg]

/-- The algebraic logarithmic one-form, embedded in Mathlib's exterior algebra.
`dz` specifies the degree-one generators; no analytic derivative is assumed. -/
def dlogExterior {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (i j : Fin n) : ExteriorAlgebra K M :=
  dlogCoefficient z i j • ExteriorAlgebra.ι K (dz i - dz j)

@[simp] theorem dlogExterior_self {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (i : Fin n) : dlogExterior z dz i i = 0 := by
  simp [dlogExterior]

/-- Concrete Arnold cancellation in the native exterior algebra, with
nonzero denominators supplied by the injective configuration. -/
theorem dlogExterior_arnold {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    dlogExterior z dz i j * dlogExterior z dz j k +
      dlogExterior z dz j k * dlogExterior z dz k i +
      dlogExterior z dz k i * dlogExterior z dz i j = 0 := by
  dsimp only [dlogExterior]
  simp only [smul_mul_smul]
  rw [(exterior_difference_products (K := K) (dz i) (dz j) (dz k)).1,
    (exterior_difference_products (K := K) (dz i) (dz j) (dz k)).2]
  rw [← add_smul, ← add_smul, dlog_partial_fraction z hij hjk hik, zero_smul]

end Exterior

section LieResidues

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M]

/-- Operator-valued triangle contribution. The Lie carrier `L` is independent
of both the scalar coefficients and the exterior-algebra carrier. -/
def triangleContribution {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L) (i j k : Fin n) :
    L ⊗[K] ExteriorAlgebra K M :=
  triangleCurvature (T i j) (T j k) (T k i)
    (dlogExterior z dz i j) (dlogExterior z dz j k) (dlogExterior z dz k i)

/-- The native Arnold relation and the two relevant Kohno relations cancel
each triangle, without assuming pairwise commutation of its residues. -/
theorem triangleContribution_eq_zero {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L)
    (hsym : ∀ i j, T i j = T j i)
    (hshared : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ⁅T i j, T i k + T j k⁆ = 0)
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    triangleContribution z dz T i j k = 0 := by
  have hx : ⁅T i j, T k i + T j k⁆ = 0 := by
    rw [hsym k i]
    exact hshared i j k hij hik hjk
  have hy : ⁅T j k, T i j + T k i⁆ = 0 := by
    rw [hsym i j]
    exact hshared j k i hjk hij.symm hik.symm
  exact arnold_kohno_triangle_flat (T i j) (T j k) (T k i)
    (dlogExterior z dz i j) (dlogExterior z dz j k) (dlogExterior z dz k i)
    (dlogExterior_arnold z dz hij hjk hik) hx hy

/-- The sum of all ordered triangle contributions, omitting repeated indices. -/
def totalTriangleContribution {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L) : L ⊗[K] ExteriorAlgebra K M :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    if i ≠ j ∧ j ≠ k ∧ i ≠ k then triangleContribution z dz T i j k else 0

/-- Cancellation of the full finite ordered triangle sum. -/
theorem totalTriangleContribution_eq_zero {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L)
    (hsym : ∀ i j, T i j = T j i)
    (hshared : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ⁅T i j, T i k + T j k⁆ = 0) :
    totalTriangleContribution z dz T = 0 := by
  unfold totalTriangleContribution
  refine Finset.sum_eq_zero fun i _ => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  split
  · rename_i h
    exact triangleContribution_eq_zero z dz T hsym hshared h.1 h.2.1 h.2.2
  · rfl

/-- An operator-valued contribution from two disjoint edges. -/
def disjointContribution {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L) (i j k l : Fin n) :
    L ⊗[K] ExteriorAlgebra K M :=
  ⁅T i j, T k l⁆ ⊗ₜ[K] (dlogExterior z dz i j * dlogExterior z dz k l)

/-- The disjoint-edge Kohno relation kills the corresponding tensor. -/
theorem disjointContribution_eq_zero {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L) {i j k l : Fin n}
    (hcomm : ⁅T i j, T k l⁆ = 0) :
    disjointContribution z dz T i j k l = 0 := by
  simp only [disjointContribution, hcomm, TensorProduct.zero_tmul]

/-- All ordered disjoint-edge contributions, with repeated indices excluded. -/
def totalDisjointContribution {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L) : L ⊗[K] ExteriorAlgebra K M :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
    if i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l then
      disjointContribution z dz T i j k l
    else 0

/-- Cancellation of the full finite ordered disjoint-edge sum. -/
theorem totalDisjointContribution_eq_zero {n : ℕ} (z : Conf n K) (dz : Fin n → M)
    (T : Fin n → Fin n → L)
    (hdisjoint : ∀ i j k l,
      i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
      ⁅T i j, T k l⁆ = 0) :
    totalDisjointContribution z dz T = 0 := by
  unfold totalDisjointContribution
  refine Finset.sum_eq_zero fun i _ => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  refine Finset.sum_eq_zero fun l _ => ?_
  split
  · rename_i h
    exact disjointContribution_eq_zero z dz T
      (hdisjoint i j k l h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
  · rfl

/-- A noncommutative family of three-channel examples: `x` and `y` are
arbitrary, and the third residue is `-(x + y)`. Their individual bracket
is unrestricted; the Kohno relations follow from the zero total residue. -/
theorem triangle_negative_sum_eq_zero (z : Conf 3 K) (dz : Fin 3 → M)
    (x y : L) :
    triangleCurvature x y (-(x + y))
      (dlogExterior z dz 0 1) (dlogExterior z dz 1 2) (dlogExterior z dz 2 0) = 0 := by
  apply arnold_kohno_triangle_flat
  · exact dlogExterior_arnold z dz (by decide) (by decide) (by decide)
  · have h : -(x + y) + y = -x := by abel
    rw [h, lie_neg, lie_self, neg_zero]
  · have h : x + -(x + y) = -y := by abel
    rw [h, lie_neg, lie_self, neg_zero]

end LieResidues

section AssociativeResidues

variable {K A M : Type*} [Field K] [Ring A] [Algebra K A]
  [AddCommGroup M] [Module K M]

attribute [local instance] LieRing.ofAssociativeRing

/-- Existing indexed cyclic commutator data implies the shared-index Kohno
relation on the same associative algebra, viewed as a native Lie algebra. -/
theorem shared_relation_of_indexed_residues {n : ℕ}
    (T : IndexedArnoldKZComplex.InfinitesimalBraidResidues n A)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅T.residue i j, T.residue i k + T.residue j k⁆ = 0 := by
  have hcyclic : ⁅T.residue i j, T.residue j k⁆ =
      ⁅T.residue k i, T.residue i j⁆ :=
    (T.cyclic_commute i j k hij hjk hik).1.trans
      (T.cyclic_commute i j k hij hjk hik).2
  rw [lie_add, T.symmetric i k,
    ← lie_skew (T.residue i j) (T.residue k i), hcyclic]
  exact neg_add_cancel _

/-- The existing indexed associative residues now act in the independent
operator factor of the tensor product, rather than being specialized to the
commutative coefficient field. -/
theorem indexed_residue_contributions_eq_zero {n : ℕ}
    (z : Conf n K) (dz : Fin n → M)
    (T : IndexedArnoldKZComplex.InfinitesimalBraidResidues n A) :
    totalTriangleContribution z dz T.residue = 0 ∧
      totalDisjointContribution z dz T.residue = 0 := by
  constructor
  · exact totalTriangleContribution_eq_zero z dz T.residue T.symmetric
      (shared_relation_of_indexed_residues T)
  · apply totalDisjointContribution_eq_zero z dz T.residue
    intro i j k l hij hkl hik hil hjk hjl
    exact T.disjoint_commute i j k l hij hkl hik hil hjk hjl

end AssociativeResidues

end InfoGeometry.Canonical.IndexedArnoldKohnoExterior
