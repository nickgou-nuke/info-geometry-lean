/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ChiralityAlgebra
import InfoGeometry.Clifford.Cl11ColimitDimension
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

/-!
# Jordan--Wigner graded differentials on the infinite algebraic colimit

The stage and site indices select a charge; each endomorphism acts on every
element of the existing `Cl11TensorTowerLimit.Limit`. Its infinite dimension
is established separately by `Cl11ColimitDimension.not_finiteDimensional`.
The operators use the actual global chirality action and ordered products.

Creation square-zero and the same-site CAR relation give a nonzero differential
and a square-zero contracting homotopy. Their anticommutator is the identity,
so the differential's range equals its kernel. This is an algebraic contraction
with zero projection. No norm, Hilbert adjoint, vacuum, or spectral gap is asserted.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11GradedDifferential

open Cl11TensorTower Cl11TensorTowerLimit Cl11ChiralityAlgebra
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

/-- Exact finite-representative readback, retaining both multiplication orders. -/
theorem gradedAdjoint_ofStage (n : ℕ) (Q X : Stage n) :
    gradedAdjoint limitChiralityAlgEquiv (ofStage n Q) (ofStage n X) =
      ofStage n (Q * X - (globalChirality n * X * globalChirality n) * Q) := by
  simp only [gradedAdjoint_apply, limitChiralityAlgEquiv_apply,
    limitChiralityConj_ofStage, ofStage_sub, ofStage_mul]

/-- The creation charge induces a native endomorphism of the entire colimit. -/
def jwDifferential (n : ℕ) (k : Fin n) : Module.End ℝ Limit :=
  gradedAdjoint limitChiralityAlgEquiv (ofStage n (jwCreation n k))

/-- Nilpotency follows from the charge square, in addition to its oddness. -/
theorem jwDifferential_sq (n : ℕ) (k : Fin n) :
    jwDifferential n k * jwDifferential n k = 0 := by
  have hsq : ofStage n (jwCreation n k) * ofStage n (jwCreation n k) = 0 :=
    limit_square_zero (InfoGeometry.Canonical.Cl55WittCAR.creation_sq n k)
  unfold jwDifferential
  rw [gradedAdjoint_square limitChiralityAlgEquiv
    limitChiralityConj_involutive _ (limitChiralityConj_jwCreation n k)]
  simp [hsq]

/-- The actual annihilation generator detects the nonzero differential. -/
theorem jwDifferential_annihilation (n : ℕ) (k : Fin n) :
    jwDifferential n k (ofStage n (jwAnnihilation n k)) = 1 := by
  unfold jwDifferential
  rw [gradedAdjoint_of_odd limitChiralityAlgEquiv _ _
    (limitChiralityConj_jwAnnihilation n k)]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add,
    InfoGeometry.Canonical.Cl55WittCAR.same_site_car, ofStage_one]

theorem jwDifferential_ne_zero (n : ℕ) (k : Fin n) : jwDifferential n k ≠ 0 := by
  intro h
  have hz := congrArg (fun T : Module.End ℝ Limit =>
    T (ofStage n (jwAnnihilation n k))) h
  change jwDifferential n k (ofStage n (jwAnnihilation n k)) = 0 at hz
  rw [jwDifferential_annihilation] at hz
  exact one_ne_zero hz

/-- Left multiplication by the matching annihilator contracts the differential. -/
def jwHomotopy (n : ℕ) (k : Fin n) : Module.End ℝ Limit :=
  LinearMap.mulLeft ℝ (ofStage n (jwAnnihilation n k))

theorem jwHomotopy_sq (n : ℕ) (k : Fin n) :
    jwHomotopy n k * jwHomotopy n k = 0 := by
  apply LinearMap.ext
  intro X
  change ofStage n (jwAnnihilation n k) *
    (ofStage n (jwAnnihilation n k) * X) = 0
  rw [← mul_assoc,
    limit_square_zero (InfoGeometry.Canonical.Cl55WittCAR.annihilation_sq n k), zero_mul]

/-- The graded Leibniz rule and CAR give an identity on every colimit element. -/
theorem jwDifferential_homotopy (n : ℕ) (k : Fin n) :
    jwDifferential n k * jwHomotopy n k +
      jwHomotopy n k * jwDifferential n k = 1 := by
  apply LinearMap.ext
  intro X
  change jwDifferential n k (ofStage n (jwAnnihilation n k) * X) +
    ofStage n (jwAnnihilation n k) * jwDifferential n k X = X
  have hder := gradedAdjoint_leibniz limitChiralityAlgEquiv
    (ofStage n (jwCreation n k)) (ofStage n (jwAnnihilation n k)) X
  change jwDifferential n k (ofStage n (jwAnnihilation n k) * X) =
    jwDifferential n k (ofStage n (jwAnnihilation n k)) * X +
      limitChiralityConj (ofStage n (jwAnnihilation n k)) * jwDifferential n k X at hder
  rw [hder, jwDifferential_annihilation, limitChiralityConj_jwAnnihilation,
    one_mul, neg_mul]
  abel

/-- Every closed element has the explicit primitive supplied by the homotopy. -/
theorem jwDifferential_range_eq_ker (n : ℕ) (k : Fin n) :
    LinearMap.range (jwDifferential n k) = LinearMap.ker (jwDifferential n k) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (jwDifferential_sq n k)
  · intro X hX
    apply LinearMap.mem_range.mpr
    refine ⟨jwHomotopy n k X, ?_⟩
    have hcon := congrArg (fun T : Module.End ℝ Limit => T X)
      (jwDifferential_homotopy n k)
    change jwDifferential n k (jwHomotopy n k X) +
      jwHomotopy n k (jwDifferential n k X) = X at hcon
    have hzero : jwDifferential n k X = 0 := LinearMap.mem_ker.mp hX
    rw [hzero, map_zero, add_zero] at hcon
    exact hcon

end InfoGeometry.Clifford.Cl11GradedDifferential
