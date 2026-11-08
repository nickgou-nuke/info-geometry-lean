/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.GenericMetriplecticFlow
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Metriplectic reduction through native bilinear duality

For a nondegenerate form B on W and a linear map A : W → V, construct
A B♯ A* : V* → V. Skewness, symmetry and positivity descend by congruence.
This builds actual GENERIC systems when the two covectors annihilate the
appropriate images. No Jacobi identity for state-dependent operators or
existence of trajectories is asserted.
-/

noncomputable section

namespace InfoGeometry.Thermo.BilinearMetriplecticReduction

open GenericMetriplecticFlow

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- Congruence reduction of the inverse bilinear duality. -/
def reducedSharp (B : LinearMap.BilinForm ℝ W) (hB : B.Nondegenerate)
    (A : W →ₗ[ℝ] V) : Covector V →ₗ[ℝ] V :=
  A.comp ((B.toDual hB).symm.toLinearMap.comp A.dualMap)

theorem reducedSharp_pairing (B : LinearMap.BilinForm ℝ W) (hB : B.Nondegenerate)
    (A : W →ₗ[ℝ] V) (α β : Covector V) :
    α (reducedSharp B hB A β) =
      B ((B.toDual hB).symm (A.dualMap α)) ((B.toDual hB).symm (A.dualMap β)) := by
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  rfl

theorem reducedSharp_skew (B : LinearMap.BilinForm ℝ W) (hB : B.Nondegenerate)
    (hskew : ∀ x y, B x y = -B y x) (A : W →ₗ[ℝ] V) (α β : Covector V) :
    α (reducedSharp B hB A β) = -β (reducedSharp B hB A α) := by
  rw [reducedSharp_pairing, reducedSharp_pairing, hskew]

theorem reducedSharp_symmetric (B : LinearMap.BilinForm ℝ W) (hB : B.Nondegenerate)
    (hsymm : ∀ x y, B x y = B y x) (A : W →ₗ[ℝ] V) (α β : Covector V) :
    α (reducedSharp B hB A β) = β (reducedSharp B hB A α) := by
  rw [reducedSharp_pairing, reducedSharp_pairing, hsymm]

theorem reducedSharp_nonneg (B : LinearMap.BilinForm ℝ W) (hB : B.Nondegenerate)
    (hpos : ∀ x, 0 ≤ B x x) (A : W →ₗ[ℝ] V) (α : Covector V) :
    0 ≤ α (reducedSharp B hB A α) := by
  rw [reducedSharp_pairing]
  exact hpos _

theorem reducedSharp_annihilates (B : LinearMap.BilinForm ℝ W)
    (hB : B.Nondegenerate) (A : W →ₗ[ℝ] V) (α : Covector V)
    (hα : A.dualMap α = 0) : reducedSharp B hB A α = 0 := by
  simp [reducedSharp, hα]

/-- For positive B, reduction kills exactly covectors annihilating the image. -/
theorem reducedSharp_eq_zero_iff (B : LinearMap.BilinForm ℝ W)
    (hB : B.Nondegenerate) (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    (A : W →ₗ[ℝ] V) (α : Covector V) :
    reducedSharp B hB A α = 0 ↔ A.dualMap α = 0 := by
  constructor
  · intro h
    have hz : (B.toDual hB).symm (A.dualMap α) = 0 := by
      by_contra hn
      have hp := hpos _ hn
      rw [← reducedSharp_pairing, h, map_zero] at hp
      exact (lt_irrefl 0) hp
    have := congrArg (B.toDual hB) hz
    simpa using this
  · exact reducedSharp_annihilates B hB A α

/-- Concrete construction from forms and image-annihilation conditions.
No GENERIC law is supplied as an unproved structure field. -/
def system (ω H : LinearMap.BilinForm ℝ W)
    (hω : ω.Nondegenerate) (hH : H.Nondegenerate)
    (hskew : ∀ x y, ω x y = -ω y x) (hsymm : ∀ x y, H x y = H y x)
    (hpos : ∀ x, 0 ≤ H x x) (P C : W →ₗ[ℝ] V) (dH dS : Covector V)
    (hS : P.dualMap dS = 0) (hE : C.dualMap dH = 0) :
    GenericMetriplecticFlow.System V where
  dH := dH
  dS := dS
  L := reducedSharp ω hω P
  M := reducedSharp H hH C
  L_skew := reducedSharp_skew ω hω hskew P
  L_entropy_casimir := reducedSharp_annihilates ω hω P dS hS
  M_symmetric := reducedSharp_symmetric H hH hsymm C
  M_hamiltonian_casimir := reducedSharp_annihilates H hH C dH hE
  M_nonneg := reducedSharp_nonneg H hH hpos C

end InfoGeometry.Thermo.BilinearMetriplecticReduction
