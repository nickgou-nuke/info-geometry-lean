/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-!
# Closed central curvings from the operator Bianchi identity

The carrier is the existing native Chevalley--Eilenberg two-cochain module
of a `DerivationLieLane`.  The connection and its curvature retain their
noncommutative coefficient algebra.  A prescribed curving `B` satisfying
`F + B = 0` is covariantly closed.  If its values commute with the connection
values, it is closed for the original CE differential.

The Lie directions need not commute.  These are local algebraic statements;
no bundle gerbe, integral class, spectral gap, or torsion conclusion is supplied.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- The covariant exterior differential is additive in its two-form argument. -/
theorem covariantExteriorDerivativeTwo_add
    (Γ : OneForm K) (B C : TwoForm K) (x y z : K.L) :
    covariantExteriorDerivativeTwo K Γ (B + C) x y z =
      covariantExteriorDerivativeTwo K Γ B x y z +
        covariantExteriorDerivativeTwo K Γ C x y z := by
  simp only [covariantExteriorDerivativeTwo, map_add, LinearMap.add_apply,
    LieModule.Cohomology.add_apply_apply]
  noncomm_ring

/-- A curving cancelling the connection curvature is covariantly closed. -/
theorem covariant_curving_closed_of_twisted_flat
    (Γ : OneForm K) (B : TwoForm K)
    (hflat : connectionCurvature K Γ + B = 0) (x y z : K.L) :
    covariantExteriorDerivativeTwo K Γ B x y z = 0 := by
  have h := congrArg (fun C : TwoForm K =>
    covariantExteriorDerivativeTwo K Γ C x y z) hflat
  rw [covariantExteriorDerivativeTwo_add, connectionCurvature_bianchi] at h
  have hz (u v : K.L) : (0 : TwoForm K) u v = 0 := rfl
  have hzero : covariantExteriorDerivativeTwo K Γ (0 : TwoForm K) x y z = 0 := by
    simp only [covariantExteriorDerivativeTwo, map_zero, LinearMap.zero_apply, hz,
      mul_zero, zero_mul, sub_zero, add_zero]
  simpa only [zero_add, hzero] using h

/-- Before centrality is imposed, the precise obstruction to ordinary
closedness is the alternating sum of connection--curving commutators. -/
theorem curving_derivative_eq_neg_correction_of_twisted_flat
    (Γ : OneForm K) (B : TwoForm K)
    (hflat : connectionCurvature K Γ + B = 0) (x y z : K.L) :
    exteriorDerivativeTwo K B x y z =
      -((Γ x * B y z - B y z * Γ x) -
          (Γ y * B x z - B x z * Γ y) +
            (Γ z * B x y - B x y * Γ z)) := by
  apply eq_neg_iff_add_eq_zero.mpr
  calc
    _ = covariantExteriorDerivativeTwo K Γ B x y z := by
      unfold covariantExteriorDerivativeTwo
      abel
    _ = 0 := covariant_curving_closed_of_twisted_flat K Γ B hflat x y z

/-- Centrality relative to the connection values removes the commutator
correction.  No abelian hypothesis on the derivation Lie algebra is used. -/
theorem central_curving_closed_of_twisted_flat
    (Γ : OneForm K) (B : TwoForm K)
    (hflat : connectionCurvature K Γ + B = 0)
    (hcentral : ∀ x y z : K.L, Commute (Γ x) (B y z)) :
    exteriorDerivativeTwo K B = 0 := by
  ext x y z
  change exteriorDerivativeTwo K B x y z = 0
  have h := covariant_curving_closed_of_twisted_flat K Γ B hflat x y z
  simpa only [covariantExteriorDerivativeTwo, (hcentral x y z).eq,
    (hcentral y x z).eq, (hcentral z x y).eq, sub_self, add_zero, sub_zero] using h

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
