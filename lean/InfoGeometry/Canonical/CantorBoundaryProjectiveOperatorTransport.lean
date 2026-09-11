import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFBoundaryOperatorTopology
import InfoGeometry.Canonical.UHFBoundaryFunctionOperatorTopCat

/-!
# Projective-limit transport of the binary Cantor boundary operators

The binary stream boundary and the categorical prefix inverse limit are
already canonically isomorphic.  This file records the operator readout on
the inverse-limit carrier by pullback along that isomorphism.  It does not
construct a new boundary, completion, or operator-algebraic state.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryProjectiveOperatorTransport

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFBoundaryOperatorTopology
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

abbrev InverseLimitBoundary := ↑(limit prefixDiagram)
abbrev BoundaryFunction := (ℕ → Bool) → ℂ
abbrev InverseLimitFunction := InverseLimitBoundary → ℂ
abbrev BoundaryContinuousFunction := C((ℕ → Bool), ℂ)
abbrev InverseLimitContinuousFunction := C(InverseLimitBoundary, ℂ)

def inverseLimitPullback (f : BoundaryFunction) : InverseLimitFunction :=
  fun z => f (prefixBoundaryLimitIso.inv.hom z)

def inverseLimitPushforward (g : InverseLimitFunction) : BoundaryFunction :=
  fun x => g (prefixBoundaryLimitIso.hom.hom x)

noncomputable def inverseLimitContinuousPullback
    (f : BoundaryContinuousFunction) : InverseLimitContinuousFunction :=
  { toFun := inverseLimitPullback f
    continuous_toFun := f.continuous.comp prefixBoundaryLimitIso.inv.hom.continuous }

noncomputable def inverseLimitContinuousPushforward
    (g : InverseLimitContinuousFunction) : BoundaryContinuousFunction :=
  { toFun := inverseLimitPushforward g
    continuous_toFun := g.continuous.comp prefixBoundaryLimitIso.hom.hom.continuous }

noncomputable def inverseLimitContinuousS_L
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (S_L_continuousMap (inverseLimitContinuousPushforward g))

noncomputable def inverseLimitContinuousS_R
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (S_R_continuousMap (inverseLimitContinuousPushforward g))

noncomputable def inverseLimitContinuousStarS_L
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (star_S_L_continuousMap (inverseLimitContinuousPushforward g))

noncomputable def inverseLimitContinuousStarS_R
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (star_S_R_continuousMap (inverseLimitContinuousPushforward g))

def inverseLimitS_L (g : InverseLimitFunction) : InverseLimitFunction :=
  inverseLimitPullback (S_L_op (inverseLimitPushforward g))

def inverseLimitS_R (g : InverseLimitFunction) : InverseLimitFunction :=
  inverseLimitPullback (S_R_op (inverseLimitPushforward g))

def inverseLimitStarS_L (g : InverseLimitFunction) : InverseLimitFunction :=
  inverseLimitPullback (star_S_L_op (inverseLimitPushforward g))

def inverseLimitStarS_R (g : InverseLimitFunction) : InverseLimitFunction :=
  inverseLimitPullback (star_S_R_op (inverseLimitPushforward g))

theorem inverseLimitPullback_apply
    (f : BoundaryFunction) (z : InverseLimitBoundary) :
    inverseLimitPullback f z = f (prefixBoundaryLimitIso.inv.hom z) :=
  rfl

@[simp] theorem inverseLimitContinuousPullback_apply
    (f : BoundaryContinuousFunction) (z : InverseLimitBoundary) :
    inverseLimitContinuousPullback f z =
      f (prefixBoundaryLimitIso.inv.hom z) := rfl

@[simp] theorem inverseLimitContinuousPushforward_apply
    (g : InverseLimitContinuousFunction) (x : ℕ → Bool) :
    inverseLimitContinuousPushforward g x =
      g (prefixBoundaryLimitIso.hom.hom x) := rfl

theorem inverseLimitContinuousPullback_pushforward
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousPullback
        (inverseLimitContinuousPushforward g) = g := by
  apply ContinuousMap.ext
  intro z
  change inverseLimitPullback (inverseLimitPushforward (g : InverseLimitFunction)) z = g z
  change g (prefixBoundaryLimitIso.hom.hom
      (prefixBoundaryLimitIso.inv.hom z)) = g z
  simp

theorem inverseLimitContinuousPushforward_pullback
    (f : BoundaryContinuousFunction) :
    inverseLimitContinuousPushforward
        (inverseLimitContinuousPullback f) = f := by
  apply ContinuousMap.ext
  intro x
  change inverseLimitPushforward (inverseLimitPullback (f : BoundaryFunction)) x = f x
  change f (prefixBoundaryLimitIso.inv.hom
      (prefixBoundaryLimitIso.hom.hom x)) = f x
  simp

theorem inverseLimitContinuousPullback_intertwines_S_L
    (f : BoundaryContinuousFunction) :
    inverseLimitContinuousS_L (inverseLimitContinuousPullback f) =
      inverseLimitContinuousPullback (S_L_continuousMap f) := by
  rw [inverseLimitContinuousS_L,
    inverseLimitContinuousPushforward_pullback]

theorem inverseLimitContinuousPullback_intertwines_S_R
    (f : BoundaryContinuousFunction) :
    inverseLimitContinuousS_R (inverseLimitContinuousPullback f) =
      inverseLimitContinuousPullback (S_R_continuousMap f) := by
  rw [inverseLimitContinuousS_R,
    inverseLimitContinuousPushforward_pullback]

theorem inverseLimitContinuousPullback_intertwines_star_S_L
    (f : BoundaryContinuousFunction) :
    inverseLimitContinuousStarS_L (inverseLimitContinuousPullback f) =
      inverseLimitContinuousPullback (star_S_L_continuousMap f) := by
  rw [inverseLimitContinuousStarS_L,
    inverseLimitContinuousPushforward_pullback]

theorem inverseLimitContinuousPullback_intertwines_star_S_R
    (f : BoundaryContinuousFunction) :
    inverseLimitContinuousStarS_R (inverseLimitContinuousPullback f) =
      inverseLimitContinuousPullback (star_S_R_continuousMap f) := by
  rw [inverseLimitContinuousStarS_R,
    inverseLimitContinuousPushforward_pullback]

noncomputable def inverseLimitContinuousBoundaryOp
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (UHF_boundary_continuousMap (inverseLimitContinuousPushforward g))

noncomputable def inverseLimitContinuousStarBoundaryOp
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (star_UHF_boundary_continuousMap (inverseLimitContinuousPushforward g))

theorem inverseLimitContinuousBoundaryOp_sq
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousBoundaryOp
        (inverseLimitContinuousBoundaryOp g) = 0 := by
  simp only [inverseLimitContinuousBoundaryOp]
  rw [inverseLimitContinuousPushforward_pullback]
  rw [UHF_boundary_continuousMap_sq_zero]
  rfl

theorem inverseLimitContinuousStarBoundaryOp_sq
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousStarBoundaryOp
        (inverseLimitContinuousStarBoundaryOp g) = 0 := by
  simp only [inverseLimitContinuousStarBoundaryOp]
  rw [inverseLimitContinuousPushforward_pullback]
  rw [star_UHF_boundary_continuousMap_sq_zero]
  rfl

noncomputable def inverseLimitContinuousLaplacian
    (g : InverseLimitContinuousFunction) : InverseLimitContinuousFunction :=
  inverseLimitContinuousPullback
    (UHF_Laplacian_continuousMap (inverseLimitContinuousPushforward g))

theorem inverseLimitContinuousLaplacian_eq_id
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousLaplacian g = g := by
  simp only [inverseLimitContinuousLaplacian]
  rw [UHF_Laplacian_continuousMap_eq_id
    (inverseLimitContinuousPushforward g)]
  exact inverseLimitContinuousPullback_pushforward g

theorem inverseLimitContinuous_cuntz_partition
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousS_L
        (inverseLimitContinuousStarS_L g) +
      inverseLimitContinuousS_R
        (inverseLimitContinuousStarS_R g) = g := by
  simp only [inverseLimitContinuousS_L, inverseLimitContinuousS_R,
    inverseLimitContinuousStarS_L, inverseLimitContinuousStarS_R]
  rw [inverseLimitContinuousPushforward_pullback,
    inverseLimitContinuousPushforward_pullback]
  apply ContinuousMap.ext
  intro z
  change
    S_L_continuousMap (star_S_L_continuousMap
      (inverseLimitContinuousPushforward g))
        (prefixBoundaryLimitIso.inv.hom z) +
      S_R_continuousMap (star_S_R_continuousMap
        (inverseLimitContinuousPushforward g))
        (prefixBoundaryLimitIso.inv.hom z) = g z
  have hpart := congrArg
    (fun q : BoundaryContinuousFunction =>
      q (prefixBoundaryLimitIso.inv.hom z))
    (cuntz_partition_continuousMap (inverseLimitContinuousPushforward g))
  have hg' : inverseLimitPushforward (g : InverseLimitFunction)
      (prefixBoundaryLimitIso.inv.hom z) = g z := by
    change g (prefixBoundaryLimitIso.hom.hom
      (prefixBoundaryLimitIso.inv.hom z)) = g z
    simp
  exact hpart.trans hg'

theorem projective_cuntz_ortho_left
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousStarS_L (inverseLimitContinuousS_L g) = g := by
  simp only [inverseLimitContinuousStarS_L, inverseLimitContinuousS_L]
  rw [inverseLimitContinuousPushforward_pullback,
    star_S_L_continuousMap_S_L]
  exact inverseLimitContinuousPullback_pushforward g

theorem projective_cuntz_ortho_right
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousStarS_R (inverseLimitContinuousS_R g) = g := by
  simp only [inverseLimitContinuousStarS_R, inverseLimitContinuousS_R]
  rw [inverseLimitContinuousPushforward_pullback,
    star_S_R_continuousMap_S_R]
  exact inverseLimitContinuousPullback_pushforward g

theorem projective_cuntz_ortho_cross_left
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousStarS_L (inverseLimitContinuousS_R g) = 0 := by
  simp only [inverseLimitContinuousStarS_L, inverseLimitContinuousS_R]
  rw [inverseLimitContinuousPushforward_pullback,
    star_S_L_continuousMap_S_R]
  exact congrArg inverseLimitContinuousPullback
    (star_S_L_continuousMap_S_R (inverseLimitContinuousPushforward g))

theorem projective_cuntz_ortho_cross_right
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousStarS_R (inverseLimitContinuousS_L g) = 0 := by
  simp only [inverseLimitContinuousStarS_R, inverseLimitContinuousS_L]
  rw [inverseLimitContinuousPushforward_pullback,
    star_S_R_continuousMap_S_L]
  exact congrArg inverseLimitContinuousPullback
    (star_S_R_continuousMap_S_L (inverseLimitContinuousPushforward g))

theorem projective_boundaryDifferential_square
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousBoundaryOp
        (inverseLimitContinuousBoundaryOp g) = 0 :=
  inverseLimitContinuousBoundaryOp_sq g

theorem projective_boundaryDifferential_star_square
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousStarBoundaryOp
        (inverseLimitContinuousStarBoundaryOp g) = 0 :=
  inverseLimitContinuousStarBoundaryOp_sq g

theorem projective_boundaryDifferential_hodge
    (g : InverseLimitContinuousFunction) :
    inverseLimitContinuousBoundaryOp
        (inverseLimitContinuousStarBoundaryOp g) +
      inverseLimitContinuousStarBoundaryOp
        (inverseLimitContinuousBoundaryOp g) = g := by
  simp only [inverseLimitContinuousBoundaryOp,
    inverseLimitContinuousStarBoundaryOp]
  rw [inverseLimitContinuousPushforward_pullback,
    inverseLimitContinuousPushforward_pullback]
  apply ContinuousMap.ext
  intro z
  change
    UHF_boundary_continuousMap (star_UHF_boundary_continuousMap
      (inverseLimitContinuousPushforward g))
        (prefixBoundaryLimitIso.inv.hom z) +
      star_UHF_boundary_continuousMap (UHF_boundary_continuousMap
        (inverseLimitContinuousPushforward g))
        (prefixBoundaryLimitIso.inv.hom z) = g z
  have h := congrArg
    (fun q : BoundaryContinuousFunction =>
      q (prefixBoundaryLimitIso.inv.hom z))
    (UHF_Laplacian_continuousMap_eq_id
      (inverseLimitContinuousPushforward g))
  simpa [UHF_Laplacian_continuousMap] using h

theorem inverseLimitPullback_pushforward (g : InverseLimitFunction) :
    inverseLimitPullback (inverseLimitPushforward g) = g := by
  funext z
  simp [inverseLimitPullback, inverseLimitPushforward]

theorem inverseLimitPushforward_pullback (f : BoundaryFunction) :
    inverseLimitPushforward (inverseLimitPullback f) = f := by
  funext x
  simp [inverseLimitPullback, inverseLimitPushforward]

theorem inverseLimitPullback_intertwines_S_L (f : BoundaryFunction) :
    inverseLimitS_L (inverseLimitPullback f) =
      inverseLimitPullback (S_L_op f) := by
  rw [inverseLimitS_L]
  rw [inverseLimitPushforward_pullback]

theorem inverseLimitPullback_intertwines_S_R (f : BoundaryFunction) :
    inverseLimitS_R (inverseLimitPullback f) =
      inverseLimitPullback (S_R_op f) := by
  rw [inverseLimitS_R]
  rw [inverseLimitPushforward_pullback]

theorem inverseLimitPullback_intertwines_star_S_L (f : BoundaryFunction) :
    inverseLimitStarS_L (inverseLimitPullback f) =
      inverseLimitPullback (star_S_L_op f) := by
  rw [inverseLimitStarS_L]
  rw [inverseLimitPushforward_pullback]

theorem inverseLimitPullback_intertwines_star_S_R (f : BoundaryFunction) :
    inverseLimitStarS_R (inverseLimitPullback f) =
      inverseLimitPullback (star_S_R_op f) := by
  rw [inverseLimitStarS_R]
  rw [inverseLimitPushforward_pullback]

def inverseLimitBoundaryOp (g : InverseLimitFunction) : InverseLimitFunction :=
  inverseLimitPullback (UHF_boundary_op (inverseLimitPushforward g))

def inverseLimitStarBoundaryOp (g : InverseLimitFunction) : InverseLimitFunction :=
  inverseLimitPullback (star_UHF_boundary_op (inverseLimitPushforward g))

theorem inverseLimitBoundaryOp_sq (g : InverseLimitFunction) :
    inverseLimitBoundaryOp (inverseLimitBoundaryOp g) = 0 := by
  simp only [inverseLimitBoundaryOp]
  rw [inverseLimitPushforward_pullback]
  rw [InfoGeometry.Canonical.UHFBoundaryExactSequence.UHF_boundary_op_sq_zero]
  rfl

theorem inverseLimitStarBoundaryOp_sq (g : InverseLimitFunction) :
    inverseLimitStarBoundaryOp (inverseLimitStarBoundaryOp g) = 0 := by
  simp only [inverseLimitStarBoundaryOp]
  rw [inverseLimitPushforward_pullback]
  rw [InfoGeometry.Canonical.UHFColimitRepresentationBridge.star_UHF_boundary_op_sq_zero]
  rfl

/-- The two transported differentials satisfy the source anticommutator identity. -/
theorem inverseLimitBoundaryOp_star_add_star_boundary (g : InverseLimitFunction) :
    inverseLimitBoundaryOp (inverseLimitStarBoundaryOp g) +
      inverseLimitStarBoundaryOp (inverseLimitBoundaryOp g) = g := by
  simp only [inverseLimitBoundaryOp, inverseLimitStarBoundaryOp,
    inverseLimitPushforward_pullback]
  have h := congrArg inverseLimitPullback
    (UHF_Laplacian_op_eq_id (inverseLimitPushforward g))
  rw [inverseLimitPullback_pushforward] at h
  exact h

/-- A closed inverse-limit function has the explicitly given primitive `d* g`. -/
theorem inverseLimitBoundaryOp_exact_of_closed (g : InverseLimitFunction)
    (hg : inverseLimitBoundaryOp g = 0) :
    inverseLimitBoundaryOp (inverseLimitStarBoundaryOp g) = g := by
  have h := inverseLimitBoundaryOp_star_add_star_boundary g
  rw [hg] at h
  have hzero : inverseLimitStarBoundaryOp 0 = 0 := by
    funext z
    simp [inverseLimitStarBoundaryOp, inverseLimitPushforward,
      inverseLimitPullback, star_UHF_boundary_op, S_R_op, star_S_L_op]
  simpa only [hzero, add_zero] using h

theorem inverseLimitPullback_intertwines_boundary_op
    (f : BoundaryFunction) :
    inverseLimitBoundaryOp (inverseLimitPullback f) =
      inverseLimitPullback (UHF_boundary_op f) := by
  rw [inverseLimitBoundaryOp, inverseLimitPushforward_pullback]

theorem inverseLimitPullback_intertwines_star_boundary_op
    (f : BoundaryFunction) :
    inverseLimitStarBoundaryOp (inverseLimitPullback f) =
      inverseLimitPullback (star_UHF_boundary_op f) := by
  rw [inverseLimitStarBoundaryOp, inverseLimitPushforward_pullback]

theorem inverseLimit_cuntz_partition (g : InverseLimitFunction) :
    inverseLimitS_L (inverseLimitStarS_L g) +
        inverseLimitS_R (inverseLimitStarS_R g) = g := by
  simp only [inverseLimitS_L, inverseLimitS_R,
    inverseLimitStarS_L, inverseLimitStarS_R]
  rw [inverseLimitPushforward_pullback, inverseLimitPushforward_pullback]
  funext z
  change
    S_L_op (star_S_L_op (inverseLimitPushforward g))
          (prefixBoundaryLimitIso.inv.hom z) +
      S_R_op (star_S_R_op (inverseLimitPushforward g))
          (prefixBoundaryLimitIso.inv.hom z) = g z
  have hg := congrFun (inverseLimitPullback_pushforward g) z
  rw [← hg]
  change
    S_L_op (star_S_L_op (inverseLimitPushforward g))
          (prefixBoundaryLimitIso.inv.hom z) +
      S_R_op (star_S_R_op (inverseLimitPushforward g))
          (prefixBoundaryLimitIso.inv.hom z) =
      inverseLimitPushforward g (prefixBoundaryLimitIso.inv.hom z)
  exact congrFun (cuntz_partition_op (inverseLimitPushforward g))
    (prefixBoundaryLimitIso.inv.hom z)

theorem inverseLimit_cuntz_ortho_left (g : InverseLimitFunction) :
    inverseLimitStarS_L (inverseLimitS_L g) = g := by
  simp only [inverseLimitStarS_L, inverseLimitS_L]
  rw [inverseLimitPushforward_pullback]
  exact (congrArg inverseLimitPullback
    (star_S_L_op_S_L_op (inverseLimitPushforward g))).trans
      (inverseLimitPullback_pushforward g)

theorem inverseLimit_cuntz_ortho_right (g : InverseLimitFunction) :
    inverseLimitStarS_R (inverseLimitS_R g) = g := by
  simp only [inverseLimitStarS_R, inverseLimitS_R]
  rw [inverseLimitPushforward_pullback]
  exact (congrArg inverseLimitPullback
    (star_S_R_op_S_R_op (inverseLimitPushforward g))).trans
      (inverseLimitPullback_pushforward g)

theorem inverseLimit_cuntz_ortho_cross_left (g : InverseLimitFunction) :
    inverseLimitStarS_L (inverseLimitS_R g) = 0 := by
  simp only [inverseLimitStarS_L, inverseLimitS_R]
  rw [inverseLimitPushforward_pullback]
  exact congrArg inverseLimitPullback
    (star_S_L_op_S_R_op (inverseLimitPushforward g))

theorem inverseLimit_cuntz_ortho_cross_right (g : InverseLimitFunction) :
    inverseLimitStarS_R (inverseLimitS_L g) = 0 := by
  simp only [inverseLimitStarS_R, inverseLimitS_L]
  rw [inverseLimitPushforward_pullback]
  exact congrArg inverseLimitPullback
    (star_S_R_op_S_L_op (inverseLimitPushforward g))

theorem prefixLimitPrependBit_transport (b : Bool)
    (z : InverseLimitBoundary) :
    prefixBoundaryLimitIso.inv.hom ((prefixLimitPrependBit b).hom z) =
      prependBit b (prefixBoundaryLimitIso.inv.hom z) := by
  simp [prefixLimitPrependBit, prependBitHom]
  rfl

theorem inverseLimitPullback_star_S_L_apply
    (f : BoundaryFunction) (z : InverseLimitBoundary) :
    inverseLimitPullback (star_S_L_op f) z =
      f (prefixBoundaryLimitIso.inv.hom
        ((prefixLimitPrependBit false).hom z)) := by
  rw [inverseLimitPullback_apply, prefixLimitPrependBit_transport]
  rfl

theorem inverseLimitPullback_star_S_R_apply
    (f : BoundaryFunction) (z : InverseLimitBoundary) :
    inverseLimitPullback (star_S_R_op f) z =
      f (prefixBoundaryLimitIso.inv.hom
        ((prefixLimitPrependBit true).hom z)) := by
  rw [inverseLimitPullback_apply, prefixLimitPrependBit_transport]
  rfl

theorem inverseLimitPullback_cylinder
    (n : ℕ) (f : DiagAlg n) (z : InverseLimitBoundary) :
    inverseLimitPullback (cylinder n f) z =
      f ((limit.π prefixDiagram (Opposite.op n)).hom z) := by
  rw [inverseLimitPullback_apply]
  unfold cylinder
  congr 1
  rw [prefixLimit_projection_eq_boundaryPrefix]
  rfl

theorem inverseLimitPullback_UHF_boundary_op_apply
    (f : BoundaryFunction) (z : InverseLimitBoundary) :
    inverseLimitPullback (UHF_boundary_op f) z =
      S_L_op (star_S_R_op f) (prefixBoundaryLimitIso.inv.hom z) :=
  rfl

end InfoGeometry.Canonical.CantorBoundaryProjectiveOperatorTransport
