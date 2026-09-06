import InfoGeometry.Algebra.DerivationLieLane

/-!
# Equivariant projector and ideal representations

This is the representation-side companion to `DerivationLieLane`.  A Peirce
projector or a Clifford left/right-ideal projector is data on a representation
space, not a replacement for the derivation Lie algebra.  The contract records
exactly the intertwining equation needed to compare such realizations.
-/

namespace InfoGeometry.Algebra

variable {R A S : Type*} [CommRing R] [NonUnitalNonAssocRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommGroup S] [Module R S]

structure EquivariantProjectorRepresentation (K : DerivationLieLane R A) where
  rho : K.L →ₗ⁅R⁆ Module.End R S
  projector : Module.End R S
  projector_idempotent : projector * projector = projector
  equivariant : ∀ x, rho x * projector = projector * rho x

namespace EquivariantProjectorRepresentation

variable {K : DerivationLieLane R A}

theorem preserves_projector_range (P : EquivariantProjectorRepresentation K)
    (x : K.L) (s : S) (hs : P.projector s = s) :
    P.projector (P.rho x s) = P.rho x s := by
  rw [← Module.End.mul_apply, ← P.equivariant, Module.End.mul_apply, hs]

theorem projector_apply_idempotent (P : EquivariantProjectorRepresentation K)
    (s : S) : P.projector (P.projector s) = P.projector s := by
  exact congrArg (fun T : Module.End R S => T s) P.projector_idempotent

end EquivariantProjectorRepresentation

/-- A pair of complementary representation projectors, useful for chiral or
left/right ideal decompositions.  The exchange equation is deliberately
explicit: commuting with a projector and exchanging two projectors are
different representation claims. -/
structure EquivariantProjectorPair (K : DerivationLieLane R A) where
  rho : K.L →ₗ⁅R⁆ Module.End R S
  leftProjector : Module.End R S
  rightProjector : Module.End R S
  left_idempotent : leftProjector * leftProjector = leftProjector
  right_idempotent : rightProjector * rightProjector = rightProjector
  left_right_orthogonal : leftProjector * rightProjector = 0
  right_left_orthogonal : rightProjector * leftProjector = 0
  equivariant_left : ∀ x, rho x * leftProjector = leftProjector * rho x
  equivariant_right : ∀ x, rho x * rightProjector = rightProjector * rho x

/-- An orthogonal projector pair whose two sectors are also complementary.
This stronger structure is separate so orthogonality alone never implies a
decomposition of the representation space. -/
structure ComplementaryProjectorPair (K : DerivationLieLane R A)
    extends EquivariantProjectorPair (R := R) (A := A) (S := S) K where
  complete : leftProjector + rightProjector = (1 : Module.End R S)

namespace EquivariantProjectorPair

variable {K : DerivationLieLane R A}

theorem preserves_left_range (P : EquivariantProjectorPair K)
    (x : K.L) (s : S) (hs : P.leftProjector s = s) :
    P.leftProjector (P.rho x s) = P.rho x s := by
  rw [← Module.End.mul_apply, ← P.equivariant_left, Module.End.mul_apply, hs]

theorem preserves_right_range (P : EquivariantProjectorPair K)
    (x : K.L) (s : S) (hs : P.rightProjector s = s) :
    P.rightProjector (P.rho x s) = P.rho x s := by
  rw [← Module.End.mul_apply, ← P.equivariant_right, Module.End.mul_apply, hs]

end EquivariantProjectorPair

end InfoGeometry.Algebra
