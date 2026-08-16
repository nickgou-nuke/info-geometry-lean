universe u

/-!
# Sullivan/ Shimura transfer interface

The former version of this file modeled the target as `PUnit` and proved the
transfer and bordism statements by reflexivity.  That did not formalize a
K-theoretic transfer.  This file therefore keeps only the typed data and the
actual compatibility propositions needed by a future owner.

No transfer, Mittag--Leffler, or bordism theorem is asserted without a
concrete target and a proof of its compatibility maps.
-/

structure SullivanManifold (k : Nat) where
  manifold_type : Type u
  boundary : Type u

/-- A concrete target and transfer family supplied by a genuine owner. -/
structure SullivanShimuraTransferData where
  target : Type u
  transfer : {k : Nat} → SullivanManifold.{u} k → target
  transition : {k : Nat} → SullivanManifold.{u} k → target → target
  transfer_compatible :
    ∀ {k : Nat} (M : SullivanManifold.{u} k),
      transition M (transfer M) = transfer M

/-- The actual Mittag--Leffler compatibility proposition for supplied data. -/
def MittagLefflerCondition
    (D : SullivanShimuraTransferData.{u}) : Prop :=
  ∀ {k : Nat} (M : SullivanManifold.{u} k),
    D.transition M (D.transfer M) = D.transfer M

theorem transfer_data_satisfies_mittag_leffler
    (D : SullivanShimuraTransferData.{u}) :
    MittagLefflerCondition D := by
  intro k M
  exact D.transfer_compatible M

/-- A supplied boundary extension witness for an actual transfer datum. -/
structure OmegaPinBordismData
    (D : SullivanShimuraTransferData.{u})
    {k : Nat} (M : SullivanManifold.{u} k) where
  boundary_map : M.boundary → D.target
  transfer_boundary_compatible :
    ∀ b, boundary_map b = D.transfer M
