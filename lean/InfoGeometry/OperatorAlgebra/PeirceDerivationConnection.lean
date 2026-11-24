/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceProjectedConnection
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus

/-!
# Peirce connections for arbitrary Lie actions by derivations

The existing Peirce range `pA = {s | p * s = s}` carries the Grassmann
connection `∇x(s) = p * ρx(s)` for every Lie action by Leibniz derivations.
Its curvature is left multiplication by `p * [ρx(p), ρy(p)] * p`.
The Lie bracket correction is essential; no faithful action or stationary
projector is required. The coefficient is also the alternating compressed
Gram tensor of the two actual derivatives of `p`.

All carriers, projections, and curvature coefficients come from existing
owners. The connection is linear in its direction, but generally is not a
Lie algebra representation. The inner specialization recovers the existing
projected inner-derivation connection.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceDerivationConnection

open InfoGeometry.Algebra
open InfoGeometry.Core.PeirceTangent
open InfoGeometry.Clifford.ChiralProjectorBerryCurvature
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
open InfoGeometry.OperatorAlgebra.PeirceProjectedConnection

section LieAction

variable {R A : Type*} [CommRing R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
variable (K : LieActionLane R A)

/-- Projection of a Lie action onto the existing Peirce submodule, linear in
the direction variable. The Leibniz rule is needed for its connection laws,
not for this composition of native linear maps. -/
def derivationConnection (p : A) (hp : p * p = p) :
    K.L →ₗ[R] Module.End R (peirceRange (R := R) p) where
  toFun x := (rangeProjection (R := R) p hp).comp
    ((K.operatorAction x).comp (peirceRange (R := R) p).subtype)
  map_add' x y := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change p * K.operatorAction (x + y) (s : A) =
      p * K.operatorAction x (s : A) + p * K.operatorAction y (s : A)
    simp only [map_add, LinearMap.add_apply, mul_add]
  map_smul' r x := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change p * K.operatorAction (r • x) (s : A) =
      r • (p * K.operatorAction x (s : A))
    simp only [map_smul, LinearMap.smul_apply, mul_smul_comm]

omit [IsScalarTower R A A] in
@[simp] theorem derivationConnection_apply (p : A) (hp : p * p = p)
    (x : K.L) (s : peirceRange (R := R) p) :
    (derivationConnection K p hp x s : A) = p * K.operatorAction x (s : A) :=
  rfl

variable (hK : IsLeibnizAction K)
include hK

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Differentiating an idempotent produces an actual Peirce tangent direction. -/
theorem operatorAction_idempotent_tangent {p : A} (hp : p * p = p) (x : K.L) :
    p * K.operatorAction x p + K.operatorAction x p * p = K.operatorAction x p := by
  calc
    p * K.operatorAction x p + K.operatorAction x p * p =
        K.operatorAction x (p * p) := by rw [hK x p p]; abel
    _ = K.operatorAction x p := by rw [hp]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- The raw Grassmann curvature identity on any element fixed by the projection. -/
theorem projected_derivation_curvature {p s : A}
    (hp : p * p = p) (hs : p * s = s) (x y : K.L) :
    p * K.operatorAction x (p * K.operatorAction y s) -
        p * K.operatorAction y (p * K.operatorAction x s) -
        p * K.operatorAction ⁅x, y⁆ s =
      projectorCurvature p (K.operatorAction x p) (K.operatorAction y p) * s := by
  have hcorner (z : K.L) : p * K.operatorAction z p * p = 0 :=
    ((tangent_iff_diagonal_corners_zero hp).mp
      (operatorAction_idempotent_tangent K hK hp z)).1
  have hsection (z : K.L) :
      K.operatorAction z s = K.operatorAction z p * s + p * K.operatorAction z s := by
    calc
      K.operatorAction z s = K.operatorAction z (p * s) := by rw [hs]
      _ = K.operatorAction z p * s + p * K.operatorAction z s := hK z p s
  have hreturn (u v : K.L) :
      p * K.operatorAction u p * K.operatorAction v s =
        p * K.operatorAction u p * K.operatorAction v p * s := by
    calc
      p * K.operatorAction u p * K.operatorAction v s =
          p * K.operatorAction u p *
            (K.operatorAction v p * s + p * K.operatorAction v s) :=
        congrArg (fun a => p * K.operatorAction u p * a) (hsection v)
      _ = p * K.operatorAction u p * K.operatorAction v p * s +
          (p * K.operatorAction u p * p) * K.operatorAction v s := by noncomm_ring
      _ = p * K.operatorAction u p * K.operatorAction v p * s := by
        rw [hcorner, zero_mul, add_zero]
  calc
    p * K.operatorAction x (p * K.operatorAction y s) -
        p * K.operatorAction y (p * K.operatorAction x s) -
        p * K.operatorAction ⁅x, y⁆ s =
        p * K.operatorAction x p * K.operatorAction y s -
          p * K.operatorAction y p * K.operatorAction x s := by
      rw [hK x p (K.operatorAction y s), hK y p (K.operatorAction x s),
        K.operatorAction_commutator_apply]
      simp only [mul_add, mul_sub, ← mul_assoc, hp]
      abel
    _ = p * K.operatorAction x p * K.operatorAction y p * s -
        p * K.operatorAction y p * K.operatorAction x p * s := by
      rw [hreturn, hreturn]
    _ = projectorCurvature p (K.operatorAction x p) (K.operatorAction y p) * s := by
      simp only [projectorCurvature,
        InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator,
        mul_sub, sub_mul, mul_assoc, hs]

/-- The right-module Leibniz law, expressed entirely in native endomorphisms. -/
theorem derivationConnection_leibniz (p : A) (hp : p * p = p) (x : K.L) (b : A) :
    derivationConnection K p hp x * rightMultiplication p b -
        rightMultiplication p b * derivationConnection K p hp x =
      rightMultiplication p (K.operatorAction x b) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change p * K.operatorAction x ((s : A) * b) -
    (p * K.operatorAction x (s : A)) * b = (s : A) * K.operatorAction x b
  rw [hK x (s : A) b, mul_add, ← mul_assoc, ← mul_assoc, s.property]
  abel

omit [IsScalarTower R A A] in
/-- Curvature of the Grassmann connection is the existing projector-curvature
coefficient acting on the full Peirce range. -/
theorem derivationConnection_curvature (p : A) (hp : p * p = p) (x y : K.L) :
    derivationConnection K p hp x * derivationConnection K p hp y -
        derivationConnection K p hp y * derivationConnection K p hp x -
        derivationConnection K p hp ⁅x, y⁆ =
      leftCornerAction p
        (projectorCurvature p (K.operatorAction x p) (K.operatorAction y p))
        (projectorCurvature_left hp (K.operatorAction x p) (K.operatorAction y p)) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact projected_derivation_curvature K hK hp s.property x y

omit [IsScalarTower R A A] in
/-- The same curvature is the difference of the two ordered off-diagonal
return products, using derivatives obtained from the actual Lie action. -/
theorem derivationConnection_curvature_apply_eq_compressedGram
    (p : A) (hp : p * p = p) (x y : K.L) (s : peirceRange (R := R) p) :
    (((derivationConnection K p hp x * derivationConnection K p hp y -
        derivationConnection K p hp y * derivationConnection K p hp x -
        derivationConnection K p hp ⁅x, y⁆ :
          Module.End R (peirceRange (R := R) p)) s) : A) =
      (compressedGram p (K.operatorAction x p) (K.operatorAction y p) -
        compressedGram p (K.operatorAction y p) (K.operatorAction x p)) * (s : A) := by
  rw [compressedGram_sub_swap_eq_projectorCurvature hp
    (operatorAction_idempotent_tangent K hK hp x)
    (operatorAction_idempotent_tangent K hK hp y)]
  exact projected_derivation_curvature K hK hp s.property x y

omit [IsScalarTower R A A] in
/-- A projector fixed by the action gives a flat projected connection. -/
theorem derivationConnection_flat_of_fixed (p : A) (hp : p * p = p)
    (hfixed : ∀ x : K.L, K.operatorAction x p = 0) (x y : K.L) :
    derivationConnection K p hp x * derivationConnection K p hp y -
        derivationConnection K p hp y * derivationConnection K p hp x -
        derivationConnection K p hp ⁅x, y⁆ = 0 := by
  rw [derivationConnection_curvature K hK p hp x y]
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change projectorCurvature p (K.operatorAction x p) (K.operatorAction y p) * (s : A) = 0
  simp only [hfixed, projectorCurvature,
    InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator, mul_zero, zero_mul,
    sub_self]

end LieAction

section InnerCompatibility

variable {A : Type*} [Ring A]

/-- The existing possibly nonfaithful inner action recovers the prior projected
inner-derivation connection, with no change of section carrier. -/
theorem derivationConnection_inner (p : A) (hp : p * p = p) (a : A) :
    derivationConnection (innerLieActionLane A) p hp a =
      projectedConnection (R := ℤ) p hp a := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

end InnerCompatibility

end InfoGeometry.OperatorAlgebra.PeirceDerivationConnection
