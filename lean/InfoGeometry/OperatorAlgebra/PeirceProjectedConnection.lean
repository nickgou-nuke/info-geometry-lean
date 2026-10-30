/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# A projected inner-derivation connection on a native Peirce submodule

For an idempotent `p` in an associative algebra, the fixed submodule
`{s | p*s=s}` carries the actual linear operators `∇a(s)=p*[a,s]`.
Their right-module Leibniz law and curvature identity are proved as equalities
in `Module.End`.  The coefficient is the existing projector curvature
`p*[[a,p],[b,p]]*p`, connected to the compressed two-point tensor in the
preceding module.  No smooth manifold or spacetime equation is presumed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceProjectedConnection

open InfoGeometry.Clifford.ChiralProjectorBerryCurvature
open InfoGeometry.OperatorAlgebra.PeirceCompressionCurvature

local notation "berryCommutator" =>
  InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator

section RingIdentities

variable {A : Type*} [Ring A]

/-- The raw curvature calculation behind the native endomorphism theorem. -/
theorem projected_inner_derivation_curvature {p s : A}
    (hp : p * p = p) (hs : p * s = s) (a b : A) :
    p * berryCommutator a (p * berryCommutator b s) -
        p * berryCommutator b (p * berryCommutator a s) -
        p * berryCommutator (berryCommutator a b) s =
      projectorCurvature p (berryCommutator a p) (berryCommutator b p) * s := by
  have hpp (z : A) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  have hps (z : A) : p * (s * z) = s * z := by rw [← mul_assoc, hs]
  unfold projectorCurvature InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
  simp only [mul_sub, sub_mul, mul_assoc, hpp, hps, hs]
  noncomm_ring

/-- The projected derivation satisfies the right-module Leibniz law. -/
theorem projected_inner_derivation_leibniz {p s : A}
    (hs : p * s = s) (a b : A) :
    p * berryCommutator a (s * b) - (p * berryCommutator a s) * b =
      s * berryCommutator a b := by
  calc
    p * berryCommutator a (s * b) - (p * berryCommutator a s) * b =
        (p * s) * berryCommutator a b := by
          unfold InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
          noncomm_ring
    _ = s * berryCommutator a b := by rw [hs]

end RingIdentities

section NativeSubmodule

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The fixed submodule of left multiplication by `p`.  For an idempotent it
is the range of that projection and the underlying module of the right ideal `pA`. -/
def peirceRange (p : A) : Submodule R A where
  carrier := {s | p * s = s}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change p * s = s at hs
    change p * t = t at ht
    change p * (s + t) = s + t
    rw [mul_add, hs, ht]
  smul_mem' := by
    intro r s hs
    change p * s = s at hs
    change p * (r • s) = r • s
    rw [mul_smul_comm, hs]

/-- The native linear retraction onto the Peirce submodule. -/
def rangeProjection (p : A) (hp : p * p = p) : A →ₗ[R] peirceRange (R := R) p where
  toFun s := ⟨p * s, by
    change p * (p * s) = p * s
    rw [← mul_assoc, hp]⟩
  map_add' s t := by
    apply Subtype.ext
    exact mul_add p s t
  map_smul' r s := by
    apply Subtype.ext
    exact mul_smul_comm r p s

/-- The projection retracts the native inclusion of the full Peirce range. -/
theorem rangeProjection_comp_subtype (p : A) (hp : p * p = p) :
    (rangeProjection (R := R) p hp).comp (peirceRange (R := R) p).subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact s.property

/-- The projected connection is a native linear endomorphism of the Peirce range. -/
def projectedConnection (p : A) (hp : p * p = p) (a : A) :
    Module.End R (peirceRange (R := R) p) where
  toFun s := ⟨p * berryCommutator a (s : A), by
    change p * (p * berryCommutator a (s : A)) = p * berryCommutator a (s : A)
    rw [← mul_assoc, hp]⟩
  map_add' s t := by
    apply Subtype.ext
    change p * berryCommutator a ((s : A) + (t : A)) =
      p * berryCommutator a (s : A) + p * berryCommutator a (t : A)
    unfold InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
    noncomm_ring
  map_smul' r s := by
    apply Subtype.ext
    change p * berryCommutator a (r • (s : A)) = r • (p * berryCommutator a (s : A))
    unfold InfoGeometry.Clifford.ChiralProjectorBerryCurvature.commutator
    simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub]

/-- Right multiplication preserves the Peirce right ideal. -/
def rightMultiplication (p b : A) : Module.End R (peirceRange (R := R) p) where
  toFun s := ⟨(s : A) * b, by
    change p * ((s : A) * b) = (s : A) * b
    rw [← mul_assoc, s.property]⟩
  map_add' s t := by
    apply Subtype.ext
    change ((s : A) + (t : A)) * b = (s : A) * b + (t : A) * b
    exact add_mul _ _ _
  map_smul' r s := by
    apply Subtype.ext
    change (r • (s : A)) * b = r • ((s : A) * b)
    exact smul_mul_assoc _ _ _

/-- Left multiplication by an element supported in the Peirce range. -/
def leftCornerAction (p c : A) (hc : p * c = c) :
    Module.End R (peirceRange (R := R) p) where
  toFun s := ⟨c * (s : A), by
    change p * (c * (s : A)) = c * (s : A)
    rw [← mul_assoc, hc]⟩
  map_add' s t := by
    apply Subtype.ext
    change c * ((s : A) + (t : A)) = c * (s : A) + c * (t : A)
    exact mul_add _ _ _
  map_smul' r s := by
    apply Subtype.ext
    change c * (r • (s : A)) = r • (c * (s : A))
    exact mul_smul_comm _ _ _

/-- The Leibniz law expressed as an identity of actual linear operators. -/
theorem projectedConnection_leibniz (p : A) (hp : p * p = p) (a b : A) :
    projectedConnection (R := R) p hp a * rightMultiplication p b -
        rightMultiplication p b * projectedConnection p hp a =
      rightMultiplication p (berryCommutator a b) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact projected_inner_derivation_leibniz s.property a b

/-- Curvature of the projected inner-derivation connection is left action by
the existing projector-curvature coefficient. -/
theorem projectedConnection_curvature (p : A) (hp : p * p = p) (a b : A) :
    projectedConnection (R := R) p hp a * projectedConnection p hp b -
        projectedConnection p hp b * projectedConnection p hp a -
        projectedConnection p hp (berryCommutator a b) =
      leftCornerAction p
        (projectorCurvature p (berryCommutator a p) (berryCommutator b p))
        (projectorCurvature_left hp (berryCommutator a p) (berryCommutator b p)) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact projected_inner_derivation_curvature hp s.property a b

/-- The same connection curvature is the alternating compressed Gram tensor
of its two canonical tangent directions `[a,p]` and `[b,p]`. -/
theorem projectedConnection_curvature_apply_eq_compressedGram
    (p : A) (hp : p * p = p) (a b : A) (s : peirceRange (R := R) p) :
    (((projectedConnection (R := R) p hp a * projectedConnection p hp b -
        projectedConnection p hp b * projectedConnection p hp a -
        projectedConnection p hp (berryCommutator a b) :
          Module.End R (peirceRange (R := R) p)) s) : A) =
      (compressedGram p (berryCommutator a p) (berryCommutator b p) -
        compressedGram p (berryCommutator b p) (berryCommutator a p)) * (s : A) := by
  have ha : p * berryCommutator a p + berryCommutator a p * p = berryCommutator a p :=
    InfoGeometry.Core.PeirceTangent.commutator_tangent hp a
  have hb : p * berryCommutator b p + berryCommutator b p * p = berryCommutator b p :=
    InfoGeometry.Core.PeirceTangent.commutator_tangent hp b
  rw [compressedGram_sub_swap_eq_projectorCurvature hp ha hb]
  exact projected_inner_derivation_curvature hp s.property a b

end NativeSubmodule

end InfoGeometry.OperatorAlgebra.PeirceProjectedConnection
