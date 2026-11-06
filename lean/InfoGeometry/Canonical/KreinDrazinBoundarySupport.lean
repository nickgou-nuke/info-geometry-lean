/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge

/-!
# Krein--Drazin Boundary Support

The Drazin inverse is algebraic.  The Krein structure enters only after the
Drazin split, where the support and defect complement are interpreted in a
doubled indefinite metric carrier.

The conformal boundary is not the full Drazin complement and not the full
Krein isotropic cone.  It is the projectivized Krein-null part of the Drazin
defect support:

```text
  P({x ≠ 0 : q x = x, [x,x] = 0})
```
-/

noncomputable section

namespace InfoGeometry.Canonical.KreinDrazinBoundarySupport

set_option linter.dupNamespace false

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge

/-- Algebraic Drazin data for an operator and its regular/defect split. -/
structure AlgebraicDrazinSplit
    (Op : Type*)
    [Ring Op] where
  /-- Operator being split. -/
  A : Op
  /-- Algebraic Drazin inverse candidate. -/
  AD : Op
  /-- Drazin index. -/
  index : ℕ
  /-- Algebraic Drazin inverse laws. -/
  hDrazin : IsDrazinInverse A AD index
  /-- Regular support `p = A Aᴰ`. -/
  p : Op
  /-- Defect support `q = 1 - p`. -/
  q : Op
  /-- Definition of the regular support. -/
  p_def : p = A * AD
  /-- Definition of the defect support. -/
  q_def : q = 1 - p
  /-- Regular support is idempotent. -/
  p_idempotent : p * p = p
  /-- Defect support is idempotent. -/
  q_idempotent : q * q = q
  /-- Regular and defect supports are left-orthogonal. -/
  pq_zero : p * q = 0
  /-- Regular and defect supports are right-orthogonal. -/
  qp_zero : q * p = 0

/-- The Drazin equations are read back from the algebraic split. -/
theorem drazin_laws
    {Op : Type*}
    [Ring Op]
    (D : AlgebraicDrazinSplit Op) :
    IsDrazinInverse D.A D.AD D.index :=
  D.hDrazin

/-- The defect support annihilates the regular support on the left. -/
theorem defect_regular_left_annihilation
    {Op : Type*}
    [Ring Op]
    (D : AlgebraicDrazinSplit Op) :
    D.q * D.p = 0 :=
  D.qp_zero

/-- The regular support annihilates the defect support on the right. -/
theorem regular_defect_right_annihilation
    {Op : Type*}
    [Ring Op]
    (D : AlgebraicDrazinSplit Op) :
    D.p * D.q = 0 :=
  D.pq_zero

/-- Doubled/Krein carrier and action used to interpret the algebraic split. -/
structure DoubledKreinCarrier
    (K Op : Type*) where
  /-- Operator action on the doubled/Krein carrier. -/
  act : Op → K → K
  /-- Indefinite Krein form. -/
  kreinForm : K → K → ℝ
  /-- Distinguished zero vector. -/
  zero : K

/-- Krein adjoint data for the operator host. -/
structure KreinAdjointData
    (Op : Type*) [Ring Op] where
  /-- Krein adjoint, e.g. `T ↦ ε T† ε` in a concrete model. -/
  sharp : Op → Op
  /-- Krein adjoint is involutive. -/
  sharp_involutive : ∀ T, sharp (sharp T) = T
  /-- Krein adjoint reverses products. -/
  sharp_mul : ∀ S T, sharp (S * T) = sharp T * sharp S
  /-- Krein adjoint preserves addition. -/
  sharp_add : ∀ S T, sharp (S + T) = sharp S + sharp T

/--
Krein interpretation of an algebraic Drazin split.

The Drazin inverse remains algebraic.  These fields say that the resulting
regular and defect supports are meaningful in the doubled Krein metric.
-/
structure KreinDrazinBoundarySupport
    (K Op : Type*)
    [Ring Op] where
  /-- Doubled/Krein carrier. -/
  carrier : DoubledKreinCarrier K Op
  /-- Krein adjoint data on operators. -/
  adjoint : KreinAdjointData Op
  /-- Algebraic Drazin split. -/
  drazin : AlgebraicDrazinSplit Op
  /-- Regular support is Krein-self-adjoint. -/
  p_sharp : adjoint.sharp drazin.p = drazin.p
  /-- Defect support is Krein-self-adjoint. -/
  q_sharp : adjoint.sharp drazin.q = drazin.q
  /-- The distinguished zero vector belongs to the Drazin defect support. -/
  generalized_zero_sector_zero :
    carrier.act drazin.q carrier.zero = carrier.zero
  /-- The Drazin inverse is inverse on the regular support corner. -/
  inverse_on_regular_sector :
    drazin.p * drazin.A * drazin.AD = drazin.p

/-! ## Tomita-realified boundary polarization -/

/--
Witness that the Krein form used on the Drazin boundary is supplied by a
realified Tomita polarization.

The Drazin split stays algebraic.  This packet only identifies the indefinite
form on the generalized-zero sector with the realified Tomita/Krein datum.
-/
structure TomitaRealifiedDrazinBoundaryPolarization
    (K Op : Type*)
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- Realification witness connecting complex Tomita data to Krein polarization. -/
  tomitaRealification : TomitaKreinRealificationWitness.{0, 0, 0, 0, 0, 0}
  /-- Predicate selecting the generalized-zero/Drazin-defect sector. -/
  generalizedZeroSector : K → Prop
  /-- The generalized-zero sector is the Drazin defect support. -/
  generalizedZeroSector_eq_defectSupport :
    ∀ x : K, generalizedZeroSector x ↔ D.carrier.act D.drazin.q x = x

namespace TomitaRealifiedDrazinBoundaryPolarization

/-- The generalized-zero sector is exactly the Drazin defect support. -/
theorem generalizedZeroSector_iff_defectSupport
    {K Op : Type*}
    [Ring Op]
    {D : KreinDrazinBoundarySupport K Op}
    (P : TomitaRealifiedDrazinBoundaryPolarization K Op D)
    (x : K) :
    P.generalizedZeroSector x ↔ D.carrier.act D.drazin.q x = x :=
  P.generalizedZeroSector_eq_defectSupport x

end TomitaRealifiedDrazinBoundaryPolarization

/-- A vector lies in the Drazin defect support when `q x = x`. -/
def InDefectSupport
    {K Op : Type*}
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op)
    (x : K) : Prop :=
  D.carrier.act D.drazin.q x = x

/-- A vector is Krein-null when its indefinite norm vanishes. -/
def IsKreinNull
    {K Op : Type*}
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op)
    (x : K) : Prop :=
  D.carrier.kreinForm x x = 0

/-- Boundary lightlike vectors are nonzero, defect-supported, and Krein-null. -/
def BoundaryNullRayRepresentative
    {K Op : Type*}
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op)
    (x : K) : Prop :=
  x ≠ D.carrier.zero ∧ InDefectSupport D x ∧ IsKreinNull D x

/-- Structured membership in the Drazin complement/generalized-zero sector. -/
structure InDrazinComplement
    {K Op : Type*}
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op)
    (x : K) where
  /-- The vector is fixed by the defect support `q`. -/
  projectedByComplement : InDefectSupport D x

/-- A vector in the Drazin complement that is also Krein-null. -/
structure DrazinKreinNullVector
    {K Op : Type*}
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- Representative vector. -/
  vector : K
  /-- The vector lies in the Drazin complement. -/
  inDrazinComplement : InDrazinComplement D vector
  /-- The vector is Krein-null. -/
  kreinNull : IsKreinNull D vector

/-- Read back the propositional boundary representative from a structured null vector. -/
theorem drazinKreinNullVector_is_boundary_null
    {K Op : Type*}
    [Ring Op]
    {D : KreinDrazinBoundarySupport K Op}
    (v : DrazinKreinNullVector D)
    (hv : v.vector ≠ D.carrier.zero) :
    BoundaryNullRayRepresentative D v.vector :=
  ⟨hv, v.inDrazinComplement.projectedByComplement, v.kreinNull⟩

/--
Homogeneity data for the Krein form under real Weyl scaling.

This is deliberately separate from the Drazin split: it belongs to the Krein
metric/projective layer, not to the algebraic inverse.
-/
structure KreinFormHomogeneous
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- The distinguished zero vector is stable under nonzero real scaling. -/
  smul_zero_eq_zero : ∀ c : ℝ, c • D.carrier.zero = D.carrier.zero
  /-- Nonzero real scaling preserves nonzero representatives. -/
  smul_nonzero :
    ∀ c : ℝ, c ≠ 0 → ∀ x, x ≠ D.carrier.zero → c • x ≠ D.carrier.zero
  /-- Defect support is stable under nonzero real scaling. -/
  defect_support_smul :
    ∀ c : ℝ, c ≠ 0 → ∀ x, InDefectSupport D x → InDefectSupport D (c • x)
  /-- Krein norm is homogeneous under real scaling. -/
  kreinForm_smul_self :
    ∀ c : ℝ, ∀ x, D.carrier.kreinForm (c • x) (c • x) =
      c ^ 2 * D.carrier.kreinForm x x

/-- Real projective scaling preserves Krein nullity under a homogeneity witness. -/
theorem projective_scaling_preserves_null
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    {D : KreinDrazinBoundarySupport K Op}
    (H : KreinFormHomogeneous D)
    (c : ℝ)
    {x : K}
    (hx : IsKreinNull D x) :
    IsKreinNull D (c • x) := by
  unfold IsKreinNull at hx ⊢
  rw [H.kreinForm_smul_self c x, hx, mul_zero]

/-- Real projective scaling preserves boundary-null representatives. -/
theorem boundary_null_vector_scaled
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    {D : KreinDrazinBoundarySupport K Op}
    (H : KreinFormHomogeneous D)
    {c : ℝ}
    (hc : c ≠ 0)
    {x : K}
    (hx : BoundaryNullRayRepresentative D x) :
    BoundaryNullRayRepresentative D (c • x) := by
  refine ⟨H.smul_nonzero c hc x hx.1, H.defect_support_smul c hc x hx.2.1,
    projective_scaling_preserves_null H c hx.2.2⟩

/-- Real projective equivalence by nonzero Weyl scaling. -/
def ProjectivelyEquivalent
    {K : Type*}
    [SMul ℝ K]
    (x y : K) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ y = c • x

/-- Abstract projectivized Drazin--Krein null boundary. -/
structure ProjectiveDrazinNullBoundary
    (K Op : Type*)
    [Ring Op]
    [SMul ℝ K]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- Ray carrier. -/
  Ray : Type*
  /-- Representative vector for each ray. -/
  representative : Ray → K
  /-- Representatives are nonzero. -/
  representative_nonzero : ∀ r, representative r ≠ D.carrier.zero
  /-- Representatives lie in the Drazin defect support. -/
  representative_in_defect : ∀ r, InDefectSupport D (representative r)
  /-- Representatives are Krein-null. -/
  representative_krein_null : ∀ r, IsKreinNull D (representative r)

/-- A single projective Drazin--Krein null ray with a structured representative. -/
structure ProjectiveDrazinNullRay
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- Structured Drazin-complement/Krein-null representative. -/
  representative : DrazinKreinNullVector D
  /-- Representative is nonzero. -/
  nonzero : representative.vector ≠ D.carrier.zero

/-- A projective null ray has a boundary-null representative. -/
theorem projectiveDrazinNullRay_is_boundary_null
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    {D : KreinDrazinBoundarySupport K Op}
    (r : ProjectiveDrazinNullRay D) :
    BoundaryNullRayRepresentative D r.representative.vector :=
  drazinKreinNullVector_is_boundary_null r.representative r.nonzero

/-- Representatives of projective boundary rays are boundary-null representatives. -/
theorem representative_is_boundary_null
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    {D : KreinDrazinBoundarySupport K Op}
    (B : ProjectiveDrazinNullBoundary K Op D)
    (r : B.Ray) :
    BoundaryNullRayRepresentative D (B.representative r) :=
  ⟨B.representative_nonzero r, B.representative_in_defect r, B.representative_krein_null r⟩

/-- Conformal/projective symmetry of the Drazin-null boundary. -/
structure DrazinNullConformalSymmetry
    (K Op : Type*)
    [Ring Op]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- Underlying map on representatives. -/
  map : K → K
  /-- Weyl scale attached to the map. -/
  scale : ℝ
  /-- The Weyl scale is nonzero. -/
  scale_nonzero : scale ≠ 0
  /-- The map preserves nonzero representatives. -/
  preserves_nonzero : ∀ x, x ≠ D.carrier.zero → map x ≠ D.carrier.zero
  /-- The map preserves the Drazin defect support. -/
  preserves_defect_support : ∀ x, InDefectSupport D x → InDefectSupport D (map x)
  /-- The map preserves the Krein-null condition. -/
  preserves_krein_null : ∀ x, IsKreinNull D x → IsKreinNull D (map x)
  /-- Projective-linear symmetry carrier. -/
  PGL : Type*
  /-- Conformal subgroup preserving the null-ray sector. -/
  conformalSubgroup : Type*
  /-- Affine chart after choosing a projective section. -/
  affineChart : Type*
  /-- Weyl gauge carrier for representative rescaling. -/
  weylGauge : Type*

/-- Conformal maps preserve Drazin-defect Krein-null representatives. -/
theorem conformal_map_preserves_boundary_null_ray
    {K Op : Type*}
    [Ring Op]
    {D : KreinDrazinBoundarySupport K Op}
    (C : DrazinNullConformalSymmetry K Op D)
    {x : K}
    (hx : BoundaryNullRayRepresentative D x) :
    BoundaryNullRayRepresentative D (C.map x) :=
  ⟨C.preserves_nonzero x hx.1,
    C.preserves_defect_support x hx.2.1,
    C.preserves_krein_null x hx.2.2⟩

/-- KMS/state/topological weighting replaces trace/rank/determinant volume. -/
structure KMSWeightOnDrazinNullBoundary
    (Ray : Type*) where
  /-- Weight assigned to a projective null ray. -/
  rayWeight : Ray → ℝ
  /-- Weights are nonnegative. -/
  rayWeight_nonnegative : ∀ r, 0 ≤ rayWeight r

/-- KMS/state/topological weighting on structured projective Drazin-null rays. -/
structure KMSWeightOnProjectiveDrazinNullRays
    {K Op : Type*}
    [Ring Op]
    [SMul ℝ K]
    (D : KreinDrazinBoundarySupport K Op) where
  /-- State/weight carrier replacing a Type III trace. -/
  stateOrWeight : Type*
  /-- Modular/KMS data carrier. -/
  modularData : Type*
  /-- Weight assigned to a projective null ray. -/
  rayWeight : ProjectiveDrazinNullRay D → ℝ
  /-- Weights are nonnegative. -/
  rayWeight_nonnegative : ∀ r, 0 ≤ rayWeight r

/-! ## Minimal split API

This section gives the exact theorem-safe split:

* Drazin data is algebraic and does not mention `sharp`.
* Krein nullity is a carrier/form predicate.
* The boundary is `P(Ran(H) ∩ Null_J)`.
* Conformal preservation is carried by explicit preservation fields.
-/

/-- Algebraic Drazin data with no Hilbert/Krein adjoint dependency. -/
structure AlgebraicDrazinData
    (Op : Type*)
    [Ring Op] where
  /-- Operator being split. -/
  L : Op
  /-- Algebraic Drazin inverse candidate. -/
  LD : Op
  /-- Drazin complement/generalized-zero projector. -/
  H : Op
  /-- Drazin index. -/
  index : ℕ
  /-- Owner proof of the Drazin inverse laws. -/
  isDrazinInverse : IsDrazinInverse L LD index
  /-- Complement definition `H = 1 - L Lᴰ`. -/
  H_def : H = IsDrazinInverse.complementaryProjection L LD

namespace AlgebraicDrazinData

variable {Op : Type*} [Ring Op]
variable (D : AlgebraicDrazinData Op)

/-- The Drazin commutation law is read back from the owner predicate. -/
theorem commute : D.L * D.LD = D.LD * D.L :=
  D.isDrazinInverse.comm

/-- The Drazin reflexivity law is read back from the owner predicate. -/
theorem reflexive : D.LD * D.L * D.LD = D.LD :=
  D.isDrazinInverse.idempotent

/-- The Drazin power law is read back from the owner predicate. -/
theorem power : D.L ^ (D.index + 1) * D.LD = D.L ^ D.index :=
  D.isDrazinInverse.power

/-- The complementary Drazin projector is idempotent by the owner theorem. -/
theorem H_idempotent : D.H * D.H = D.H := by
  rw [D.H_def]
  exact IsDrazinInverse.complementaryProjection_is_idempotent D.isDrazinInverse

end AlgebraicDrazinData

namespace DoubledKreinCarrier

/-- Carrier-level Krein nullity: zero indefinite norm. -/
def IsKreinNull
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    (v : V) : Prop :=
  K.kreinForm v v = 0

end DoubledKreinCarrier

/-- Vector lies in the Drazin generalized-zero sector when `H v = v`. -/
def InDrazinZeroSector
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  K.act D.H v = v

/-- A vector is both Drazin-zero and Krein-null. -/
def IsDrazinKreinNullVector
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  InDrazinZeroSector K D v ∧ DoubledKreinCarrier.IsKreinNull K v

/--
Projective Drazin--Krein null boundary.

Mathematically: `P(Ran(1 - L Lᴰ) ∩ Null_J)`.
-/
structure DrazinKreinNullBoundary
    (V Op : Type*)
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op) where
  /-- Ray carrier. -/
  Ray : Type*
  /-- Representative vector for each ray. -/
  representative : Ray → V
  /-- Representatives are nonzero. -/
  representative_nonzero : ∀ r : Ray, representative r ≠ K.zero
  /-- Representatives lie in the Drazin--Krein null sector. -/
  representative_is_null :
    ∀ r : Ray, IsDrazinKreinNullVector K D (representative r)

/-- Krein adjoint data attached to a doubled carrier. -/
def IsCarrierKreinAdjoint
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    (sharp : Op → Op) : Prop :=
  ∀ A v w, K.kreinForm (K.act A v) w =
    K.kreinForm v (K.act (sharp A) w)

/-- Krein adjoint data attached to a doubled carrier. -/
structure CarrierKreinAdjointData
    (V Op : Type*)
    (K : DoubledKreinCarrier V Op) where
  /-- Krein adjoint on operators. -/
  sharp : Op → Op
  /-- Defining adjoint predicate for the indefinite form. -/
  isCarrierKreinAdjoint : IsCarrierKreinAdjoint K sharp

namespace CarrierKreinAdjointData

variable {V Op : Type*}
variable {K : DoubledKreinCarrier V Op}
variable (Adj : CarrierKreinAdjointData V Op K)

/-- The Krein adjoint form identity supplied by the carrier predicate. -/
theorem kreinForm_act_eq (A : Op) (v w : V) :
    K.kreinForm (K.act A v) w =
      K.kreinForm v (K.act (Adj.sharp A) w) :=
  Adj.isCarrierKreinAdjoint A v w

end CarrierKreinAdjointData

/-- Krein compatibility of the algebraic Drazin complement. -/
structure KreinCompatibleDrazinComplement
    (V Op : Type*)
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (Adj : CarrierKreinAdjointData V Op K) where
  /-- The generalized-zero projector respects the Krein polarization. -/
  H_krein_self_adjoint : Adj.sharp D.H = D.H

/-- Predicate for preservation of the Krein form up to a scalar. -/
def PreservesKreinFormUpToScale
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    (U : Op)
    (scale : ℝ) : Prop :=
  ∀ v w : V, K.kreinForm (K.act U v) (K.act U w) =
    scale * K.kreinForm v w

/-- Conformal Krein symmetry: the form is preserved up to positive scale. -/
structure KreinConformalSymmetry
    (V Op : Type*)
    (K : DoubledKreinCarrier V Op) where
  /-- Operator implementing the symmetry. -/
  U : Op
  /-- Conformal scale. -/
  scale : ℝ
  /-- The scale is positive. -/
  scale_positive : 0 < scale
  /-- Conformal predicate for the Krein form. -/
  preservesKreinForm : PreservesKreinFormUpToScale K U scale

namespace KreinConformalSymmetry

variable {V Op : Type*}
variable {K : DoubledKreinCarrier V Op}
variable (U : KreinConformalSymmetry V Op K)

/-- The conformal Krein form identity supplied by the symmetry predicate. -/
theorem kreinForm_act_act_eq (v w : V) :
    K.kreinForm (K.act U.U v) (K.act U.U w) =
      U.scale * K.kreinForm v w :=
  U.preservesKreinForm v w

end KreinConformalSymmetry

/-- Boundary-preservation witness for a conformal symmetry. -/
structure PreservesDrazinKreinBoundary
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (U : KreinConformalSymmetry V Op K) where
  /-- The map preserves the Drazin zero sector. -/
  preserves_zero_sector :
    ∀ v, InDrazinZeroSector K D v → InDrazinZeroSector K D (K.act U.U v)
  /-- The map preserves Krein nullity. -/
  preserves_null :
    ∀ v, DoubledKreinCarrier.IsKreinNull K v →
      DoubledKreinCarrier.IsKreinNull K (K.act U.U v)

/-- Conformal symmetries preserving both cuts preserve Drazin--Krein null vectors. -/
theorem conformal_symmetry_preserves_drazin_krein_null_vectors
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (U : KreinConformalSymmetry V Op K)
    (h : PreservesDrazinKreinBoundary K D U)
    (v : V)
    (hv : IsDrazinKreinNullVector K D v) :
    IsDrazinKreinNullVector K D (K.act U.U v) := by
  constructor
  · exact h.preserves_zero_sector v hv.1
  · exact h.preserves_null v hv.2

/-! ## Isotropic cone vs. normal/conormal obstruction geometry -/

/-- Tangent condition to the Krein isotropic cone at `x`. -/
def TangentToNullCone
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    (x v : V) : Prop :=
  K.kreinForm x v = 0

/-- Conormal covector to the Krein isotropic cone at `x`. -/
def ConormalToNullCone
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    (x : V) : V → ℝ :=
  fun v => K.kreinForm x v

/--
Krein-symmetric form witness, used only for tangent/conormal geometry.

This is separate from the Drazin split and from the boundary-location
definition.
-/
structure KreinFormSymmetric
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op) where
  /-- Symmetry of the real Krein form. -/
  symmetric : ∀ x y : V, K.kreinForm x y = K.kreinForm y x

/-- A Krein-null vector is tangent to the isotropic cone at itself. -/
theorem krein_null_radial_tangent
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    {x : V}
    (hx : DoubledKreinCarrier.IsKreinNull K x) :
    TangentToNullCone K x x :=
  hx

/-- The conormal covector vanishes on tangent directions. -/
theorem conormal_vanishes_on_tangent
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    {x v : V}
    (hv : TangentToNullCone K x v) :
    ConormalToNullCone K x v = 0 :=
  hv

/-- The conormal covector evaluates to zero on the radial null direction. -/
theorem conormal_radial_zero_on_null
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    {x : V}
    (hx : DoubledKreinCarrier.IsKreinNull K x) :
    ConormalToNullCone K x x = 0 :=
  hx

/--
Hilbert-normal representative data.

The identification of a conormal covector with a vector is model-dependent.
This packet records the fundamental symmetry representative, e.g. `η x`.
-/
structure HilbertNormalRepresentative
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op) where
  /-- Fundamental symmetry or chosen metric-identification map. -/
  eta : V → V
  /-- Background Hilbert pairing used to identify covectors with vectors. -/
  hilbertPairing : V → V → ℝ
  /-- The Hilbert representative realizes the Krein conormal functional. -/
  eta_represents_conormal :
    ∀ x v : V, hilbertPairing (eta x) v = ConormalToNullCone K x v

/-- The Hilbert normal representative evaluates tangent directions to zero. -/
theorem hilbert_normal_vanishes_on_tangent
    {V Op : Type*}
    (K : DoubledKreinCarrier V Op)
    (N : HilbertNormalRepresentative K)
    {x v : V}
    (hv : TangentToNullCone K x v) :
    N.hilbertPairing (N.eta x) v = 0 := by
  rw [N.eta_represents_conormal x v]
  exact conormal_vanishes_on_tangent K hv

/-- Normal/conormal obstruction data at a Drazin--Krein null boundary point. -/
structure BoundaryNormalObstruction
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (x : V) where
  /-- The point lies on the Drazin--Krein null boundary carrier. -/
  boundary_point : IsDrazinKreinNullVector K D x
  /-- Obstruction/normal direction carrier. -/
  obstruction : Type*
  /-- The obstruction carrier contains at least one normal/anomaly channel. -/
  obstruction_nonempty : Nonempty obstruction

/-- Orthogonality to every vector in the Drazin zero sector. -/
def KreinOrthogonalToDrazinZeroSector
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  ∀ z : V, InDrazinZeroSector K D z → K.kreinForm v z = 0

/--
Radical of the Krein form restricted to the Drazin zero sector:
`Z_D ∩ Z_D^{⊥J}`.

This is stronger than mere Drazin-zero Krein nullity.
-/
def InRestrictedDrazinRadical
    {V Op : Type*}
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  InDrazinZeroSector K D v ∧ KreinOrthogonalToDrazinZeroSector K D v

/-- Restricted radical points are Drazin-zero. -/
theorem restricted_radical_in_zero_sector
    {V Op : Type*}
    [Ring Op]
    {K : DoubledKreinCarrier V Op}
    {D : AlgebraicDrazinData Op}
    {v : V}
    (hv : InRestrictedDrazinRadical K D v) :
    InDrazinZeroSector K D v :=
  hv.1

/-- Restricted radical points are Krein-null. -/
theorem restricted_radical_is_krein_null
    {V Op : Type*}
    [Ring Op]
    {K : DoubledKreinCarrier V Op}
    {D : AlgebraicDrazinData Op}
    {v : V}
    (hv : InRestrictedDrazinRadical K D v) :
    DoubledKreinCarrier.IsKreinNull K v :=
  hv.2 v hv.1

/-- Restricted radical points are Drazin--Krein null vectors. -/
theorem restricted_radical_is_drazin_krein_null
    {V Op : Type*}
    [Ring Op]
    {K : DoubledKreinCarrier V Op}
    {D : AlgebraicDrazinData Op}
    {v : V}
    (hv : InRestrictedDrazinRadical K D v) :
    IsDrazinKreinNullVector K D v :=
  ⟨restricted_radical_in_zero_sector hv, restricted_radical_is_krein_null hv⟩

/--
Normal/conormal data for a projective Drazin--Krein null boundary.

This records the normal/conormal carrier over each projective ray.
-/
structure BoundaryNormalCone
    (V Op : Type*)
    [Ring Op]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
  (B : DrazinKreinNullBoundary V Op K D) where
  /-- Normal/conormal carrier over each projective ray. -/
  Normal : B.Ray → Type*

/-! ## Concrete consistency model

One small model inhabits the structures of this file and shows that their
hypotheses are jointly satisfiable with a *non-invertible* operator and a
*nonzero* Krein-null defect vector.

* Operators: the commutative ring `ℝ × ℝ`, acting on `ℝ³` by
  `(a₁, a₂) · (x, y, z) = (a₁ x, a₂ y, a₂ z)`.
* Krein form of signature `(2, 1)`: `[v, w] = v₁ w₁ + v₂ w₂ - v₃ w₃`.
* Operator `A = (1, 0)`: a singular idempotent, its own index-one Drazin inverse,
  with regular support `p = (1, 0)` and defect support `q = (0, 1)`.
* Defect support `{x = 0}` is a Lorentzian plane containing the null vector
  `(0, 1, 1)`.

The Krein adjoint is the identity: in this commutative model every operator acts
diagonally and is Krein-self-adjoint.  The model witnesses consistency only; it
is not a model of the doubled/Tomita physics.
-/

section ConsistencyModel

/-- Model operator action of `ℝ × ℝ` on `ℝ × ℝ × ℝ`. -/
def modelAct (a : ℝ × ℝ) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a.1 * v.1, a.2 * v.2.1, a.2 * v.2.2)

/-- Model Krein form of signature `(2, 1)`. -/
def modelForm (v w : ℝ × ℝ × ℝ) : ℝ :=
  v.1 * w.1 + v.2.1 * w.2.1 - v.2.2 * w.2.2

/-- The model Krein form is indefinite. -/
theorem modelForm_indefinite :
    0 < modelForm (1, 0, 0) (1, 0, 0) ∧ modelForm (0, 0, 1) (0, 0, 1) < 0 := by
  constructor <;> norm_num [modelForm]

/-- Model doubled/Krein carrier. -/
def modelCarrier : DoubledKreinCarrier (ℝ × ℝ × ℝ) (ℝ × ℝ) where
  act := modelAct
  kreinForm := modelForm
  zero := 0

/-- Model Krein adjoint: the identity, valid because the operator ring is commutative. -/
def modelAdjoint : KreinAdjointData (ℝ × ℝ) where
  sharp := id
  sharp_involutive := fun _ => rfl
  sharp_mul := fun S T => mul_comm S T
  sharp_add := fun _ _ => rfl

/-- The singular idempotent `(1, 0)` is its own index-one Drazin inverse. -/
theorem model_isDrazinInverse : IsDrazinInverse ((1, 0) : ℝ × ℝ) (1, 0) 1 :=
  IsDrazinInverse.of_idempotent (by ext <;> simp)

/-- The model operator `(1, 0)` is not invertible. -/
theorem model_operator_not_isUnit : ¬ IsUnit ((1, 0) : ℝ × ℝ) := by
  intro h
  have h2 := (Prod.isUnit_iff.mp h).2
  simp at h2

/-- Model algebraic Drazin split of `(1, 0)`. -/
def modelSplit : AlgebraicDrazinSplit (ℝ × ℝ) where
  A := (1, 0)
  AD := (1, 0)
  index := 1
  hDrazin := model_isDrazinInverse
  p := (1, 0)
  q := (0, 1)
  p_def := by ext <;> simp
  q_def := by ext <;> simp
  p_idempotent := by ext <;> simp
  q_idempotent := by ext <;> simp
  pq_zero := by ext <;> simp
  qp_zero := by ext <;> simp

/-- Model Krein--Drazin boundary support. -/
def modelSupport : KreinDrazinBoundarySupport (ℝ × ℝ × ℝ) (ℝ × ℝ) where
  carrier := modelCarrier
  adjoint := modelAdjoint
  drazin := modelSplit
  p_sharp := rfl
  q_sharp := rfl
  generalized_zero_sector_zero := by
    simp [modelCarrier, modelAct, modelSplit]
  inverse_on_regular_sector := by
    simp [modelSplit]

/-- The model null vector `(0, 1, 1)`. -/
def modelNullVector : ℝ × ℝ × ℝ := (0, 1, 1)

theorem modelNullVector_inDefectSupport : InDefectSupport modelSupport modelNullVector := by
  simp [InDefectSupport, modelSupport, modelCarrier, modelAct, modelSplit, modelNullVector]

theorem modelNullVector_isKreinNull : IsKreinNull modelSupport modelNullVector := by
  simp [IsKreinNull, modelSupport, modelCarrier, modelForm, modelNullVector]

theorem modelNullVector_ne_zero : modelNullVector ≠ modelSupport.carrier.zero := by
  simp [modelNullVector, modelSupport, modelCarrier, Prod.ext_iff]

/-- The model has a genuine boundary null ray representative. -/
theorem modelNullVector_boundary :
    BoundaryNullRayRepresentative modelSupport modelNullVector :=
  ⟨modelNullVector_ne_zero, modelNullVector_inDefectSupport, modelNullVector_isKreinNull⟩

/-- Model membership in the Drazin complement. -/
theorem modelInDrazinComplement : InDrazinComplement modelSupport modelNullVector where
  projectedByComplement := modelNullVector_inDefectSupport

/-- Model Drazin--Krein null vector. -/
def modelDrazinKreinNullVector : DrazinKreinNullVector modelSupport where
  vector := modelNullVector
  inDrazinComplement := modelInDrazinComplement
  kreinNull := modelNullVector_isKreinNull

/-- Model Krein form homogeneity under real scaling. -/
theorem modelKreinFormHomogeneous : KreinFormHomogeneous modelSupport where
  smul_zero_eq_zero := fun c => by simp [modelSupport, modelCarrier]
  smul_nonzero := fun c hc x hx => by
    simpa [modelSupport, modelCarrier] using smul_ne_zero hc hx
  defect_support_smul := fun c _ x hx => by
    simp only [InDefectSupport, modelSupport, modelCarrier, modelAct, modelSplit,
      Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx ⊢
    obtain ⟨h1, -, -⟩ := hx
    have hx1 : x.1 = 0 := by linarith
    refine ⟨?_, by ring, by ring⟩
    rw [hx1]; ring
  kreinForm_smul_self := fun c x => by
    simp only [modelSupport, modelCarrier, modelForm, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring

/-- Model projective null boundary with a single ray. -/
def modelProjectiveNullBoundary :
    ProjectiveDrazinNullBoundary (ℝ × ℝ × ℝ) (ℝ × ℝ) modelSupport where
  Ray := Unit
  representative := fun _ => modelNullVector
  representative_nonzero := fun _ => modelNullVector_ne_zero
  representative_in_defect := fun _ => modelNullVector_inDefectSupport
  representative_krein_null := fun _ => modelNullVector_isKreinNull

/-- Model projective null ray. -/
def modelProjectiveNullRay : ProjectiveDrazinNullRay modelSupport where
  representative := modelDrazinKreinNullVector
  nonzero := modelNullVector_ne_zero

/-- Model conformal symmetry: scaling by `2`.  The extra carrier fields are
unconstrained type data and are set to `Unit`. -/
def modelConformalSymmetry :
    DrazinNullConformalSymmetry (ℝ × ℝ × ℝ) (ℝ × ℝ) modelSupport where
  map := fun v => (2 : ℝ) • v
  scale := 2
  scale_nonzero := by norm_num
  preserves_nonzero := fun x hx => by
    simpa [modelSupport, modelCarrier] using smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx
  preserves_defect_support := fun x hx =>
    modelKreinFormHomogeneous.defect_support_smul 2 (by norm_num) x hx
  preserves_krein_null := fun x hx =>
    projective_scaling_preserves_null modelKreinFormHomogeneous 2 hx
  PGL := Unit
  conformalSubgroup := Unit
  affineChart := Unit
  weylGauge := Unit

/-- Model nonnegative weight on a one-ray boundary. -/
def modelKMSWeight : KMSWeightOnDrazinNullBoundary Unit where
  rayWeight := fun _ => 1
  rayWeight_nonnegative := fun _ => by norm_num

/-- Model nonnegative weight on structured projective null rays. -/
def modelKMSWeightOnRays : KMSWeightOnProjectiveDrazinNullRays modelSupport where
  stateOrWeight := Unit
  modularData := Unit
  rayWeight := fun _ => 1
  rayWeight_nonnegative := fun _ => by norm_num

/-- Model Tomita polarization packet.  `TomitaKreinRealificationWitness` consists of
type fields only, so this witness carries content only through the defect-sector
characterization. -/
def modelTomitaPolarization :
    TomitaRealifiedDrazinBoundaryPolarization (ℝ × ℝ × ℝ) (ℝ × ℝ) modelSupport where
  tomitaRealification :=
    { ComplexCarrier := Unit, RealCarrier := Unit, complexStructure := Unit,
      tomitaJ := Unit, realifiedJ := Unit, kreinSymmetry := Unit }
  generalizedZeroSector := fun x => modelSupport.carrier.act modelSupport.drazin.q x = x
  generalizedZeroSector_eq_defectSupport := fun _ => Iff.rfl

/-- Model algebraic Drazin data for the minimal split API. -/
def modelDrazinData : AlgebraicDrazinData (ℝ × ℝ) where
  L := (1, 0)
  LD := (1, 0)
  H := (0, 1)
  index := 1
  isDrazinInverse := model_isDrazinInverse
  H_def := by
    simp only [IsDrazinInverse.complementaryProjection, IsDrazinInverse.projection]
    ext <;> simp

theorem modelNullVector_isDrazinKreinNull :
    IsDrazinKreinNullVector modelCarrier modelDrazinData modelNullVector := by
  constructor
  · simp [InDrazinZeroSector, modelCarrier, modelAct, modelDrazinData, modelNullVector]
  · simp [DoubledKreinCarrier.IsKreinNull, modelCarrier, modelForm, modelNullVector]

/-- Model projective Drazin--Krein null boundary for the minimal split API. -/
def modelDrazinKreinNullBoundary :
    DrazinKreinNullBoundary (ℝ × ℝ × ℝ) (ℝ × ℝ) modelCarrier modelDrazinData where
  Ray := Unit
  representative := fun _ => modelNullVector
  representative_nonzero := fun _ => by
    simp [modelNullVector, modelCarrier, Prod.ext_iff]
  representative_is_null := fun _ => modelNullVector_isDrazinKreinNull

/-- Model carrier Krein adjoint: every model operator is Krein-self-adjoint. -/
def modelCarrierAdjoint : CarrierKreinAdjointData (ℝ × ℝ × ℝ) (ℝ × ℝ) modelCarrier where
  sharp := id
  isCarrierKreinAdjoint := fun A v w => by
    simp only [modelCarrier, modelForm, modelAct, id]
    ring

/-- Model Krein compatibility of the Drazin complement. -/
theorem modelKreinCompatibleComplement :
    KreinCompatibleDrazinComplement (ℝ × ℝ × ℝ) (ℝ × ℝ) modelCarrier modelDrazinData
      modelCarrierAdjoint where
  H_krein_self_adjoint := rfl

/-- Model conformal Krein symmetry: the operator `(2, 2)` scales the form by `4`. -/
def modelKreinConformalSymmetry : KreinConformalSymmetry (ℝ × ℝ × ℝ) (ℝ × ℝ) modelCarrier where
  U := (2, 2)
  scale := 4
  scale_positive := by norm_num
  preservesKreinForm := fun v w => by
    simp only [modelCarrier, modelForm, modelAct]
    ring

/-- The model conformal symmetry preserves the Drazin--Krein boundary. -/
theorem modelPreservesBoundary :
    PreservesDrazinKreinBoundary modelCarrier modelDrazinData modelKreinConformalSymmetry where
  preserves_zero_sector := fun v hv => by
    simp only [InDrazinZeroSector, modelCarrier, modelAct, modelDrazinData,
      modelKreinConformalSymmetry, Prod.ext_iff] at hv ⊢
    obtain ⟨h1, h2, h3⟩ := hv
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [h1, h2, h3]
  preserves_null := fun v hv => by
    simp only [DoubledKreinCarrier.IsKreinNull, modelCarrier, modelForm, modelAct,
      modelKreinConformalSymmetry] at hv ⊢
    nlinarith [hv]

/-- The model Krein form is symmetric. -/
theorem modelKreinFormSymmetric : KreinFormSymmetric modelCarrier where
  symmetric := fun x y => by
    simp only [modelCarrier, modelForm]
    ring

/-- Model Hilbert-normal representative: fundamental symmetry `η (x, y, z) = (x, y, -z)`
with the Euclidean pairing. -/
def modelHilbertNormal : HilbertNormalRepresentative modelCarrier where
  eta := fun x => (x.1, x.2.1, -x.2.2)
  hilbertPairing := fun v w => v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2
  eta_represents_conormal := fun x v => by
    simp only [ConormalToNullCone, modelCarrier, modelForm]
    ring

/-- Model normal obstruction at the null vector. -/
def modelBoundaryNormalObstruction :
    BoundaryNormalObstruction modelCarrier modelDrazinData modelNullVector where
  boundary_point := modelNullVector_isDrazinKreinNull
  obstruction := Unit
  obstruction_nonempty := ⟨()⟩

/-- Model normal cone over the one-ray boundary. -/
def modelBoundaryNormalCone :
    BoundaryNormalCone (ℝ × ℝ × ℝ) (ℝ × ℝ) modelCarrier modelDrazinData
      modelDrazinKreinNullBoundary where
  Normal := fun _ => Unit

end ConsistencyModel

end InfoGeometry.Canonical.KreinDrazinBoundarySupport
