  /-- Weights are nonnegative. -/
  rayWeight_nonnegative : ∀ r, 0 ≤ rayWeight r
  /-- Guardrail: this replaces trace, determinant, and rank volume. -/
  nontracialVolumeWitness : Prop

/-- Complete packet for the Drazin--Krein null boundary construction. -/
structure KreinDrazinNullBoundaryPacket where
  K : Type*
  Op : Type*
  instRing : Ring Op
  instSMul : SMul ℝ K
  support : @KreinDrazinBoundarySupport K Op instRing
  boundary : @ProjectiveDrazinNullBoundary K Op instRing instSMul support
  conformalSymmetry : @DrazinNullConformalSymmetry K Op instRing support
  kmsWeights : KMSWeightOnDrazinNullBoundary boundary.Ray
  /-- Guardrail: defect support is not automatically the full light cone. -/
  complement_vs_lightcone_guard : Prop
  /-- Guardrail: Type III volume is not trace/determinant/rank. -/
  no_trace_no_determinant_guard : Prop

/-- Owner target for the null-boundary layer. -/
structure KreinDrazinNullBoundaryTarget where
  /-- Concrete packet witnessing the target. -/
  packet : KreinDrazinNullBoundaryPacket

/-! ## Minimal split API

This section gives the exact theorem-safe split:

* Drazin data is algebraic and does not mention `sharp`.
* Krein nullity is a carrier/form predicate.
* The boundary is `P(Ran(H) ∩ Null_J)`.
* Conformal preservation is witness-gated.
-/

/-- Algebraic Drazin data with no Hilbert/Krein adjoint dependency. -/
structure AlgebraicDrazinData
    (Op : Type*)
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ] where
  /-- Operator being split. -/
  L : Op
  /-- Algebraic Drazin inverse candidate. -/
  LD : Op
  /-- Drazin complement/generalized-zero projector. -/
  H : Op
  /-- Drazin index. -/
  index : ℕ
  /-- Algebraic commutation law. -/
  commute : L * LD = LD * L
  /-- Algebraic reflexivity law. -/
  reflexive : LD * L * LD = LD
  /-- Algebraic Drazin power law. -/
  power_True : L ^ (index + 1) * LD = L ^ index
  /-- Complement definition `H = 1 - L Lᴰ`. -/
  H_def : H = 1 - L * LD
  /-- Complement idempotence. -/
  H_idempotent : H * H = H

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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  K.act D.H v = v

/-- A vector is both Drazin-zero and Krein-null. -/
def IsDrazinKreinNullVector
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
  /-- Abstract quotient by nonzero scale. -/
  projective_identification : Prop

/-- Krein adjoint data attached to a doubled carrier. -/
structure CarrierKreinAdjointData
    (V Op : Type*)
    (K : DoubledKreinCarrier V Op) where
  /-- Krein adjoint on operators. -/
  sharp : Op → Op
  /-- Defining adjoint law for the indefinite form. -/
  adjoint_True :
    ∀ A v w, K.kreinForm (K.act A v) w =
      K.kreinForm v (K.act (sharp A) w)

/-- Krein compatibility of the algebraic Drazin complement. -/
structure KreinCompatibleDrazinComplement
    (V Op : Type*)
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (Adj : CarrierKreinAdjointData V Op K) where
  /-- The generalized-zero projector respects the Krein polarization. -/
  H_krein_self_adjoint : Adj.sharp D.H = D.H

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
  /-- Conformal law for the Krein form. -/
  conformal_True :
    ∀ v w : V, K.kreinForm (K.act U v) (K.act U w) =
      scale * K.kreinForm v w

/-- Boundary-preservation witness for a conformal symmetry. -/
structure PreservesDrazinKreinBoundary
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
-- [STITCHER: MISSING OVERLAP] --
import Mathlib
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
  tomitaRealification : TomitaKreinRealificationWitness
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
    {c : ℝ}
    (_hc : c ≠ 0)
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
    projective_scaling_preserves_null H hc hx.2.2⟩

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
  /-- Quotient-by-scale witness for the ray carrier. -/
  projective_identification : Prop

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
  /-- Quotient by nonzero real Weyl/projective scaling. -/
  projectiveScaleWitness : Prop

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
  /-- Witness that legal symmetries preserve projective null rays. -/
  preservesNullRaysWitness : Prop
  /-- Witness that Weyl gauge changes representatives, not rays. -/
  weylGaugeProjectiveWitness : Prop

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
  /-- Guardrail: this is a nontracial volume/readout witness. -/
  nontracialVolumeWitness : Prop

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
  /-- Guardrail: this replaces trace, determinant, and rank volume. -/
  nontracialVolumeWitness : Prop

/-- Complete packet for the Drazin--Krein null boundary construction. -/
structure KreinDrazinNullBoundaryPacket where
  K : Type*
  Op : Type*
  instRing : Ring Op
  instSMul : SMul ℝ K
  support : @KreinDrazinBoundarySupport K Op instRing
  boundary : @ProjectiveDrazinNullBoundary K Op instRing instSMul support
  conformalSymmetry : @DrazinNullConformalSymmetry K Op instRing support
  kmsWeights : KMSWeightOnDrazinNullBoundary boundary.Ray
  /-- Guardrail: defect support is not automatically the full light cone. -/
  complement_vs_lightcone_guard : Prop
  /-- Guardrail: Type III volume is not trace/determinant/rank. -/
  no_trace_no_determinant_guard : Prop

/-- Owner target for the null-boundary layer. -/
structure KreinDrazinNullBoundaryTarget where
  /-- Concrete packet witnessing the target. -/
  packet : KreinDrazinNullBoundaryPacket

/-! ## Minimal split API

This section gives the exact theorem-safe split:

* Drazin data is algebraic and does not mention `sharp`.
* Krein nullity is a carrier/form predicate.
* The boundary is `P(Ran(H) ∩ Null_J)`.
* Conformal preservation is witness-gated.
-/

/-- Algebraic Drazin data with no Hilbert/Krein adjoint dependency. -/
structure AlgebraicDrazinData
    (Op : Type*)
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ] where
  /-- Operator being split. -/
  L : Op
  /-- Algebraic Drazin inverse candidate. -/
  LD : Op
  /-- Drazin complement/generalized-zero projector. -/
  H : Op
  /-- Drazin index. -/
  index : ℕ
  /-- Algebraic commutation law. -/
  commute : L * LD = LD * L
  /-- Algebraic reflexivity law. -/
  reflexive : LD * L * LD = LD
  /-- Algebraic Drazin power law. -/
  power_True : L ^ (index + 1) * LD = L ^ index
  /-- Complement definition `H = 1 - L Lᴰ`. -/
  H_def : H = 1 - L * LD
  /-- Complement idempotence. -/
  H_idempotent : H * H = H

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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  K.act D.H v = v

/-- A vector is both Drazin-zero and Krein-null. -/
def IsDrazinKreinNullVector
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
  /-- Abstract quotient by nonzero scale. -/
  projective_identification : Prop

/-- Krein adjoint data attached to a doubled carrier. -/
structure CarrierKreinAdjointData
    (V Op : Type*)
    (K : DoubledKreinCarrier V Op) where
  /-- Krein adjoint on operators. -/
  sharp : Op → Op
  /-- Defining adjoint law for the indefinite form. -/
  adjoint_True :
    ∀ A v w, K.kreinForm (K.act A v) w =
      K.kreinForm v (K.act (sharp A) w)

/-- Krein compatibility of the algebraic Drazin complement. -/
structure KreinCompatibleDrazinComplement
    (V Op : Type*)
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (Adj : CarrierKreinAdjointData V Op K) where
  /-- The generalized-zero projector respects the Krein polarization. -/
  H_krein_self_adjoint : Adj.sharp D.H = D.H

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
  /-- Conformal law for the Krein form. -/
  conformal_True :
    ∀ v w : V, K.kreinForm (K.act U v) (K.act U w) =
      scale * K.kreinForm v w

/-- Boundary-preservation witness for a conformal symmetry. -/
structure PreservesDrazinKreinBoundary
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
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
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (v : V) : Prop :=
  InDrazinZeroSector K D v ∧ KreinOrthogonalToDrazinZeroSector K D v

/-- Restricted radical points are Drazin-zero. -/
theorem restricted_radical_in_zero_sector
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    {K : DoubledKreinCarrier V Op}
    {D : AlgebraicDrazinData Op}
    {v : V}
    (hv : InRestrictedDrazinRadical K D v) :
    InDrazinZeroSector K D v :=
  hv.1

/-- Restricted radical points are Krein-null. -/
theorem restricted_radical_is_krein_null
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    {K : DoubledKreinCarrier V Op}
    {D : AlgebraicDrazinData Op}
    {v : V}
    (hv : InRestrictedDrazinRadical K D v) :
    DoubledKreinCarrier.IsKreinNull K v :=
  hv.2 v hv.1

/-- Restricted radical points are Drazin--Krein null vectors. -/
theorem restricted_radical_is_drazin_krein_null
    {V Op : Type*}
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    {K : DoubledKreinCarrier V Op}
    {D : AlgebraicDrazinData Op}
    {v : V}
    (hv : InRestrictedDrazinRadical K D v) :
    IsDrazinKreinNullVector K D v :=
  ⟨restricted_radical_in_zero_sector hv, restricted_radical_is_krein_null hv⟩

/--
Normal/conormal witness for a projective Drazin--Krein null boundary.

This records the dual obstruction geometry: failure of nullity, leakage out of
the Drazin-zero sector, and Weyl/anomaly scaling of conormals.
-/
structure BoundaryNormalCone
    (V Op : Type*)
    [One Op] [Mul Op] [Sub Op] [Pow Op ℕ]
    (K : DoubledKreinCarrier V Op)
    (D : AlgebraicDrazinData Op)
    (B : DrazinKreinNullBoundary V Op K D) where
  /-- Normal/conormal carrier over each projective ray. -/
  Normal : B.Ray → Type*
  /-- Normal component detecting failure of the Krein-null constraint. -/
  detects_failure_of_nullity : Prop
  /-- Normal component detecting leakage out of the Drazin zero sector. -/
  detects_failure_of_drazin_zero_sector : Prop
  /-- Weyl scaling weight/anomaly channel on conormals. -/
  weyl_scaling_weight : Prop


end InfoGeometry.Canonical.KreinDrazinBoundarySupport
