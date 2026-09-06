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