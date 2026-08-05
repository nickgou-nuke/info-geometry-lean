/-
InfoGeometry/OperatorAlgebra/KreinIsotropicCone.lean

Krein isotropic cones and algebraic defect detection.

The isotropic cone is a carrier-geometric object defined by the Krein form.
Zero divisors, nilpotents, and Drazin-nil support are representation-level
detection predicates, not the primitive definition of the cone.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KreinIsotropicCone

open InfoGeometry.OperatorAlgebra

/-! ## 1. Quadratic Krein cone sockets -/

/--
A Krein quadratic datum on a carrier with real scaling.

This is the metric/quadratic primitive. Algebraic zero-divisors and nilpotents
are represented shadows supplied by bridge structures below.
-/
structure KreinQuadraticDatum
    (H : Type*) [SMul ℝ H] where
  /-- Quadratic readout, morally `inner v (J v)`. -/
  q : H → ℝ

  /-- Quadratic homogeneity. -/
  smul_q :
    ∀ (r : ℝ) (x : H), q (r • x) = r ^ 2 * q x

namespace KreinQuadraticDatum

variable {H : Type*} [SMul ℝ H]
variable (Q : KreinQuadraticDatum H)

/--
A vector is null/isotropic when its Krein quadratic readout vanishes.

This includes the zero vector.  The projective/null-boundary version should
add a separate nonzero condition.
-/
def IsNull
    (x : H) : Prop :=
  Q.q x = 0

/-- A vector is regular when it is not null. -/
def IsRegular
    (x : H) : Prop :=
  ¬ Q.IsNull x

/-- A nonzero null vector.  This is the projective cone predicate. -/
def IsNonzeroNull
    [Zero H]
    (x : H) : Prop :=
  x ≠ 0 ∧ Q.IsNull x

/-- The null cone is stable under real scalar multiplication. -/
theorem null_smul
    (r : ℝ)
    (x : H)
    (hx : Q.IsNull x) :
    Q.IsNull (r • x) := by
  dsimp [IsNull] at hx ⊢
  rw [Q.smul_q, hx, mul_zero]

end KreinQuadraticDatum

/-! ## 2. Projective rays -/

/--
Projective ray equivalence by nonzero real scalar rescaling.

This is a relation-level socket; quotient/projective-space constructions can
be added later when needed.
-/
def SameProjectiveRay
    {H : Type*} [SMul ℝ H]
    (v w : H) : Prop :=
  ∃ lam : ℝ, lam ≠ 0 ∧ w = lam • v

namespace SameProjectiveRay

variable
    {H : Type*} [AddCommMonoid H] [Module ℝ H]

/-- Every vector lies on the same projective ray as itself. -/
theorem refl
    (v : H) :
    SameProjectiveRay v v := by
  exact ⟨1, one_ne_zero, by simp⟩

/-- Projective ray equivalence is symmetric. -/
theorem symm
    {v w : H}
    (h : SameProjectiveRay v w) :
    SameProjectiveRay w v := by
  rcases h with ⟨lam, hlam, rfl⟩
  refine ⟨lam⁻¹, inv_ne_zero hlam, ?_⟩
  simp [smul_smul, hlam]

/-- Projective ray equivalence is transitive. -/
theorem trans
    {u v w : H}
    (huv : SameProjectiveRay u v)
    (hvw : SameProjectiveRay v w) :
    SameProjectiveRay u w := by
  rcases huv with ⟨a, ha, rfl⟩
  rcases hvw with ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  simp [smul_smul]

/-- Nullness is preserved along projective rays. -/
theorem null_of_sameRay
    {Q : KreinQuadraticDatum H}
    {v w : H}
    (hvw : SameProjectiveRay v w)
    (hv : Q.IsNull v) :
    Q.IsNull w := by
  rcases hvw with ⟨lam, _hlam, rfl⟩
  exact Q.null_smul lam v hv

/-- Nullness is equivalent along projective rays. -/
theorem null_iff_sameRay
    {Q : KreinQuadraticDatum H}
    {v w : H}
    (hvw : SameProjectiveRay v w) :
    Q.IsNull v ↔ Q.IsNull w := by
  constructor
  · exact null_of_sameRay hvw
  · intro hw
    exact null_of_sameRay (symm hvw) hw

end SameProjectiveRay

/-! ## 3. Algebraic shadows of the quadratic cone -/

/--
A bridge from carrier isotropy to an algebraic square-zero shadow.

The carrier null cone is not definitionally the zero-divisor locus. This datum
records a concrete representation/readout proving that isotropic vectors have
the desired algebraic shadow.
-/
structure IsotropicAlgebraicBridge
    (H Op : Type*) [SMul ℝ H] [MulZeroClass Op] where
  /-- Carrier quadratic geometry. -/
  quadratic : KreinQuadraticDatum H

  /-- Representation/readout from carrier vectors to operators. -/
  represent : H → Op

  /-- Null vectors map to square-zero represented elements. -/
  null_maps_to_square_zero :
    ∀ x : H,
      quadratic.IsNull x →
        IsSquareZeroElement (represent x)

  /--
  The represented square-zero shadow reflects isotropy in the concrete model.
  This is stated as the actual converse implication, not as an opaque marker.
  -/
  square_zero_reflects_null :
    ∀ x : H,
      IsSquareZeroElement (represent x) →
        quadratic.IsNull x

namespace IsotropicAlgebraicBridge

variable {H Op : Type*} [SMul ℝ H] [MulZeroClass Op]
variable (B : IsotropicAlgebraicBridge H Op)

/-- Re-export the square-zero shadow of null vectors. -/
theorem maps_to_square_zero
    {x : H}
    (hx : B.quadratic.IsNull x) :
    IsSquareZeroElement (B.represent x) :=
  B.null_maps_to_square_zero x hx

end IsotropicAlgebraicBridge

/-! ## 4. Square-zero shadows are nilpotent -/

/-- A square-zero represented element is nilpotent with exponent `2`. -/
theorem isNilpotentElement_of_squareZero
    {Op : Type*} [MonoidWithZero Op]
    {a : Op}
    (ha : IsSquareZeroElement a) :
    IsNilpotentElement a :=
  InfoGeometry.OperatorAlgebra.isNilpotentElement_of_squareZero ha

namespace IsotropicAlgebraicBridge

variable {H Op : Type*} [SMul ℝ H] [MonoidWithZero Op]
variable (B : IsotropicAlgebraicBridge H Op)

/--
Null vectors represented by square-zero elements are represented by nilpotent
operators.
-/
theorem null_maps_to_nilpotent
    {x : H}
    (hx : B.quadratic.IsNull x) :
    IsNilpotentElement (B.represent x) :=
  isNilpotentElement_of_squareZero (B.maps_to_square_zero hx)

end IsotropicAlgebraicBridge

/--
A bridge from carrier nullness to Drazin nil-branch support.

The Drazin projectors live in the represented operator algebra, while nullness
lives on the carrier.
-/
structure IsotropicDrazinBridge
    (H Op : Type*) [SMul ℝ H] [Ring Op] where
  /-- Carrier quadratic geometry. -/
  quadratic : KreinQuadraticDatum H

  /-- Representation/readout from carrier vectors to operators. -/
  represent : H → Op

  /-- Drazin core/nil projectors in the represented algebra. -/
  projectors : DrazinProjectorPair Op

  /-- Null vectors map to nilpotent represented elements. -/
  null_maps_to_nilpotent :
    ∀ x : H,
      quadratic.IsNull x →
        IsNilpotentElement (represent x)

  /-- Null vectors are supported on the nil branch. -/
  null_supported_by_nil :
    ∀ x : H,
      quadratic.IsNull x →
        IsLeftNilSupported projectors (represent x)

  /-- Regular vectors are supported on the core branch. -/
  regular_supported_by_core :
    ∀ x : H,
      quadratic.IsRegular x →
        IsLeftCoreSupported projectors (represent x)

namespace IsotropicDrazinBridge

variable {H Op : Type*} [SMul ℝ H] [Ring Op]
variable (B : IsotropicDrazinBridge H Op)

/-- Re-export nilpotence of represented null vectors. -/
theorem null_nilpotent
    {x : H}
    (hx : B.quadratic.IsNull x) :
    IsNilpotentElement (B.represent x) :=
  B.null_maps_to_nilpotent x hx

/-- Re-export nil-branch support of represented null vectors. -/
theorem null_nil_supported
    {x : H}
    (hx : B.quadratic.IsNull x) :
    IsLeftNilSupported B.projectors (B.represent x) :=
  B.null_supported_by_nil x hx

/-- Re-export core-branch support of represented regular vectors. -/
theorem regular_core_supported
    {x : H}
    (hx : B.quadratic.IsRegular x) :
    IsLeftCoreSupported B.projectors (B.represent x) :=
  B.regular_supported_by_core x hx

end IsotropicDrazinBridge

/-! ## 5. Krein form and isotropic cone -/

/--
The isotropic-cone layer uses the canonical Krein metric owner from
`ChiralPolarization`; it does not maintain a second metric record.
-/
abbrev KreinMetricDatum
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :=
  InfoGeometry.OperatorAlgebra.KreinMetricDatum H

/-- Krein bilinear form associated to `eta`. -/
def kreinForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K : KreinMetricDatum H)
    (v w : H) : ℝ :=
  inner (𝕜 := ℝ) v (K.eta w)

/-- The projective isotropic cone is the nonzero null locus of the Krein form. -/
def IsNonzeroKreinNull
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K : KreinMetricDatum H)
    (v : H) : Prop :=
  v ≠ 0 ∧ kreinForm K v v = 0

namespace IsNonzeroKreinNull

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {K : KreinMetricDatum H}

/-- Re-export nonzero-ness of a projective null vector. -/
theorem ne_zero
    {v : H}
    (hv : IsNonzeroKreinNull K v) :
    v ≠ 0 :=
  hv.1

/-- Re-export nullity of a projective null vector. -/
theorem kreinForm_self_eq_zero
    {v : H}
    (hv : IsNonzeroKreinNull K v) :
    kreinForm K v v = 0 :=
  hv.2

end IsNonzeroKreinNull

/-! ## 6. Projective absolute boundary versus interior metric -/

/--
A socket separating the Krein isotropic cone from an interior Poincare-type
metric domain.

The null cone is the projective absolute/boundary.  Hyperbolic/Poincare
distance lives on an interior domain, though concrete models may recover it
from boundary cross-ratio data.
-/
structure ProjectiveAbsoluteBoundaryDatum
    (H Domain : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [PseudoMetricSpace Domain]
    (K : KreinMetricDatum H) where
  /-- Interior domain carrying the Poincare/hyperbolic metric. -/
  interior : Set Domain

  /-- Boundary predicate on carrier vectors. -/
  boundary : H → Prop

  /-- The boundary is exactly the represented Krein isotropic cone. -/
  boundary_iff_isotropic :
    ∀ v : H, boundary v ↔ IsNonzeroKreinNull K v

  /-- Poincare/hyperbolic distance readout on the interior domain. -/
  poincareDistance : Domain → Domain → ℝ

  /-- The supplied distance readout is the native metric distance. -/
  poincareDistance_eq_dist :
    ∀ x y : Domain, poincareDistance x y = dist x y

  /-- Optional boundary cross-ratio style readout. -/
  boundaryCrossRatio : H → H → H → H → ℝ

namespace ProjectiveAbsoluteBoundaryDatum

variable
    {H Domain : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [PseudoMetricSpace Domain]
    {K : KreinMetricDatum H}
    (B : ProjectiveAbsoluteBoundaryDatum H Domain K)

/-- Re-export that boundary vectors are precisely isotropic vectors. -/
theorem boundary_isotropic_iff
    (v : H) :
    B.boundary v ↔ IsNonzeroKreinNull K v :=
  B.boundary_iff_isotropic v

/-- The interior distance readout is nonnegative. -/
theorem poincareDistance_nonneg
    (x y : Domain) :
    0 ≤ B.poincareDistance x y := by
  rw [B.poincareDistance_eq_dist]
  exact dist_nonneg

end ProjectiveAbsoluteBoundaryDatum

/-! ## 7. Algebraic detection bridge -/

/--
A represented algebraic defect detector for the Krein isotropic cone.

The cone remains defined by the Krein form on `H`; this bridge only records
that a representation detects isotropic vectors as algebraic defects.
-/
structure MetricIsotropicAlgebraBridge
    (H A : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [Ring A]
    (K : KreinMetricDatum H) where
  repVector : H → A
  IsZeroDivisor : A → Prop
  IsNilSupported : A → Prop
  isotropic_maps_to_zeroDivisor :
    ∀ v : H, IsNonzeroKreinNull K v →
      IsZeroDivisor (repVector v)
  zeroDivisor_maps_to_nilSupport :
    ∀ v : H, IsZeroDivisor (repVector v) →
      IsNilSupported (repVector v)

namespace MetricIsotropicAlgebraBridge

variable
    {H A : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    [Ring A]
    {K : KreinMetricDatum H}
    (B : MetricIsotropicAlgebraBridge H A K)

/--
The represented image of an isotropic vector is nil-supported once the bridge
detects zero divisors and nil support.
-/
theorem isotropic_maps_to_nilSupport
    (v : H)
    (hv : IsNonzeroKreinNull K v) :
    B.IsNilSupported (B.repVector v) :=
  B.zeroDivisor_maps_to_nilSupport v
    (B.isotropic_maps_to_zeroDivisor v hv)

end MetricIsotropicAlgebraBridge

/-! ## 8. Drazin inverse and Drazin-nil support -/

/--
An element `a` has a Drazin inverse `x` with witness index `index`.

The identities are:

* `a * x = x * a`;
* `x * a * x = x`;
* `a^(index + 1) * x = a^index`.

The index is a witness, not asserted here to be minimal.
-/
def HasDrazinInverse
    {A : Type*} [Ring A]
    (a : A) : Type _ :=
  {p : A × ℕ //
    a * p.1 = p.1 * a ∧
      p.1 * a * p.1 = p.1 ∧
        a ^ (p.2 + 1) * p.1 = a ^ p.2}

namespace HasDrazinInverse

abbrev x {A : Type*} [Ring A] {a : A} (h : HasDrazinInverse a) : A := h.1.1

abbrev index {A : Type*} [Ring A] {a : A} (h : HasDrazinInverse a) : ℕ := h.1.2

theorem commute {A : Type*} [Ring A] {a : A} (h : HasDrazinInverse a) :
    a * h.x = h.x * a :=
  h.2.1

theorem inverse_identity {A : Type*} [Ring A] {a : A} (h : HasDrazinInverse a) :
    h.x * a * h.x = h.x :=
  h.2.2.1

theorem power_identity {A : Type*} [Ring A] {a : A} (h : HasDrazinInverse a) :
    a ^ (h.index + 1) * h.x = a ^ h.index :=
  h.2.2.2

end HasDrazinInverse

/--
Drazin-nilpotent support.

An element is Drazin-nilpotent if it has a Drazin inverse equal to zero, with a
nonzero index witness.
-/
def IsDrazinNilpotent
    {A : Type*} [Ring A]
    (a : A) : Prop :=
  ∃ h : HasDrazinInverse a,
    h.x = 0 ∧ h.index ≠ 0

/--
Drazin-nilpotence implies repository-local nilpotence with a nonzero exponent.
-/
theorem isNilpotentElement_of_isDrazinNilpotent
    {A : Type*} [Ring A]
    {a : A}
    (h : IsDrazinNilpotent a) :
    IsNilpotentElement a := by
  rcases h with ⟨hD, hx_zero, hindex_ne_zero⟩
  refine ⟨hD.index, hindex_ne_zero, ?_⟩
  have hp := hD.power_identity
  rw [hx_zero, mul_zero] at hp
  exact hp.symm

/--
Bridge theorem: if `IsNilSupported` is calibrated to Drazin-nil support, then
every nonzero Krein-null vector maps to a nilpotent represented element.
-/
theorem nilpotent_of_isotropic_bridge_drazin
    {H A : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [Ring A]
    {K : KreinMetricDatum H}
    (B : MetricIsotropicAlgebraBridge H A K)
    (v : H)
    (hv : IsNonzeroKreinNull K v)
    (hNil :
      ∀ a : A,
        B.IsNilSupported a ↔ IsDrazinNilpotent a) :
    IsNilpotentElement (B.repVector v) := by
  have h_supported :
      B.IsNilSupported (B.repVector v) :=
    B.isotropic_maps_to_nilSupport v hv
  have h_drazin :
      IsDrazinNilpotent (B.repVector v) :=
    (hNil (B.repVector v)).1 h_supported
  exact isNilpotentElement_of_isDrazinNilpotent h_drazin

namespace HasDrazinInverse

variable
    {A : Type*} [Ring A]
    {a : A}

/--
The Drazin core projector:

`Pcore = a * aᴰ`.
-/
def coreProjector
    (h : HasDrazinInverse a) : A :=
  a * h.x

/--
The Drazin nil/generalized-zero projector:

`Pnil = 1 - Pcore`.
-/
def nilProjector
    (h : HasDrazinInverse a) : A :=
  1 - h.coreProjector

/--
The core projector may also be written as `aᴰ * a`.
-/
theorem coreProjector_eq_x_mul
    (h : HasDrazinInverse a) :
    h.coreProjector = h.x * a := by
  dsimp [coreProjector]
  exact h.commute

/--
The Drazin core projector is idempotent.
-/
theorem coreProjector_idempotent
    (h : HasDrazinInverse a) :
    h.coreProjector * h.coreProjector = h.coreProjector := by
  dsimp [coreProjector]
  calc
    (a * h.x) * (a * h.x)
        = a * (h.x * (a * h.x)) := by
            rw [mul_assoc]
    _ = a * ((h.x * a) * h.x) := by
            rw [← mul_assoc h.x a h.x]
    _ = a * h.x := by
            rw [h.inverse_identity]

/--
The nil projector is idempotent.

This uses only `Pcore² = Pcore`.
-/
theorem nilProjector_idempotent
    (h : HasDrazinInverse a) :
    h.nilProjector * h.nilProjector = h.nilProjector := by
  have hp : h.coreProjector * h.coreProjector = h.coreProjector :=
    h.coreProjector_idempotent
  dsimp [nilProjector]
  noncomm_ring [hp]

/--
The core and nil projectors are disjoint on the left.
-/
theorem core_mul_nilProjector
    (h : HasDrazinInverse a) :
    h.coreProjector * h.nilProjector = 0 := by
  have hp : h.coreProjector * h.coreProjector = h.coreProjector :=
    h.coreProjector_idempotent
  dsimp [nilProjector]
  noncomm_ring [hp]

/--
The core and nil projectors are disjoint on the right.
-/
theorem nil_mul_coreProjector
    (h : HasDrazinInverse a) :
    h.nilProjector * h.coreProjector = 0 := by
  have hp : h.coreProjector * h.coreProjector = h.coreProjector :=
    h.coreProjector_idempotent
  dsimp [nilProjector]
  noncomm_ring [hp]

/--
The Drazin projectors sum to the identity.
-/
theorem core_add_nilProjector
    (h : HasDrazinInverse a) :
    h.coreProjector + h.nilProjector = 1 := by
  dsimp [nilProjector]
  abel

end HasDrazinInverse

/--
If an isotropic carrier vector is represented by a Drazin-nilpotent algebra
element, then its represented image is supported entirely on the Drazin nil
branch.
-/
theorem isotropic_representation_is_drazin_nil
    {H A : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [Ring A]
    {K : KreinMetricDatum H}
    (B : MetricIsotropicAlgebraBridge H A K)
    (v : H)
    (hv : IsNonzeroKreinNull K v)
    (hNil :
      ∀ a : A,
        B.IsNilSupported a ↔ IsDrazinNilpotent a) :
    IsNilpotentElement (B.repVector v) :=
  nilpotent_of_isotropic_bridge_drazin B v hv hNil

end InfoGeometry.OperatorAlgebra.KreinIsotropicCone
