import Mathlib
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham

/-!
# Time, Tripotent Operators, and Self-Concordant Barriers

This module provides the structural stepping stone formalizing:
* The extraction of null projectors from tripotent operators
* Zero volume zero determinant null space
* Self-concordant barrier and log generating potential
* Time as the de Rham 1-form cohomology of winding around the cone of the chiral Klein quadric

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas/theorems with zero open goals.]

- Plücker coordinate gradient, polar, Taylor, and logarithmic-direction identities.
- Tripotent projection algebra.
- Log-barrier Hessian algebraic symmetry/readout.
- Existing Grothendieck winding readbacks imported from the de Rham motive lane.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems depending only on explicitly named premises.]

- Logarithmic derivative statements depend on explicit nonzero/slit-plane hypotheses.

#### BUCKET 3: OPEN CLOSURE DEBT
[Exact unproved mathematical gaps.]

- Analytic self-concordance inequalities for the Klein barrier.
- A global geometric theorem identifying physical time with this winding class.
- A full de Rham cohomology computation of the Klein-quadric complement.
-/

namespace InfoGeometry.Projective.KleinQuadric.Plucker6

variable {R : Type*} [CommRing R]

/-- Coordinate dot pairing on the six Plücker coordinates. -/
def coordinatePairing (P Q : Plucker6 R) : R :=
  P.p01 * Q.p01 + P.p02 * Q.p02 + P.p03 * Q.p03 +
    P.p12 * Q.p12 + P.p13 * Q.p13 + P.p23 * Q.p23

/--
The coordinate gradient of the Klein quadratic form
`p01*p23 - p02*p13 + p03*p12`.
-/
def kleinGradient (P : Plucker6 R) : Plucker6 R where
  p01 := P.p23
  p02 := -P.p13
  p03 := P.p12
  p12 := P.p03
  p13 := -P.p02
  p23 := P.p01

/-- Pairing the Klein gradient with a direction gives the Klein polar numerator. -/
theorem coordinatePairing_kleinGradient_eq_polar (P X : Plucker6 R) :
    coordinatePairing (kleinGradient P) X = polar P X := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases X with ⟨x01, x02, x03, x12, x13, x23⟩
  simp [coordinatePairing, kleinGradient, polar, kleinQ, add]
  ring

/--
Quadratic Taylor identity for the Klein form.

The coefficient of `t` is the polar form, so the logarithmic de Rham numerator
is the directional derivative of the Klein potential.
-/
theorem kleinQ_add_scale (P X : Plucker6 R) (t : R) :
    kleinQ (add P (scale t X)) =
      kleinQ P + t * polar P X + t ^ 2 * kleinQ X := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases X with ⟨x01, x02, x03, x12, x13, x23⟩
  simp [kleinQ, add, scale, polar]
  ring_nf

/-- The Klein polar form is symmetric. -/
theorem polar_symm (P Q : Plucker6 R) :
    polar P Q = polar Q P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  simp [polar, kleinQ, add]
  ring

/-- The self-polar value is twice the Klein quadratic form. -/
theorem polar_self_eq_two_mul_kleinQ (P : Plucker6 R) :
    polar P P = (2 : R) * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  simp [polar, kleinQ, add]
  ring

/--
Algebraic Hessian bilinear form for the logarithmic barrier `-log(Q)`.

For the Klein quadratic form `Q`, this is the exact bilinear expression
`dQ(P)[X] dQ(P)[Y] / Q(P)^2 - d²Q(X,Y) / Q(P)`.
-/
noncomputable def kleinBarrierHessian (P X Y : Plucker6 ℂ) : ℂ :=
  polar P X * polar P Y / (kleinQ P) ^ 2 - polar X Y / kleinQ P

/-- The Klein logarithmic-barrier Hessian is symmetric. -/
theorem kleinBarrierHessian_symm (P X Y : Plucker6 ℂ) :
    kleinBarrierHessian P X Y = kleinBarrierHessian P Y X := by
  unfold kleinBarrierHessian
  rw [polar_symm X Y]
  ring

/-- Diagonal readout of the Klein logarithmic-barrier Hessian. -/
theorem kleinBarrierHessian_self (P X : Plucker6 ℂ) :
    kleinBarrierHessian P X X =
      polar P X ^ 2 / (kleinQ P) ^ 2 - (2 : ℂ) * kleinQ X / kleinQ P := by
  unfold kleinBarrierHessian
  rw [polar_self_eq_two_mul_kleinQ]
  ring

end InfoGeometry.Projective.KleinQuadric.Plucker6

namespace InfoGeometry.Projective.KleinQuadric.Time

noncomputable section

open Complex
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive

/-- Tripotent algebra element where T^3 = T. -/
def IsTripotent {A : Type*} [Ring A] (T : A) : Prop :=
  T * T * T = T

/-- The fourth power of a tripotent collapses to its square. -/
theorem tripotent_fourth_eq_square {A : Type*} [Ring A] {T : A}
    (hT : IsTripotent T) :
    T * T * T * T = T * T := by
  calc
    T * T * T * T = (T * T * T) * T := rfl
    _ = T * T := by rw [hT]

/-- The square of a tripotent is an idempotent. -/
theorem tripotent_square_idempotent {A : Type*} [Ring A] {T : A}
    (hT : IsTripotent T) :
    (T * T) * (T * T) = T * T := by
  simpa [mul_assoc] using tripotent_fourth_eq_square (T := T) hT

/--
The idempotent operator extracted from the tripotent operator.

`P = 1 - T^2` is the complementary projection to the idempotent `T^2`.
-/
def nullSpaceProjection {A : Type*} [Ring A] (T : A) (_ : IsTripotent T) : A :=
  1 - T * T

/-- The complementary tripotent projection is idempotent. -/
theorem nullSpaceProjection_idempotent {A : Type*} [Ring A] {T : A}
    (hT : IsTripotent T) :
    nullSpaceProjection T hT * nullSpaceProjection T hT = nullSpaceProjection T hT := by
  dsimp [nullSpaceProjection]
  have h4 : T * T * T * T = T * T := tripotent_fourth_eq_square (T := T) hT
  calc
    (1 - T * T) * (1 - T * T)
        = 1 - T * T - (T * T - T * T * T * T) := by noncomm_ring
    _ = 1 - T * T := by rw [h4]; simp

/-- The complementary projection kills the tripotent on the right. -/
theorem nullSpaceProjection_mul_tripotent_eq_zero {A : Type*} [Ring A] {T : A}
    (hT : IsTripotent T) :
    nullSpaceProjection T hT * T = 0 := by
  dsimp [nullSpaceProjection]
  calc
    (1 - T * T) * T = T - T * T * T := by noncomm_ring
    _ = 0 := by rw [hT, sub_self]

/-- The tripotent kills the complementary projection on the left. -/
theorem tripotent_mul_nullSpaceProjection_eq_zero {A : Type*} [Ring A] {T : A}
    (hT : IsTripotent T) :
    T * nullSpaceProjection T hT = 0 := by
  dsimp [nullSpaceProjection]
  calc
    T * (1 - T * T) = T - T * T * T := by noncomm_ring
    _ = 0 := by rw [hT, sub_self]

/-- The zero volume, zero determinant null space parameterizing parafermions. -/
structure ParafermionZeroVolume where
  volume : ℝ
  determinant : ℝ
  volume_eq_zero : volume = 0
  determinant_eq_zero : determinant = 0

/-- The canonical zero-volume parafermion witness. -/
def zeroVolumeParafermion : ParafermionZeroVolume where
  volume := 0
  determinant := 0
  volume_eq_zero := rfl
  determinant_eq_zero := rfl

/-- The log generating potential (self-concordant barrier) on the cone.
    This provides the multivalued potential whose derivative gives the de Rham 1-form. -/
noncomputable def logGeneratingPotential (Q : ℂ) : ℂ :=
  -Complex.log Q

/--
The algebraic logarithmic derivative of the Klein potential in a Plücker
direction.  It is the coordinate numerator `dQ(P)[X]` divided by `Q(P)`.
-/
noncomputable def kleinDLogAlong
    (P X : InfoGeometry.Projective.KleinQuadric.Plucker6 ℂ) : ℂ :=
  InfoGeometry.Projective.KleinQuadric.Plucker6.polar P X /
    InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ P

/-- The numerator of `kleinDLogAlong` is the coordinate gradient pairing. -/
theorem kleinDLogAlong_eq_gradient_pairing_div
    (P X : InfoGeometry.Projective.KleinQuadric.Plucker6 ℂ) :
    kleinDLogAlong P X =
      InfoGeometry.Projective.KleinQuadric.Plucker6.coordinatePairing
        (InfoGeometry.Projective.KleinQuadric.Plucker6.kleinGradient P) X /
          InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ P := by
  rw [InfoGeometry.Projective.KleinQuadric.Plucker6.coordinatePairing_kleinGradient_eq_polar]
  rfl

/-- Along the radial Plücker direction, `d log Q` reads the degree `2`. -/
theorem kleinDLogAlong_self_eq_two
    (P : InfoGeometry.Projective.KleinQuadric.Plucker6 ℂ)
    (hP : InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ P ≠ 0) :
    kleinDLogAlong P P = (2 : ℂ) := by
  unfold kleinDLogAlong
  rw [InfoGeometry.Projective.KleinQuadric.Plucker6.polar_self_eq_two_mul_kleinQ]
  field_simp [hP]

/-- The barrier derivative is the negative logarithmic de Rham form away from the branch cut. -/
theorem logGeneratingPotential_hasDerivAt (Q : ℂ) (hQ : Q ∈ Complex.slitPlane) :
    HasDerivAt logGeneratingPotential (-(1 / Q)) Q := by
  simpa [logGeneratingPotential] using (Complex.hasDerivAt_log hQ).neg

/-- Time is formalized as the de Rham 1-form cohomology of winding around the cone
    of the chiral Klein quadric of the chiral causal algebra.
    We represent this functionally as the fundamental Grothendieck winding class (n=1). -/
noncomputable def timeCohomologyWinding : ℂ :=
  grothendieckWindingClass 1

/-- Theorem: Time corresponds to one fundamental cycle of winding (2πi). -/
theorem timeCohomology_eq_two_pi_I :
    timeCohomologyWinding = 2 * Real.pi * Complex.I := by
  unfold timeCohomologyWinding
  unfold grothendieckWindingClass
  simp

/-- The time cohomology class has trivial exponential monodromy. -/
theorem timeCohomology_exp_eq_one :
    Complex.exp timeCohomologyWinding = (1 : ℂ) := by
  simpa [timeCohomologyWinding] using grothendieckWinding_of_sheet 1

/-- The time class equals the `d log` period around any positive-radius circle. -/
theorem timeCohomology_eq_circleIntegral_grothendieck_dlog (R : ℝ) (hR : 0 < R) :
    timeCohomologyWinding = (∮ z in C((0 : ℂ), R), grothendieck_dlog z) := by
  rw [timeCohomology_eq_two_pi_I, circleIntegral_grothendieck_dlog R hR]

end

end InfoGeometry.Projective.KleinQuadric.Time
