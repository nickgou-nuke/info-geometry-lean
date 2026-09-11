import InfoGeometry.Optics.QuaternionCl44TwistedConjugationLift
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option autoImplicit false

/-!
# A real versor and Dirac implementer for quaternionic twisted conjugation

The transported split-octonion conjugation fixes the positive scalar axis and
negates its seven-dimensional quadratic orthogonal complement.  Consequently
it is implemented inside the real Clifford algebra by ordinary conjugation
with the unit vector on that fixed axis.

The implementing vector has positive Clifford square.  With Mathlib's current
`star` convention it belongs to the native Lipschitz group but not to the
unitary `pinGroup`; the latter boundary is proved explicitly rather than
silently identifying two different real Pin conventions.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44DiracImplementer

open CanonicalZornRealSpin44
open CliffordAlgebra
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge
open InfoGeometry.Optics.QuaternionCl44TwistedConjugationLift

/-- The unique positive basis direction fixed by transported canonical Zorn
conjugation. -/
def scalarPositiveDirection : CartesianCoordinates :=
  positiveQuaternionDirection 0

/-- Its generator in the pulled-back real Clifford algebra. -/
def scalarPositiveClifford : CartesianCl44 :=
  CliffordAlgebra.ι cartesianQuadratic44 scalarPositiveDirection

@[simp] theorem cartesianQuadratic44_scalarPositiveDirection :
    cartesianQuadratic44 scalarPositiveDirection = 1 := by
  exact cartesianQuadratic44_positiveQuaternionDirection 0

@[simp] theorem scalarPositiveClifford_sq :
    scalarPositiveClifford * scalarPositiveClifford = 1 := by
  rw [scalarPositiveClifford, CliffordAlgebra.ι_sq_scalar,
    cartesianQuadratic44_scalarPositiveDirection]
  simp

/-- The fixed positive Clifford vector bundled as an invertible versor. -/
def scalarPositiveCliffordUnit : CartesianCl44ˣ where
  val := scalarPositiveClifford
  inv := scalarPositiveClifford
  val_inv := scalarPositiveClifford_sq
  inv_val := scalarPositiveClifford_sq

@[simp] theorem scalarPositiveCliffordUnit_coe :
    (scalarPositiveCliffordUnit : CartesianCl44) = scalarPositiveClifford :=
  rfl

/-- The implementer is a native Mathlib Lipschitz/versor element. -/
theorem scalarPositiveCliffordUnit_mem_lipschitzGroup :
    scalarPositiveCliffordUnit ∈
      lipschitzGroup cartesianQuadratic44 := by
  apply Subgroup.subset_closure
  exact ⟨scalarPositiveDirection, rfl⟩

/-- Honest signature boundary: the positive versor is excluded from
Mathlib's unitary `pinGroup` for the current real Clifford star convention. -/
theorem scalarPositiveClifford_not_mem_pinGroup :
    scalarPositiveClifford ∉
      pinGroup cartesianQuadratic44 := by
  intro h
  have hunit :
      star scalarPositiveClifford * scalarPositiveClifford = 1 :=
    pinGroup.star_mul_self_of_mem h
  rw [scalarPositiveClifford, CliffordAlgebra.star_ι, neg_mul,
    CliffordAlgebra.ι_sq_scalar,
    cartesianQuadratic44_scalarPositiveDirection] at hunit
  have hscalar : (-1 : ℝ) = 1 := by
    apply (algebraMap ℝ CartesianCl44).injective
    simpa only [map_neg, map_one] using hunit
  norm_num at hscalar

/-- Vector-level line-reflection formula for transported split-octonion
conjugation. -/
theorem cartesianTwistedConj_eq_scalar_line_reflection
    (X : CartesianCoordinates) :
    cartesianTwistedConj X =
      (2 * X.1.1) • scalarPositiveDirection - X := by
  rcases X with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
  apply Prod.ext <;> apply Prod.ext
  · simp [cartesianTwistedConj, scalarPositiveDirection,
      positiveQuaternionDirection, cartesianToRealSplit44]
    ring
  · funext i
    fin_cases i <;>
      simp [cartesianTwistedConj, scalarPositiveDirection,
        positiveQuaternionDirection, cartesianToRealSplit44]
  · simp [cartesianTwistedConj, scalarPositiveDirection,
      positiveQuaternionDirection, cartesianToRealSplit44]
  · funext i
    fin_cases i <;>
      simp [cartesianTwistedConj, scalarPositiveDirection,
        positiveQuaternionDirection, cartesianToRealSplit44]

/-- Polar pairing with the fixed scalar direction extracts twice the scalar
quaternion coordinate. -/
theorem polar_scalarPositiveDirection (X : CartesianCoordinates) :
    QuadraticMap.polar (⇑cartesianQuadratic44)
        X scalarPositiveDirection = 2 * X.1.1 := by
  rcases X with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
  simp [QuadraticMap.polar, cartesianQuadratic44_apply,
    scalarPositiveDirection, positiveQuaternionDirection,
    cartesianToRealSplit44, quaternionNorm,
    InfoGeometry.Canonical.ZornMatrix.dot]
  ring

/-- Ordinary Clifford conjugation by the positive scalar versor implements
the transported Zorn conjugation on every vector generator. -/
theorem scalarPositiveClifford_conj_ι (X : CartesianCoordinates) :
    scalarPositiveClifford *
          CliffordAlgebra.ι cartesianQuadratic44 X *
        scalarPositiveClifford =
      CliffordAlgebra.ι cartesianQuadratic44 (cartesianTwistedConj X) := by
  have hpolar := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := cartesianQuadratic44) X scalarPositiveDirection
  rw [polar_scalarPositiveDirection] at hpolar
  have hleft :
      scalarPositiveClifford * CliffordAlgebra.ι cartesianQuadratic44 X =
        algebraMap ℝ CartesianCl44 (2 * X.1.1) -
          CliffordAlgebra.ι cartesianQuadratic44 X * scalarPositiveClifford := by
    exact eq_sub_of_add_eq (by
      simpa [scalarPositiveClifford, add_comm] using hpolar)
  rw [hleft, sub_mul]
  calc
    algebraMap ℝ CartesianCl44 (2 * X.1.1) * scalarPositiveClifford -
          CliffordAlgebra.ι cartesianQuadratic44 X *
            scalarPositiveClifford * scalarPositiveClifford =
        algebraMap ℝ CartesianCl44 (2 * X.1.1) * scalarPositiveClifford -
          CliffordAlgebra.ι cartesianQuadratic44 X *
            (scalarPositiveClifford * scalarPositiveClifford) := by
              rw [mul_assoc]
    _ = algebraMap ℝ CartesianCl44 (2 * X.1.1) * scalarPositiveClifford -
          CliffordAlgebra.ι cartesianQuadratic44 X := by
            rw [scalarPositiveClifford_sq]
            simp
    _ = CliffordAlgebra.ι cartesianQuadratic44
          (cartesianTwistedConj X) := by
      rw [cartesianTwistedConj_eq_scalar_line_reflection,
        map_sub, map_smul]
      simp only [Algebra.smul_def]
      rfl

/-- Inner algebra homomorphism supplied by the positive scalar versor. -/
def scalarPositiveInnerHom : CartesianCl44 →ₐ[ℝ] CartesianCl44 where
  toFun a := scalarPositiveClifford * a * scalarPositiveClifford
  map_one' := by simp
  map_mul' a b := by
    calc
      scalarPositiveClifford * (a * b) * scalarPositiveClifford =
          scalarPositiveClifford * a * 1 * b * scalarPositiveClifford := by
            noncomm_ring
      _ = scalarPositiveClifford * a *
          (scalarPositiveClifford * scalarPositiveClifford) *
            b * scalarPositiveClifford := by
              rw [scalarPositiveClifford_sq]
      _ = (scalarPositiveClifford * a * scalarPositiveClifford) *
          (scalarPositiveClifford * b * scalarPositiveClifford) := by
            noncomm_ring
  map_zero' := by simp
  map_add' a b := by noncomm_ring
  commutes' r := by
    calc
      scalarPositiveClifford * algebraMap ℝ CartesianCl44 r *
          scalarPositiveClifford =
        algebraMap ℝ CartesianCl44 r *
          (scalarPositiveClifford * scalarPositiveClifford) := by
            rw [(Algebra.commutes r scalarPositiveClifford).symm]
            ac_rfl
      _ = algebraMap ℝ CartesianCl44 r := by
        rw [scalarPositiveClifford_sq]
        simp

/-- The inner implementation is involutive and hence an algebra
automorphism. -/
def scalarPositiveInnerClifford : CartesianCl44 ≃ₐ[ℝ] CartesianCl44 :=
  AlgEquiv.ofAlgHom scalarPositiveInnerHom scalarPositiveInnerHom
    (by
      apply CliffordAlgebra.hom_ext
      apply LinearMap.ext
      intro X
      simp [scalarPositiveInnerHom, scalarPositiveClifford_conj_ι])
    (by
      apply CliffordAlgebra.hom_ext
      apply LinearMap.ext
      intro X
      simp [scalarPositiveInnerHom, scalarPositiveClifford_conj_ι])

/-- The functorial isometry lift constructed previously is exactly the inner
automorphism implemented by the positive scalar versor. -/
theorem cartesianTwistedConjClifford_eq_scalarPositiveInnerClifford :
    cartesianTwistedConjClifford = scalarPositiveInnerClifford := by
  have h : cartesianTwistedConjClifford.toAlgHom =
      scalarPositiveInnerClifford.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro X
    change cartesianTwistedConjClifford
        (CliffordAlgebra.ι cartesianQuadratic44 X) =
      scalarPositiveInnerClifford
        (CliffordAlgebra.ι cartesianQuadratic44 X)
    rw [cartesianTwistedConjClifford_ι]
    exact (scalarPositiveClifford_conj_ι X).symm
  apply AlgEquiv.ext
  intro a
  exact DFunLike.congr_fun h a

/-- Operator-level Dirac implementation on the maintained sixteen-dimensional
real spinor carrier. -/
theorem scalarPositiveGamma_conjugates
    (X : CartesianCoordinates) :
    gammaPositive 0 * cartesianGammaLinear X * gammaPositive 0 =
      cartesianGammaLinear (cartesianTwistedConj X) := by
  have h := congrArg (fun a : CartesianCl44 =>
      cartesianCliffordRepresentation a)
    (scalarPositiveClifford_conj_ι X)
  simpa [scalarPositiveClifford, scalarPositiveDirection,
    gammaPositive, cartesianCliffordRepresentation_ι] using h

/-- Final implementer packet: isometry lift, inner Clifford action, and Dirac
operator conjugation are the same transformation, while native unitary-Pin
membership remains correctly separated from Lipschitz membership. -/
theorem quaternion_twisted_conjugation_implementer_packet
    (X : CartesianCoordinates) :
    scalarPositiveCliffordUnit ∈
        lipschitzGroup cartesianQuadratic44 ∧
      scalarPositiveClifford ∉
        pinGroup cartesianQuadratic44 ∧
      cartesianTwistedConjClifford
          (CliffordAlgebra.ι cartesianQuadratic44 X) =
        scalarPositiveClifford *
            CliffordAlgebra.ι cartesianQuadratic44 X *
          scalarPositiveClifford ∧
      gammaPositive 0 * cartesianGammaLinear X * gammaPositive 0 =
        cartesianGammaLinear (cartesianTwistedConj X) := by
  exact ⟨scalarPositiveCliffordUnit_mem_lipschitzGroup,
    scalarPositiveClifford_not_mem_pinGroup,
    by rw [cartesianTwistedConjClifford_ι,
      scalarPositiveClifford_conj_ι],
    scalarPositiveGamma_conjugates X⟩

end InfoGeometry.Optics.QuaternionCl44DiracImplementer

end noncomputable section
