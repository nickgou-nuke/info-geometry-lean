import InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge

set_option autoImplicit false

/-!
# Quaternionic twisted conjugation lifted to the real `Cl(4,4)` algebra

The canonical split-octonion conjugation is already expressed on the
quaternion-pair carrier by `cartesianTwistedConj`.  This file proves that this
linear involution is an isometry of the maintained `(4,4)` quadratic form and
therefore lifts, through Mathlib's `CliffordAlgebra.equivOfIsometry`, to an
actual algebra automorphism of the real Clifford algebra.

On each fixed-colour four-dimensional sector the carrier reflection is exactly
the coordinate split-quaternion Clifford conjugation.  The induced Clifford
automorphism must not be confused with the intrinsic Clifford conjugation
anti-involution: it is the functorial lift of that coordinate-space isometry.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44TwistedConjugationLift

open CanonicalZornRealSpin44
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge
open InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge

abbrev CartesianCl44 := CliffordAlgebra cartesianQuadratic44

/-- The transported canonical Zorn conjugation as a linear equivalence of the
quaternionic `(4+4)` coordinate carrier. -/
def cartesianTwistedConjLinearEquiv :
    CartesianCoordinates ≃ₗ[ℝ] CartesianCoordinates :=
  LinearEquiv.ofLinear cartesianTwistedConj cartesianTwistedConj
    (by
      apply LinearMap.ext
      intro X
      exact cartesianTwistedConj_involutive X)
    (by
      apply LinearMap.ext
      intro X
      exact cartesianTwistedConj_involutive X)

@[simp] theorem cartesianTwistedConjLinearEquiv_apply
    (X : CartesianCoordinates) :
    cartesianTwistedConjLinearEquiv X = cartesianTwistedConj X :=
  rfl

/-- Canonical split-octonion conjugation preserves the pulled-back real
quadratic form of signature `(4,4)`. -/
theorem cartesianTwistedConj_preserves_cartesianQuadratic44
    (X : CartesianCoordinates) :
    cartesianQuadratic44 (cartesianTwistedConj X) =
      cartesianQuadratic44 X := by
  rw [cartesianQuadratic44_apply, cartesianQuadratic44_apply]
  exact cartesianTwistedConj_preserves_normDifference X

/-- The quaternionic twisted conjugation bundled as a quadratic-form
isometry. -/
def cartesianTwistedConjIsometry :
    cartesianQuadratic44.IsometryEquiv cartesianQuadratic44 where
  __ := cartesianTwistedConjLinearEquiv
  map_app' := cartesianTwistedConj_preserves_cartesianQuadratic44

@[simp] theorem cartesianTwistedConjIsometry_apply
    (X : CartesianCoordinates) :
    cartesianTwistedConjIsometry X = cartesianTwistedConj X :=
  rfl

/-- Functorial Clifford-algebra automorphism induced by canonical Zorn
conjugation on the vector carrier. -/
def cartesianTwistedConjClifford : CartesianCl44 ≃ₐ[ℝ] CartesianCl44 :=
  CliffordAlgebra.equivOfIsometry cartesianTwistedConjIsometry

@[simp] theorem cartesianTwistedConjClifford_ι
    (X : CartesianCoordinates) :
    cartesianTwistedConjClifford
        (CliffordAlgebra.ι cartesianQuadratic44 X) =
      CliffordAlgebra.ι cartesianQuadratic44 (cartesianTwistedConj X) := by
  change CliffordAlgebra.map cartesianTwistedConjIsometry.toIsometry
      (CliffordAlgebra.ι cartesianQuadratic44 X) = _
  rw [CliffordAlgebra.map_apply_ι]
  rfl

/-- The lifted algebra automorphism is itself involutive. -/
theorem cartesianTwistedConjClifford_involutive (a : CartesianCl44) :
    cartesianTwistedConjClifford
        (cartesianTwistedConjClifford a) = a := by
  let lhs : CartesianCl44 →ₐ[ℝ] CartesianCl44 :=
    (cartesianTwistedConjClifford : CartesianCl44 →ₐ[ℝ] CartesianCl44).comp
      (cartesianTwistedConjClifford : CartesianCl44 →ₐ[ℝ] CartesianCl44)
  have hlhs : lhs = AlgHom.id ℝ CartesianCl44 := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro X
    change cartesianTwistedConjClifford
        (cartesianTwistedConjClifford
          (CliffordAlgebra.ι cartesianQuadratic44 X)) =
      CliffordAlgebra.ι cartesianQuadratic44 X
    rw [cartesianTwistedConjClifford_ι,
      cartesianTwistedConjClifford_ι,
      cartesianTwistedConj_involutive]
  exact DFunLike.congr_fun hlhs a

/-- On every fixed-colour associative plane, the carrier isometry is exactly
split-quaternion Clifford conjugation. -/
@[simp] theorem cartesianTwistedConjIsometry_cl11Cartesian
    (i : Fin 3) (q : Cl11) :
    cartesianTwistedConjIsometry (cl11Cartesian i q) =
      cl11Cartesian i (cliffordConjugate q) := by
  simpa only [cartesianTwistedConjIsometry_apply] using
    cartesianTwistedConj_cl11Cartesian i q

/-- The `Cl(4,4)` automorphism restricts on a fixed-colour generator to the
split-quaternion Clifford-conjugate coordinate. -/
theorem cartesianTwistedConjClifford_cl11Generator
    (i : Fin 3) (q : Cl11) :
    cartesianTwistedConjClifford
        (CliffordAlgebra.ι cartesianQuadratic44 (cl11Cartesian i q)) =
      CliffordAlgebra.ι cartesianQuadratic44
        (cl11Cartesian i (cliffordConjugate q)) := by
  rw [cartesianTwistedConjClifford_ι,
    cartesianTwistedConj_cl11Cartesian]

/-- Dirac readout of the fixed-colour conjugated generator.  This explicitly
connects the algebraic lift to the maintained sixteen-dimensional operator
representation. -/
theorem represented_twistedConj_cl11Generator
    (i : Fin 3) (q : Cl11) :
    realClifford44Representation
        (CliffordAlgebra.ι realQuadratic44
          (cartesianToRealSplit44
            (cartesianTwistedConjIsometry (cl11Cartesian i q)))) =
      cartesianGammaLinear
        (cl11Cartesian i (cliffordConjugate q)) := by
  rw [cartesianTwistedConjIsometry_cl11Cartesian,
    realClifford44Representation_ι]
  rfl

/-! ## Action on the two explicit groups of four generators -/

@[simp] theorem cartesianTwistedConj_positive_zero :
    cartesianTwistedConj (positiveQuaternionDirection 0) =
      positiveQuaternionDirection 0 := by
  change cartesianTwistedConj
      (cartesianToRealSplit44.symm (Pi.single 0 1, 0)) = _
  apply cartesianToRealSplit44.injective
  ext j <;> fin_cases j <;>
    simp [positiveQuaternionDirection, cartesianToRealSplit44,
      cartesianTwistedConj]

@[simp] theorem cartesianTwistedConj_positive_succ (i : Fin 3) :
    cartesianTwistedConj (positiveQuaternionDirection i.succ) =
      -positiveQuaternionDirection i.succ := by
  change cartesianTwistedConj
      (cartesianToRealSplit44.symm (Pi.single i.succ 1, 0)) = _
  apply cartesianToRealSplit44.injective
  ext j <;> fin_cases i <;> fin_cases j <;>
    simp [positiveQuaternionDirection, cartesianToRealSplit44,
      cartesianTwistedConj]

@[simp] theorem cartesianTwistedConj_negative
    (i : Fin 4) :
    cartesianTwistedConj (negativeHypercomplexDirection i) =
      -negativeHypercomplexDirection i := by
  change cartesianTwistedConj
      (cartesianToRealSplit44.symm (0, Pi.single i 1)) = _
  apply cartesianToRealSplit44.injective
  ext j <;> fin_cases i <;> fin_cases j <;>
    simp [negativeHypercomplexDirection, cartesianToRealSplit44,
      cartesianTwistedConj]

/-- Complete closure packet: the transported split-octonion conjugation is a
quadratic involution, its Clifford lift is involutive, and each fixed-colour
split-quaternion generator is sent to its Clifford conjugate. -/
theorem quaternion_twisted_conjugation_cl44_packet
    (i : Fin 3) (q : Cl11) (a : CartesianCl44) :
    cartesianQuadratic44 (cartesianTwistedConj (cl11Cartesian i q)) =
        cartesianQuadratic44 (cl11Cartesian i q) ∧
      cartesianTwistedConjClifford
          (cartesianTwistedConjClifford a) = a ∧
      cartesianTwistedConjClifford
          (CliffordAlgebra.ι cartesianQuadratic44 (cl11Cartesian i q)) =
        CliffordAlgebra.ι cartesianQuadratic44
          (cl11Cartesian i (cliffordConjugate q)) := by
  exact ⟨cartesianTwistedConj_preserves_cartesianQuadratic44 _,
    cartesianTwistedConjClifford_involutive a,
    cartesianTwistedConjClifford_cl11Generator i q⟩

end InfoGeometry.Optics.QuaternionCl44TwistedConjugationLift

end noncomputable section
