import InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge
import InfoGeometry.Canonical.CanonicalZornRealSpin44
import InfoGeometry.Clifford.QuadraticPolarAnticommutator

set_option autoImplicit false

/-!
# Quaternionic `(4+4)` coordinates in the real `Cl(4,4)` Dirac representation

The existing quaternion-pair carrier is identified isometrically with the
standard real split carrier used by `CanonicalZornRealSpin44`.  The existing
sixteen-dimensional gamma representation is then pulled back along that
equivalence.  Its square and full polarized anticommutator are proved, followed
by their restriction to every fixed-colour `Cl(1,1)` plane.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge

open CanonicalZornCliffordRepresentation
open CanonicalZornRealSpin44
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge

abbrev DiracEnd44 := Module.End ℝ DiracSpinor16

/-- Coordinate ordering equivalence from two scalar/vector quaternion copies
to the standard diagonal `ℝ⁴ ⊕ ℝ⁴` split carrier. -/
def cartesianToRealSplit44 : CartesianCoordinates ≃ₗ[ℝ] RealSplit44 where
  toFun X :=
    (![X.1.1, X.1.2 0, X.1.2 1, X.1.2 2],
      ![X.2.1, X.2.2 0, X.2.2 1, X.2.2 2])
  invFun x :=
    ((x.1 0, ![x.1 1, x.1 2, x.1 3]),
      (x.2 0, ![x.2 1, x.2 2, x.2 3]))
  left_inv X := by
    apply Prod.ext <;> apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' X Y := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' c X := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- Pullback of the maintained real split `(4,4)` quadratic form. -/
def cartesianQuadratic44 : QuadraticForm ℝ CartesianCoordinates :=
  realQuadratic44.comp cartesianToRealSplit44.toLinearMap

@[simp] theorem cartesianQuadratic44_apply (X : CartesianCoordinates) :
    cartesianQuadratic44 X =
      quaternionNorm X.1 - quaternionNorm X.2 := by
  rcases X with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
  simp [cartesianQuadratic44, cartesianToRealSplit44,
    realQuadratic44_apply, quaternionNorm,
    InfoGeometry.Canonical.ZornMatrix.dot,
    Fin.sum_univ_four, pow_two]
  ring_nf

/-- The existing real Zorn gamma representation pulled back to quaternionic
`(4+4)` coordinates. -/
def cartesianGammaLinear :
    CartesianCoordinates →ₗ[ℝ] DiracEnd44 :=
  realGammaLinear.comp cartesianToRealSplit44.toLinearMap

@[simp] theorem cartesianGammaLinear_apply (X : CartesianCoordinates) :
    cartesianGammaLinear X = realGammaLinear (cartesianToRealSplit44 X) :=
  rfl

/-- Genuine Clifford square relation in quaternionic coordinates. -/
theorem cartesianGamma_sq (X : CartesianCoordinates) :
    cartesianGammaLinear X * cartesianGammaLinear X =
      algebraMap ℝ DiracEnd44 (cartesianQuadratic44 X) := by
  change realGammaLinear (cartesianToRealSplit44 X) *
      realGammaLinear (cartesianToRealSplit44 X) = _
  rw [realGamma_sq]
  rfl

/-- Genuine real Clifford representation on the quaternionic `(4+4)`
coordinate carrier. -/
def cartesianCliffordRepresentation :
    CliffordAlgebra cartesianQuadratic44 →ₐ[ℝ] DiracEnd44 :=
  CliffordAlgebra.lift cartesianQuadratic44
    ⟨cartesianGammaLinear, cartesianGamma_sq⟩

@[simp] theorem cartesianCliffordRepresentation_ι
    (X : CartesianCoordinates) :
    cartesianCliffordRepresentation
        (CliffordAlgebra.ι cartesianQuadratic44 X) =
      cartesianGammaLinear X := by
  exact CliffordAlgebra.lift_ι_apply
    cartesianGammaLinear cartesianGamma_sq X

/-- Full Dirac/Clifford anticommutator, obtained by polarizing the square law. -/
theorem cartesianGamma_anticommutator (X Y : CartesianCoordinates) :
    cartesianGammaLinear X * cartesianGammaLinear Y +
        cartesianGammaLinear Y * cartesianGammaLinear X =
      algebraMap ℝ DiracEnd44
        (polarFromQuadratic cartesianQuadratic44 X Y) := by
  exact clifford_anticommutator_from_square_relation
    cartesianQuadratic44 cartesianGammaLinear
    (fun X Y => cartesianGammaLinear.map_add X Y)
    cartesianGamma_sq X Y

/-! ## Two orthogonal groups of four gamma generators -/

/-- The four positive quaternion-coordinate directions. -/
def positiveQuaternionDirection (i : Fin 4) : CartesianCoordinates :=
  cartesianToRealSplit44.symm (Pi.single i 1, 0)

/-- The four negative hyperbolic-partner directions. -/
def negativeHypercomplexDirection (i : Fin 4) : CartesianCoordinates :=
  cartesianToRealSplit44.symm (0, Pi.single i 1)

def gammaPositive (i : Fin 4) : DiracEnd44 :=
  cartesianGammaLinear (positiveQuaternionDirection i)

def gammaNegative (i : Fin 4) : DiracEnd44 :=
  cartesianGammaLinear (negativeHypercomplexDirection i)

@[simp] theorem cartesianQuadratic44_positiveQuaternionDirection (i : Fin 4) :
    cartesianQuadratic44 (positiveQuaternionDirection i) = 1 := by
  change realQuadratic44
      (cartesianToRealSplit44 (cartesianToRealSplit44.symm (Pi.single i 1, 0))) = 1
  rw [cartesianToRealSplit44.apply_symm_apply]
  fin_cases i <;>
    simp [realQuadratic44_apply, Pi.single_apply]

@[simp] theorem cartesianQuadratic44_negativeHypercomplexDirection (i : Fin 4) :
    cartesianQuadratic44 (negativeHypercomplexDirection i) = -1 := by
  change realQuadratic44
      (cartesianToRealSplit44 (cartesianToRealSplit44.symm (0, Pi.single i 1))) = -1
  rw [cartesianToRealSplit44.apply_symm_apply]
  fin_cases i <;>
    simp [realQuadratic44_apply, Pi.single_apply]

@[simp] theorem gammaPositive_sq (i : Fin 4) :
    gammaPositive i * gammaPositive i = 1 := by
  rw [gammaPositive, cartesianGamma_sq,
    cartesianQuadratic44_positiveQuaternionDirection]
  exact map_one (algebraMap ℝ DiracEnd44)

@[simp] theorem gammaNegative_sq (i : Fin 4) :
    gammaNegative i * gammaNegative i = -1 := by
  rw [gammaNegative, cartesianGamma_sq,
    cartesianQuadratic44_negativeHypercomplexDirection, map_neg, map_one]

/-- Every positive quaternion gamma anticommutes with every negative
hypercomplex gamma. -/
theorem gammaPositive_gammaNegative_anticommutator
    (i j : Fin 4) :
    gammaPositive i * gammaNegative j +
        gammaNegative j * gammaPositive i = 0 := by
  rw [gammaPositive, gammaNegative, cartesianGamma_anticommutator]
  suffices h : polarFromQuadratic cartesianQuadratic44
      (positiveQuaternionDirection i) (negativeHypercomplexDirection j) = 0 by
    rw [h, map_zero]
  unfold polarFromQuadratic positiveQuaternionDirection negativeHypercomplexDirection
  change realQuadratic44
      (cartesianToRealSplit44
        (cartesianToRealSplit44.symm (Pi.single i 1, 0) +
          cartesianToRealSplit44.symm (0, Pi.single j 1))) -
      realQuadratic44 (Pi.single i 1, 0) -
      realQuadratic44 (0, Pi.single j 1) = 0
  rw [map_add, cartesianToRealSplit44.apply_symm_apply,
    cartesianToRealSplit44.apply_symm_apply]
  fin_cases i <;> fin_cases j <;>
    simp [realQuadratic44_apply, Pi.single_apply]

/-- Polarized Clifford relation in the maintained standard real split
carrier. -/
theorem realGamma_anticommutator (x y : RealSplit44) :
    realGammaLinear x * realGammaLinear y +
        realGammaLinear y * realGammaLinear x =
      algebraMap ℝ DiracEnd44
        (polarFromQuadratic realQuadratic44 x y) := by
  exact clifford_anticommutator_from_square_relation
    realQuadratic44 realGammaLinear
    (fun x y => realGammaLinear.map_add x y)
    realGamma_sq x y

set_option maxHeartbeats 1000000 in
/-- Distinct generators inside the positive group anticommute. -/
theorem gammaPositive_anticommutator_of_ne
    (i j : Fin 4) (hij : i ≠ j) :
    gammaPositive i * gammaPositive j +
        gammaPositive j * gammaPositive i = 0 := by
  change realGammaLinear (Pi.single i 1, 0) *
      realGammaLinear (Pi.single j 1, 0) +
        realGammaLinear (Pi.single j 1, 0) *
          realGammaLinear (Pi.single i 1, 0) = 0
  rw [realGamma_anticommutator]
  unfold polarFromQuadratic
  fin_cases i <;> fin_cases j <;>
    simp_all [realQuadratic44_apply, Pi.single_apply, Fin.sum_univ_four]

set_option maxHeartbeats 1000000 in
/-- Distinct generators inside the negative group anticommute. -/
theorem gammaNegative_anticommutator_of_ne
    (i j : Fin 4) (hij : i ≠ j) :
    gammaNegative i * gammaNegative j +
        gammaNegative j * gammaNegative i = 0 := by
  change realGammaLinear (0, Pi.single i 1) *
      realGammaLinear (0, Pi.single j 1) +
        realGammaLinear (0, Pi.single j 1) *
          realGammaLinear (0, Pi.single i 1) = 0
  rw [realGamma_anticommutator]
  unfold polarFromQuadratic
  fin_cases i <;> fin_cases j <;>
    simp_all [realQuadratic44_apply, Pi.single_apply, Fin.sum_univ_four]

/-- The eight explicit generators have signature `(4,4)` and all generators
from different basis directions anticommute. -/
theorem eight_gamma_generator_packet :
    (∀ i : Fin 4, gammaPositive i * gammaPositive i = 1) ∧
      (∀ i : Fin 4, gammaNegative i * gammaNegative i = -1) ∧
      (∀ i j : Fin 4, gammaPositive i * gammaNegative j +
          gammaNegative j * gammaPositive i = 0) ∧
      (∀ i j : Fin 4, i ≠ j →
        gammaPositive i * gammaPositive j + gammaPositive j * gammaPositive i = 0) ∧
      (∀ i j : Fin 4, i ≠ j →
        gammaNegative i * gammaNegative j + gammaNegative j * gammaNegative i = 0) := by
  exact ⟨gammaPositive_sq, gammaNegative_sq,
    gammaPositive_gammaNegative_anticommutator,
    gammaPositive_anticommutator_of_ne,
    gammaNegative_anticommutator_of_ne⟩

/-- On a fixed-colour `Cl(1,1)` plane, the eight-dimensional gamma square is
the embedded `(2,2)` split norm. -/
theorem cl11Cartesian_gamma_sq (i : Fin 3) (q : Cl11) :
    cartesianGammaLinear (cl11Cartesian i q) *
        cartesianGammaLinear (cl11Cartesian i q) =
      algebraMap ℝ DiracEnd44 (splitNorm q) := by
  rw [cartesianGamma_sq, cartesianQuadratic44_apply,
    normDifference_cl11Cartesian]

/-- On the same associative plane, the global `Cl(4,4)` gamma
anticommutator restricts to twice the native `Cl(1,1)` Krein pairing. -/
theorem cl11Cartesian_gamma_anticommutator
    (i : Fin 3) (q r : Cl11) :
    cartesianGammaLinear (cl11Cartesian i q) *
          cartesianGammaLinear (cl11Cartesian i r) +
        cartesianGammaLinear (cl11Cartesian i r) *
          cartesianGammaLinear (cl11Cartesian i q) =
      algebraMap ℝ DiracEnd44 (2 * kreinMetric q r) := by
  rw [cartesianGamma_anticommutator]
  congr 1
  unfold polarFromQuadratic
  rw [cartesianQuadratic44_apply, cartesianQuadratic44_apply,
    cartesianQuadratic44_apply]
  simpa [cartesianNormPolar] using cartesianNormPolar_cl11Cartesian i q r

/-- Operator-level closure packet for the quaternionic `(4+4)` carrier and
its fixed-colour `Cl(1,1)` subplanes. -/
theorem quaternion_cl44_cl11_dirac_packet
    (i : Fin 3) (q r : Cl11) :
    cartesianQuadratic44 (cl11Cartesian i q) = splitNorm q ∧
      cartesianGammaLinear (cl11Cartesian i q) *
          cartesianGammaLinear (cl11Cartesian i q) =
        algebraMap ℝ DiracEnd44 (splitNorm q) ∧
      cartesianGammaLinear (cl11Cartesian i q) *
            cartesianGammaLinear (cl11Cartesian i r) +
          cartesianGammaLinear (cl11Cartesian i r) *
            cartesianGammaLinear (cl11Cartesian i q) =
        algebraMap ℝ DiracEnd44 (2 * kreinMetric q r) := by
  exact ⟨by simp [normDifference_cl11Cartesian],
    cl11Cartesian_gamma_sq i q,
    cl11Cartesian_gamma_anticommutator i q r⟩

end InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge
