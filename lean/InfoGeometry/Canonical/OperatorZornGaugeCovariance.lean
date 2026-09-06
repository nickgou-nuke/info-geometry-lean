import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.Canonical.OperatorZornRepresentationCurvatureBridge
import InfoGeometry.Canonical.OperatorZornRealModule

/-!
# Gauge covariance without replacing the operator-Zorn product

A coefficient ring homomorphism acts on all eight entries of the existing
Zorn carrier. This is not a homomorphism into an associative replacement of
that carrier. It preserves the actual ordered Zorn multiplication and its
associator, as well as the curvature and Bianchi identities.

Unit conjugation supplies a concrete gauge family. Its transformation of the
coefficient derivative generator includes the exact inhomogeneous commutator
term. No constancy or commutation with that generator is assumed. This is
coefficient-unit gauge covariance, not a classification of every Zorn-frame
automorphism and not a claim that every such automorphism is inner.
-/

namespace InfoGeometry.Canonical.OperatorZornGaugeCovariance

open InfoGeometry.Physics.NCG
open OperatorZornFourPotentialGauge
open OperatorZornRepresentationCurvatureBridge

variable {A B : Type*} [Ring A] [Ring B]

/-- Entrywise coefficient transport; the Zorn carrier and product are retained. -/
def mapCoefficients (f : A →+* B) (X : OperatorZornMatrix A) : OperatorZornMatrix B :=
  operatorZornCoordinates (f X.n_plus) (f X.n_minus)
    (mapOperatorVector f X.sigma_plus) (mapOperatorVector f X.sigma_minus)

theorem mapCoefficients_add (f : A →+* B) (X Y : OperatorZornMatrix A) :
    mapCoefficients f (X + Y) = mapCoefficients f X + mapCoefficients f Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals change f (_ + _) = f _ + f _
  all_goals exact f.map_add _ _

theorem mapCoefficients_sub (f : A →+* B) (X Y : OperatorZornMatrix A) :
    mapCoefficients f (X - Y) = mapCoefficients f X - mapCoefficients f Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals change f (_ + -_) = f _ + -f _
  all_goals simp only [map_add, map_neg]

theorem mapCoefficients_mul (f : A →+* B) (X Y : OperatorZornMatrix A) :
    mapCoefficients f (X * Y) = mapCoefficients f X * mapCoefficients f Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [mapCoefficients, mapOperatorVector, operatorZornCoordinates,
    OperatorZornRealModule.mul_n_plus, OperatorZornRealModule.mul_n_minus,
    OperatorZornRealModule.mul_sigma_plus,
    OperatorZornRealModule.mul_sigma_minus,
    mapOperatorVector_dot, mapOperatorVector_cross,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross,
    map_add, map_sub, map_mul]

/-- Transport preserves the associator rather than annihilating it. -/
theorem mapCoefficients_associator (f : A →+* B) (X Y Z : OperatorZornMatrix A) :
    mapCoefficients f (OperatorZornFourPotentialGauge.associator X Y Z) =
      OperatorZornFourPotentialGauge.associator (mapCoefficients f X)
        (mapCoefficients f Y) (mapCoefficients f Z) := by
  unfold OperatorZornFourPotentialGauge.associator
  rw [mapCoefficients_sub, mapCoefficients_mul, mapCoefficients_mul,
    mapCoefficients_mul, mapCoefficients_mul]

theorem mapCoefficients_deriv (f : A →+* B) (p : A) (X : OperatorZornMatrix A) :
    mapCoefficients f (coefficientDeriv p X) =
      coefficientDeriv (f p) (mapCoefficients f X) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [mapCoefficients, mapOperatorVector, operatorZornCoordinates,
    coefficientDeriv, coefficientBracket]
  all_goals simp only [map_sub, map_mul]

theorem mapCoefficients_covariant (f : A →+* B) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) (X : OperatorZornMatrix A) :
    mapCoefficients f (covariant p Phi mu X) =
      covariant (fun i => f (p i)) (fun i => mapCoefficients f (Phi i)) mu
        (mapCoefficients f X) := by
  unfold covariant
  rw [mapCoefficients_add, mapCoefficients_deriv, mapCoefficients_mul]

theorem mapCoefficients_fieldStrength (f : A →+* B) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) :
    mapCoefficients f (fieldStrength p Phi mu nu) =
      fieldStrength (fun i => f (p i)) (fun i => mapCoefficients f (Phi i)) mu nu := by
  unfold fieldStrength bracket
  simp only [mapCoefficients_add, mapCoefficients_sub, mapCoefficients_deriv,
    mapCoefficients_mul]

theorem mapCoefficients_curvatureAction (f : A →+* B) (p : Fin 4 → A)
    (Phi : FourPotential A) (mu nu : Fin 4) (X : OperatorZornMatrix A) :
    mapCoefficients f (curvatureAction p Phi mu nu X) =
      curvatureAction (fun i => f (p i)) (fun i => mapCoefficients f (Phi i)) mu nu
        (mapCoefficients f X) := by
  unfold curvatureAction
  rw [mapCoefficients_sub]
  simp only [mapCoefficients_covariant]

theorem mapCoefficients_adjointCovariant (f : A →+* B) (p : Fin 4 → A)
    (Phi : FourPotential A) (mu : Fin 4) (X : OperatorZornMatrix A) :
    mapCoefficients f (adjointCovariant p Phi mu X) =
      adjointCovariant (fun i => f (p i)) (fun i => mapCoefficients f (Phi i)) mu
        (mapCoefficients f X) := by
  unfold adjointCovariant bracket
  simp only [mapCoefficients_add, mapCoefficients_sub, mapCoefficients_deriv,
    mapCoefficients_mul]

theorem mapCoefficients_bianchi (f : A →+* B) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu rho : Fin 4) :
    mapCoefficients f (bianchi p Phi mu nu rho) =
      bianchi (fun i => f (p i)) (fun i => mapCoefficients f (Phi i)) mu nu rho := by
  unfold bianchi
  simp only [mapCoefficients_add, mapCoefficients_adjointCovariant,
    mapCoefficients_fieldStrength]

/-- Conjugation in the coefficient algebra, not conjugation of Zorn elements. -/
def coefficientConjugation (g : Aˣ) : A →+* A where
  toFun x := (g : A) * x * ((g⁻¹ : Aˣ) : A)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]
  map_mul' x y := by
    change (g : A) * (x * y) * ((g⁻¹ : Aˣ) : A) =
      ((g : A) * x * ((g⁻¹ : Aˣ) : A)) * ((g : A) * y * ((g⁻¹ : Aˣ) : A))
    symm
    calc
      _ = (g : A) * x * (((g⁻¹ : Aˣ) : A) * (g : A)) * y *
          ((g⁻¹ : Aˣ) : A) := by simp only [mul_assoc]
      _ = (g : A) * (x * y) * ((g⁻¹ : Aˣ) : A) := by
        calc
          _ = (g : A) * x * (((g⁻¹ : Aˣ) : A) * (g : A)) * y *
              ((g⁻¹ : Aˣ) : A) := by rfl
          _ = (g : A) * x * 1 * y * ((g⁻¹ : Aˣ) : A) := by
            have hgi : ((g⁻¹ : Aˣ) : A) * (g : A) = 1 := g.inv_val
            rw [hgi]
          _ = (g : A) * (x * y) * ((g⁻¹ : Aˣ) : A) := by noncomm_ring

theorem coefficientConjugation_inverse_apply (g : Aˣ) (x : A) :
    coefficientConjugation g⁻¹ (coefficientConjugation g x) = x := by
  change ((g⁻¹ : Aˣ) : A) * ((g : A) * x * ((g⁻¹ : Aˣ) : A)) * (g : A) = x
  calc
    _ = (((g⁻¹ : Aˣ) : A) * (g : A)) * x *
        (((g⁻¹ : Aˣ) : A) * (g : A)) := by simp only [mul_assoc]
    _ = x := by
      have hgi : ((g⁻¹ : Aˣ) : A) * (g : A) = 1 := g.inv_val
      rw [hgi]
      simp

/-- The inhomogeneous frame term is retained even when `g` does not commute with `p`. -/
theorem transformed_generator_eq (g : Aˣ) (p : A) :
    coefficientConjugation g p =
      p - coefficientBracket p (g : A) * ((g⁻¹ : Aˣ) : A) := by
  change (g : A) * p * ((g⁻¹ : Aˣ) : A) =
    p - (p * (g : A) - (g : A) * p) * ((g⁻¹ : Aˣ) : A)
  rw [sub_mul]
  have hg : (g : A) * ((g⁻¹ : Aˣ) : A) = 1 := g.val_inv
  rw [mul_assoc p (g : A), hg, mul_one]
  abel

def gauge (g : Aˣ) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  mapCoefficients (coefficientConjugation g) X

theorem gauge_inverse_apply (g : Aˣ) (X : OperatorZornMatrix A) :
    gauge g⁻¹ (gauge g X) = X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals change coefficientConjugation g⁻¹ (coefficientConjugation g _) = _
  all_goals exact coefficientConjugation_inverse_apply g _

/-- An actual bijective gauge change of the same nonassociative carrier. -/
def gaugeEquiv (g : Aˣ) : OperatorZornMatrix A ≃ OperatorZornMatrix A where
  toFun := gauge g
  invFun := gauge g⁻¹
  left_inv := gauge_inverse_apply g
  right_inv X := by simpa only [inv_inv] using gauge_inverse_apply g⁻¹ X

/-- A genuine action on the nonassociative multiplication, not an associative quotient. -/
theorem gauge_mul (g : Aˣ) (X Y : OperatorZornMatrix A) :
    gauge g (X * Y) = gauge g X * gauge g Y :=
  mapCoefficients_mul (coefficientConjugation g) X Y

theorem gauge_associator (g : Aˣ) (X Y Z : OperatorZornMatrix A) :
    gauge g (associator X Y Z) = associator (gauge g X) (gauge g Y) (gauge g Z) :=
  mapCoefficients_associator (coefficientConjugation g) X Y Z

theorem gauge_covariant (g : Aˣ) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) (X : OperatorZornMatrix A) :
    gauge g (covariant p Phi mu X) =
      covariant (fun i => coefficientConjugation g (p i)) (fun i => gauge g (Phi i))
        mu (gauge g X) :=
  mapCoefficients_covariant (coefficientConjugation g) p Phi mu X

theorem gauge_fieldStrength (g : Aˣ) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) :
    gauge g (fieldStrength p Phi mu nu) =
      fieldStrength (fun i => coefficientConjugation g (p i)) (fun i => gauge g (Phi i))
        mu nu :=
  mapCoefficients_fieldStrength (coefficientConjugation g) p Phi mu nu

theorem gauge_curvatureAction (g : Aˣ) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) (X : OperatorZornMatrix A) :
    gauge g (curvatureAction p Phi mu nu X) =
      curvatureAction (fun i => coefficientConjugation g (p i)) (fun i => gauge g (Phi i))
        mu nu (gauge g X) :=
  mapCoefficients_curvatureAction (coefficientConjugation g) p Phi mu nu X

theorem gauge_bianchi (g : Aˣ) (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu rho : Fin 4) :
    gauge g (bianchi p Phi mu nu rho) =
      bianchi (fun i => coefficientConjugation g (p i)) (fun i => gauge g (Phi i))
        mu nu rho :=
  mapCoefficients_bianchi (coefficientConjugation g) p Phi mu nu rho

end InfoGeometry.Canonical.OperatorZornGaugeCovariance
