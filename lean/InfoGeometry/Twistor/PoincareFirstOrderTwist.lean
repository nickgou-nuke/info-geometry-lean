import InfoGeometry.QuantumAlgebra.FirstOrderTwist
import InfoGeometry.Twistor.TwistedGaugeCoefficients

/-!
# A nontrivial Poincare first-order twistor example

The polynomial coordinates are lambda0, lambda1, mu0, mu1. The commuting
Poincare vector fields lambda0 d_mu0 and lambda0 d_lambda1 give an exact
associative deformation modulo h^2. Fibre products are unchanged but mixed
products are not. This is an explicit instance, not the classification of all
Poincare twists, nor an all-orders exponential/twist-unimodularity proof.
-/
noncomputable section
namespace InfoGeometry.Twistor.PoincareFirstOrder
open InfoGeometry.QuantumAlgebra.FirstOrderTwist
open MvPolynomial

abbrev Coordinates := MvPolynomial (Fin 4) ℂ

def translation : Derivation ℂ Coordinates Coordinates := X 0 • pderiv 2

def leftLorentz : Derivation ℂ Coordinates Coordinates := X 0 • pderiv 1

@[simp] theorem translation_apply (f : Coordinates) : translation f=X 0*pderiv 2 f := rfl
@[simp] theorem leftLorentz_apply (f : Coordinates) : leftLorentz f=X 0*pderiv 1 f := rfl

/-- Mixed formal derivatives commute, derived on native polynomial coefficients. -/
theorem partials_commute (i j : Fin 4) (f : Coordinates) :
    pderiv i (pderiv j f)=pderiv j (pderiv i f) := by
  ext m
  by_cases h : i=j
  · subst j
    rfl
  · have hji : j≠i := Ne.symm h
    simp [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, h, hji,
      add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

theorem poincare_legs_commute (f : Coordinates) :
    translation (leftLorentz f)=leftLorentz (translation f) := by
  simp only [translation_apply, leftLorentz_apply, pderiv_mul]
  norm_num [pderiv_X, Pi.single_apply]
  rw [partials_commute 2 1 f]

def cocycle := derivationCocycle translation leftLorentz
abbrev TwistedCoordinates := cocycle.Jet

def coordinate (i : Fin 4) : TwistedCoordinates := cocycle.constant (X i)

def hbar : TwistedCoordinates := cocycle.parameter

theorem hbar_square_zero : hbar*hbar=0 := Cocycle.parameter_sq _

theorem left_fibre_product (i j : Fin 2) :
    coordinate (Fin.castLE (by omega) i)*coordinate (Fin.castLE (by omega) j) =
      cocycle.constant (X (Fin.castLE (by omega) i)*X (Fin.castLE (by omega) j)) := by
  apply invariant_fibre_product
  fin_cases i <;> simp [translation_apply, pderiv_X, Pi.single_apply]

theorem left_fibre_commutes (i j : Fin 2) :
    coordinate (Fin.castLE (by omega) i)*coordinate (Fin.castLE (by omega) j) =
      coordinate (Fin.castLE (by omega) j)*coordinate (Fin.castLE (by omega) i) := by
  rw [left_fibre_product, left_fibre_product, mul_comm]

/-- The commutator is hbar lambda0^2, not zero. -/
theorem mixed_commutator : coordinate 2*coordinate 1-coordinate 1*coordinate 2 =
    ((0,(X 0 : Coordinates)^2) : TwistedCoordinates) := by
  rw [coordinate, coordinate, Cocycle.constant_commutator]
  apply Prod.ext
  · rfl
  · change translation (X 2)*leftLorentz (X 1)-translation (X 1)*leftLorentz (X 2)=_
    norm_num [translation_apply, leftLorentz_apply, pderiv_X, Pi.single_apply, pow_two]

theorem fibre_not_central : coordinate 2*coordinate 1 ≠ coordinate 1*coordinate 2 := by
  intro h
  have hh : coordinate 2*coordinate 1-coordinate 1*coordinate 2=0 := sub_eq_zero.mpr h
  rw [mixed_commutator] at hh
  have hp : (X 0 : Coordinates)^2=0 := congrArg Prod.snd hh
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 4 => (1 : ℂ))) hp
  norm_num at he

/-- Two commuting differentials on the actual noncommutative coefficient ring. -/
def differential (i : Fin 2) : TwistedCoordinates →+ TwistedCoordinates :=
  liftDifferential translation leftLorentz (if i=0 then translation else leftLorentz)

theorem differential_leibniz (i : Fin 2) (x y : TwistedCoordinates) :
    differential i (x*y)=differential i x*y+x*differential i y := by
  apply liftDifferential_leibniz
  · intro f
    fin_cases i
    · rfl
    · exact (poincare_legs_commute f).symm
  · intro f
    fin_cases i
    · exact poincare_legs_commute f
    · rfl

theorem differentials_commute (i j : Fin 2) (x : TwistedCoordinates) :
    differential i (differential j x)=differential j (differential i x) := by
  fin_cases i <;> fin_cases j
  · rfl
  · apply Prod.ext <;> exact poincare_legs_commute _
  · apply Prod.ext <;> exact (poincare_legs_commute _).symm
  · rfl

/-- Generic gauge covariance instantiated on the constructed noncommutative ring. -/
theorem twisted_curvature_covariant (a : Fin 2 → TwistedCoordinates) (e : TwistedCoordinates)
    (i j : Fin 2) :
    TwistedGauge.curvatureVariation differential a (TwistedGauge.variation differential a e) i j =
      e * InfoGeometry.Optics.OperatorValuedConnection.curvature
        (TwistedGauge.connection differential a) () i j -
      InfoGeometry.Optics.OperatorValuedConnection.curvature
        (TwistedGauge.connection differential a) () i j * e :=
  TwistedGauge.variation_covariance differential differential_leibniz differentials_commute a e i j

end InfoGeometry.Twistor.PoincareFirstOrder
