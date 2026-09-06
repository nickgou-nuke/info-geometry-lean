import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Canonical.ZornFiniteVectorCalculus
import InfoGeometry.Canonical.ZornMaxwellGaugeBridge
import InfoGeometry.Canonical.ZornPotentialDifferentialReadout
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Circular/chiral coordinate readout for the Zorn vector channel

This file is the finite coordinate bridge behind the chiral Zorn Maxwell
readout.  It keeps the real three-vector carrier and records its circular
coordinates over `ℂ`.  The transform is deliberately unnormalised: this
avoids importing a square-root convention into the algebraic owner.  The
factor `1 / 2` in the dot-product formula is the corresponding normalization.

No differential operator or helicity-decoupling claim is introduced here.
Those belong to the existing finite-calculus and differential-form owners.
-/

namespace InfoGeometry.Canonical.ChiralZornMaxwellReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornMaxwellDifferentialBridge
open InfoGeometry.Canonical.ZornFiniteVectorCalculus
open InfoGeometry.Canonical.ZornMaxwellGaugeBridge
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout

abbrev RealVec3 := ZornVec3 ℝ
abbrev ChiralVec3 := ZornVec3 ℂ

def chiralCoordinates (v : RealVec3) : ChiralVec3 := fun i =>
  if i = (0 : Fin 3) then
    (v 0 : ℂ) - Complex.I * (v 1 : ℂ)
  else if i = (1 : Fin 3) then
    (v 0 : ℂ) + Complex.I * (v 1 : ℂ)
  else
    (v 2 : ℂ)

@[simp] theorem chiralCoordinates_zero (v : RealVec3) :
    chiralCoordinates v 0 = (v 0 : ℂ) - Complex.I * (v 1 : ℂ) := by
  simp [chiralCoordinates]

@[simp] theorem chiralCoordinates_one (v : RealVec3) :
    chiralCoordinates v 1 = (v 0 : ℂ) + Complex.I * (v 1 : ℂ) := by
  simp [chiralCoordinates]

@[simp] theorem chiralCoordinates_two (v : RealVec3) :
    chiralCoordinates v 2 = (v 2 : ℂ) := by
  simp [chiralCoordinates]

noncomputable def chiralDot (u v : ChiralVec3) : ℂ :=
  ((1 : ℂ) / 2) * (u 0 * v 1 + u 1 * v 0) + u 2 * v 2

theorem chiralDot_coordinates (u v : RealVec3) :
    chiralDot (chiralCoordinates u) (chiralCoordinates v) =
      ((ZornVec3.dot u v : ℝ) : ℂ) := by
  simp [chiralDot, ZornVec3.dot_eq_sum_coords, chiralCoordinates]
  ring_nf
  have hI : (Complex.I : ℂ) ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  rw [hI]
  ring

def chiralCrossReadout (u v : RealVec3) : ChiralVec3 :=
  chiralCoordinates (ZornVec3.cross u v)

theorem chiralCrossReadout_coordinates (u v : RealVec3) :
    chiralCrossReadout u v 0 =
      ((u 1 * v 2 - u 2 * v 1 : ℝ) : ℂ) -
        Complex.I * ((u 2 * v 0 - u 0 * v 2 : ℝ) : ℂ) ∧
    chiralCrossReadout u v 1 =
      ((u 1 * v 2 - u 2 * v 1 : ℝ) : ℂ) +
        Complex.I * ((u 2 * v 0 - u 0 * v 2 : ℝ) : ℂ) ∧
    chiralCrossReadout u v 2 =
      ((u 0 * v 1 - u 1 * v 0 : ℝ) : ℂ) := by
  simp [chiralCrossReadout, chiralCoordinates, ZornVec3.cross]

theorem chiralCrossReadout_antisymmetric (u v : RealVec3) :
    chiralCrossReadout v u =
      fun i => -chiralCrossReadout u v i := by
  funext i
  fin_cases i <;>
    simp [chiralCrossReadout, chiralCoordinates, ZornVec3.cross] <;>
    ring

def chiralGradient
    (D : DifferentialCarrier (R := ℝ)) (x : ℝ) : ChiralVec3 :=
  chiralCoordinates (gradient D x)

def chiralCurl
    (D : DifferentialCarrier (R := ℝ)) (v : RealVec3) : ChiralVec3 :=
  chiralCoordinates (curl D v)

@[simp] theorem chiralGradient_zero
    (D : DifferentialCarrier (R := ℝ)) (x : ℝ) :
    chiralGradient D x 0 =
      (D.spatialDerivative 0 x : ℂ) -
        Complex.I * (D.spatialDerivative 1 x : ℂ) := by
  simp [chiralGradient, gradient, chiralCoordinates]

@[simp] theorem chiralGradient_one
    (D : DifferentialCarrier (R := ℝ)) (x : ℝ) :
    chiralGradient D x 1 =
      (D.spatialDerivative 0 x : ℂ) +
        Complex.I * (D.spatialDerivative 1 x : ℂ) := by
  simp [chiralGradient, gradient, chiralCoordinates]

@[simp] theorem chiralGradient_two
    (D : DifferentialCarrier (R := ℝ)) (x : ℝ) :
    chiralGradient D x 2 = (D.spatialDerivative 2 x : ℂ) := by
  simp [chiralGradient, gradient, chiralCoordinates]

theorem chiralCurl_gradient_zero
    (D : DifferentialCarrier (R := ℝ)) (x : ℝ) :
    chiralCurl D (gradient D x) = fun _ => 0 := by
  change chiralCoordinates (curl D (gradient D x)) = fun _ => 0
  rw [curl_gradient D x]
  funext i
  simp [chiralCurl, chiralCoordinates]

theorem chiralCurl_coordinates
    (D : DifferentialCarrier (R := ℝ)) (v : RealVec3) :
    chiralCurl D v 0 =
        ((D.spatialDerivative 1 (v 2) -
          D.spatialDerivative 2 (v 1) : ℝ) : ℂ) -
          Complex.I * ((D.spatialDerivative 2 (v 0) -
            D.spatialDerivative 0 (v 2) : ℝ) : ℂ) ∧
    chiralCurl D v 1 =
        ((D.spatialDerivative 1 (v 2) -
          D.spatialDerivative 2 (v 1) : ℝ) : ℂ) +
          Complex.I * ((D.spatialDerivative 2 (v 0) -
            D.spatialDerivative 0 (v 2) : ℝ) : ℂ) ∧
    chiralCurl D v 2 =
      ((D.spatialDerivative 0 (v 1) -
        D.spatialDerivative 1 (v 0) : ℝ) : ℂ) := by
  simp [chiralCurl, curl, chiralCoordinates]

theorem chiral_gauge_electric_invariant
    (D : DifferentialCarrier (R := ℝ))
    (hneg : ∀ x, timeNeg D x)
    (hcomm : ∀ i x, D.spatialDerivative i (D.timeDerivative x) =
      D.timeDerivative (D.spatialDerivative i x))
    (scalar : ℝ) (vector : RealVec3) (g : ℝ) :
    chiralCoordinates (electricReadout
      (potentialData D (gaugeScalar D scalar g)
        (gaugeVector D vector g))) =
      chiralCoordinates (electricReadout (potentialData D scalar vector)) := by
  exact congrArg chiralCoordinates
    (gauge_electric_invariant D hneg hcomm scalar vector g)

theorem chiral_gauge_magnetic_invariant
    (D : DifferentialCarrier (R := ℝ))
    (scalar : ℝ) (vector : RealVec3) (g : ℝ) :
    chiralCoordinates (magneticReadout
      (potentialData D (gaugeScalar D scalar g)
        (gaugeVector D vector g))) =
      chiralCoordinates (magneticReadout (potentialData D scalar vector)) := by
  exact congrArg chiralCoordinates
    (gauge_magnetic_invariant D scalar vector g)

theorem chiralMaxwell_vector_channels
    (e b : RealVec3) :
    (chiralCoordinates (fun i => e i + b i) =
        fun i => chiralCoordinates e i + chiralCoordinates b i) ∧
    (chiralCoordinates (fun i => e i - b i) =
        fun i => chiralCoordinates e i - chiralCoordinates b i) := by
  constructor <;> funext i <;>
    fin_cases i <;>
    simp [chiralCoordinates] <;>
    ring

def riemannSilbersteinPlus (e b : RealVec3) : ChiralVec3 :=
  fun i => chiralCoordinates e i + Complex.I * chiralCoordinates b i

def riemannSilbersteinMinus (e b : RealVec3) : ChiralVec3 :=
  fun i => chiralCoordinates e i - Complex.I * chiralCoordinates b i

theorem riemannSilberstein_sum (e b : RealVec3) :
    (fun i => riemannSilbersteinPlus e b i +
      riemannSilbersteinMinus e b i) =
      fun i => (2 : ℂ) * chiralCoordinates e i := by
  funext i
  simp [riemannSilbersteinPlus, riemannSilbersteinMinus]
  ring_nf

theorem riemannSilberstein_difference (e b : RealVec3) :
    (fun i => riemannSilbersteinPlus e b i -
      riemannSilbersteinMinus e b i) =
      fun i => (2 : ℂ) * Complex.I * chiralCoordinates b i := by
  funext i
  simp [riemannSilbersteinPlus, riemannSilbersteinMinus]
  ring_nf

theorem chiral_e_add_b_from_riemannSilberstein (e b : RealVec3) :
    (fun i =>
      ((1 - Complex.I) / 2) * riemannSilbersteinPlus e b i +
        ((1 + Complex.I) / 2) * riemannSilbersteinMinus e b i) =
      fun i => chiralCoordinates e i + chiralCoordinates b i := by
  funext i
  simp [riemannSilbersteinPlus, riemannSilbersteinMinus]
  ring_nf
  simp [pow_two, Complex.I_mul_I]
  ring

theorem chiral_e_sub_b_from_riemannSilberstein (e b : RealVec3) :
    (fun i =>
      ((1 + Complex.I) / 2) * riemannSilbersteinPlus e b i +
        ((1 - Complex.I) / 2) * riemannSilbersteinMinus e b i) =
      fun i => chiralCoordinates e i - chiralCoordinates b i := by
  funext i
  simp [riemannSilbersteinPlus, riemannSilbersteinMinus]
  ring_nf
  simp [pow_two, Complex.I_mul_I]
  ring

def chiralDifferentialFieldReadout
    (P : PotentialDifferentialData (R := ℝ)) : ℝ × ChiralVec3 × ChiralVec3 :=
  (lorenzResidual P,
    chiralCoordinates (upperFieldReadout P),
    chiralCoordinates (fun i => -(upperFieldReadout P i)))

theorem chiralUpperFieldReadout_eq_neg_electric_add_magnetic
    (P : PotentialDifferentialData (R := ℝ)) :
    chiralCoordinates (upperFieldReadout P) =
      fun i => -(chiralCoordinates (electricReadout P) i +
        chiralCoordinates (magneticReadout P) i) := by
  rw [upperFieldReadout_eq_neg_electric_add_magnetic P]
  funext i
  fin_cases i <;>
    simp [chiralCoordinates] <;>
    ring

theorem chiralLowerFieldReadout_eq_electric_add_magnetic
    (P : PotentialDifferentialData (R := ℝ)) :
    chiralCoordinates (fun i => -(upperFieldReadout P i)) =
      fun i => chiralCoordinates (electricReadout P) i +
        chiralCoordinates (magneticReadout P) i := by
  rw [lowerFieldReadout_eq_electric_add_magnetic P]
  funext i
  fin_cases i <;>
    simp [chiralCoordinates] <;>
    ring

theorem chiralDifferentialFieldReadout_lorenzGauge
    (P : PotentialDifferentialData (R := ℝ))
    (hGauge : P.timePotentialDerivative = P.potentialDivergence) :
    chiralDifferentialFieldReadout P =
      (0, chiralCoordinates (upperFieldReadout P),
        chiralCoordinates (fun i => -(upperFieldReadout P i))) := by
  simp [chiralDifferentialFieldReadout, lorenzResidual, hGauge]

theorem riemannSilberstein_plus_coordinate_zero
    (e b : RealVec3) :
    riemannSilbersteinPlus e b 0 =
      ((e 0 : ℂ) - Complex.I * (e 1 : ℂ)) +
        Complex.I * ((b 0 : ℂ) - Complex.I * (b 1 : ℂ)) := by
  rfl

theorem riemannSilberstein_minus_coordinate_zero
    (e b : RealVec3) :
    riemannSilbersteinMinus e b 0 =
      ((e 0 : ℂ) - Complex.I * (e 1 : ℂ)) -
        Complex.I * ((b 0 : ℂ) - Complex.I * (b 1 : ℂ)) := by
  rfl

end InfoGeometry.Canonical.ChiralZornMaxwellReadout
