import InfoGeometry.Projective.LogRatioDifferential
import InfoGeometry.Canonical.OperatorZornRealModule
import InfoGeometry.Canonical.OperatorZornGaugeCovariance

/-!
# Homogeneous state variations, full Zorn potentials, and expectation readouts

The state carrier is the existing positive-ray quotient. A family of real
linear coefficient functionals is mixed with its finite positive weights.
Linearity is not multiplicativity: Zorn products and associators are formed
BEFORE taking expectations. General coefficient-unit changes are algebraic
frames; preserving positivity of a star-state additionally requires a
star-compatible frame, and is not asserted for arbitrary units here.

`statePotential` is a native fiberwise linear form with arbitrary ray-dependent
Zorn coefficients. Its homogeneous/horizontal descent is proved. No smoothness
of that arbitrary coefficient family or manifold derivative is postulated.
-/

noncomputable section
namespace InfoGeometry.Projective.OperatorZornStateGeometry

open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG
open OperatorZornRealModule OperatorZornFourPotentialGauge OperatorZornGaugeCovariance
open ExpectationRatioMetric LogRatioDifferential
open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [Nonempty ι] [Ring A] [Algebra ℝ A]

/-- Finite convex mixing of linear coefficient observations. -/
def evaluation (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ) : A →ₗ[ℝ] ℝ where
  toFun a := rayMean q (fun i => E i a)
  map_add' a b := by
    simp only [map_add]
    exact rayMean_add q (fun i => E i a) (fun i => E i b)
  map_smul' c a := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    exact rayMean_smul q c (fun i => E i a)

/-- Entrywise expectation is linear; it is deliberately not an algebra morphism. -/
def coefficientReadout (m : A →ₗ[ℝ] ℝ) :
    OperatorZornMatrix A →ₗ[ℝ] OperatorZornMatrix ℝ where
  toFun X := operatorZornCoordinates (m X.n_plus) (m X.n_minus)
    (fun i => m (X.sigma_plus i)) (fun i => m (X.sigma_minus i))
  map_add' X Y := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals change m (_ + _) = m _ + m _
    all_goals exact m.map_add _ _
  map_smul' c X := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals change m (c • _) = c • m _
    all_goals exact m.map_smul c _

def readout (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ) :
    OperatorZornMatrix A →ₗ[ℝ] OperatorZornMatrix ℝ := coefficientReadout (evaluation q E)

/-- Representative scale cannot change a full eight-entry expectation readout. -/
theorem readout_scale (w : Weight ι) (c : ℝ) (hc : 0 < c)
    (E : ι → A →ₗ[ℝ] ℝ) (X : OperatorZornMatrix A) :
    readout (ray (InfoGeometry.PositiveMeasure.scale c hc w)) E X =
      readout (ray w) E X := by rw [ray_scale]

/-- Nonassociativity is read out before linear observation. -/
theorem readout_associator (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ)
    (X Y Z : OperatorZornMatrix A) :
    readout q E (associator X Y Z) =
      readout q E ((X*Y)*Z) - readout q E (X*(Y*Z)) := by
  exact map_sub (readout q E) _ _

/-- The complete curvature-action identity survives normalized observation. -/
theorem readout_curvatureAction (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ)
    (p : Fin 4 → A) (Phi : FourPotential A)
    (ξ η : Fin 4) (X : OperatorZornMatrix A) :
    readout q E (curvatureAction p Phi ξ η X) =
      readout q E (coefficientDeriv (coefficientBracket (p ξ) (p η)) X) +
      readout q E (fieldStrength p Phi ξ η * X) -
      readout q E (associator (Phi ξ) (Phi η) X) +
      readout q E (associator (Phi η) (Phi ξ) X) := by
  rw [curvatureAction_eq]
  simp only [map_add, map_sub]

def conjugationLinear (g : Aˣ) : A →ₗ[ℝ] A where
  toFun := coefficientConjugation g
  map_add' := (coefficientConjugation g).map_add
  map_smul' c a := by
    change (g : A) * (c • a) * ((g⁻¹ : Aˣ) : A) =
      c • ((g : A) * a * ((g⁻¹ : Aˣ) : A))
    rw [mul_smul_comm, smul_mul_assoc]

def dualFrame (E : ι → A →ₗ[ℝ] ℝ) (g : Aˣ) : ι → A →ₗ[ℝ] ℝ :=
  fun i => (E i).comp (conjugationLinear g⁻¹)

/-- States/observations transform contragrediently to the operator frame. -/
theorem readout_gauge (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ) (g : Aˣ)
    (X : OperatorZornMatrix A) :
    readout q (dualFrame E g) (gauge g X) = readout q E X := by
  have h (a : A) : evaluation q (dualFrame E g) (coefficientConjugation g a) =
      evaluation q E a := by
    change rayMean q (fun i => E i (coefficientConjugation g⁻¹
      (coefficientConjugation g a))) = rayMean q (fun i => E i a)
    simp only [coefficientConjugation_inverse_apply]
  apply operatorZornMatrix_ext
  · exact h X.n_plus
  · exact h X.n_minus
  · funext i; exact h (X.sigma_plus i)
  · funext i; exact h (X.sigma_minus i)

theorem readout_gauge_associator (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ) (g : Aˣ)
    (X Y Z : OperatorZornMatrix A) :
    readout q (dualFrame E g) (associator (gauge g X) (gauge g Y) (gauge g Z)) =
      readout q E (associator X Y Z) := by
  rw [← gauge_associator]
  exact readout_gauge q E g _

theorem readout_gauge_curvature (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ) (g : Aˣ)
    (p : Fin 4 → A) (Phi : FourPotential A)
    (ξ η : Fin 4) (X : OperatorZornMatrix A) :
    readout q (dualFrame E g)
      (curvatureAction (fun i => coefficientConjugation g (p i))
        (fun i => gauge g (Phi i)) ξ η (gauge g X)) =
      readout q E (curvatureAction p Phi ξ η X) := by
  rw [← gauge_curvatureAction]
  exact readout_gauge q E g _

theorem readout_gauge_bianchi (q : Ray ι) (E : ι → A →ₗ[ℝ] ℝ) (g : Aˣ)
    (p : Fin 4 → A) (Phi : FourPotential A) (ξ η ζ : Fin 4) :
    readout q (dualFrame E g)
      (bianchi (fun i => coefficientConjugation g (p i)) (fun i => gauge g (Phi i)) ξ η ζ) =
      readout q E (bianchi p Phi ξ η ζ) := by
  rw [← gauge_bianchi]
  exact readout_gauge q E g _

/-- The full Zorn potential on homogeneous state variations, not on spacetime.
The arbitrary coefficients C depend on the ray and need not commute. -/
def statePotential (C : Ray ι → (ι × ι) → OperatorZornMatrix A) (w : Weight ι) :
    (ι → ℝ) →ₗ[ℝ] OperatorZornMatrix A where
  toFun v := ∑ ij, logDifferential w v ij • C (ray w) ij
  map_add' v z := by
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

omit [Nonempty ι] in
/-- All radial directions are vertical gauge and are annihilated. -/
theorem statePotential_radial (C : Ray ι → (ι × ι) → OperatorZornMatrix A)
    (w : Weight ι) (c : ℝ) : statePotential C w (fun i => c*w i) = 0 := by
  change (∑ ij, logDifferential w (fun i => c*w i) ij • C (ray w) ij) = 0
  rw [logDifferential_radial]
  simp

omit [Nonempty ι] in
/-- Descent includes the derivative of an arbitrary representative rescaling. -/
theorem statePotential_change_lift (C : Ray ι → (ι × ι) → OperatorZornMatrix A)
    (w : Weight ι) (v : ι → ℝ) (c b : ℝ) (hc : 0 < c) :
    statePotential C (InfoGeometry.PositiveMeasure.scale c hc w) (fun i => c*v i+b*w i) =
      statePotential C w v := by
  change (∑ ij, logDifferential (InfoGeometry.PositiveMeasure.scale c hc w)
      (fun i => c*v i+b*w i) ij • C (ray (InfoGeometry.PositiveMeasure.scale c hc w)) ij) = _
  rw [logDifferential_change_lift, ray_scale]
  rfl

omit [Nonempty ι] in
/-- Scale descent does not annihilate the noncommuting potential wedge. -/
theorem statePotential_bracket_change_lift
    (C : Ray ι → (ι × ι) → OperatorZornMatrix A)
    (w : Weight ι) (v z : ι → ℝ) (c b d : ℝ) (hc : 0 < c) :
    bracket
      (statePotential C (InfoGeometry.PositiveMeasure.scale c hc w) (fun i => c*v i+b*w i))
      (statePotential C (InfoGeometry.PositiveMeasure.scale c hc w) (fun i => c*z i+d*w i)) =
    bracket (statePotential C w v) (statePotential C w z) := by
  rw [statePotential_change_lift, statePotential_change_lift]

end InfoGeometry.Projective.OperatorZornStateGeometry

