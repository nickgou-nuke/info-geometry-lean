import InfoGeometry.Canonical.OperatorZornConnectionCurvatureBridge

/-!
# Four-component gauge potentials on the nonassociative operator-Zorn carrier

The coefficient algebra may be any associative ring of operators. The Zorn
product is the existing `NCZornElement.mul`, not composition of endomorphisms.
No associative or alternative instance is installed on the Zorn carrier.
Both scalar blocks and all six vector entries remain independent.

`coefficientDeriv p` is the coefficientwise commutator with an actual element
`p` of the coefficient algebra. Its product rule is proved. Four such
operators need not commute: their curvature is retained in every identity.
These are algebraic operator identities, not a claim that arbitrary operators
are coordinate partial derivatives on a manifold.
-/

namespace InfoGeometry.Canonical.OperatorZornFourPotentialGauge

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

/-- Four spacetime-indexed, full operator-Zorn connection coefficients. -/
abbrev FourPotential (A : Type*) [Ring A] := Fin 4 → OperatorZornMatrix A

/-- Ordered commutator in the coefficient operator algebra. -/
def coefficientBracket (p q : A) : A := p * q - q * p

/-- Ordered commutator of the actual nonassociative Zorn product. -/
def bracket (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  X * Y - Y * X

/-- Parentheses are part of the definition and must not be reassociated. -/
def associator (X Y Z : OperatorZornMatrix A) : OperatorZornMatrix A :=
  (X * Y) * Z - X * (Y * Z)

/-- A derivation induced coefficientwise by an operator commutator. -/
def coefficientDeriv (p : A) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorZornCoordinates
    (coefficientBracket p X.n_plus) (coefficientBracket p X.n_minus)
    (fun i => coefficientBracket p (X.sigma_plus i))
    (fun i => coefficientBracket p (X.sigma_minus i))

theorem coefficientDeriv_add (p : A) (X Y : OperatorZornMatrix A) :
    coefficientDeriv p (X + Y) = coefficientDeriv p X + coefficientDeriv p Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [coefficientDeriv, coefficientBracket, operatorZornCoordinates]
  all_goals noncomm_ring

theorem coefficientDeriv_sub (p : A) (X Y : OperatorZornMatrix A) :
    coefficientDeriv p (X - Y) = coefficientDeriv p X - coefficientDeriv p Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [coefficientDeriv, coefficientBracket, operatorZornCoordinates]
  all_goals noncomm_ring

/-- The product rule is derived from coefficient multiplication, not postulated. -/
theorem coefficientDeriv_mul (p : A) (X Y : OperatorZornMatrix A) :
    coefficientDeriv p (X * Y) = coefficientDeriv p X * Y + X * coefficientDeriv p Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [coefficientDeriv, coefficientBracket, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

/-- The coefficient differential operators need not commute. -/
theorem coefficientDeriv_commutator (p q : A) (X : OperatorZornMatrix A) :
    coefficientDeriv p (coefficientDeriv q X) -
        coefficientDeriv q (coefficientDeriv p X) =
      coefficientDeriv (coefficientBracket p q) X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [coefficientDeriv, coefficientBracket, operatorZornCoordinates]
  all_goals noncomm_ring

/-- Covariant differentiation of Zorn-valued fields, with the Zorn product intact. -/
def covariant (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  coefficientDeriv (p mu) X + Phi mu * X

/-- Zorn-valued field strength, before acting on a field. -/
def fieldStrength (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) : OperatorZornMatrix A :=
  coefficientDeriv (p mu) (Phi nu) - coefficientDeriv (p nu) (Phi mu) +
    bracket (Phi mu) (Phi nu)

/-- Curvature action; its associator contribution is not absorbed into `fieldStrength`. -/
def curvatureAction (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  covariant p Phi mu (covariant p Phi nu X) -
    covariant p Phi nu (covariant p Phi mu X)

theorem fieldStrength_swap (p : Fin 4 → A) (Phi : FourPotential A) (mu nu : Fin 4) :
    fieldStrength p Phi nu mu = -fieldStrength p Phi mu nu := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [fieldStrength, bracket, coefficientDeriv, coefficientBracket,
    operatorZornCoordinates, NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

/-- Full curvature identity: background curvature and both associators survive. -/
theorem curvatureAction_eq (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) (X : OperatorZornMatrix A) :
    curvatureAction p Phi mu nu X =
      coefficientDeriv (coefficientBracket (p mu) (p nu)) X +
        fieldStrength p Phi mu nu * X -
          associator (Phi mu) (Phi nu) X + associator (Phi nu) (Phi mu) X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [curvatureAction, covariant, fieldStrength, bracket, associator,
    coefficientDeriv, coefficientBracket, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

/-- Adjoint covariant derivative, without claiming that the Zorn bracket is Lie. -/
def adjointCovariant (p : Fin 4 → A) (Phi : FourPotential A)
    (mu : Fin 4) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  coefficientDeriv (p mu) X + bracket (Phi mu) X

/-- The six-term Akivis alternation, with no alternativity assumption. -/
def associatorAlternation (X Y Z : OperatorZornMatrix A) : OperatorZornMatrix A :=
  associator X Y Z + associator Y Z X + associator Z X Y -
    associator Y X Z - associator Z Y X - associator X Z Y

/-- Concrete specialization of the right-nested Akivis identity to the native NC carrier. -/
theorem rightJacobiator_eq (X Y Z : OperatorZornMatrix A) :
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) =
      -associatorAlternation X Y Z := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [bracket, associatorAlternation, associator,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

/-- Bianchi expression in the coefficient-commutator differential calculus. -/
def bianchi (p : Fin 4 → A) (Phi : FourPotential A) (mu nu rho : Fin 4) :
    OperatorZornMatrix A :=
  adjointCovariant p Phi mu (fieldStrength p Phi nu rho) +
    adjointCovariant p Phi nu (fieldStrength p Phi rho mu) +
      adjointCovariant p Phi rho (fieldStrength p Phi mu nu)

/-- Neither the coefficient-curvature source nor the Akivis source is set to zero. -/
theorem bianchi_eq (p : Fin 4 → A) (Phi : FourPotential A) (mu nu rho : Fin 4) :
    bianchi p Phi mu nu rho =
      coefficientDeriv (coefficientBracket (p mu) (p nu)) (Phi rho) +
        coefficientDeriv (coefficientBracket (p nu) (p rho)) (Phi mu) +
          coefficientDeriv (coefficientBracket (p rho) (p mu)) (Phi nu) -
            associatorAlternation (Phi mu) (Phi nu) (Phi rho) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [bianchi, adjointCovariant, fieldStrength, bracket,
    associatorAlternation, associator, coefficientDeriv, coefficientBracket,
    operatorZornCoordinates, NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

/-- The temporal/spatial field-strength sector; no electrostatic specialization. -/
def electric (p : Fin 4 → A) (Phi : FourPotential A) : Fin 3 → OperatorZornMatrix A :=
  fun i => fieldStrength p Phi 0 i.succ

/-- Oriented spatial field-strength sector, still Zorn-valued. -/
def magnetic (p : Fin 4 → A) (Phi : FourPotential A) : Fin 3 → OperatorZornMatrix A
  | 0 => fieldStrength p Phi 2 3
  | 1 => fieldStrength p Phi 3 1
  | 2 => fieldStrength p Phi 1 2

/-- Electric curvature retains the temporal/spatial Zorn commutator. -/
theorem electric_eq (p : Fin 4 → A) (Phi : FourPotential A) (i : Fin 3) :
    electric p Phi i = coefficientDeriv (p 0) (Phi i.succ) -
      coefficientDeriv (p i.succ) (Phi 0) + bracket (Phi 0) (Phi i.succ) := rfl

/-- Native spatial curvature channels from the existing operator-Zorn owner. -/
theorem chiral_square_retains_curvature (U V : OperatorVector A) :
    operatorZornMul (chiralOperatorZorn U V) (chiralOperatorZorn U V) =
      OperatorZornConnectionCurvatureBridge.operatorZornMetricPart U V +
        OperatorZornConnectionCurvatureBridge.operatorZornCurvaturePart U V := by
  exact OperatorZornConnectionCurvatureBridge.chiralOperatorZorn_square_eq_metric_add_curvature U V

end InfoGeometry.Canonical.OperatorZornFourPotentialGauge
