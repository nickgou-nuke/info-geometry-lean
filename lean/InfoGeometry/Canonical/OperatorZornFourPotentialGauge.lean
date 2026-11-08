import InfoGeometry.Canonical.OperatorZornConnectionCurvatureBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.NCZornProjectionNormalization

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

set_option maxHeartbeats 2000000

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

@[simp] theorem coefficientDeriv_nPlus (p : A) (X : OperatorZornMatrix A) :
    (coefficientDeriv p X).n_plus = coefficientBracket p X.n_plus := by
  rfl

@[simp] theorem coefficientDeriv_nMinus (p : A) (X : OperatorZornMatrix A) :
    (coefficientDeriv p X).n_minus = coefficientBracket p X.n_minus := by
  rfl

@[simp] theorem coefficientDeriv_sigmaPlus (p : A) (X : OperatorZornMatrix A) :
    (coefficientDeriv p X).sigma_plus = fun i =>
      coefficientBracket p (X.sigma_plus i) := by
  rfl

@[simp] theorem coefficientDeriv_sigmaMinus (p : A) (X : OperatorZornMatrix A) :
    (coefficientDeriv p X).sigma_minus = fun i =>
      coefficientBracket p (X.sigma_minus i) := by
  rfl

@[simp] theorem coefficientDeriv_sigmaPlus_apply (p : A)
    (X : OperatorZornMatrix A) (i : Fin 3) :
    (coefficientDeriv p X).sigma_plus i = coefficientBracket p (X.sigma_plus i) := by
  rfl

@[simp] theorem coefficientDeriv_sigmaMinus_apply (p : A)
    (X : OperatorZornMatrix A) (i : Fin 3) :
    (coefficientDeriv p X).sigma_minus i = coefficientBracket p (X.sigma_minus i) := by
  rfl

@[simp] theorem coefficientDeriv_mul_sigmaPlus_apply (p : A)
    (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (coefficientDeriv p (X * Y)).sigma_plus i =
      coefficientBracket p
        (X.n_plus * Y.sigma_plus i + X.sigma_plus i * Y.n_minus -
          NCZornElement.zornCross X.sigma_minus Y.sigma_minus i) := by
  rfl

@[simp] theorem coefficientDeriv_mul_sigmaMinus_apply (p : A)
    (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (coefficientDeriv p (X * Y)).sigma_minus i =
      coefficientBracket p
        (X.n_minus * Y.sigma_minus i + X.sigma_minus i * Y.n_plus +
          NCZornElement.zornCross X.sigma_plus Y.sigma_plus i) := by
  rfl

@[simp] theorem coefficientDeriv_coefficientDeriv_sigmaPlus_apply
    (p q : A) (X : OperatorZornMatrix A) (i : Fin 3) :
    (coefficientDeriv p (coefficientDeriv q X)).sigma_plus i =
      coefficientBracket p (coefficientBracket q (X.sigma_plus i)) := by
  rfl

@[simp] theorem coefficientDeriv_coefficientDeriv_sigmaMinus_apply
    (p q : A) (X : OperatorZornMatrix A) (i : Fin 3) :
    (coefficientDeriv p (coefficientDeriv q X)).sigma_minus i =
      coefficientBracket p (coefficientBracket q (X.sigma_minus i)) := by
  rfl

theorem coefficientDeriv_add (p : A) (X Y : OperatorZornMatrix A) :
    coefficientDeriv p (X + Y) = coefficientDeriv p X + coefficientDeriv p Y := by
  apply operatorZornMatrix_ext
  · change p * (X.n_plus + Y.n_plus) - (X.n_plus + Y.n_plus) * p =
      (p * X.n_plus - X.n_plus * p) + (p * Y.n_plus - Y.n_plus * p)
    noncomm_ring
  · change p * (X.n_minus + Y.n_minus) - (X.n_minus + Y.n_minus) * p =
      (p * X.n_minus - X.n_minus * p) + (p * Y.n_minus - Y.n_minus * p)
    noncomm_ring
  · funext i
    change p * (X.sigma_plus i + Y.sigma_plus i) -
      (X.sigma_plus i + Y.sigma_plus i) * p =
      (p * X.sigma_plus i - X.sigma_plus i * p) +
        (p * Y.sigma_plus i - Y.sigma_plus i * p)
    noncomm_ring
  · funext i
    change p * (X.sigma_minus i + Y.sigma_minus i) -
      (X.sigma_minus i + Y.sigma_minus i) * p =
      (p * X.sigma_minus i - X.sigma_minus i * p) +
        (p * Y.sigma_minus i - Y.sigma_minus i * p)
    noncomm_ring

theorem coefficientDeriv_neg (p : A) (X : OperatorZornMatrix A) :
    coefficientDeriv p (-X) = -coefficientDeriv p X := by
  apply operatorZornMatrix_ext
  · change p * (-X.n_plus) - (-X.n_plus) * p = -(p * X.n_plus - X.n_plus * p)
    noncomm_ring
  · change p * (-X.n_minus) - (-X.n_minus) * p = -(p * X.n_minus - X.n_minus * p)
    noncomm_ring
  · funext i
    change p * (-X.sigma_plus i) - (-X.sigma_plus i) * p =
      -(p * X.sigma_plus i - X.sigma_plus i * p)
    noncomm_ring
  · funext i
    change p * (-X.sigma_minus i) - (-X.sigma_minus i) * p =
      -(p * X.sigma_minus i - X.sigma_minus i * p)
    noncomm_ring

theorem coefficientDeriv_sub (p : A) (X Y : OperatorZornMatrix A) :
    coefficientDeriv p (X - Y) = coefficientDeriv p X - coefficientDeriv p Y := by
  change coefficientDeriv p (X + -Y) = coefficientDeriv p X + -coefficientDeriv p Y
  rw [coefficientDeriv_add, coefficientDeriv_neg]

@[simp] theorem zornSub_nPlus (X Y : OperatorZornMatrix A) :
    (X - Y).n_plus = X.n_plus - Y.n_plus := by
  change (X + -Y).n_plus = X.n_plus - Y.n_plus
  change X.n_plus + -Y.n_plus = X.n_plus - Y.n_plus
  simp only [sub_eq_add_neg]

@[simp] theorem zornSub_nMinus (X Y : OperatorZornMatrix A) :
    (X - Y).n_minus = X.n_minus - Y.n_minus := by
  change (X + -Y).n_minus = X.n_minus - Y.n_minus
  change X.n_minus + -Y.n_minus = X.n_minus - Y.n_minus
  simp only [sub_eq_add_neg]

@[simp] theorem zornSub_sigmaPlus (X Y : OperatorZornMatrix A) :
    (X - Y).sigma_plus = fun i => X.sigma_plus i - Y.sigma_plus i := by
  funext i
  change (X + -Y).sigma_plus i = X.sigma_plus i - Y.sigma_plus i
  change X.sigma_plus i + -Y.sigma_plus i = X.sigma_plus i - Y.sigma_plus i
  simp only [sub_eq_add_neg]

@[simp] theorem zornSub_sigmaMinus (X Y : OperatorZornMatrix A) :
    (X - Y).sigma_minus = fun i => X.sigma_minus i - Y.sigma_minus i := by
  funext i
  change (X + -Y).sigma_minus i = X.sigma_minus i - Y.sigma_minus i
  change X.sigma_minus i + -Y.sigma_minus i = X.sigma_minus i - Y.sigma_minus i
  simp only [sub_eq_add_neg]

@[simp] theorem zornAdd_nPlus (X Y : OperatorZornMatrix A) :
    (X + Y).n_plus = X.n_plus + Y.n_plus := by
  change X.n_plus + Y.n_plus = X.n_plus + Y.n_plus
  rfl

@[simp] theorem zornAdd_nMinus (X Y : OperatorZornMatrix A) :
    (X + Y).n_minus = X.n_minus + Y.n_minus := by
  change X.n_minus + Y.n_minus = X.n_minus + Y.n_minus
  rfl

@[simp] theorem zornAdd_sigmaPlus (X Y : OperatorZornMatrix A) :
    (X + Y).sigma_plus = fun i => X.sigma_plus i + Y.sigma_plus i := by
  funext i
  change X.sigma_plus i + Y.sigma_plus i = X.sigma_plus i + Y.sigma_plus i
  rfl

@[simp] theorem zornAdd_sigmaMinus (X Y : OperatorZornMatrix A) :
    (X + Y).sigma_minus = fun i => X.sigma_minus i + Y.sigma_minus i := by
  funext i
  change X.sigma_minus i + Y.sigma_minus i = X.sigma_minus i + Y.sigma_minus i
  rfl

@[simp] theorem zornNeg_nPlus (X : OperatorZornMatrix A) :
    (-X).n_plus = -X.n_plus := by
  change -X.n_plus = -X.n_plus
  rfl

@[simp] theorem zornNeg_nMinus (X : OperatorZornMatrix A) :
    (-X).n_minus = -X.n_minus := by
  change -X.n_minus = -X.n_minus
  rfl

@[simp] theorem zornNeg_sigmaPlus (X : OperatorZornMatrix A) :
    (-X).sigma_plus = fun i => -X.sigma_plus i := by
  funext i
  change -X.sigma_plus i = -X.sigma_plus i
  rfl

@[simp] theorem zornNeg_sigmaMinus (X : OperatorZornMatrix A) :
    (-X).sigma_minus = fun i => -X.sigma_minus i := by
  funext i
  change -X.sigma_minus i = -X.sigma_minus i
  rfl

@[simp] theorem zornAdd_sigmaPlus_apply (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X + Y).sigma_plus i = X.sigma_plus i + Y.sigma_plus i := by
  rfl

@[simp] theorem zornAdd_sigmaMinus_apply (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X + Y).sigma_minus i = X.sigma_minus i + Y.sigma_minus i := by
  rfl

@[simp] theorem zornNeg_sigmaPlus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (-X).sigma_plus i = -X.sigma_plus i := by
  rfl

@[simp] theorem zornNeg_sigmaMinus_apply (X : OperatorZornMatrix A) (i : Fin 3) :
    (-X).sigma_minus i = -X.sigma_minus i := by
  rfl

@[simp] theorem zornSub_sigmaPlus_apply (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X - Y).sigma_plus i = X.sigma_plus i - Y.sigma_plus i := by
  change (X + -Y).sigma_plus i = X.sigma_plus i - Y.sigma_plus i
  change X.sigma_plus i + -Y.sigma_plus i = X.sigma_plus i - Y.sigma_plus i
  simp only [sub_eq_add_neg]

@[simp] theorem zornSub_sigmaMinus_apply (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X - Y).sigma_minus i = X.sigma_minus i - Y.sigma_minus i := by
  change (X + -Y).sigma_minus i = X.sigma_minus i - Y.sigma_minus i
  change X.sigma_minus i + -Y.sigma_minus i = X.sigma_minus i - Y.sigma_minus i
  simp only [sub_eq_add_neg]

@[simp] theorem zornAddAddSub_sigmaPlus_apply
    (X Y Z W : OperatorZornMatrix A) (i : Fin 3) :
    ((X + Y) + Z - W).sigma_plus i =
      X.sigma_plus i + Y.sigma_plus i + Z.sigma_plus i - W.sigma_plus i := by
  simp only [zornSub_sigmaPlus_apply, zornAdd_sigmaPlus_apply,
    zornNeg_sigmaPlus_apply]

@[simp] theorem zornAddAddSub_sigmaMinus_apply
    (X Y Z W : OperatorZornMatrix A) (i : Fin 3) :
    ((X + Y) + Z - W).sigma_minus i =
      X.sigma_minus i + Y.sigma_minus i + Z.sigma_minus i - W.sigma_minus i := by
  simp only [zornSub_sigmaMinus_apply, zornAdd_sigmaMinus_apply,
    zornNeg_sigmaMinus_apply]

@[simp] theorem zornMul_nPlus (X Y : OperatorZornMatrix A) :
    (X * Y).n_plus = X.n_plus * Y.n_plus +
      NCZornElement.zornDot X.sigma_plus Y.sigma_minus := by
  rfl

@[simp] theorem zornMul_nMinus (X Y : OperatorZornMatrix A) :
    (X * Y).n_minus = X.n_minus * Y.n_minus +
      NCZornElement.zornDot X.sigma_minus Y.sigma_plus := by
  rfl

@[simp] theorem zornMul_sigmaPlus (X Y : OperatorZornMatrix A) :
    (X * Y).sigma_plus = fun i =>
      X.n_plus * Y.sigma_plus i + X.sigma_plus i * Y.n_minus -
        NCZornElement.zornCross X.sigma_minus Y.sigma_minus i := by
  rfl

@[simp] theorem zornMul_sigmaMinus (X Y : OperatorZornMatrix A) :
    (X * Y).sigma_minus = fun i =>
      X.n_minus * Y.sigma_minus i + X.sigma_minus i * Y.n_plus +
        NCZornElement.zornCross X.sigma_plus Y.sigma_plus i := by
  rfl

@[simp] theorem zornMul_sigmaPlus_apply (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X * Y).sigma_plus i =
      X.n_plus * Y.sigma_plus i + X.sigma_plus i * Y.n_minus -
        NCZornElement.zornCross X.sigma_minus Y.sigma_minus i := by
  rfl

@[simp] theorem zornMul_sigmaMinus_apply (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X * Y).sigma_minus i =
      X.n_minus * Y.sigma_minus i + X.sigma_minus i * Y.n_plus +
        NCZornElement.zornCross X.sigma_plus Y.sigma_plus i := by
  rfl

/-- The product rule is derived from coefficient multiplication, not postulated. -/
theorem coefficientDeriv_mul (p : A) (X Y : OperatorZornMatrix A) :
    coefficientDeriv p (X * Y) = coefficientDeriv p X * Y + X * coefficientDeriv p Y := by
  apply operatorZornMatrix_ext
  · change coefficientBracket p ((X * Y).n_plus) =
      (coefficientDeriv p X * Y + X * coefficientDeriv p Y).n_plus
    change coefficientBracket p
        (X.n_plus * Y.n_plus + NCZornElement.zornDot X.sigma_plus Y.sigma_minus) = _
    change coefficientBracket p
        (X.n_plus * Y.n_plus + NCZornElement.zornDot X.sigma_plus Y.sigma_minus) =
      (coefficientBracket p X.n_plus * Y.n_plus +
        NCZornElement.zornDot (fun i => coefficientBracket p (X.sigma_plus i)) Y.sigma_minus) +
      (X.n_plus * coefficientBracket p Y.n_plus +
        NCZornElement.zornDot X.sigma_plus (fun i => coefficientBracket p (Y.sigma_minus i)))
    simp only [coefficientBracket, NCZornElement.zornDot]
    noncomm_ring
  · change coefficientBracket p ((X * Y).n_minus) =
      (coefficientDeriv p X * Y + X * coefficientDeriv p Y).n_minus
    change coefficientBracket p
        (X.n_minus * Y.n_minus + NCZornElement.zornDot X.sigma_minus Y.sigma_plus) = _
    change coefficientBracket p
        (X.n_minus * Y.n_minus + NCZornElement.zornDot X.sigma_minus Y.sigma_plus) =
      (coefficientBracket p X.n_minus * Y.n_minus +
        NCZornElement.zornDot (fun i => coefficientBracket p (X.sigma_minus i)) Y.sigma_plus) +
      (X.n_minus * coefficientBracket p Y.n_minus +
        NCZornElement.zornDot X.sigma_minus (fun i => coefficientBracket p (Y.sigma_plus i)))
    simp only [coefficientBracket, NCZornElement.zornDot]
    noncomm_ring
  · funext i
    change coefficientBracket p
        (X.n_plus * Y.sigma_plus i + X.sigma_plus i * Y.n_minus -
          NCZornElement.zornCross X.sigma_minus Y.sigma_minus i) =
      (coefficientBracket p X.n_plus * Y.sigma_plus i +
          coefficientBracket p (X.sigma_plus i) * Y.n_minus -
          NCZornElement.zornCross
            (fun j => coefficientBracket p (X.sigma_minus j)) Y.sigma_minus i) +
        (X.n_plus * coefficientBracket p (Y.sigma_plus i) +
          X.sigma_plus i * coefficientBracket p Y.n_minus -
          NCZornElement.zornCross X.sigma_minus
            (fun j => coefficientBracket p (Y.sigma_minus j)) i)
    fin_cases i <;>
      simp only [NCZornElement.zornCross, coefficientBracket]
      <;> noncomm_ring
  · funext i
    change coefficientBracket p
        (X.n_minus * Y.sigma_minus i + X.sigma_minus i * Y.n_plus +
          NCZornElement.zornCross X.sigma_plus Y.sigma_plus i) =
      (coefficientBracket p X.n_minus * Y.sigma_minus i +
          coefficientBracket p (X.sigma_minus i) * Y.n_plus +
          NCZornElement.zornCross
            (fun j => coefficientBracket p (X.sigma_plus j)) Y.sigma_plus i) +
        (X.n_minus * coefficientBracket p (Y.sigma_minus i) +
          X.sigma_minus i * coefficientBracket p Y.n_plus +
          NCZornElement.zornCross X.sigma_plus
            (fun j => coefficientBracket p (Y.sigma_plus j)) i)
    fin_cases i <;>
      simp only [NCZornElement.zornCross, coefficientBracket]
      <;> noncomm_ring

/-- The coefficient differential operators need not commute. -/
theorem coefficientDeriv_commutator (p q : A) (X : OperatorZornMatrix A) :
    coefficientDeriv p (coefficientDeriv q X) -
        coefficientDeriv q (coefficientDeriv p X) =
      coefficientDeriv (coefficientBracket p q) X := by
  cases X with
  | mk np nm sp sm =>
    apply operatorZornMatrix_ext
    all_goals dsimp [coefficientDeriv, coefficientBracket, operatorZornCoordinates]
    all_goals simp only [zornSub_nPlus, zornSub_nMinus,
      zornSub_sigmaPlus, zornSub_sigmaMinus]
    · noncomm_ring
    · noncomm_ring
    · funext i
      noncomm_ring
    · funext i
      noncomm_ring

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

theorem zorn_mul_add_right (X Y Z : OperatorZornMatrix A) :
    X * (Y + Z) = X * Y + X * Z := by
  cases X with
  | mk xp xm xsp xsm =>
    cases Y with
    | mk yp ym ysp ysm =>
      cases Z with
      | mk zp zm zsp zsm =>
        apply operatorZornMatrix_ext
        · change xp * (yp + zp) + NCZornElement.zornDot xsp
              (fun i => ysm i + zsm i) =
            (xp * yp + NCZornElement.zornDot xsp ysm) +
              (xp * zp + NCZornElement.zornDot xsp zsm)
          simp [NCZornElement.zornDot]
          noncomm_ring
        · change xm * (ym + zm) + NCZornElement.zornDot xsm
              (fun i => ysp i + zsp i) =
            (xm * ym + NCZornElement.zornDot xsm ysp) +
              (xm * zm + NCZornElement.zornDot xsm zsp)
          simp [NCZornElement.zornDot]
          noncomm_ring
        · funext i
          change xp * (ysp i + zsp i) +
              xsp i * (ym + zm) -
              NCZornElement.zornCross xsm
                (fun j => ysm j + zsm j) i =
            (xp * ysp i + xsp i * ym -
              NCZornElement.zornCross xsm ysm i) +
            (xp * zsp i + xsp i * zm -
              NCZornElement.zornCross xsm zsm i)
          fin_cases i <;>
            simp [NCZornElement.zornCross] <;> noncomm_ring
        · funext i
          change xm * (ysm i + zsm i) +
              xsm i * (yp + zp) +
              NCZornElement.zornCross xsp
                (fun j => ysp j + zsp j) i =
            (xm * ysm i + xsm i * yp +
              NCZornElement.zornCross xsp ysp i) +
            (xm * zsm i + xsm i * zp +
              NCZornElement.zornCross xsp zsp i)
          fin_cases i <;>
            simp [NCZornElement.zornCross] <;> noncomm_ring

theorem zorn_mul_add_left (X Y Z : OperatorZornMatrix A) :
    (X + Y) * Z = X * Z + Y * Z := by
  cases X with
  | mk xp xm xsp xsm =>
    cases Y with
    | mk yp ym ysp ysm =>
      cases Z with
      | mk zp zm zsp zsm =>
        apply operatorZornMatrix_ext
        · change (xp + yp) * zp + NCZornElement.zornDot
              (fun i => xsp i + ysp i) zsm =
            (xp * zp + NCZornElement.zornDot xsp zsm) +
            (yp * zp + NCZornElement.zornDot ysp zsm)
          simp [NCZornElement.zornDot]
          noncomm_ring
        · change (xm + ym) * zm + NCZornElement.zornDot
              (fun i => xsm i + ysm i) zsp =
            (xm * zm + NCZornElement.zornDot xsm zsp) +
            (ym * zm + NCZornElement.zornDot ysm zsp)
          simp [NCZornElement.zornDot]
          noncomm_ring
        · funext i
          change (xp + yp) * zsp i +
              (xsp i + ysp i) * zm -
              NCZornElement.zornCross
                (fun j => xsm j + ysm j) zsm i =
            (xp * zsp i + xsp i * zm -
              NCZornElement.zornCross xsm zsm i) +
            (yp * zsp i + ysp i * zm -
              NCZornElement.zornCross ysm zsm i)
          fin_cases i <;>
            simp [NCZornElement.zornCross] <;> noncomm_ring
        · funext i
          change (xm + ym) * zsm i +
              (xsm i + ysm i) * zp +
              NCZornElement.zornCross
                (fun j => xsp j + ysp j) zsp i =
            (xm * zsm i + xsm i * zp +
              NCZornElement.zornCross xsp zsp i) +
            (ym * zsm i + ysm i * zp +
              NCZornElement.zornCross ysp zsp i)
          fin_cases i <;>
            simp [NCZornElement.zornCross] <;> noncomm_ring

theorem fieldStrength_swap (p : Fin 4 → A) (Phi : FourPotential A) (mu nu : Fin 4) :
    fieldStrength p Phi nu mu = -fieldStrength p Phi mu nu := by
  apply operatorZornMatrix_ext
  · simp only [fieldStrength, bracket, zornAdd_nPlus, zornAdd_nMinus,
      zornNeg_nPlus, zornNeg_nMinus, zornSub_nPlus, zornSub_nMinus]
    simp [NCZornElement.instAdd, NCZornElement.instNeg,
      NCZornElement.instSub, NCZornElement.mul,
      zornAdd_sigmaPlus_apply, zornSub_sigmaPlus_apply,
      zornNeg_sigmaPlus_apply, zornMul_sigmaPlus_apply,
      coefficientDeriv_sigmaPlus_apply, coefficientBracket,
      NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · simp only [fieldStrength, bracket, zornAdd_nPlus, zornAdd_nMinus,
      zornNeg_nPlus, zornNeg_nMinus, zornSub_nPlus, zornSub_nMinus]
    simp [zornAdd_sigmaMinus_apply, zornSub_sigmaMinus_apply,
      zornNeg_sigmaMinus_apply, zornMul_sigmaMinus_apply,
      coefficientDeriv_sigmaMinus_apply, coefficientBracket,
      NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · funext i
    simp only [fieldStrength, bracket, zornAdd_sigmaPlus, zornNeg_sigmaPlus,
      zornSub_sigmaPlus]
    simp [NCZornElement.instAdd, NCZornElement.instNeg,
      NCZornElement.instSub, NCZornElement.mul,
      coefficientBracket, NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · funext i
    simp only [fieldStrength, bracket, zornAdd_sigmaMinus, zornNeg_sigmaMinus,
      zornSub_sigmaMinus]
    simp [NCZornElement.instAdd, NCZornElement.instNeg,
      NCZornElement.instSub, NCZornElement.mul,
      coefficientBracket, NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring

/-- Full curvature identity: background curvature and both associators survive. -/
theorem curvatureAction_eq (p : Fin 4 → A) (Phi : FourPotential A)
    (mu nu : Fin 4) (X : OperatorZornMatrix A) :
    curvatureAction p Phi mu nu X =
      coefficientDeriv (coefficientBracket (p mu) (p nu)) X +
        fieldStrength p Phi mu nu * X -
          associator (Phi mu) (Phi nu) X + associator (Phi nu) (Phi mu) X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [curvatureAction, covariant, fieldStrength, bracket,
    associator, coefficientDeriv, coefficientBracket,
    operatorZornCoordinates, NCZornElement.mul, NCZornElement.zornDot,
    NCZornElement.instAdd, NCZornElement.instNeg, NCZornElement.instSub,
    NCZornElement.zornCross]
  all_goals try simp only [Algebra.smul_def, smul_eq_mul, neg_one_smul A,
    neg_smul, one_smul]
  all_goals simp [NCZornElement.zornDot, NCZornElement.zornCross,
    coefficientBracket, neg_one_smul] at *
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
  cases X
  cases Y
  cases Z
  apply operatorZornMatrix_ext
  · simp only [bracket, associatorAlternation, associator, zornAdd_nPlus,
      zornNeg_nPlus, zornSub_nPlus, zornMul_nPlus]
    simp [NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · simp only [bracket, associatorAlternation, associator, zornAdd_nMinus,
      zornNeg_nMinus, zornSub_nMinus, zornMul_nMinus]
    simp [NCZornElement.zornDot, NCZornElement.zornCross]
    noncomm_ring
  · funext i
    simp only [bracket, associatorAlternation, associator, zornAdd_sigmaPlus,
      zornAdd_sigmaPlus_apply, zornNeg_sigmaPlus, zornNeg_sigmaPlus_apply,
      zornSub_sigmaPlus, zornSub_sigmaPlus_apply, zornMul_sigmaPlus,
      zornMul_sigmaPlus_apply]
    fin_cases i <;>
      simp [NCZornElement.zornDot, NCZornElement.zornCross] <;>
      noncomm_ring
  · funext i
    simp only [bracket, associatorAlternation, associator, zornAdd_sigmaMinus,
      zornAdd_sigmaMinus_apply, zornNeg_sigmaMinus, zornNeg_sigmaMinus_apply,
      zornSub_sigmaMinus, zornSub_sigmaMinus_apply, zornMul_sigmaMinus,
      zornMul_sigmaMinus_apply]
    fin_cases i <;>
      simp [NCZornElement.zornDot, NCZornElement.zornCross] <;>
      noncomm_ring

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
    operatorZornCoordinates, NCZornElement.mul, NCZornElement.zornDot,
    NCZornElement.instAdd, NCZornElement.instNeg, NCZornElement.instSub,
    NCZornElement.zornCross]
  all_goals try simp only [Algebra.smul_def, smul_eq_mul, neg_one_smul A,
    neg_smul, one_smul]
  all_goals simp [NCZornElement.zornDot, NCZornElement.zornCross,
    coefficientBracket, neg_one_smul] at *
  all_goals noncomm_ring

/-! ### Temporal and spatial field-strength sectors -/

def electric (p : Fin 4 → A) (Phi : FourPotential A) : Fin 3 → OperatorZornMatrix A :=
  fun i => fieldStrength p Phi 0 i.succ

def magnetic (p : Fin 4 → A) (Phi : FourPotential A) : Fin 3 → OperatorZornMatrix A
  | 0 => fieldStrength p Phi 2 3
  | 1 => fieldStrength p Phi 3 1
  | 2 => fieldStrength p Phi 1 2

theorem electric_eq (p : Fin 4 → A) (Phi : FourPotential A) (i : Fin 3) :
    electric p Phi i = coefficientDeriv (p 0) (Phi i.succ) -
      coefficientDeriv (p i.succ) (Phi 0) + bracket (Phi 0) (Phi i.succ) := rfl

/-! ### 3+1 projections of the nonassociative Bianchi identity -/

theorem bianchi_magnetic_gauss (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointCovariant p Phi 1 (magnetic p Phi 0) +
      adjointCovariant p Phi 2 (magnetic p Phi 1) +
        adjointCovariant p Phi 3 (magnetic p Phi 2) =
      coefficientDeriv (coefficientBracket (p 1) (p 2)) (Phi 3) +
        coefficientDeriv (coefficientBracket (p 2) (p 3)) (Phi 1) +
          coefficientDeriv (coefficientBracket (p 3) (p 1)) (Phi 2) -
            associatorAlternation (Phi 1) (Phi 2) (Phi 3) := by
  have h := bianchi_eq p Phi 1 2 3
  dsimp [bianchi, magnetic] at h ⊢
  exact h

theorem bianchi_faraday_x (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointCovariant p Phi 0 (magnetic p Phi 0) +
      adjointCovariant p Phi 2 (fieldStrength p Phi 3 0) +
        adjointCovariant p Phi 3 (electric p Phi 1) =
      coefficientDeriv (coefficientBracket (p 0) (p 2)) (Phi 3) +
        coefficientDeriv (coefficientBracket (p 2) (p 3)) (Phi 0) +
          coefficientDeriv (coefficientBracket (p 3) (p 0)) (Phi 2) -
            associatorAlternation (Phi 0) (Phi 2) (Phi 3) := by
  have h := bianchi_eq p Phi 0 2 3
  dsimp [bianchi, electric, magnetic] at h ⊢
  exact h

theorem bianchi_faraday_y (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointCovariant p Phi 0 (magnetic p Phi 1) +
      adjointCovariant p Phi 3 (fieldStrength p Phi 1 0) +
        adjointCovariant p Phi 1 (electric p Phi 2) =
      coefficientDeriv (coefficientBracket (p 0) (p 3)) (Phi 1) +
        coefficientDeriv (coefficientBracket (p 3) (p 1)) (Phi 0) +
          coefficientDeriv (coefficientBracket (p 1) (p 0)) (Phi 3) -
            associatorAlternation (Phi 0) (Phi 3) (Phi 1) := by
  have h := bianchi_eq p Phi 0 3 1
  dsimp [bianchi, electric, magnetic] at h ⊢
  exact h

theorem bianchi_faraday_z (p : Fin 4 → A) (Phi : FourPotential A) :
    adjointCovariant p Phi 0 (magnetic p Phi 2) +
      adjointCovariant p Phi 1 (fieldStrength p Phi 2 0) +
        adjointCovariant p Phi 2 (electric p Phi 0) =
      coefficientDeriv (coefficientBracket (p 0) (p 1)) (Phi 2) +
        coefficientDeriv (coefficientBracket (p 1) (p 2)) (Phi 0) +
          coefficientDeriv (coefficientBracket (p 2) (p 0)) (Phi 1) -
            associatorAlternation (Phi 0) (Phi 1) (Phi 2) := by
  have h := bianchi_eq p Phi 0 1 2
  dsimp [bianchi, electric, magnetic] at h ⊢
  exact h

def gaugeVariation (p : Fin 4 → A) (Phi : FourPotential A)
    (Lambda : OperatorZornMatrix A) (mu : Fin 4) : OperatorZornMatrix A :=
  adjointCovariant p Phi mu Lambda

/-- Native spatial curvature channels from the existing operator-Zorn owner. -/
theorem chiral_square_retains_curvature (U V : OperatorVector A) :
    operatorZornMul (chiralOperatorZorn U V) (chiralOperatorZorn U V) =
      OperatorZornConnectionCurvatureBridge.operatorZornMetricPart U V +
        OperatorZornConnectionCurvatureBridge.operatorZornCurvaturePart U V := by
  exact OperatorZornConnectionCurvatureBridge.chiralOperatorZorn_square_eq_metric_add_curvature U V

end InfoGeometry.Canonical.OperatorZornFourPotentialGauge
