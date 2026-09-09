import InfoGeometry.Canonical.OperatorZornRealModule
import InfoGeometry.Canonical.OperatorZornExchangeAutomorphism

/-!
# The coefficient nucleus and full Peirce corners

The coefficient ring embeds in the nucleus, not generally in the center.
All three nucleus laws are proved on the existing ordered Zorn product.
The native nonassociative ring instance below adds no associativity law.
-/

noncomputable section
namespace InfoGeometry.Canonical.OperatorZornCoefficientNucleus

open InfoGeometry.Physics.NCG
open OperatorZornRealModule OperatorZornExchangeAutomorphism OperatorZornGaugeCovariance
open scoped BigOperators

variable {A : Type*} [Ring A]

def diagonalCoefficient (a : A) : OperatorZornMatrix A :=
  operatorZornCoordinates a a 0 0

theorem diagonalCoefficient_injective :
    Function.Injective (diagonalCoefficient (A := A)) := by
  intro a b h
  exact congrArg NCZornElement.n_plus h

@[simp] theorem diagonalCoefficient_mul (a b : A) :
    diagonalCoefficient a * diagonalCoefficient b = diagonalCoefficient (a*b) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [diagonalCoefficient, operatorZornCoordinates, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]

def coefficientMulHom : A →ₙ* OperatorZornMatrix A where
  toFun := diagonalCoefficient
  map_mul' a b := (diagonalCoefficient_mul a b).symm

@[simp] theorem add_n_plus (X Y : OperatorZornMatrix A) :
    (X + Y).n_plus = X.n_plus + Y.n_plus := rfl

@[simp] theorem add_n_minus (X Y : OperatorZornMatrix A) :
    (X + Y).n_minus = X.n_minus + Y.n_minus := rfl

@[simp] theorem add_sigma_plus (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X + Y).sigma_plus i = X.sigma_plus i + Y.sigma_plus i := rfl

@[simp] theorem add_sigma_minus (X Y : OperatorZornMatrix A) (i : Fin 3) :
    (X + Y).sigma_minus i = X.sigma_minus i + Y.sigma_minus i := rfl

@[simp] theorem zero_n_plus :
    (0 : OperatorZornMatrix A).n_plus = 0 := rfl

@[simp] theorem zero_n_minus :
    (0 : OperatorZornMatrix A).n_minus = 0 := rfl

@[simp] theorem zero_sigma_plus (i : Fin 3) :
    (0 : OperatorZornMatrix A).sigma_plus i = 0 := rfl

@[simp] theorem zero_sigma_minus (i : Fin 3) :
    (0 : OperatorZornMatrix A).sigma_minus i = 0 := rfl

@[simp] theorem diagonalCoefficient_zero : diagonalCoefficient (0 : A) = 0 := rfl

@[simp] theorem diagonalCoefficient_one_mul (X : OperatorZornMatrix A) :
    diagonalCoefficient (1 : A) * X = X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [diagonalCoefficient, operatorZornCoordinates, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]

@[simp] theorem mul_diagonalCoefficient_one (X : OperatorZornMatrix A) :
    X * diagonalCoefficient (1 : A) = X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [diagonalCoefficient, operatorZornCoordinates, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]

theorem coefficient_left_nucleus (a : A) (X Y : OperatorZornMatrix A) :
    (diagonalCoefficient a * X) * Y = diagonalCoefficient a * (X*Y) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [diagonalCoefficient, operatorZornCoordinates, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

theorem coefficient_middle_nucleus (a : A) (X Y : OperatorZornMatrix A) :
    (X * diagonalCoefficient a) * Y = X * (diagonalCoefficient a * Y) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [diagonalCoefficient, operatorZornCoordinates, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

theorem coefficient_right_nucleus (a : A) (X Y : OperatorZornMatrix A) :
    (X * Y) * diagonalCoefficient a = X * (Y * diagonalCoefficient a) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [diagonalCoefficient, operatorZornCoordinates, NCZornElement.mul,
    NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

section Module
variable [Algebra ℝ A]

/- The Zorn carrier has only its native `Mul`; this local additive-distributive
   structure supplies the finite-sum lemmas needed below without asserting
   associativity. -/
instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (OperatorZornMatrix A) where
  __ := (inferInstance : AddCommGroup (OperatorZornMatrix A))
  mul := NCZornElement.mul
  left_distrib X Y Z := by
    cases X
    cases Y
    cases Z
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals dsimp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
    all_goals noncomm_ring
  right_distrib X Y Z := by
    cases X
    cases Y
    cases Z
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals dsimp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
    all_goals noncomm_ring
  zero_mul X := by
    cases X
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals simp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  mul_zero X := by
    cases X
    apply operatorZornMatrix_ext
    all_goals first | (funext i; fin_cases i) | skip
    all_goals simp [NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]

def coefficientLinearMap : A →ₗ[ℝ] OperatorZornMatrix A where
  toFun := diagonalCoefficient
  map_add' a b := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals simp [diagonalCoefficient, operatorZornCoordinates]
  map_smul' c a := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals simp [diagonalCoefficient, operatorZornCoordinates]

/-- The parentheses remain part of the definition. -/
def corner (p q : A) (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  (diagonalCoefficient p * X) * diagonalCoefficient q

theorem corner_coordinates (p q : A) (X : OperatorZornMatrix A) :
    corner p q X = operatorZornCoordinates
      (p*X.n_plus*q) (p*X.n_minus*q)
      (fun i => p*X.sigma_plus i*q) (fun i => p*X.sigma_minus i*q) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [corner, diagonalCoefficient, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]

theorem corner_product (p q r s : A) (X Y : OperatorZornMatrix A) :
    corner p q X * corner r s Y =
      corner p s (X * (diagonalCoefficient (q*r) * Y)) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [corner, diagonalCoefficient, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

theorem corner_product_zero (p q r s : A) (hqr : q*r = 0)
    (X Y : OperatorZornMatrix A) : corner p q X * corner r s Y = 0 := by
  rw [corner_product, hqr, diagonalCoefficient_zero]
  rw [corner_coordinates]
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp [operatorZornCoordinates]

/-- The finite matrix family in the next module discharges this resolution premise. -/
theorem corner_reconstruction {J : Type*} [Fintype J]
    (P : J → A) (hP : ∑ j, P j = 1) (X : OperatorZornMatrix A) :
    (∑ j, ∑ k, corner (P j) (P k) X) = X := by
  have hs : (∑ j, diagonalCoefficient (P j)) = diagonalCoefficient (1 : A) := by
    change (∑ j, coefficientLinearMap (P j)) = _
    rw [← map_sum, hP]
    rfl
  calc
    (∑ j, ∑ k, corner (P j) (P k) X) =
        ((∑ j, diagonalCoefficient (P j)) * X) * (∑ k, diagonalCoefficient (P k)) := by
      simp only [corner]
      conv_rhs =>
        rw [Finset.mul_sum, Finset.sum_mul]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = X := by rw [hs, diagonalCoefficient_one_mul, mul_diagonalCoefficient_one]

theorem exchange_corner (p q : A) (X : OperatorZornMatrix A) :
    exchange (corner p q X) = corner p q (exchange X) := by
  have hd (a : A) : exchange (diagonalCoefficient a) = diagonalCoefficient a := by
    apply operatorZornMatrix_ext <;>
      simp [exchange, diagonalCoefficient, operatorZornCoordinates]
  unfold corner
  rw [exchange_mul, exchange_mul, hd, hd]

theorem gauge_corner (g : Aˣ) (p q : A) (X : OperatorZornMatrix A) :
    OperatorZornGaugeCovariance.gauge g (corner p q X) =
      corner (coefficientConjugation g p) (coefficientConjugation g q) (gauge g X) := by
  have hd (a : A) : OperatorZornGaugeCovariance.gauge g (diagonalCoefficient a) =
      diagonalCoefficient (coefficientConjugation g a) := by
    apply operatorZornMatrix_ext
    all_goals first | (funext i) | skip
    all_goals simp [OperatorZornGaugeCovariance.gauge, mapCoefficients, diagonalCoefficient, operatorZornCoordinates,
      OperatorZornRepresentationCurvatureBridge.mapOperatorVector, coefficientConjugation]
  unfold corner
  rw [gauge_mul, gauge_mul, hd, hd]

end Module
end InfoGeometry.Canonical.OperatorZornCoefficientNucleus
