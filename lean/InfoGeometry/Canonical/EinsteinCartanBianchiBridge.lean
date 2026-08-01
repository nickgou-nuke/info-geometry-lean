import Mathlib
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge

set_option linter.unusedVariables false

namespace InfoGeometry.Canonical

open BigOperators
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {d_dim : ℕ}

/-- 1. Дефиниция на Тетрадата e (Вектор от 1-форми) -/
def TetradVector (d_dim : ℕ) (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  Fin d_dim → ExteriorAlgebra R V

/-- 2. Дефиниция на Спиновата Свързаност ω (Матрица от 1-форми) -/
def SpinConnectionMatrix (d_dim : ℕ) (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  Matrix (Fin d_dim) (Fin d_dim) (ExteriorAlgebra R V)

/-- 3. Външно умножение на Спинова Свързаност и Тетрада: (ω ∧ e)^a = ∑_b ω^{ab} ∧ e^b -/
def spinConnectionWedgeTetrad
    (omega : SpinConnectionMatrix d_dim R V)
    (e : TetradVector d_dim R V) : TetradVector d_dim R V :=
  fun a => ∑ b, omega a b * e b

/-- 4. Дефиниция на 2-формата на Торзията: T = d e + ω ∧ e -/
def torsionForm
    (diff : Module.End R (ExteriorAlgebra R V))
    (omega : SpinConnectionMatrix d_dim R V)
    (e : TetradVector d_dim R V) : TetradVector d_dim R V :=
  fun a => diff (e a) + spinConnectionWedgeTetrad omega e a

/-- Дефиниция на matrixExteriorDerivative (добавена локално) -/
def matrixExteriorDerivative (diff : Module.End R (ExteriorAlgebra R V)) (M : Matrix (Fin d_dim) (Fin d_dim) (ExteriorAlgebra R V)) : Matrix (Fin d_dim) (Fin d_dim) (ExteriorAlgebra R V) :=
  Matrix.of (fun i j => diff (M i j))

/-- 5. Дефиниция на 2-формата на Римановата Кривина: R = d ω + ω ∧ ω -/
def riemannCurvatureForm
    (diff : Module.End R (ExteriorAlgebra R V))
    (omega : SpinConnectionMatrix d_dim R V) : SpinConnectionMatrix d_dim R V :=
  fun i j => (matrixExteriorDerivative diff omega) i j + ∑ k, omega i k * omega k j

/-- **Теорема**: ПЪРВО ТЪЖДЕСТВО НА БИАНКИ ЗА ТОРЗИЯТА (dT + ω ∧ T = R ∧ e).
    Доказано алгебрично от d² = 0 и Козуловия знак за 1-форми (-1)¹ = -1. -/
theorem first_bianchi_identity_torsion
    (D : ExteriorDifferentialData R V)
    (omega : SpinConnectionMatrix d_dim R V)
    (e : TetradVector d_dim R V)
    (h_d2_e : ∀ a, D.d (D.d (e a)) = 0)
    (h_leibniz_omega_e : ∀ a b, D.d (omega a b * e b) = D.d (omega a b) * e b - omega a b * D.d (e b)) :
    (fun a => D.d (torsionForm D.d omega e a) + spinConnectionWedgeTetrad omega (torsionForm D.d omega e) a) =
    spinConnectionWedgeTetrad (riemannCurvatureForm D.d omega) e := by
  funext a
  dsimp [torsionForm, spinConnectionWedgeTetrad, riemannCurvatureForm, matrixExteriorDerivative]
  simp only [map_add, map_sum, h_d2_e, zero_add]
  simp only [h_leibniz_omega_e, Finset.sum_sub_distrib]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have h_assoc : (∑ b : Fin d_dim, ∑ c : Fin d_dim, omega a b * (omega b c * e c)) =
                 (∑ b : Fin d_dim, ∑ c : Fin d_dim, (omega a c * omega c b) * e b) := by
    -- we swap b and c on the rhs
    rw [Finset.sum_comm]
    apply congrArg
    funext b
    apply congrArg
    funext c
    rw [mul_assoc]
  rw [h_assoc]
  abel

/-- **Теорема**: ВТОРО ТЪЖДЕСТВО НА БИАНКИ ЗА КРИВИНАТА (dR + ω ∧ R - R ∧ ω = 0).
    Доказано алгебрично от d² = 0 и градуираната деривация за 1-форми. -/
theorem second_bianchi_identity_curvature
    (D : ExteriorDifferentialData R V)
    (omega : SpinConnectionMatrix d_dim R V)
    (h_d2_omega : ∀ a b, D.d (D.d (omega a b)) = 0)
    (h_leibniz_omega_omega : ∀ a b c, D.d (omega a c * omega c b) = D.d (omega a c) * omega c b - omega a c * D.d (omega c b)) :
    (fun i j => (matrixExteriorDerivative D.d (riemannCurvatureForm D.d omega)) i j +
      (∑ k, omega i k * riemannCurvatureForm D.d omega k j) -
      (∑ k, riemannCurvatureForm D.d omega i k * omega k j)) = 0 := by
  funext i j
  dsimp [riemannCurvatureForm, matrixExteriorDerivative]
  simp only [map_add, map_sum, h_d2_omega, zero_add]
  simp only [h_leibniz_omega_omega, Finset.sum_sub_distrib]
  simp only [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have h_assoc_1 : (∑ k : Fin d_dim, ∑ m : Fin d_dim, omega i k * (omega k m * omega m j)) =
                   (∑ k : Fin d_dim, ∑ m : Fin d_dim, omega i m * omega m k * omega k j) := by
    rw [Finset.sum_comm]
    apply congrArg
    funext k
    apply congrArg
    funext m
    rw [mul_assoc]
  rw [h_assoc_1]
  abel



/-- 6. Действие на Айнщайн-Картан: S_EC = ∫ ε_{abcd} e^a ∧ e^b ∧ R^{cd}
    Тук дефинираме 4-формата на лагранжиана (Lagrangian 4-form), 
    интегрирането е имплицитно като проекция върху топ-формата. -/
def einsteinCartanAction (D : ExteriorDifferentialData R V)
    (e : TetradVector 4 R V)
    (omega : SpinConnectionMatrix 4 R V) : ExteriorAlgebra R V :=
  ∑ σ : Equiv.Perm (Fin 4),
    (Equiv.Perm.sign σ : ℤ) • (e (σ 0) * e (σ 1) * riemannCurvatureForm D.d omega (σ 2) (σ 3))

@[simp] theorem spinConnectionWedgeTetrad_zero
    (e : TetradVector d_dim R V) :
    spinConnectionWedgeTetrad
        (fun _ : Fin d_dim => fun _ : Fin d_dim => (0 : ExteriorAlgebra R V)) e =
      (fun _ : Fin d_dim => (0 : ExteriorAlgebra R V)) := by
  funext a
  simp [spinConnectionWedgeTetrad]

@[simp] theorem matrixExteriorDerivative_zero
    (diff : Module.End R (ExteriorAlgebra R V)) :
    matrixExteriorDerivative diff
        (fun _ : Fin d_dim => fun _ : Fin d_dim => (0 : ExteriorAlgebra R V)) =
      (fun _ : Fin d_dim => fun _ : Fin d_dim => (0 : ExteriorAlgebra R V)) := by
  ext i j
  simp [matrixExteriorDerivative]

@[simp] theorem riemannCurvatureForm_zero
    (D : ExteriorDifferentialData R V) :
    riemannCurvatureForm D.d
        (fun _ : Fin d_dim => fun _ : Fin d_dim => (0 : ExteriorAlgebra R V)) =
      (fun _ : Fin d_dim => fun _ : Fin d_dim => (0 : ExteriorAlgebra R V)) := by
  funext i j
  simp [riemannCurvatureForm, matrixExteriorDerivative]

theorem einsteinCartanAction_zero_connection
    (D : ExteriorDifferentialData R V)
    (e : TetradVector 4 R V) :
    einsteinCartanAction D e
        (fun _ : Fin 4 => fun _ : Fin 4 => (0 : ExteriorAlgebra R V)) = 0 := by
  simp [einsteinCartanAction, riemannCurvatureForm, matrixExteriorDerivative]

theorem einsteinCartanAction_zero_tetrad
    (D : ExteriorDifferentialData R V)
    (e : TetradVector 4 R V)
    (omega : SpinConnectionMatrix 4 R V)
    (h_e : e = fun _ : Fin 4 => (0 : ExteriorAlgebra R V)) :
    einsteinCartanAction D e omega = 0 := by
  rw [h_e]
  simp [einsteinCartanAction]

end InfoGeometry.Canonical
