import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section

open MvPolynomial

namespace SplitQuaternionWheelerDeWitt

abbrev WavePolynomial := MvPolynomial (Fin 4) ℝ

def pderiv (i : Fin 4) (ψ : WavePolynomial) : WavePolynomial :=
  MvPolynomial.pderiv i ψ

lemma pderiv_zero (i : Fin 4) : pderiv i (0 : WavePolynomial) = 0 := by
  unfold pderiv; exact map_zero _

lemma pderiv_add (i : Fin 4) (p q : WavePolynomial) : pderiv i (p + q) = pderiv i p + pderiv i q := by
  unfold pderiv; exact map_add (MvPolynomial.pderiv i) p q

lemma pderiv_sub (i : Fin 4) (p q : WavePolynomial) : pderiv i (p - q) = pderiv i p - pderiv i q := by
  unfold pderiv; exact map_sub (MvPolynomial.pderiv i) p q

lemma pderiv_neg (i : Fin 4) (p : WavePolynomial) : pderiv i (-p) = -pderiv i p := by
  unfold pderiv; exact map_neg (MvPolynomial.pderiv i) p

lemma pderiv_comm (i j : Fin 4) (ψ : WavePolynomial) :
    pderiv i (pderiv j ψ) = pderiv j (pderiv i ψ) := by
  unfold pderiv
  induction ψ using MvPolynomial.induction_on
  case C c =>
    rw [MvPolynomial.pderiv_C, MvPolynomial.pderiv_C, map_zero, map_zero]
  case add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, hp, hq]
  case mul_X =>
    rename_i p k hp
    have hd1 : MvPolynomial.pderiv i (p * X k) = MvPolynomial.pderiv i p * X k + p * MvPolynomial.pderiv i (X k) := by rw [MvPolynomial.pderiv_mul]
    have hd2 : MvPolynomial.pderiv j (p * X k) = MvPolynomial.pderiv j p * X k + p * MvPolynomial.pderiv j (X k) := by rw [MvPolynomial.pderiv_mul]
    rw [hd1, hd2, map_add, map_add]
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
    have hc : MvPolynomial.pderiv i (MvPolynomial.pderiv j (X k : WavePolynomial)) = MvPolynomial.pderiv j (MvPolynomial.pderiv i (X k : WavePolynomial)) := by
      rw [MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
      by_cases h1 : j = k
      · rw [h1, Pi.single_eq_same]
        by_cases h2 : i = k
        · rw [h2, Pi.single_eq_same]
        · have hne : k ≠ i := Ne.symm h2
          rw [Pi.single_eq_of_ne hne, MvPolynomial.pderiv_one, map_zero]
      · have hne : k ≠ j := Ne.symm h1
        rw [Pi.single_eq_of_ne hne, map_zero]
        by_cases h2 : i = k
        · rw [h2, Pi.single_eq_same, MvPolynomial.pderiv_one]
        · have hne2 : k ≠ i := Ne.symm h2
          rw [Pi.single_eq_of_ne hne2, map_zero]
    rw [hp, hc]
    ring

lemma pderiv_comm_sq (i j : Fin 4) (ψ : WavePolynomial) :
    pderiv i (pderiv j (pderiv j ψ)) = pderiv j (pderiv j (pderiv i ψ)) := by
  rw [pderiv_comm i j, pderiv_comm i j]

lemma pderiv_X_mul (i j : Fin 4) (ψ : WavePolynomial) :
    pderiv i (X j * ψ) = (if i = j then ψ else 0) + X j * pderiv i ψ := by
  unfold pderiv
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same]
    ring
  · have hne : j ≠ i := by intro h2; apply h; exact h2.symm
    rw [Pi.single_eq_of_ne hne, zero_mul, zero_add]

lemma pderiv_sq_X_mul (i j : Fin 4) (ψ : WavePolynomial) :
    pderiv i (pderiv i (X j * ψ)) =
      (if i = j then 2 * pderiv i ψ else 0) + X j * pderiv i (pderiv i ψ) := by
  rw [pderiv_X_mul]
  unfold pderiv at *
  rw [map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same]
    ring
  · rw [map_zero, zero_add, Pi.single_eq_of_ne (Ne.symm h), zero_mul, zero_add]

lemma pderiv_sq_X (i : Fin 4) : pderiv i (X i ^ 2 : WavePolynomial) = 2 * X i := by
  unfold pderiv
  rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_eq_same, one_mul, mul_one]
  ring

lemma pderiv_sq_X_ne (i j : Fin 4) (h : i ≠ j) : pderiv i (X j ^ 2 : WavePolynomial) = 0 := by
  unfold pderiv
  rw [pow_two, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  have hne : j ≠ i := by intro h2; apply h; exact h2.symm
  rw [Pi.single_eq_of_ne hne, zero_mul, mul_zero, zero_add]

def secondDerivative (i : Fin 4) (ψ : WavePolynomial) : WavePolynomial :=
  pderiv i (pderiv i ψ)

def deWittBox (ψ : WavePolynomial) : WavePolynomial :=
  secondDerivative 0 ψ +
  secondDerivative 1 ψ -
  secondDerivative 2 ψ -
  secondDerivative 3 ψ

def deWittQuadratic : WavePolynomial :=
  X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 - X 3 ^ 2

def bogoliubovVectorField (ψ : WavePolynomial) : WavePolynomial :=
  X 2 * pderiv 0 ψ +
  X 3 * pderiv 1 ψ +
  X 0 * pderiv 2 ψ +
  X 1 * pderiv 3 ψ

theorem bogoliubovVectorField_deWittQuadratic :
    bogoliubovVectorField deWittQuadratic = 0 := by
  unfold bogoliubovVectorField deWittQuadratic
  have p0 : pderiv 0 (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 - X 3 ^ 2 : WavePolynomial) = 2 * X 0 := by
    rw [pderiv_sub, pderiv_sub, pderiv_add]
    have h1 : (0:Fin 4) ≠ 1 := by decide
    have h2 : (0:Fin 4) ≠ 2 := by decide
    have h3 : (0:Fin 4) ≠ 3 := by decide
    rw [pderiv_sq_X_ne _ _ h1, pderiv_sq_X_ne _ _ h2, pderiv_sq_X_ne _ _ h3, pderiv_sq_X 0]
    simp
  have p1 : pderiv 1 (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 - X 3 ^ 2 : WavePolynomial) = 2 * X 1 := by
    rw [pderiv_sub, pderiv_sub, pderiv_add]
    have h0 : (1:Fin 4) ≠ 0 := by decide
    have h2 : (1:Fin 4) ≠ 2 := by decide
    have h3 : (1:Fin 4) ≠ 3 := by decide
    rw [pderiv_sq_X_ne _ _ h0, pderiv_sq_X_ne _ _ h2, pderiv_sq_X_ne _ _ h3, pderiv_sq_X 1]
    simp
  have p2 : pderiv 2 (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 - X 3 ^ 2 : WavePolynomial) = -2 * X 2 := by
    rw [pderiv_sub, pderiv_sub, pderiv_add]
    have h0 : (2:Fin 4) ≠ 0 := by decide
    have h1 : (2:Fin 4) ≠ 1 := by decide
    have h3 : (2:Fin 4) ≠ 3 := by decide
    rw [pderiv_sq_X_ne _ _ h0, pderiv_sq_X_ne _ _ h1, pderiv_sq_X_ne _ _ h3, pderiv_sq_X 2]
    simp
  have p3 : pderiv 3 (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 - X 3 ^ 2 : WavePolynomial) = -2 * X 3 := by
    rw [pderiv_sub, pderiv_sub, pderiv_add]
    have h0 : (3:Fin 4) ≠ 0 := by decide
    have h1 : (3:Fin 4) ≠ 1 := by decide
    have h2 : (3:Fin 4) ≠ 2 := by decide
    rw [pderiv_sq_X_ne _ _ h0, pderiv_sq_X_ne _ _ h1, pderiv_sq_X_ne _ _ h2, pderiv_sq_X 3]
    simp
  rw [p0, p1, p2, p3]
  ring

theorem deWittBox_commutes_bogoliubovVectorField (ψ : WavePolynomial) :
    deWittBox (bogoliubovVectorField ψ) = bogoliubovVectorField (deWittBox ψ) := by
  unfold deWittBox bogoliubovVectorField secondDerivative
  simp only [pderiv_add, pderiv_sub]
  -- pderiv 0 on X 2 * ...
  have h02 : pderiv 0 (pderiv 0 (X 2 * pderiv 0 ψ)) = X 2 * pderiv 0 (pderiv 0 (pderiv 0 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (0:Fin 4) ≠ 2 := by decide
    rw [if_neg h, zero_add]
  have h03 : pderiv 0 (pderiv 0 (X 3 * pderiv 1 ψ)) = X 3 * pderiv 0 (pderiv 0 (pderiv 1 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (0:Fin 4) ≠ 3 := by decide
    rw [if_neg h, zero_add]
  have h00 : pderiv 0 (pderiv 0 (X 0 * pderiv 2 ψ)) = 2 * pderiv 0 (pderiv 2 ψ) + X 0 * pderiv 0 (pderiv 0 (pderiv 2 ψ)) := by
    rw [pderiv_sq_X_mul, if_pos rfl]
  have h01 : pderiv 0 (pderiv 0 (X 1 * pderiv 3 ψ)) = X 1 * pderiv 0 (pderiv 0 (pderiv 3 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (0:Fin 4) ≠ 1 := by decide
    rw [if_neg h, zero_add]

  -- pderiv 1
  have h12 : pderiv 1 (pderiv 1 (X 2 * pderiv 0 ψ)) = X 2 * pderiv 1 (pderiv 1 (pderiv 0 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (1:Fin 4) ≠ 2 := by decide
    rw [if_neg h, zero_add]
  have h13 : pderiv 1 (pderiv 1 (X 3 * pderiv 1 ψ)) = X 3 * pderiv 1 (pderiv 1 (pderiv 1 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (1:Fin 4) ≠ 3 := by decide
    rw [if_neg h, zero_add]
  have h10 : pderiv 1 (pderiv 1 (X 0 * pderiv 2 ψ)) = X 0 * pderiv 1 (pderiv 1 (pderiv 2 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (1:Fin 4) ≠ 0 := by decide
    rw [if_neg h, zero_add]
  have h11 : pderiv 1 (pderiv 1 (X 1 * pderiv 3 ψ)) = 2 * pderiv 1 (pderiv 3 ψ) + X 1 * pderiv 1 (pderiv 1 (pderiv 3 ψ)) := by
    rw [pderiv_sq_X_mul, if_pos rfl]

  -- pderiv 2
  have h22 : pderiv 2 (pderiv 2 (X 2 * pderiv 0 ψ)) = 2 * pderiv 2 (pderiv 0 ψ) + X 2 * pderiv 2 (pderiv 2 (pderiv 0 ψ)) := by
    rw [pderiv_sq_X_mul, if_pos rfl]
  have h23 : pderiv 2 (pderiv 2 (X 3 * pderiv 1 ψ)) = X 3 * pderiv 2 (pderiv 2 (pderiv 1 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (2:Fin 4) ≠ 3 := by decide
    rw [if_neg h, zero_add]
  have h20 : pderiv 2 (pderiv 2 (X 0 * pderiv 2 ψ)) = X 0 * pderiv 2 (pderiv 2 (pderiv 2 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (2:Fin 4) ≠ 0 := by decide
    rw [if_neg h, zero_add]
  have h21 : pderiv 2 (pderiv 2 (X 1 * pderiv 3 ψ)) = X 1 * pderiv 2 (pderiv 2 (pderiv 3 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (2:Fin 4) ≠ 1 := by decide
    rw [if_neg h, zero_add]

  -- pderiv 3
  have h32 : pderiv 3 (pderiv 3 (X 2 * pderiv 0 ψ)) = X 2 * pderiv 3 (pderiv 3 (pderiv 0 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (3:Fin 4) ≠ 2 := by decide
    rw [if_neg h, zero_add]
  have h33 : pderiv 3 (pderiv 3 (X 3 * pderiv 1 ψ)) = 2 * pderiv 3 (pderiv 1 ψ) + X 3 * pderiv 3 (pderiv 3 (pderiv 1 ψ)) := by
    rw [pderiv_sq_X_mul, if_pos rfl]
  have h30 : pderiv 3 (pderiv 3 (X 0 * pderiv 2 ψ)) = X 0 * pderiv 3 (pderiv 3 (pderiv 2 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (3:Fin 4) ≠ 0 := by decide
    rw [if_neg h, zero_add]
  have h31 : pderiv 3 (pderiv 3 (X 1 * pderiv 3 ψ)) = X 1 * pderiv 3 (pderiv 3 (pderiv 3 ψ)) := by
    rw [pderiv_sq_X_mul]
    have h : (3:Fin 4) ≠ 1 := by decide
    rw [if_neg h, zero_add]

  rw [h02, h03, h00, h01, h12, h13, h10, h11, h22, h23, h20, h21, h32, h33, h30, h31]

  have c00 : pderiv 0 (pderiv 0 (pderiv 0 ψ)) = pderiv 0 (pderiv 0 (pderiv 0 ψ)) := rfl
  have c01 : pderiv 0 (pderiv 1 (pderiv 1 ψ)) = pderiv 1 (pderiv 1 (pderiv 0 ψ)) := pderiv_comm_sq 0 1 ψ
  have c02 : pderiv 0 (pderiv 2 (pderiv 2 ψ)) = pderiv 2 (pderiv 2 (pderiv 0 ψ)) := pderiv_comm_sq 0 2 ψ
  have c03 : pderiv 0 (pderiv 3 (pderiv 3 ψ)) = pderiv 3 (pderiv 3 (pderiv 0 ψ)) := pderiv_comm_sq 0 3 ψ

  have c10 : pderiv 1 (pderiv 0 (pderiv 0 ψ)) = pderiv 0 (pderiv 0 (pderiv 1 ψ)) := pderiv_comm_sq 1 0 ψ
  have c11 : pderiv 1 (pderiv 1 (pderiv 1 ψ)) = pderiv 1 (pderiv 1 (pderiv 1 ψ)) := rfl
  have c12 : pderiv 1 (pderiv 2 (pderiv 2 ψ)) = pderiv 2 (pderiv 2 (pderiv 1 ψ)) := pderiv_comm_sq 1 2 ψ
  have c13 : pderiv 1 (pderiv 3 (pderiv 3 ψ)) = pderiv 3 (pderiv 3 (pderiv 1 ψ)) := pderiv_comm_sq 1 3 ψ

  have c20 : pderiv 2 (pderiv 0 (pderiv 0 ψ)) = pderiv 0 (pderiv 0 (pderiv 2 ψ)) := pderiv_comm_sq 2 0 ψ
  have c21 : pderiv 2 (pderiv 1 (pderiv 1 ψ)) = pderiv 1 (pderiv 1 (pderiv 2 ψ)) := pderiv_comm_sq 2 1 ψ
  have c22 : pderiv 2 (pderiv 2 (pderiv 2 ψ)) = pderiv 2 (pderiv 2 (pderiv 2 ψ)) := rfl
  have c23 : pderiv 2 (pderiv 3 (pderiv 3 ψ)) = pderiv 3 (pderiv 3 (pderiv 2 ψ)) := pderiv_comm_sq 2 3 ψ

  have c30 : pderiv 3 (pderiv 0 (pderiv 0 ψ)) = pderiv 0 (pderiv 0 (pderiv 3 ψ)) := pderiv_comm_sq 3 0 ψ
  have c31 : pderiv 3 (pderiv 1 (pderiv 1 ψ)) = pderiv 1 (pderiv 1 (pderiv 3 ψ)) := pderiv_comm_sq 3 1 ψ
  have c32 : pderiv 3 (pderiv 2 (pderiv 2 ψ)) = pderiv 2 (pderiv 2 (pderiv 3 ψ)) := pderiv_comm_sq 3 2 ψ
  have c33 : pderiv 3 (pderiv 3 (pderiv 3 ψ)) = pderiv 3 (pderiv 3 (pderiv 3 ψ)) := rfl

  rw [c01, c02, c03, c10, c12, c13, c20, c21, c23, c30, c31, c32]

  have c02' : pderiv 0 (pderiv 2 ψ) = pderiv 2 (pderiv 0 ψ) := pderiv_comm 0 2 ψ
  have c13' : pderiv 1 (pderiv 3 ψ) = pderiv 3 (pderiv 1 ψ) := pderiv_comm 1 3 ψ
  rw [c02', c13']
  ring

def freeWheelerDeWitt (m : ℝ) (ψ : WavePolynomial) : WavePolynomial :=
  -deWittBox ψ + C (m ^ 2) * ψ

def IsWheelerDeWittSolution (m : ℝ) (ψ : WavePolynomial) : Prop :=
  freeWheelerDeWitt m ψ = 0

lemma pderiv_C_mul (i : Fin 4) (c : ℝ) (ψ : WavePolynomial) :
    pderiv i (C c * ψ) = C c * pderiv i ψ := by
  unfold pderiv
  rw [MvPolynomial.pderiv_C_mul]

theorem freeWheelerDeWitt_commutes_bogoliubov (m : ℝ) (ψ : WavePolynomial) :
    freeWheelerDeWitt m (bogoliubovVectorField ψ) =
      bogoliubovVectorField (freeWheelerDeWitt m ψ) := by
  unfold freeWheelerDeWitt
  rw [deWittBox_commutes_bogoliubovVectorField]
  unfold bogoliubovVectorField
  simp only [pderiv_add, pderiv_neg, pderiv_C_mul]
  ring

theorem IsWheelerDeWittSolution_bogoliubovVectorField
    {m : ℝ} {ψ : WavePolynomial}
    (hψ : IsWheelerDeWittSolution m ψ) :
    IsWheelerDeWittSolution m (bogoliubovVectorField ψ) := by
  unfold IsWheelerDeWittSolution at hψ ⊢
  rw [freeWheelerDeWitt_commutes_bogoliubov]
  rw [hψ]
  unfold bogoliubovVectorField
  rw [pderiv_zero 0, pderiv_zero 1, pderiv_zero 2, pderiv_zero 3]
  ring

def wheelerDeWittWithPotential (m : ℝ) (V ψ : WavePolynomial) : WavePolynomial :=
  freeWheelerDeWitt m ψ - V * ψ

theorem wheelerDeWittWithPotential_commutes_bogoliubov
    (m : ℝ) (V ψ : WavePolynomial)
    (hV : bogoliubovVectorField V = 0) :
    wheelerDeWittWithPotential m V (bogoliubovVectorField ψ) =
      bogoliubovVectorField (wheelerDeWittWithPotential m V ψ) := by
  unfold wheelerDeWittWithPotential
  rw [freeWheelerDeWitt_commutes_bogoliubov]
  unfold bogoliubovVectorField
  simp only [pderiv_sub]
  have hK_V_psi :
      X 2 * pderiv 0 (V * ψ) + X 3 * pderiv 1 (V * ψ) + X 0 * pderiv 2 (V * ψ) + X 1 * pderiv 3 (V * ψ) =
      (X 2 * pderiv 0 V + X 3 * pderiv 1 V + X 0 * pderiv 2 V + X 1 * pderiv 3 V) * ψ +
      V * (X 2 * pderiv 0 ψ + X 3 * pderiv 1 ψ + X 0 * pderiv 2 ψ + X 1 * pderiv 3 ψ) := by
    unfold pderiv
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
    ring
  have hK_V_zero : X 2 * pderiv 0 V + X 3 * pderiv 1 V + X 0 * pderiv 2 V + X 1 * pderiv 3 V = 0 := hV
  calc
    X 2 * pderiv 0 (freeWheelerDeWitt m ψ) + X 3 * pderiv 1 (freeWheelerDeWitt m ψ) +
    X 0 * pderiv 2 (freeWheelerDeWitt m ψ) + X 1 * pderiv 3 (freeWheelerDeWitt m ψ) -
    V * (X 2 * pderiv 0 ψ + X 3 * pderiv 1 ψ + X 0 * pderiv 2 ψ + X 1 * pderiv 3 ψ)
      = (X 2 * pderiv 0 (freeWheelerDeWitt m ψ) + X 3 * pderiv 1 (freeWheelerDeWitt m ψ) +
         X 0 * pderiv 2 (freeWheelerDeWitt m ψ) + X 1 * pderiv 3 (freeWheelerDeWitt m ψ)) -
        (0 * ψ + V * (X 2 * pderiv 0 ψ + X 3 * pderiv 1 ψ + X 0 * pderiv 2 ψ + X 1 * pderiv 3 ψ)) := by ring
    _ = (X 2 * pderiv 0 (freeWheelerDeWitt m ψ) + X 3 * pderiv 1 (freeWheelerDeWitt m ψ) +
         X 0 * pderiv 2 (freeWheelerDeWitt m ψ) + X 1 * pderiv 3 (freeWheelerDeWitt m ψ)) -
        ((X 2 * pderiv 0 V + X 3 * pderiv 1 V + X 0 * pderiv 2 V + X 1 * pderiv 3 V) * ψ +
         V * (X 2 * pderiv 0 ψ + X 3 * pderiv 1 ψ + X 0 * pderiv 2 ψ + X 1 * pderiv 3 ψ)) := by rw [←hK_V_zero]
    _ = (X 2 * pderiv 0 (freeWheelerDeWitt m ψ) + X 3 * pderiv 1 (freeWheelerDeWitt m ψ) +
         X 0 * pderiv 2 (freeWheelerDeWitt m ψ) + X 1 * pderiv 3 (freeWheelerDeWitt m ψ)) -
        (X 2 * pderiv 0 (V * ψ) + X 3 * pderiv 1 (V * ψ) + X 0 * pderiv 2 (V * ψ) + X 1 * pderiv 3 (V * ψ)) := by rw [←hK_V_psi]
    _ = X 2 * (pderiv 0 (freeWheelerDeWitt m ψ) - pderiv 0 (V * ψ)) +
        X 3 * (pderiv 1 (freeWheelerDeWitt m ψ) - pderiv 1 (V * ψ)) +
        X 0 * (pderiv 2 (freeWheelerDeWitt m ψ) - pderiv 2 (V * ψ)) +
        X 1 * (pderiv 3 (freeWheelerDeWitt m ψ) - pderiv 3 (V * ψ)) := by ring

end SplitQuaternionWheelerDeWitt
