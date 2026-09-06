import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralRealBivectorRotor

variable {A : Type*} [Ring A] [Algebra ℝ A]

def conjugate (mirror : Units A) (X : A) : A :=
  (mirror : A) * X * (↑(mirror⁻¹) : A)

def peircePlus (K : A) : A :=
  ((2 : ℝ)⁻¹) • (1 : A) + ((2 : ℝ)⁻¹) • K

def peirceMinus (K : A) : A :=
  ((2 : ℝ)⁻¹) • (1 : A) - ((2 : ℝ)⁻¹) • K

def rotor (B : A) (θ : ℝ) : A :=
  (Real.cos (θ / 2) : ℝ) • (1 : A) +
    (Real.sin (θ / 2) : ℝ) • B

def reverseRotor (B : A) (θ : ℝ) : A :=
  (Real.cos (θ / 2) : ℝ) • (1 : A) -
    (Real.sin (θ / 2) : ℝ) • B

theorem conjugate_mul (mirror : Units A) (X Y : A) :
    conjugate mirror (X * Y) = conjugate mirror X * conjugate mirror Y := by
  simp [conjugate, mul_assoc]

theorem conjugate_add (mirror : Units A) (X Y : A) :
    conjugate mirror (X + Y) = conjugate mirror X + conjugate mirror Y := by
  simp [conjugate, add_mul, mul_add]

theorem conjugate_smul (mirror : Units A) (r : ℝ) (X : A) :
    conjugate mirror (r • X) = r • conjugate mirror X := by
  unfold conjugate
  rw [Algebra.smul_def, Algebra.smul_def]
  have hcomm :
      (mirror : A) * algebraMap ℝ A r = algebraMap ℝ A r * (mirror : A) :=
    (Algebra.commutes r (mirror : A)).symm
  calc
    (mirror : A) * (algebraMap ℝ A r * X) * (↑(mirror⁻¹) : A) =
        ((mirror : A) * algebraMap ℝ A r) * X * (↑(mirror⁻¹) : A) := by
          simp [mul_assoc]
    _ = (algebraMap ℝ A r * (mirror : A)) * X * (↑(mirror⁻¹) : A) := by
          rw [hcomm]
    _ = algebraMap ℝ A r * ((mirror : A) * X) * (↑(mirror⁻¹) : A) := by
          simp [mul_assoc]
    _ = algebraMap ℝ A r * ((mirror : A) * X * (↑(mirror⁻¹) : A)) := by
          simp [mul_assoc]

theorem conjugate_neg (mirror : Units A) (X : A) :
    conjugate mirror (-X) = -conjugate mirror X := by
  simp [conjugate]

theorem conjugate_sub (mirror : Units A) (X Y : A) :
    conjugate mirror (X - Y) = conjugate mirror X - conjugate mirror Y := by
  rw [sub_eq_add_neg, conjugate_add, conjugate_neg]
  exact (sub_eq_add_neg _ _).symm

theorem conjugate_one (mirror : Units A) : conjugate mirror (1 : A) = 1 := by
  simp [conjugate, mul_assoc]

theorem conjugate_splitClock (mirror : Units A) (K : A)
    (hK : conjugate mirror K = -K) :
    conjugate mirror K = -K := hK

theorem conjugate_circularBivector (mirror : Units A) (B : A)
    (hB : conjugate mirror B = -B) :
    conjugate mirror B = -B := hB

theorem conjugate_peircePlus (mirror : Units A) (K : A)
    (hK : conjugate mirror K = -K) :
    conjugate mirror (peircePlus K) = peirceMinus K := by
  unfold peircePlus peirceMinus
  rw [conjugate_add, conjugate_smul, conjugate_smul,
    conjugate_one, hK]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem conjugate_peirceMinus (mirror : Units A) (K : A)
    (hK : conjugate mirror K = -K) :
    conjugate mirror (peirceMinus K) = peircePlus K := by
  unfold peircePlus peirceMinus
  rw [conjugate_sub, conjugate_smul, conjugate_smul,
    conjugate_one, hK]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem conjugate_retained_word (mirror : Units A) (X Y : A) :
    conjugate mirror (X * Y) = conjugate mirror X * conjugate mirror Y :=
  conjugate_mul mirror X Y

theorem conjugate_commutator (mirror : Units A) (X Y : A) :
    conjugate mirror (X * Y - Y * X) =
      conjugate mirror X * conjugate mirror Y -
        conjugate mirror Y * conjugate mirror X := by
  rw [conjugate_sub, conjugate_mul, conjugate_mul]

theorem conjugate_anticommutator (mirror : Units A) (X Y : A) :
    conjugate mirror (X * Y + Y * X) =
      conjugate mirror X * conjugate mirror Y +
        conjugate mirror Y * conjugate mirror X := by
  rw [conjugate_add, conjugate_mul, conjugate_mul]

theorem conjugate_rotor (mirror : Units A) (B : A) (θ : ℝ)
    (hB : conjugate mirror B = -B) :
    conjugate mirror (rotor B θ) = reverseRotor B θ := by
  unfold rotor reverseRotor
  rw [conjugate_add, conjugate_smul, conjugate_smul,
    conjugate_one, hB]
  simp [sub_eq_add_neg]


end InfoGeometry.OperatorAlgebra.ChiralRealBivectorRotor
