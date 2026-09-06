import InfoGeometry.Clifford.Cl11TensorTower

/-!
# The native geometric compass for the `Cl(1,1)` tensor atom

This owner separates the two existing local decompositions:

* the grade-one split generators and their null directions;
* the volume-element projectors used for Clifford chirality.

It does not identify the volume projectors with the sheet projectors used by
another convention, and it introduces no new Clifford or matrix carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11GeometricCompass

open InfoGeometry.Clifford.Cl11TensorTower

abbrev spaceGenerator : Matrix (Fin 2) (Fin 2) ℝ := gamma_0_base
abbrev timeGenerator : Matrix (Fin 2) (Fin 2) ℝ := gamma_1_base

def volumeElement : Matrix (Fin 2) (Fin 2) ℝ :=
  spaceGenerator * timeGenerator

def nullPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  spaceGenerator + timeGenerator

def nullMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  spaceGenerator - timeGenerator

def chiralProjectorPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + volumeElement)

def chiralProjectorMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - volumeElement)

@[simp] theorem spaceGenerator_sq :
    spaceGenerator * spaceGenerator = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact modularReflectionBase_sq

@[simp] theorem timeGenerator_sq :
    timeGenerator * timeGenerator =
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact phaseAxisBase_sq

theorem nullPlus_sq : nullPlus * nullPlus = 0 := by
  rw [show nullPlus = (2 : ℝ) • wittCreationBase by
    rw [wittCreationBase_eq_half_gamma_sum]
    simp [nullPlus, spaceGenerator, timeGenerator]
    ]
  simp [wittCreationBase_sq]

theorem nullMinus_sq : nullMinus * nullMinus = 0 := by
  rw [show nullMinus = (2 : ℝ) • wittAnnihilationBase by
    rw [wittAnnihilationBase_eq_half_gamma_sub]
    simp [nullMinus, spaceGenerator, timeGenerator]
    ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wittAnnihilationBase, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem volumeElement_sq :
    volumeElement * volumeElement = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  change modularSignBase * modularSignBase =
    (1 : Matrix (Fin 2) (Fin 2) ℝ)
  exact modularSignBase_sq

@[simp] theorem chiralProjectors_add :
    chiralProjectorPlus + chiralProjectorMinus =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold chiralProjectorPlus chiralProjectorMinus
  module

theorem chiralProjectors_mul_zero :
    chiralProjectorPlus * chiralProjectorMinus = 0 := by
  unfold chiralProjectorPlus chiralProjectorMinus
  simp [sub_eq_add_neg, add_mul, mul_add, volumeElement_sq]
  module

theorem chiralProjectors_mul_zero' :
    chiralProjectorMinus * chiralProjectorPlus = 0 := by
  unfold chiralProjectorPlus chiralProjectorMinus
  simp [sub_eq_add_neg, add_mul, mul_add, volumeElement_sq]
  module

@[simp] theorem chiralProjectorPlus_idempotent :
    chiralProjectorPlus * chiralProjectorPlus = chiralProjectorPlus := by
  have hsum := chiralProjectors_add
  have hzero := chiralProjectors_mul_zero
  calc
    chiralProjectorPlus * chiralProjectorPlus =
        chiralProjectorPlus * (chiralProjectorPlus + chiralProjectorMinus) := by
          simp only [mul_add, hzero, add_zero]
    _ = chiralProjectorPlus * 1 := by rw [hsum]
    _ = chiralProjectorPlus := by simp

@[simp] theorem chiralProjectorMinus_idempotent :
    chiralProjectorMinus * chiralProjectorMinus = chiralProjectorMinus := by
  have hsum := chiralProjectors_add
  have hzero := chiralProjectors_mul_zero'
  calc
    chiralProjectorMinus * chiralProjectorMinus =
        chiralProjectorMinus * (chiralProjectorPlus + chiralProjectorMinus) := by
          simp only [mul_add, hzero, zero_add]
    _ = chiralProjectorMinus * 1 := by rw [hsum]
    _ = chiralProjectorMinus := by simp

theorem volumeElement_eq_gamma_chiral_base :
    volumeElement = gamma_chiral_base := rfl

theorem nullPlus_eq_two_wittCreationBase :
    nullPlus = (2 : ℝ) • wittCreationBase := by
  rw [wittCreationBase_eq_half_gamma_sum]
  simp [nullPlus, spaceGenerator, timeGenerator]

theorem nullMinus_eq_two_wittAnnihilationBase :
    nullMinus = (2 : ℝ) • wittAnnihilationBase := by
  rw [wittAnnihilationBase_eq_half_gamma_sub]
  simp [nullMinus, spaceGenerator, timeGenerator]

end InfoGeometry.Clifford.Cl11GeometricCompass
