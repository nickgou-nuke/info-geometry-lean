import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11TensorTower
import Mathlib.Tactic

/-!
# The geometric compass inside `Cl(1,1)`

This owner separates two valid, but different, local frames already present in
the repository.

* The standard Clifford frame uses a square-plus spatial generator `eₛ`, a
  square-minus temporal generator `eₜ`, and the volume element `ω = eₛeₜ`.
  Its null directions are `eₛ ± eₜ`, and its canonical chiral projectors are
  `(1 ± ω) / 2`.
* `Cl11TensorTower` uses the frame `γ₀ = J1`, `γ₁ = Eminus`.  In the standard
  frame this is `γ₀ = ω`, `γ₁ = eₜ`, hence `γ₀γ₁ = -eₛ`.  Its Witt creation and
  annihilation operators are the normalized tensor-frame null directions.

The distinction is structural: spatial corner projectors `(1 ± eₛ) / 2` are
not the standard chiral projectors `(1 ± ω) / 2`.  The tensor convention turns
its own chiral projectors into the standard spatial projectors, with the signs
interchanged.
-/

noncomputable section

open scoped Matrix

namespace InfoGeometry.Clifford.Cl11GeometricCompass

open InfoGeometry.Clifford.Cl11Matrix

abbrev Cl11 := CliffordAlgebra q11
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-! ## Standard geometric frame -/

/-- Standard square-plus spatial generator. -/
def spaceGenerator : Cl11 :=
  CliffordAlgebra.ι q11 (1, 0)

/-- Standard square-minus temporal generator. -/
def timeGenerator : Cl11 :=
  CliffordAlgebra.ι q11 (0, 1)

/-- Standard oriented volume element `ω = eₛeₜ`. -/
def volumeElement : Cl11 :=
  spaceGenerator * timeGenerator

@[simp]
theorem cl11EquivMat_spaceGenerator :
    cl11EquivMat spaceGenerator = Eplus := by
  change cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) = Eplus
  exact cl11EquivMat_iota_pos

@[simp]
theorem cl11EquivMat_timeGenerator :
    cl11EquivMat timeGenerator = Eminus := by
  change cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) = Eminus
  exact cl11EquivMat_iota_neg

@[simp]
theorem cl11EquivMat_volumeElement :
    cl11EquivMat volumeElement = J1 := by
  simp [volumeElement, Eplus_mul_Eminus]

@[simp]
theorem spaceGenerator_sq :
    spaceGenerator * spaceGenerator = (1 : Cl11) := by
  apply cl11EquivMat.injective
  simp [Eplus_sq]

@[simp]
theorem timeGenerator_sq :
    timeGenerator * timeGenerator = -(1 : Cl11) := by
  apply cl11EquivMat.injective
  simp

/-- The standard space and time generators anticommute. -/
theorem space_time_anticommute :
    spaceGenerator * timeGenerator + timeGenerator * spaceGenerator = 0 := by
  apply cl11EquivMat.injective
  simpa [spaceGenerator, timeGenerator] using
    cl11EquivMat_iota_pos_neg_anticomm

@[simp]
theorem volumeElement_sq :
    volumeElement * volumeElement = (1 : Cl11) := by
  apply cl11EquivMat.injective
  simp

/-- Spatial reflection reverses the oriented volume element. -/
theorem spaceGenerator_conjugates_volumeElement :
    spaceGenerator * volumeElement * spaceGenerator = -volumeElement := by
  apply cl11EquivMat.injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spaceGenerator, volumeElement, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The inverse temporal generator is `-eₜ`, and temporal reflection also
reverses the oriented volume element. -/
theorem timeGenerator_conjugates_volumeElement :
    timeGenerator * volumeElement * (-timeGenerator) = -volumeElement := by
  apply cl11EquivMat.injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [timeGenerator, volumeElement, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Causal vectors and null directions -/

/-- Standard grade-one vector with coordinates `(a,b)` and quadratic value
`a² - b²`. -/
def causalVector (a b : ℝ) : Cl11 :=
  a • spaceGenerator + b • timeGenerator

@[simp]
theorem cl11EquivMat_causalVector (a b : ℝ) :
    cl11EquivMat (causalVector a b) = gen (a, b) := by
  simp [causalVector, gen]

/-- Exact Clifford square of a causal vector. -/
theorem causalVector_sq (a b : ℝ) :
    causalVector a b * causalVector a b =
      (a ^ 2 - b ^ 2) • (1 : Cl11) := by
  apply cl11EquivMat.injective
  simpa [q11_apply] using (gen_sq (a, b))

/-- Future/right null direction in the standard frame. -/
def nullPlus : Cl11 :=
  causalVector 1 1

/-- Past/left null direction in the standard frame. -/
def nullMinus : Cl11 :=
  causalVector 1 (-1)

@[simp]
theorem nullPlus_sq : nullPlus * nullPlus = 0 := by
  change causalVector 1 1 * causalVector 1 1 = 0
  rw [causalVector_sq]
  norm_num

@[simp]
theorem nullMinus_sq : nullMinus * nullMinus = 0 := by
  change causalVector 1 (-1) * causalVector 1 (-1) = 0
  rw [causalVector_sq]
  norm_num

@[simp]
theorem cl11EquivMat_nullPlus :
    cl11EquivMat nullPlus = !![(1 : ℝ), 1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nullPlus, causalVector, spaceGenerator, timeGenerator,
      Eplus, Eminus, Matrix.smul_apply, Matrix.add_apply]

@[simp]
theorem cl11EquivMat_nullMinus :
    cl11EquivMat nullMinus = !![(1 : ℝ), -1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nullMinus, causalVector, spaceGenerator, timeGenerator,
      Eplus, Eminus, Matrix.smul_apply, Matrix.add_apply]

/-! ## Chiral projectors versus spatial corner projectors -/

/-- Positive standard chirality projector `(1 + ω)/2`. -/
def chiralProjectorPlus : Cl11 :=
  (1 / 2 : ℝ) • ((1 : Cl11) + volumeElement)

/-- Negative standard chirality projector `(1 - ω)/2`. -/
def chiralProjectorMinus : Cl11 :=
  (1 / 2 : ℝ) • ((1 : Cl11) - volumeElement)

/-- Positive spatial corner projector `(1 + eₛ)/2`. -/
def spatialProjectorPlus : Cl11 :=
  (1 / 2 : ℝ) • ((1 : Cl11) + spaceGenerator)

/-- Negative spatial corner projector `(1 - eₛ)/2`. -/
def spatialProjectorMinus : Cl11 :=
  (1 / 2 : ℝ) • ((1 : Cl11) - spaceGenerator)

@[simp]
theorem cl11EquivMat_chiralProjectorPlus :
    cl11EquivMat chiralProjectorPlus =
      !![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2] := by
  calc
    cl11EquivMat chiralProjectorPlus =
        (1 / 2 : ℝ) • ((1 : Mat2) + J1) := by
      simp [chiralProjectorPlus]
    _ = !![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [J1, Matrix.smul_apply, Matrix.add_apply]

@[simp]
theorem cl11EquivMat_chiralProjectorMinus :
    cl11EquivMat chiralProjectorMinus =
      !![(1 / 2 : ℝ), -1 / 2; -1 / 2, 1 / 2] := by
  calc
    cl11EquivMat chiralProjectorMinus =
        (1 / 2 : ℝ) • ((1 : Mat2) - J1) := by
      simp [chiralProjectorMinus]
    _ = !![(1 / 2 : ℝ), -1 / 2; -1 / 2, 1 / 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [J1, Matrix.smul_apply, Matrix.sub_apply]

@[simp]
theorem cl11EquivMat_spatialProjectorPlus :
    cl11EquivMat spatialProjectorPlus =
      !![(1 : ℝ), 0; 0, 0] := by
  calc
    cl11EquivMat spatialProjectorPlus =
        (1 / 2 : ℝ) • ((1 : Mat2) + Eplus) := by
      simp [spatialProjectorPlus]
    _ = !![(1 : ℝ), 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Eplus, Matrix.smul_apply, Matrix.add_apply]

@[simp]
theorem cl11EquivMat_spatialProjectorMinus :
    cl11EquivMat spatialProjectorMinus =
      !![(0 : ℝ), 0; 0, 1] := by
  calc
    cl11EquivMat spatialProjectorMinus =
        (1 / 2 : ℝ) • ((1 : Mat2) - Eplus) := by
      simp [spatialProjectorMinus]
    _ = !![(0 : ℝ), 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Eplus, Matrix.smul_apply, Matrix.sub_apply]

@[simp]
theorem chiralProjectorPlus_sq :
    chiralProjectorPlus * chiralProjectorPlus = chiralProjectorPlus := by
  apply cl11EquivMat.injective
  simp only [map_mul, cl11EquivMat_chiralProjectorPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem chiralProjectorMinus_sq :
    chiralProjectorMinus * chiralProjectorMinus = chiralProjectorMinus := by
  apply cl11EquivMat.injective
  simp only [map_mul, cl11EquivMat_chiralProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem chiralProjectorPlus_mul_minus :
    chiralProjectorPlus * chiralProjectorMinus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_chiralProjectorPlus,
    cl11EquivMat_chiralProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem chiralProjectorMinus_mul_plus :
    chiralProjectorMinus * chiralProjectorPlus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_chiralProjectorPlus,
    cl11EquivMat_chiralProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem chiralProjectorPlus_add_minus :
    chiralProjectorPlus + chiralProjectorMinus = (1 : Cl11) := by
  apply cl11EquivMat.injective
  simp only [map_add, map_one, cl11EquivMat_chiralProjectorPlus,
    cl11EquivMat_chiralProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

@[simp]
theorem spatialProjectorPlus_sq :
    spatialProjectorPlus * spatialProjectorPlus = spatialProjectorPlus := by
  apply cl11EquivMat.injective
  simp only [map_mul, cl11EquivMat_spatialProjectorPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem spatialProjectorMinus_sq :
    spatialProjectorMinus * spatialProjectorMinus = spatialProjectorMinus := by
  apply cl11EquivMat.injective
  simp only [map_mul, cl11EquivMat_spatialProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem spatialProjectorPlus_mul_minus :
    spatialProjectorPlus * spatialProjectorMinus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_spatialProjectorPlus,
    cl11EquivMat_spatialProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem spatialProjectorMinus_mul_plus :
    spatialProjectorMinus * spatialProjectorPlus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_spatialProjectorPlus,
    cl11EquivMat_spatialProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem spatialProjectorPlus_add_minus :
    spatialProjectorPlus + spatialProjectorMinus = (1 : Cl11) := by
  apply cl11EquivMat.injective
  simp only [map_add, map_one, cl11EquivMat_spatialProjectorPlus,
    cl11EquivMat_spatialProjectorMinus]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- Standard chirality is not the same projector as the selected spatial
corner polarization. -/
theorem chiralProjectorPlus_ne_spatialProjectorPlus :
    chiralProjectorPlus ≠ spatialProjectorPlus := by
  intro h
  have hm := congrArg cl11EquivMat h
  rw [cl11EquivMat_chiralProjectorPlus,
    cl11EquivMat_spatialProjectorPlus] at hm
  have h01 := congrArg (fun M : Mat2 => M 0 1) hm
  norm_num at h01

/-! ## Bridge to the tensor/Witt convention -/

/-- `γ₀` of `Cl11TensorTower`, transported to the native Clifford carrier. -/
def tensorGammaZero : Cl11 :=
  cl11EquivMat.symm InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base

/-- `γ₁` of `Cl11TensorTower`, transported to the native Clifford carrier. -/
def tensorGammaOne : Cl11 :=
  cl11EquivMat.symm InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base

/-- Tensor-frame volume element `γ₀γ₁`. -/
def tensorVolumeElement : Cl11 :=
  tensorGammaZero * tensorGammaOne

@[simp]
theorem cl11EquivMat_tensorGammaZero :
    cl11EquivMat tensorGammaZero =
      InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base :=
  cl11EquivMat.apply_symm_apply _

@[simp]
theorem cl11EquivMat_tensorGammaOne :
    cl11EquivMat tensorGammaOne =
      InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base :=
  cl11EquivMat.apply_symm_apply _

/-- The tensor-frame square-plus generator is the standard volume element. -/
theorem tensorGammaZero_eq_volumeElement :
    tensorGammaZero = volumeElement := by
  apply cl11EquivMat.injective
  simp [InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base]

/-- Both repository frames use the same square-minus temporal generator. -/
theorem tensorGammaOne_eq_timeGenerator :
    tensorGammaOne = timeGenerator := by
  apply cl11EquivMat.injective
  simp [InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base]

/-- The tensor-frame volume element is the negative standard spatial
generator. -/
theorem tensorVolumeElement_eq_neg_spaceGenerator :
    tensorVolumeElement = -spaceGenerator := by
  simp [tensorVolumeElement, tensorGammaZero_eq_volumeElement,
    tensorGammaOne_eq_timeGenerator, volumeElement, mul_assoc]

/-- Matrix-level convention bridge: `γ₀γ₁ = -Eplus`. -/
theorem tensorGammaVolume_eq_neg_standardSpaceMatrix :
    InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base = -Eplus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Cl11TensorTower.gamma_chiral_base,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base,
      J1, Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Positive tensor-frame null direction. -/
def tensorNullPlus : Cl11 :=
  tensorGammaZero + tensorGammaOne

/-- Negative tensor-frame null direction. -/
def tensorNullMinus : Cl11 :=
  tensorGammaZero - tensorGammaOne

@[simp]
theorem cl11EquivMat_tensorNullPlus :
    cl11EquivMat tensorNullPlus =
      InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base +
        InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base := by
  simp [tensorNullPlus]

@[simp]
theorem cl11EquivMat_tensorNullMinus :
    cl11EquivMat tensorNullMinus =
      InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base -
        InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base := by
  simp [tensorNullMinus]

@[simp]
theorem tensorNullPlus_sq : tensorNullPlus * tensorNullPlus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_tensorNullPlus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base,
      J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply]

@[simp]
theorem tensorNullMinus_sq : tensorNullMinus * tensorNullMinus = 0 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_zero, cl11EquivMat_tensorNullMinus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base,
      InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base,
      J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply]

/-- Native Clifford lift of the tensor/Witt creation atom. -/
def tensorWittCreation : Cl11 :=
  (1 / 2 : ℝ) • tensorNullPlus

/-- Native Clifford lift of the tensor/Witt annihilation atom. -/
def tensorWittAnnihilation : Cl11 :=
  (1 / 2 : ℝ) • tensorNullMinus

@[simp]
theorem cl11EquivMat_tensorWittCreation :
    cl11EquivMat tensorWittCreation =
      InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase := by
  calc
    cl11EquivMat tensorWittCreation =
        (1 / 2 : ℝ) •
          (InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base +
            InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base) := by
      simp [tensorWittCreation]
    _ = InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase :=
      InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase_eq_half_gamma_sum.symm

@[simp]
theorem cl11EquivMat_tensorWittAnnihilation :
    cl11EquivMat tensorWittAnnihilation =
      InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase := by
  calc
    cl11EquivMat tensorWittAnnihilation =
        (1 / 2 : ℝ) •
          (InfoGeometry.Clifford.Cl11TensorTower.gamma_0_base -
            InfoGeometry.Clifford.Cl11TensorTower.gamma_1_base) := by
      simp [tensorWittAnnihilation]
    _ = InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase :=
      InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase_eq_half_gamma_sub.symm

@[simp]
theorem tensorWittCreation_sq :
    tensorWittCreation * tensorWittCreation = 0 := by
  apply cl11EquivMat.injective
  simpa using InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase_sq

@[simp]
theorem tensorWittAnnihilation_sq :
    tensorWittAnnihilation * tensorWittAnnihilation = 0 := by
  apply cl11EquivMat.injective
  simpa using InfoGeometry.Clifford.Cl11TensorTower.wittAnnihilationBase_sq

/-- The tensor-frame Witt atoms satisfy the one-site CAR relation. -/
theorem tensorWitt_anticommute :
    tensorWittCreation * tensorWittAnnihilation +
      tensorWittAnnihilation * tensorWittCreation = (1 : Cl11) := by
  apply cl11EquivMat.injective
  have h := InfoGeometry.Clifford.Cl11TensorTower.realEncodedWitt_anticomm
  rw [InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittCreationBase_eq,
    InfoGeometry.Clifford.Cl11TensorTower.realEncodedWittAnnihilationBase_eq] at h
  simpa using h

/-- Positive chirality projector in the tensor frame. -/
def tensorChiralProjectorPlus : Cl11 :=
  (1 / 2 : ℝ) • ((1 : Cl11) + tensorVolumeElement)

/-- Negative chirality projector in the tensor frame. -/
def tensorChiralProjectorMinus : Cl11 :=
  (1 / 2 : ℝ) • ((1 : Cl11) - tensorVolumeElement)

/-- Tensor-positive chirality is standard negative spatial polarization. -/
theorem tensorChiralProjectorPlus_eq_spatialProjectorMinus :
    tensorChiralProjectorPlus = spatialProjectorMinus := by
  simp [tensorChiralProjectorPlus, spatialProjectorMinus,
    tensorVolumeElement_eq_neg_spaceGenerator, sub_eq_add_neg]

/-- Tensor-negative chirality is standard positive spatial polarization. -/
theorem tensorChiralProjectorMinus_eq_spatialProjectorPlus :
    tensorChiralProjectorMinus = spatialProjectorPlus := by
  simp [tensorChiralProjectorMinus, spatialProjectorPlus,
    tensorVolumeElement_eq_neg_spaceGenerator, sub_eq_add_neg]

end InfoGeometry.Clifford.Cl11GeometricCompass