import InfoGeometry.OperatorAlgebra.FiniteParityChainHomotopy

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

variable {Vplus Vminus Wplus Wminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]
variable [AddCommGroup Wplus] [Module ℝ Wplus]
variable [AddCommGroup Wminus] [Module ℝ Wminus]

namespace Hom

def zero
    (C : TwoPeriodicComplex Vplus Vminus)
    (D : TwoPeriodicComplex Wplus Wminus) :
    Hom C D where
  positive := 0
  negative := 0
  commutes_dPlus := by simp
  commutes_dMinus := by simp

@[simp]
theorem zero_positiveCohomologyMap
    (C : TwoPeriodicComplex Vplus Vminus)
    (D : TwoPeriodicComplex Wplus Wminus) :
    (zero C D).positiveCohomologyMap = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.positiveBoundaries.mkQ_surjective q
  rfl

@[simp]
theorem zero_negativeCohomologyMap
    (C : TwoPeriodicComplex Vplus Vminus)
    (D : TwoPeriodicComplex Wplus Wminus) :
    (zero C D).negativeCohomologyMap = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := C.negativeBoundaries.mkQ_surjective q
  rfl

def NullHomotopic
    {C : TwoPeriodicComplex Vplus Vminus}
    {D : TwoPeriodicComplex Wplus Wminus}
    (f : Hom C D) : Prop :=
  Nonempty (Homotopy f (zero C D))

namespace NullHomotopic

variable {C : TwoPeriodicComplex Vplus Vminus}
variable {D : TwoPeriodicComplex Wplus Wminus}
variable {f : Hom C D}

theorem positiveCohomologyMap_eq_zero
    (hf : f.NullHomotopic) :
    f.positiveCohomologyMap = 0 := by
  rcases hf with ⟨H⟩
  rw [H.positiveCohomologyMap_eq, zero_positiveCohomologyMap]

theorem negativeCohomologyMap_eq_zero
    (hf : f.NullHomotopic) :
    f.negativeCohomologyMap = 0 := by
  rcases hf with ⟨H⟩
  rw [H.negativeCohomologyMap_eq, zero_negativeCohomologyMap]

end NullHomotopic

end Hom

def Contractible (C : TwoPeriodicComplex Vplus Vminus) : Prop :=
  Nonempty (Homotopy (Hom.id C) (Hom.zero C C))

namespace Contractible

variable {C : TwoPeriodicComplex Vplus Vminus}

theorem positiveCohomology_subsingleton
    (hC : Contractible C) :
    Subsingleton C.PositiveCohomology := by
  rcases hC with ⟨H⟩
  have hmap : (LinearMap.id : C.PositiveCohomology →ₗ[ℝ]
      C.PositiveCohomology) = 0 := by
    rw [← Hom.positiveCohomologyMap_id C,
      H.positiveCohomologyMap_eq, Hom.zero_positiveCohomologyMap]
  constructor
  intro x y
  have hx : x = 0 := by
    have h := LinearMap.congr_fun hmap x
    simpa using h
  have hy : y = 0 := by
    have h := LinearMap.congr_fun hmap y
    simpa using h
  exact hx.trans hy.symm

theorem negativeCohomology_subsingleton
    (hC : Contractible C) :
    Subsingleton C.NegativeCohomology := by
  rcases hC with ⟨H⟩
  have hmap : (LinearMap.id : C.NegativeCohomology →ₗ[ℝ]
      C.NegativeCohomology) = 0 := by
    rw [← Hom.negativeCohomologyMap_id C,
      H.negativeCohomologyMap_eq, Hom.zero_negativeCohomologyMap]
  constructor
  intro x y
  have hx : x = 0 := by
    have h := LinearMap.congr_fun hmap x
    simpa using h
  have hy : y = 0 := by
    have h := LinearMap.congr_fun hmap y
    simpa using h
  exact hx.trans hy.symm

theorem positiveCohomology_finrank_zero
    (hC : Contractible C) :
    Module.finrank ℝ C.PositiveCohomology = 0 := by
  letI : Subsingleton C.PositiveCohomology :=
    hC.positiveCohomology_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem negativeCohomology_finrank_zero
    (hC : Contractible C) :
    Module.finrank ℝ C.NegativeCohomology = 0 := by
  letI : Subsingleton C.NegativeCohomology :=
    hC.negativeCohomology_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem finrank_positive_eq_negative
    (hC : Contractible C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    Module.finrank ℝ Vplus = Module.finrank ℝ Vminus := by
  have hEuler := C.eulerPoincare
  rw [hC.positiveCohomology_finrank_zero,
    hC.negativeCohomology_finrank_zero] at hEuler
  omega

theorem eulerCharacteristic_zero
    (hC : Contractible C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    (Module.finrank ℝ Vplus : ℤ) -
      Module.finrank ℝ Vminus = 0 := by
  rw [hC.finrank_positive_eq_negative]
  simp

end Contractible

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
