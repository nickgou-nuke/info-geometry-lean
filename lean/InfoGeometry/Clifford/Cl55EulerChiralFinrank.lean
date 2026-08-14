import InfoGeometry.Clifford.Cl55OddChiralityExchange
import InfoGeometry.Clifford.Cl55SpinorDimensionReadout

namespace InfoGeometry.Clifford.Cl55SpinorChirality

open InfoGeometry.Clifford.SpinorRep

noncomputable section

abbrev EulerSpinor := SpinorSpace 5

def eulerPlusMap : EulerSpinor →ₗ[ℝ] EulerSpinor :=
  cl55EulerProjectorPlus.mulVecLin

def eulerMinusMap : EulerSpinor →ₗ[ℝ] EulerSpinor :=
  cl55EulerProjectorMinus.mulVecLin

def r0Map : EulerSpinor →ₗ[ℝ] EulerSpinor :=
  cl55Atom.r0.mulVecLin

def eulerPlusRange : Submodule ℝ EulerSpinor :=
  LinearMap.range eulerPlusMap

def eulerMinusRange : Submodule ℝ EulerSpinor :=
  LinearMap.range eulerMinusMap

@[simp] theorem eulerPlusMap_apply (w : EulerSpinor) :
    eulerPlusMap w = matrixApply cl55EulerProjectorPlus w :=
  rfl

@[simp] theorem eulerMinusMap_apply (w : EulerSpinor) :
    eulerMinusMap w = matrixApply cl55EulerProjectorMinus w :=
  rfl

@[simp] theorem r0Map_apply (w : EulerSpinor) :
    r0Map w = matrixApply cl55Atom.r0 w :=
  rfl

theorem eulerProjectors_orthogonal :
    cl55EulerProjectorPlus * cl55EulerProjectorMinus = 0 := by
  rw [cl55EulerProjectorPlus, cl55EulerProjectorMinus, smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [add_mul, mul_sub, one_mul, mul_one, cl55ChiralityOperator_sq]
  module

theorem r0Map_sq (w : EulerSpinor) : r0Map (r0Map w) = w := by
  change matrixApply cl55Atom.r0 (matrixApply cl55Atom.r0 w) = w
  rw [← matrixApply_mul, cl55Atom.r0_sq, matrixApply_one]

theorem euler_projector_decomposition (w : EulerSpinor) :
    w = eulerPlusMap w + eulerMinusMap w := by
  calc
    w = matrixApply (1 : SpinorMatrix 5) w := (matrixApply_one w).symm
    _ = matrixApply
        (cl55EulerProjectorPlus + cl55EulerProjectorMinus) w := by
      have hproj : cl55EulerProjectorPlus + cl55EulerProjectorMinus =
          (1 : SpinorMatrix 5) := by
        rw [cl55EulerProjectorPlus, cl55EulerProjectorMinus]
        module
      rw [hproj]
    _ = eulerPlusMap w + eulerMinusMap w := by
      exact matrixApply_add cl55EulerProjectorPlus
        cl55EulerProjectorMinus w

theorem r0Map_mem_eulerMinusRange (w : EulerSpinor)
    (hw : w ∈ eulerPlusRange) : r0Map w ∈ eulerMinusRange := by
  rcases hw with ⟨u, rfl⟩
  refine ⟨r0Map (eulerPlusMap u), ?_⟩
  exact cl55_r0_maps_euler_plus_to_minus u

theorem r0Map_mem_eulerPlusRange (w : EulerSpinor)
    (hw : w ∈ eulerMinusRange) : r0Map w ∈ eulerPlusRange := by
  rcases hw with ⟨u, rfl⟩
  refine ⟨r0Map (eulerMinusMap u), ?_⟩
  exact cl55_r0_maps_euler_minus_to_plus u

def r0PlusToMinus : eulerPlusRange →ₗ[ℝ] eulerMinusRange where
  toFun w := ⟨r0Map w, r0Map_mem_eulerMinusRange w w.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact r0Map.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact r0Map.map_smul c x

def r0MinusToPlus : eulerMinusRange →ₗ[ℝ] eulerPlusRange where
  toFun w := ⟨r0Map w, r0Map_mem_eulerPlusRange w w.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact r0Map.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact r0Map.map_smul c x

theorem r0PlusToMinus_bijective : Function.Bijective r0PlusToMinus := by
  constructor
  · intro x y h
    apply Subtype.ext
    have h' := congrArg
      (fun z : eulerMinusRange => r0Map (z : EulerSpinor)) h
    change r0Map (r0Map (x : EulerSpinor)) =
      r0Map (r0Map (y : EulerSpinor)) at h'
    exact (r0Map_sq x).symm.trans (h'.trans (r0Map_sq y))
  · intro y
    refine ⟨r0MinusToPlus y, ?_⟩
    apply Subtype.ext
    change r0Map (r0Map (y : EulerSpinor)) = y
    exact r0Map_sq (y : EulerSpinor)

noncomputable def r0PlusToMinusEquiv :
    eulerPlusRange ≃ₗ[ℝ] eulerMinusRange :=
  LinearEquiv.ofBijective r0PlusToMinus r0PlusToMinus_bijective

theorem euler_chiral_ranges_finrank_eq :
    Module.finrank ℝ eulerPlusRange =
      Module.finrank ℝ eulerMinusRange :=
  r0PlusToMinusEquiv.finrank_eq

theorem euler_chiral_ranges_sup :
    eulerPlusRange ⊔ eulerMinusRange = ⊤ := by
  apply top_unique
  intro w hw
  rw [euler_projector_decomposition w]
  have hp : eulerPlusMap w ∈ eulerPlusRange ⊔ eulerMinusRange :=
    (le_sup_left : eulerPlusRange ≤ eulerPlusRange ⊔ eulerMinusRange)
      (LinearMap.mem_range_self _ w)
  have hm : eulerMinusMap w ∈ eulerPlusRange ⊔ eulerMinusRange :=
    (le_sup_right : eulerMinusRange ≤ eulerPlusRange ⊔ eulerMinusRange)
      (LinearMap.mem_range_self _ w)
  exact add_mem hp hm

theorem euler_chiral_ranges_inf :
    eulerPlusRange ⊓ eulerMinusRange = ⊥ := by
  apply bot_unique
  rintro w ⟨hwPlus, hwMinus⟩
  rcases hwPlus with ⟨u, hu⟩
  rcases hwMinus with ⟨v, hv⟩
  have hfixed : eulerPlusMap w = w := by
    calc
      eulerPlusMap w = eulerPlusMap (eulerPlusMap u) := by rw [hu]
      _ = w := by
        change matrixApply cl55EulerProjectorPlus
          (matrixApply cl55EulerProjectorPlus u) = w
        rw [← matrixApply_mul, cl55EulerProjectorPlus_sq]
        exact hu
  have hzero : eulerPlusMap w = 0 := by
    rw [← hv]
    change matrixApply cl55EulerProjectorPlus
      (matrixApply cl55EulerProjectorMinus v) = 0
    rw [← matrixApply_mul, eulerProjectors_orthogonal]
    ext i
    simp [matrixApply]
  rw [hfixed] at hzero
  simpa using hzero

theorem euler_chiral_ranges_finrank_add :
    Module.finrank ℝ eulerPlusRange +
        Module.finrank ℝ eulerMinusRange = 32 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    eulerPlusRange eulerMinusRange
  rw [euler_chiral_ranges_sup, euler_chiral_ranges_inf] at h
  simpa [finrank_top, finrank_bot, spinorSpace_five_finrank] using h.symm

theorem euler_chiral_ranges_finrank_plus :
    Module.finrank ℝ eulerPlusRange = 16 := by
  have hsum := euler_chiral_ranges_finrank_add
  have heq := euler_chiral_ranges_finrank_eq
  omega

theorem euler_chiral_ranges_finrank_minus :
    Module.finrank ℝ eulerMinusRange = 16 := by
  have hsum := euler_chiral_ranges_finrank_add
  have heq := euler_chiral_ranges_finrank_eq
  omega

end

end InfoGeometry.Clifford.Cl55SpinorChirality
