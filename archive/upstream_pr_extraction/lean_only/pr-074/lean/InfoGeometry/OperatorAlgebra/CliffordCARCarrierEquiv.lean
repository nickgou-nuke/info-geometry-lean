import InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.SpinorRep

noncomputable section

open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.SpinorRep

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

abbrev FlatCAR4 := SplitModule 4
abbrev RecursiveCAR4 := Carrier 4

def flatToRecursive : FlatCAR4 → RecursiveCAR4 := fun v =>
  ((v (Sum.inl 0), v (Sum.inr 0)),
    ((v (Sum.inl 1), v (Sum.inr 1)),
      ((v (Sum.inl 2), v (Sum.inr 2)),
        ((v (Sum.inl 3), v (Sum.inr 3)), (0 : Carrier 0)))))

def recursiveToFlat : RecursiveCAR4 → FlatCAR4 := fun v => fun i =>
  match i with
  | Sum.inl 0 => v.1.1
  | Sum.inr 0 => v.1.2
  | Sum.inl 1 => v.2.1.1
  | Sum.inr 1 => v.2.1.2
  | Sum.inl 2 => v.2.2.1.1
  | Sum.inr 2 => v.2.2.1.2
  | Sum.inl 3 => v.2.2.2.1.1
  | Sum.inr 3 => v.2.2.2.1.2

def flatToRecursiveLinear : FlatCAR4 →ₗ[ℝ] RecursiveCAR4 where
  toFun := flatToRecursive
  map_add' := by
    intro v w
    apply Prod.ext
    · apply Prod.ext <;> simp [flatToRecursive]
    · apply Prod.ext
      · apply Prod.ext <;> simp [flatToRecursive]
      · apply Prod.ext
        · apply Prod.ext <;> simp [flatToRecursive]
        · apply Prod.ext
          · apply Prod.ext <;> simp [flatToRecursive]
          · exact Subsingleton.elim _ _
  map_smul' := by
    intro c v
    apply Prod.ext
    · apply Prod.ext <;> simp [flatToRecursive]
    · apply Prod.ext
      · apply Prod.ext <;> simp [flatToRecursive]
      · apply Prod.ext
        · apply Prod.ext <;> simp [flatToRecursive]
        · apply Prod.ext
          · apply Prod.ext <;> simp [flatToRecursive]
          · exact Subsingleton.elim _ _

def recursiveToFlatLinear : RecursiveCAR4 →ₗ[ℝ] FlatCAR4 where
  toFun := recursiveToFlat
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> simp [recursiveToFlat]
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> simp [recursiveToFlat]

def flatRecursiveEquiv : FlatCAR4 ≃ₗ[ℝ] RecursiveCAR4 where
  toLinearMap := flatToRecursiveLinear
  invFun := recursiveToFlat
  left_inv := by
    intro v
    funext i
    fin_cases i <;>
      simp [flatToRecursiveLinear, flatToRecursive, recursiveToFlat]
  right_inv := by
    intro v
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply Prod.ext
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · apply Prod.ext <;> rfl
        · apply Prod.ext
          · apply Prod.ext <;> rfl
          · exact Subsingleton.elim _ _

@[simp] theorem flatRecursiveEquiv_apply (v : FlatCAR4) :
    flatRecursiveEquiv v = flatToRecursive v := rfl

@[simp] theorem flatRecursiveEquiv_symm_apply (v : RecursiveCAR4) :
    flatRecursiveEquiv.symm v = recursiveToFlat v := rfl

theorem flatRecursiveEquiv_quad (v : FlatCAR4) :
    Quad 4 (flatRecursiveEquiv v) = splitQuadraticForm 4 v := by
  simp [flatRecursiveEquiv, flatToRecursiveLinear, flatToRecursive,
    splitQuadraticForm, splitWeight, Qsplit, Fin.sum_univ_four]
  ring

def flatRecursiveIsometry :
    (splitQuadraticForm 4).IsometryEquiv (Quad 4) where
  toLinearEquiv := flatRecursiveEquiv
  map_app' := flatRecursiveEquiv_quad

def flatRecursiveCliffordEquiv :
    CliffordAlgebra (splitQuadraticForm 4) ≃ₐ[ℝ] CliffordAlgebra (Quad 4) :=
  CliffordAlgebra.equivOfIsometry flatRecursiveIsometry

@[simp] theorem flatRecursiveCliffordEquiv_ι (v : FlatCAR4) :
    flatRecursiveCliffordEquiv (CliffordAlgebra.ι (splitQuadraticForm 4) v) =
      CliffordAlgebra.ι (Quad 4) (flatRecursiveEquiv v) := by
  unfold flatRecursiveCliffordEquiv CliffordAlgebra.equivOfIsometry
  change CliffordAlgebra.map flatRecursiveIsometry.toIsometry
      (CliffordAlgebra.ι (splitQuadraticForm 4) v) = _
  rw [CliffordAlgebra.map_apply_ι]
  rfl

def carRecursiveGamma : FlatCAR4 →ₗ[ℝ] SpinorMatrix 4 :=
  (recursiveGamma 4).comp flatRecursiveEquiv.toLinearMap

theorem carRecursiveGamma_sq (v : FlatCAR4) :
    carRecursiveGamma v * carRecursiveGamma v =
      algebraMap ℝ (SpinorMatrix 4) (splitQuadraticForm 4 v) := by
  rw [carRecursiveGamma, LinearMap.comp_apply, recursiveGamma_sq]
  simpa only [SplitQuad, Quad] using
    congrArg (algebraMap ℝ (SpinorMatrix 4)) (flatRecursiveEquiv_quad v)

def carSpinorRepresentation :
    CliffordAlgebra (splitQuadraticForm 4) →ₐ[ℝ] SpinorMatrix 4 :=
  (spinorRepresentation 4).comp flatRecursiveCliffordEquiv.toAlgHom

@[simp] theorem carSpinorRepresentation_ι (v : FlatCAR4) :
    carSpinorRepresentation (CliffordAlgebra.ι (splitQuadraticForm 4) v) =
      carRecursiveGamma v := by
  change spinorRepresentation 4
      (flatRecursiveCliffordEquiv (CliffordAlgebra.ι (splitQuadraticForm 4) v)) = _
  rw [flatRecursiveCliffordEquiv_ι, spinorRepresentation_ι]
  rfl

@[simp] theorem carSpinorRepresentation_p (i : Fin 4) :
    carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.p i) =
      carRecursiveGamma (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.pVec i) := by
  rw [InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.p,
    carSpinorRepresentation_ι]

@[simp] theorem carSpinorRepresentation_n (i : Fin 4) :
    carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.n i) =
      carRecursiveGamma (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.nVec i) := by
  rw [InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.n,
    carSpinorRepresentation_ι]

 theorem carSpinorRepresentation_car_identity (i j : Fin 4) :
    carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a i) *
        carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag j) +
      carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag j) *
        carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a i) =
      if i = j then (1 : SpinorMatrix 4) else 0 := by
  have h := congrArg carSpinorRepresentation
    (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.car_identity i j)
  by_cases hij : i = j
  · subst j
    simpa [map_add, map_mul] using h
  · simpa [map_add, map_mul, hij] using h

 theorem carSpinorRepresentation_a_anticomm (i j : Fin 4) :
    carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a i) *
        carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a j) +
      carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a j) *
        carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a i) = 0 := by
  have h := congrArg carSpinorRepresentation
    (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.a_a_anticomm i j)
  simpa only [map_add, map_mul, map_zero] using h

 theorem carSpinorRepresentation_aDag_anticomm (i j : Fin 4) :
    carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag i) *
        carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag j) +
      carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag j) *
        carSpinorRepresentation (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag i) = 0 := by
  have h := congrArg carSpinorRepresentation
    (InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR.aDag_aDag_anticomm i j)
  simpa only [map_add, map_mul, map_zero] using h

end InfoGeometry.OperatorAlgebra.CliffordCAR
