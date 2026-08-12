import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

namespace InfoGeometry.Physics.ZornMatrixSU3

/-!
## 1. Vector Cross Product in ℝ³
-/

/-- Cross product in ℝ³ -/
def crossProduct (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3 x y

/-- Dot product in ℝ³ -/
def dotProduct (x y : Fin 3 → ℝ) : ℝ :=
  InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3 x y

def det3 (x y z : Fin 3 → ℝ) : ℝ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) -
    x 1 * (y 0 * z 2 - y 2 * z 0) +
    x 2 * (y 0 * z 1 - y 1 * z 0)

def scalarTriple (x y z : Fin 3 → ℝ) : ℝ :=
  dotProduct x (crossProduct y z)

theorem scalarTriple_eq_det3 (x y z : Fin 3 → ℝ) :
    scalarTriple x y z = det3 x y z := by
  simp [scalarTriple, det3, dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
  ring

theorem dotProduct_crossProduct_eq_det3 (x y z : Fin 3 → ℝ) :
    dotProduct x (crossProduct y z) = det3 x y z := by
  exact scalarTriple_eq_det3 x y z

theorem scalarTriple_cyclic (x y z : Fin 3 → ℝ) :
    scalarTriple x y z = scalarTriple y z x := by
  rw [scalarTriple_eq_det3, scalarTriple_eq_det3]
  simp [det3]
  ring

theorem scalarTriple_swap (x y z : Fin 3 → ℝ) :
    scalarTriple x y z = -scalarTriple x z y := by
  rw [scalarTriple_eq_det3, scalarTriple_eq_det3]
  simp [det3]
  ring

theorem scalarTriple_swap_left (x y z : Fin 3 → ℝ) :
    scalarTriple x y z = -scalarTriple y x z := by
  calc
    scalarTriple x y z = scalarTriple y z x := scalarTriple_cyclic _ _ _
    _ = -scalarTriple y x z := scalarTriple_swap _ _ _

theorem det3_cyclic (x y z : Fin 3 → ℝ) :
    det3 x y z = det3 y z x := by
  calc
    det3 x y z = scalarTriple x y z := (scalarTriple_eq_det3 _ _ _).symm
    _ = scalarTriple y z x := scalarTriple_cyclic _ _ _
    _ = det3 y z x := scalarTriple_eq_det3 _ _ _

theorem det3_swap (x y z : Fin 3 → ℝ) :
    det3 x y z = -det3 x z y := by
  calc
    det3 x y z = scalarTriple x y z := (scalarTriple_eq_det3 _ _ _).symm
    _ = -scalarTriple x z y := scalarTriple_swap _ _ _
    _ = -det3 x z y := by rw [scalarTriple_eq_det3]

theorem det3_swap_left (x y z : Fin 3 → ℝ) :
    det3 x y z = -det3 y x z := by
  calc
    det3 x y z = scalarTriple x y z := (scalarTriple_eq_det3 _ _ _).symm
    _ = -scalarTriple y x z := scalarTriple_swap_left _ _ _
    _ = -det3 y x z := by rw [scalarTriple_eq_det3]

@[simp] theorem scalarTriple_self_left (x y : Fin 3 → ℝ) :
    scalarTriple x x y = 0 := by
  rw [scalarTriple_eq_det3]
  simp [det3]
  ring

@[simp] theorem scalarTriple_self_middle (x y : Fin 3 → ℝ) :
    scalarTriple x y x = 0 := by
  rw [scalarTriple_eq_det3]
  simp [det3]
  ring

@[simp] theorem scalarTriple_self_right (x y : Fin 3 → ℝ) :
    scalarTriple x y y = 0 := by
  rw [scalarTriple_eq_det3]
  simp [det3]
  ring

@[simp] theorem det3_self_left (x y : Fin 3 → ℝ) :
    det3 x x y = 0 := by
  rw [← scalarTriple_eq_det3]
  exact scalarTriple_self_left x y

@[simp] theorem det3_self_middle (x y : Fin 3 → ℝ) :
    det3 x y x = 0 := by
  rw [← scalarTriple_eq_det3]
  exact scalarTriple_self_middle x y

@[simp] theorem det3_self_right (x y : Fin 3 → ℝ) :
    det3 x y y = 0 := by
  rw [← scalarTriple_eq_det3]
  exact scalarTriple_self_right x y

theorem dotProduct_comm (x y : Fin 3 → ℝ) :
    dotProduct x y = dotProduct y x := by
  simpa [dotProduct] using
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3_comm x y

theorem dotProduct_crossProduct_left_eq_det3 (x y z : Fin 3 → ℝ) :
    dotProduct (crossProduct x y) z = det3 x y z := by
  calc
    dotProduct (crossProduct x y) z =
        dotProduct z (crossProduct x y) := dotProduct_comm _ _
    _ = det3 z x y := dotProduct_crossProduct_eq_det3 _ _ _
    _ = det3 x y z := det3_cyclic z x y

@[simp] theorem dotProduct_zero_left (x : Fin 3 → ℝ) :
    dotProduct (fun _ : Fin 3 => 0) x = 0 := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

@[simp] theorem dotProduct_zero_right (x : Fin 3 → ℝ) :
    dotProduct x (fun _ : Fin 3 => 0) = 0 := by
  simpa [dotProduct_comm] using dotProduct_zero_left x

@[simp] theorem dotProduct_zero_zero :
    dotProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = 0 := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]

theorem dotProduct_add_left (x y z : Fin 3 → ℝ) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_add_right (x y z : Fin 3 → ℝ) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct (r • x) y = r * dotProduct x y := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

theorem dotProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    dotProduct x (r • y) = r * dotProduct x y := by
  simp [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  ring

@[simp] theorem crossProduct_zero_left (x : Fin 3 → ℝ) :
    crossProduct (fun _ : Fin 3 => 0) x = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_zero :
    crossProduct (0 : Fin 3 → ℝ) (0 : Fin 3 → ℝ) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

@[simp] theorem crossProduct_zero_right (x : Fin 3 → ℝ) :
    crossProduct x (fun _ : Fin 3 => 0) = (0 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

theorem crossProduct_add_left (x y z : Fin 3 → ℝ) :
    crossProduct (x + y) z = crossProduct x z + crossProduct y z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_add_right (x y z : Fin 3 → ℝ) :
    crossProduct x (y + z) = crossProduct x y + crossProduct x z := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_left (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct (r • x) y = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

theorem crossProduct_smul_right (r : ℝ) (x y : Fin 3 → ℝ) :
    crossProduct x (r • y) = r • crossProduct x y := by
  funext i
  fin_cases i <;>
    simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;>
    ring

noncomputable def scalarTripleMultilinear :
    MultilinearMap ℝ (fun _ : Fin 3 => (Fin 3 → ℝ)) ℝ :=
  MultilinearMap.mk' (fun v => scalarTriple (v 0) (v 1) (v 2)) (by
    intro m i x y
    fin_cases i
    · change scalarTriple (x + y) (m 1) (m 2) = _
      rw [scalarTriple, dotProduct_add_left]
      simp [Function.update, scalarTriple]
    · change scalarTriple (m 0) (x + y) (m 2) = _
      rw [scalarTriple, crossProduct_add_left, dotProduct_add_right]
      simp [Function.update, scalarTriple]
    · change scalarTriple (m 0) (m 1) (x + y) = _
      rw [scalarTriple, crossProduct_add_right, dotProduct_add_right]
      simp [Function.update, scalarTriple]) (by
    intro m i c x
    fin_cases i
    · change scalarTriple (c • x) (m 1) (m 2) = _
      rw [scalarTriple, dotProduct_smul_left]
      rfl
    · change scalarTriple (m 0) (c • x) (m 2) = _
      rw [scalarTriple, crossProduct_smul_left, dotProduct_smul_right]
      simp [Function.update, scalarTriple, smul_eq_mul]
    · change scalarTriple (m 0) (m 1) (c • x) = _
      rw [scalarTriple, crossProduct_smul_right, dotProduct_smul_right]
      simp [Function.update, scalarTriple, smul_eq_mul])

noncomputable def scalarTripleAlternatingMap :
    (Fin 3 → ℝ) [⋀^ (Fin 3)]→ₗ[ℝ] ℝ :=
  AlternatingMap.mk scalarTripleMultilinear (by
      intro v i j h hij
      fin_cases i <;> fin_cases j
      all_goals try contradiction
      · change scalarTriple (v 0) (v 1) (v 2) = 0
        have h01 : v 0 = v 1 := by simpa using h
        rw [← h01]
        exact scalarTriple_self_left (v 0) (v 2)
      · change scalarTriple (v 0) (v 1) (v 2) = 0
        have h02 : v 0 = v 2 := by simpa using h
        rw [← h02]
        exact scalarTriple_self_middle (v 0) (v 1)
      · change scalarTriple (v 0) (v 1) (v 2) = 0
        have h10 : v 1 = v 0 := by simpa using h
        rw [h10]
        exact scalarTriple_self_left (v 0) (v 2)
      · change scalarTriple (v 0) (v 1) (v 2) = 0
        have h12 : v 1 = v 2 := by simpa using h
        rw [h12]
        exact scalarTriple_self_right (v 0) (v 2)
      · change scalarTriple (v 0) (v 1) (v 2) = 0
        have h20 : v 2 = v 0 := by simpa using h
        rw [h20]
        exact scalarTriple_self_middle (v 0) (v 1)
      · change scalarTriple (v 0) (v 1) (v 2) = 0
        have h21 : v 2 = v 1 := by simpa using h
        rw [h21]
        exact scalarTriple_self_right (v 0) (v 1))

@[simp] theorem scalarTripleAlternatingMap_apply (v : Fin 3 → (Fin 3 → ℝ)) :
    scalarTripleAlternatingMap v = scalarTriple (v 0) (v 1) (v 2) := rfl

theorem scalarTripleAlternatingMap_apply_eq_det3 (v : Fin 3 → (Fin 3 → ℝ)) :
    scalarTripleAlternatingMap v = det3 (v 0) (v 1) (v 2) := by
  rw [scalarTripleAlternatingMap_apply]
  exact scalarTriple_eq_det3 _ _ _

theorem scalarTripleAlternatingMap_map_perm
    (v : Fin 3 → (Fin 3 → ℝ)) (σ : Equiv.Perm (Fin 3)) :
    scalarTripleAlternatingMap (v ∘ σ) =
      Equiv.Perm.sign σ • scalarTripleAlternatingMap v := by
  exact scalarTripleAlternatingMap.map_perm v σ

theorem crossProduct_anticomm (x y : Fin 3 → ℝ) :
    crossProduct x y = -(crossProduct y x) := by
  ext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

@[simp] theorem crossProduct_self (x : Fin 3 → ℝ) :
    crossProduct x x = (0 : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;> simp [crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3] <;> ring

theorem dotProduct_crossProduct_left (x y : Fin 3 → ℝ) :
    dotProduct x (crossProduct x y) = 0 := by
  simp [dotProduct, crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3, Fin.sum_univ_three]
  ring_nf

theorem dotProduct_crossProduct_right (x y : Fin 3 → ℝ) :
    dotProduct y (crossProduct x y) = 0 := by
  simp [dotProduct, crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3, Fin.sum_univ_three]
  ring_nf

theorem crossProduct_triple (x y z : Fin 3 → ℝ) :
    crossProduct x (crossProduct y z) =
      dotProduct x z • y - dotProduct x y • z := by
  ext i <;> fin_cases i <;>
    simp [dotProduct, crossProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3, Fin.sum_univ_three] <;>
    ring_nf

theorem dotProduct_crossProduct_cyclic (x y z : Fin 3 → ℝ) :
    dotProduct (crossProduct x y) z =
      dotProduct x (crossProduct y z) := by
  simp [dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3,
    Fin.sum_univ_three]
  ring

theorem dotProduct_crossProduct_swap (x y z : Fin 3 → ℝ) :
    dotProduct (crossProduct x y) z =
      -dotProduct (crossProduct x z) y := by
  simp [dotProduct, crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3,
    Fin.sum_univ_three]
  ring

theorem dotProduct_ext (x y : Fin 3 → ℝ)
    (h : ∀ u, dotProduct x u = dotProduct y u) :
    x = y := by
  ext i
  fin_cases i
  · simpa [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      Pi.single] using h (Pi.single (0 : Fin 3) 1)
  · simpa [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      Pi.single] using h (Pi.single (1 : Fin 3) 1)
  · simpa [dotProduct, InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
      Pi.single] using h (Pi.single (2 : Fin 3) 1)

theorem crossProduct_eq_of_dotProduct_eq_det3
    (v w x : Fin 3 → ℝ)
    (h : ∀ u, dotProduct x u = det3 v w u) :
    x = crossProduct v w := by
  apply dotProduct_ext
  intro u
  calc
    dotProduct x u = det3 v w u := h u
    _ = dotProduct (crossProduct v w) u :=
      (dotProduct_crossProduct_left_eq_det3 v w u).symm

theorem crossProduct_unique_by_dotProduct
    (v w x : Fin 3 → ℝ)
    (h : ∀ u, dotProduct x u = dotProduct (crossProduct v w) u) :
    x = crossProduct v w := by
  exact dotProduct_ext x (crossProduct v w) h

end InfoGeometry.Physics.ZornMatrixSU3
