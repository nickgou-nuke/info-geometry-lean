import InfoGeometry.Topology.CantorBoundaryCuntzFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Topology.CantorBoundaryCuntzO2

open CantorBoundaryCuntzFamily

abbrev Boundary := ℕ → Fin 2
abbrev BoundaryFunction (R : Type*) := Boundary → R
abbrev BoundaryOperator (R : Type*) [Semiring R] :=
  BoundaryFunction R →ₗ[R] BoundaryFunction R

variable {R : Type*} [Semiring R]

def S {R : Type*} [Semiring R] (i : Fin 2) : BoundaryOperator R where
  toFun f b := if headN b = i then f (tailN b) else 0
  map_add' f g := by
    ext b
    by_cases h : headN b = i <;> simp [h]
  map_smul' c f := by
    ext b
    by_cases h : headN b = i <;> simp [h]

def T {R : Type*} [Semiring R] (i : Fin 2) : BoundaryOperator R where
  toFun f b := f (prependN i b)
  map_add' f g := by
    ext b
    rfl
  map_smul' c f := by
    ext b
    rfl

theorem ortho (i j : Fin 2) :
    T i * S j =
      if i = j then (1 : BoundaryOperator R) else 0 := by
  ext f b
  dsimp [T, S]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem partition :
    (∑ i : Fin 2, S i * T i) = (1 : BoundaryOperator R) := by
  apply LinearMap.ext
  intro f
  funext b
  dsimp [S, T]
  calc
    (∑ i : Fin 2, (if headN b = i then f (prependN i (tailN b)) else 0))
        = f (prependN (headN b) (tailN b)) := by
            simp [Finset.mem_univ]
    _ = f b := by rw [prependN_headN_tailN]

theorem S_injective (i : Fin 2) :
    Function.Injective (S (R := R) i) := by
  intro f g h
  have h' := congrArg (fun u => T (R := R) i u) h
  apply funext
  intro b
  have hb := congrFun h' b
  simpa [T, S] using hb

theorem T_surjective (i : Fin 2) :
    Function.Surjective (T (R := R) i) := by
  intro f
  refine ⟨S (R := R) i f, ?_⟩
  apply funext
  intro b
  simp [T, S]

def matrixUnit {R : Type*} [Semiring R] (i j : Fin 2) : BoundaryOperator R :=
  S (R := R) i * T (R := R) j

theorem matrixUnit_mul (i j k l : Fin 2) :
    matrixUnit (R := R) i j * matrixUnit (R := R) k l =
      if j = k then matrixUnit (R := R) i l else 0 := by
  dsimp [matrixUnit]
  calc
    (S (R := R) i * T (R := R) j) * (S (R := R) k * T (R := R) l) =
        S (R := R) i * (T (R := R) j * S (R := R) k) * T (R := R) l := by
          simp [mul_assoc]
    _ = if j = k then S (R := R) i * T (R := R) l else 0 := by
      rw [ortho]
      split <;> simp_all

theorem matrixUnit_commutator {R : Type*} [Ring R]
    (i j k l : Fin 2) :
    matrixUnit (R := R) i j * matrixUnit (R := R) k l -
        matrixUnit (R := R) k l * matrixUnit (R := R) i j =
      (if j = k then matrixUnit (R := R) i l else 0) -
        (if l = i then matrixUnit (R := R) k j else 0) := by
  rw [matrixUnit_mul, matrixUnit_mul]

theorem matrixUnit_diag_sum :
    (∑ i : Fin 2, matrixUnit (R := R) i i) = (1 : BoundaryOperator R) := by
  simpa [matrixUnit] using partition

theorem matrixUnit_diag_idempotent (i : Fin 2) :
    matrixUnit (R := R) i i * matrixUnit (R := R) i i = matrixUnit (R := R) i i := by
  rw [matrixUnit_mul]
  simp

theorem matrixUnit_diag_orthogonal {i j : Fin 2} (hij : i ≠ j) :
    matrixUnit (R := R) i i * matrixUnit (R := R) j j = 0 := by
  rw [matrixUnit_mul]
  simp [hij]

theorem diagonal_projection (i : Fin 2) (f : BoundaryFunction R) (b : Boundary) :
    (S (R := R) i * T (R := R) i) f b = if headN b = i then f b else 0 := by
  dsimp [S, T]
  by_cases h : headN b = i
  · simp only [if_pos h]
    rw [← h]
    exact congrArg f (prependN_headN_tailN b)
  · simp [h]

theorem projection_idempotent (i : Fin 2) :
    (S (R := R) i * T (R := R) i) *
        (S (R := R) i * T (R := R) i) =
      S (R := R) i * T (R := R) i := by
  calc
    (S (R := R) i * T (R := R) i) *
        (S (R := R) i * T (R := R) i) =
        S (R := R) i * (T (R := R) i * S (R := R) i) *
          T (R := R) i := by simp [mul_assoc]
    _ = S (R := R) i * (1 : BoundaryOperator R) * T (R := R) i := by
      rw [ortho]
      simp
    _ = S (R := R) i * T (R := R) i := by simp

theorem projections_orthogonal {i j : Fin 2} (hij : i ≠ j) :
    (S (R := R) i * T (R := R) i) *
        (S (R := R) j * T (R := R) j) = 0 := by
  calc
    (S (R := R) i * T (R := R) i) *
        (S (R := R) j * T (R := R) j) =
        S (R := R) i * (T (R := R) i * S (R := R) j) *
          T (R := R) j := by simp [mul_assoc]
    _ = S (R := R) i * (0 : BoundaryOperator R) * T (R := R) j := by
      rw [ortho]
      simp [hij]
    _ = 0 := by simp

theorem matrixUnit_apply (i j : Fin 2) (f : BoundaryFunction R) (b : Boundary) :
    matrixUnit (R := R) i j f b =
      if headN b = i then f (prependN j (tailN b)) else 0 := by
  dsimp [matrixUnit, S, T]

end InfoGeometry.Topology.CantorBoundaryCuntzO2
