import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import InfoGeometry.Canonical.ExteriorGradedDerivationBridge

open InfoGeometry.Clifford.BivectorVectorRepresentation
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

namespace InfoGeometry.CliffordExteriorLift

lemma ι_mul_ι_add_swap (x y : V) : ι R x * ι R y + ι R y * ι R x = 0 := by
  have h := ExteriorAlgebra.ι_sq_zero (x + y)
  have hx := ExteriorAlgebra.ι_sq_zero x
  have hy := ExteriorAlgebra.ι_sq_zero y
  rw [map_add] at h
  calc ι R x * ι R y + ι R y * ι R x
    _ = (ι R x + ι R y) * (ι R x + ι R y) - ι R x * ι R x - ι R y * ι R y := by noncomm_ring
    _ = 0 - 0 - 0 := by rw [←h, hx, hy]
    _ = 0 := by simp

def liftMatrix (T : V →ₗ[R] V) : V →ₗ[R] Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V) where
  toFun v := fun i j =>
    if i = 0 ∧ j = 0 then ι R v
    else if i = 0 ∧ j = 1 then ι R (T v)
    else if i = 1 ∧ j = 1 then ι R v
    else 0
  map_add' x y := by ext i j; dsimp; split_ifs <;> simp
  map_smul' c x := by ext i j; dsimp; split_ifs <;> simp

lemma liftMatrix_sq_zero (T : V →ₗ[R] V) (v : V) : liftMatrix T v * liftMatrix T v = 0 := by
  ext i j
  dsimp [Matrix.mul, Matrix.dotProduct]
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [liftMatrix, ExteriorAlgebra.ι_sq_zero, ι_mul_ι_add_swap]

def exteriorLiftAux (T : V →ₗ[R] V) : ExteriorAlgebra R V →ₐ[R] Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V) :=
  ExteriorAlgebra.lift R (liftMatrix T) (liftMatrix_sq_zero T)

lemma exteriorLiftAux_diag (T : V →ₗ[R] V) (x : ExteriorAlgebra R V) :
    (exteriorLiftAux T x) 0 0 = x ∧ (exteriorLiftAux T x) 1 1 = x ∧ (exteriorLiftAux T x) 1 0 = 0 := by
  refine ExteriorAlgebra.induction (P := fun x => (exteriorLiftAux T x) 0 0 = x ∧ (exteriorLiftAux T x) 1 1 = x ∧ (exteriorLiftAux T x) 1 0 = 0) ?_ ?_ ?_ ?_ x
  · intro r
    dsimp [exteriorLiftAux]
    simp [Matrix.algebraMap_apply]
  · intro m
    dsimp [exteriorLiftAux, liftMatrix]
    simp
  · intro p q hp hq
    dsimp [exteriorLiftAux]
    rcases hp with ⟨hp00, hp11, hp10⟩
    rcases hq with ⟨hq00, hq11, hq10⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [hp00, hp11, hp10, hq00, hq11, hq10]
    · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [hp00, hp11, hp10, hq00, hq11, hq10]
    · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [hp00, hp11, hp10, hq00, hq11, hq10]
  · intro p q hp hq
    dsimp [exteriorLiftAux]
    rcases hp with ⟨hp00, hp11, hp10⟩
    rcases hq with ⟨hq00, hq11, hq10⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [map_add]; simp [hp00, hp11, hp10, hq00, hq11, hq10]
    · rw [map_add]; simp [hp00, hp11, hp10, hq00, hq11, hq10]
    · rw [map_add]; simp [hp00, hp11, hp10, hq00, hq11, hq10]

def exteriorLift (T : V →ₗ[R] V) : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V where
  toFun x := (exteriorLiftAux T x) 0 1
  map_add' x y := by simp [exteriorLiftAux]
  map_smul' c x := by simp [exteriorLiftAux]

/-- The lifted derivation restricts to the given linear map on generators. -/
@[simp] theorem exteriorLift_ι (T : V →ₗ[R] V) (v : V) :
    exteriorLift T (ι R v) = ι R (T v) := by
  simp [exteriorLift, exteriorLiftAux, liftMatrix,
    ExteriorAlgebra.lift_ι_apply]

theorem exteriorLift_even_derivation (T : V →ₗ[R] V) (x y : ExteriorAlgebra R V) :
    exteriorLift T (x * y) = exteriorLift T x * y + x * exteriorLift T y := by
  dsimp [exteriorLift]
  have h := map_mul (exteriorLiftAux T) x y
  have h_eval : (exteriorLiftAux T (x * y)) 0 1 = (exteriorLiftAux T x * exteriorLiftAux T y) 0 1 := by rw [h]
  rw [h_eval]
  dsimp [Matrix.mul, Matrix.dotProduct]
  rw [Fin.sum_univ_two]
  have hx := exteriorLiftAux_diag T x
  have hy := exteriorLiftAux_diag T y
  rcases hx with ⟨hx00, hx11, hx10⟩
  rcases hy with ⟨hy00, hy11, hy10⟩
  rw [hx00, hy11]

end InfoGeometry.CliffordExteriorLift
