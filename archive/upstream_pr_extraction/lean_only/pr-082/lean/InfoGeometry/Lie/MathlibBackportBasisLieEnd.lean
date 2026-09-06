module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Adjoin.Polynomial
public import InfoGeometry.Lie.MathlibBackportAEval

/-! Project-owned compatibility lemma for basis endomorphism brackets. -/

public section

open scoped Polynomial
open Polynomial

open scoped Polynomial

namespace Module.Basis

open Polynomial

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [AddCommGroup M] [Module R M]

lemma lie_end_of_apply_eq_smul
    (b : Basis ι R M) (a : ι → R) (s : Module.End R M)
    (hs : ∀ k, s (b k) = a k • b k) (i j : ι) :
    ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j) := by
  refine b.ext fun k ↦ ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Basis.end_apply_apply, smul_ite, smul_zero, sub_smul]
  rcases eq_or_ne j k with rfl | hjk
  · simp [hs, Basis.end_apply_apply]
  · simp [hs, Basis.end_apply_apply, hjk]

end Module.Basis

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

public theorem instLieRingModule_eq (x y : End R M) :
    ⁅x, y⁆ = x * y - y * x := by
  rfl

end Module.End
