/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornColorOperatorClosure
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Faithful gl3 action and the exact scalar odd-derived submodule -/
noncomputable section
namespace InfoGeometry.Algebra.ZornColorOperatorCoordinates
open ZornVectorMatrix
variable {R : Type*} [CommRing R]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Native Mathlib Lie representation of the even matrix algebra. -/
def gl3Representation : Mat R →ₗ⁅R⁆ Op R where
  toFun M := evenMap (M, 0)
  map_add' M N := by simpa using evenMap.map_add (M, (0 : R)) (N, 0)
  map_smul' c M := by simpa using evenMap.map_smul c (M, (0 : R))
  map_lie' {M N} := by
    change evenMap (M * N - N * M, 0) = _
    exact (even_even_bracket M N 0 0).symm

theorem gl3Representation_injective : Function.Injective (gl3Representation (R := R)) := by
  intro M N h
  exact congrArg Prod.fst (evenMap_injective h)

/-- Span of all actual odd-odd superbrackets, not just a selected basis table. -/
def oddDerived : Submodule R (Op R) :=
  Submodule.span R (Set.range (fun xy : oddPart (R := R) × oddPart (R := R) =>
    xy.1.1 * xy.2.1 + xy.2.1 * xy.1.1))

/-- The entire odd-derived submodule is exactly the scalar identity line. -/
theorem oddDerived_eq_scalar : oddDerived (R := R) = R ∙ (1 : Op R) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro T ⟨⟨X, Y⟩, rfl⟩
    obtain ⟨⟨p, q⟩, hx⟩ := X.2
    obtain ⟨⟨r, s⟩, hy⟩ := Y.2
    change X.1 * Y.1 + Y.1 * X.1 ∈ R ∙ (1 : Op R)
    rw [← hx, ← hy, odd_odd_bracket]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro T hT
    obtain rfl := Set.mem_singleton_iff.mp hT
    let X : oddPart (R := R) := ⟨oddMap (ZornVec3.basis 0, 0), ⟨_, rfl⟩⟩
    let Y : oddPart (R := R) := ⟨oddMap (0, ZornVec3.basis 0), ⟨_, rfl⟩⟩
    have h : (-1 : Op R) ∈ oddDerived := by
      have hmem : X.1 * Y.1 + Y.1 * X.1 ∈ oddDerived :=
        Submodule.subset_span ⟨(X, Y), rfl⟩
      change oddMap (ZornVec3.basis 0, 0) * oddMap (0, ZornVec3.basis 0) +
        oddMap (0, ZornVec3.basis 0) * oddMap (ZornVec3.basis 0, 0) ∈ oddDerived at hmem
      rw [odd_odd_bracket] at hmem
      simpa [ZornVec3.dot, ZornVec3.basis, Fin.sum_univ_three] using hmem
    simpa using (oddDerived (R := R)).neg_mem h

/-- The scalar line is nonzero over every nontrivial coefficient ring. -/
theorem operator_one_ne_zero [Nontrivial R] : (1 : Op R) ≠ 0 := by
  intro h
  have ht := congrArg (fun T : Op R => (T E11).a) h
  simp [E11] at ht

section Dimension
variable {K : Type*} [Field K]
theorem finrank_oddDerived : Module.finrank K (oddDerived (R := K)) = 1 := by
  rw [oddDerived_eq_scalar]
  exact finrank_span_singleton operator_one_ne_zero
/-- The full even-plus-odd operator space has dimension sixteen, not sixty-four. -/
theorem finrank_color_operator_space :
    Module.finrank K ↥(evenPart (R := K) ⊔ oddPart (R := K)) = 16 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (evenPart (R := K)) (oddPart (R := K))
  rw [(even_odd_disjoint (R := K)).eq_bot, finrank_bot, _root_.add_zero,
    finrank_evenPart, finrank_oddPart] at h
  exact h
end Dimension
end InfoGeometry.Algebra.ZornColorOperatorCoordinates
