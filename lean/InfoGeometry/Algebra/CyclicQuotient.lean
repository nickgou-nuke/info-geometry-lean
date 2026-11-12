/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Algebra.Hom

/-!
# Additive commutator quotient and nonunital functoriality

This is a module quotient, not a ring quotient. Multiplication is not asserted
to descend. Its functorial maps need not preserve the ambient multiplicative unit.
-/

namespace InfoGeometry.Algebra.CyclicQuotient

variable (R A : Type*) [Ring R] [Ring A] [Module R A]

/-- The linear span of associative commutators. -/
def commutatorSpan : Submodule R A :=
  Submodule.span R {c | ∃ x y : A, c = x * y - y * x}

abbrev CyclicModule := A ⧸ commutatorSpan R A

/-- The universal R-linear cyclic class; for R = ℤ this is additive universality. -/
def cyclicClass : A →ₗ[R] CyclicModule R A := (commutatorSpan R A).mkQ

theorem cyclicClass_mul_comm (x y : A) :
    cyclicClass R A (x * y) = cyclicClass R A (y * x) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero (commutatorSpan R A)).mpr
    (Submodule.subset_span ⟨x, y, rfl⟩)

section LinearDescent

variable {R A}

/-- A linear cyclic functional factors through the same commutator quotient over its
coefficient ring. This retains the original coefficient-linear structure. -/
def descLinear {M : Type*} [AddCommGroup M] [Module R M] (t : A →ₗ[R] M)
    (ht : ∀ x y, t (x * y) = t (y * x)) : CyclicModule R A →ₗ[R] M :=
  (commutatorSpan R A).liftQ t (by
    rw [commutatorSpan, Submodule.span_le]
    rintro c ⟨x, y, rfl⟩
    change t (x * y - y * x) = 0
    rw [map_sub, ht, sub_self])

@[simp] theorem descLinear_class {M : Type*} [AddCommGroup M] [Module R M]
    (t : A →ₗ[R] M) (ht : ∀ x y, t (x * y) = t (y * x)) (x : A) :
    descLinear t ht (cyclicClass R A x) = t x := rfl

end LinearDescent

section AlgebraMap

variable {k B C : Type*} [CommRing k] [Ring B] [Ring C] [Algebra k B] [Algebra k C]

/-- An algebra map preserves the linear commutator relation space. -/
theorem commutatorSpan_le_comap_algHom (f : B →ₐ[k] C) :
    commutatorSpan k B ≤ (commutatorSpan k C).comap f.toLinearMap := by
  rw [commutatorSpan, Submodule.span_le]
  rintro c ⟨x, y, rfl⟩
  change f (x * y - y * x) ∈ commutatorSpan k C
  rw [map_sub, map_mul, map_mul]
  exact Submodule.subset_span ⟨f x, f y, rfl⟩

end AlgebraMap

variable {B C : Type*} [Ring B] [Ring C]

/-- Native nonunital ring maps descend to the additive cyclic quotient. -/
def map (f : B →ₙ+* C) : CyclicModule ℤ B →ₗ[ℤ] CyclicModule ℤ C :=
  (commutatorSpan ℤ B).liftQ
    ((cyclicClass ℤ C).comp f.toAddMonoidHom.toIntLinearMap) (by
      rw [commutatorSpan, Submodule.span_le]
      rintro c ⟨x, y, rfl⟩
      change cyclicClass ℤ C (f (x * y - y * x)) = 0
      simp only [map_sub, map_mul]
      rw [cyclicClass_mul_comm ℤ C, sub_self])

@[simp] theorem map_class (f : B →ₙ+* C) (x : B) :
    map f (cyclicClass ℤ B x) = cyclicClass ℤ C (f x) := rfl

theorem map_unique (f : B →ₙ+* C)
    (g : CyclicModule ℤ B →ₗ[ℤ] CyclicModule ℤ C)
    (hg : ∀ x, g (cyclicClass ℤ B x) = cyclicClass ℤ C (f x)) : g = map f := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (commutatorSpan ℤ B).mkQ_surjective q
  exact hg x

/-- Every additive cyclic functional factors through the same quotient. -/
def desc {M : Type*} [AddCommGroup M] (t : B →+ M)
    (ht : ∀ x y, t (x * y) = t (y * x)) : CyclicModule ℤ B →ₗ[ℤ] M :=
  (commutatorSpan ℤ B).liftQ t.toIntLinearMap (by
    rw [commutatorSpan, Submodule.span_le]
    rintro c ⟨x, y, rfl⟩
    change t (x * y - y * x) = 0
    rw [map_sub, ht, sub_self])

@[simp] theorem desc_class {M : Type*} [AddCommGroup M] (t : B →+ M)
    (ht : ∀ x y, t (x * y) = t (y * x)) (x : B) :
    desc t ht (cyclicClass ℤ B x) = t x := rfl

end InfoGeometry.Algebra.CyclicQuotient
