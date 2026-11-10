/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Matrix representation induced by an exterior-algebra basis

Given a rank-32 module basis of an exterior algebra and an algebra
representation into its endomorphism ring, this file transports the
representation to `32 × 32` matrices and proves that this change of carrier
preserves and reflects injectivity.  This generic construction does not itself
define a Pin(5,5) group action or prove a Pin representation theorem.
-/

namespace InfoGeometry.AQFT.Pin55Pullback

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Over any non-commutative rings `[Ring B] [Ring C] [Ring D]`, post-composing a ring
homomorphism `ρ : B →+* C` with a ring isomorphism `e : C ≃+* D` preserves and reflects injectivity. -/
theorem ringHom_comp_equiv_injective_iff
    {B C D : Type*} [Ring B] [Ring C] [Ring D]
    (e : C ≃+* D) (ρ : B →+* C) :
    Function.Injective (e.toRingHom.comp ρ) ↔ Function.Injective ρ := by
  constructor
  · intro h a b hab
    apply h
    exact congrArg e hab
  · intro h a b hab
    apply h
    apply e.injective
    exact hab

variable {R W A : Type*}
variable [CommRing R] [AddCommGroup W] [Module R W]
variable [Ring A] [Algebra R A]

/-- The algebra equivalence from endomorphisms to matrices in the chosen basis. -/
noncomputable def endomorphismMatrixEquiv
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W)) :
    Module.End R (ExteriorAlgebra R W) ≃ₐ[R] Matrix (Fin 32) (Fin 32) R :=
  LinearMap.toMatrixAlgEquiv exteriorBasis

/-- Matrix form of an algebra representation, obtained by changing its target
from endomorphisms to matrices in `exteriorBasis`. -/
noncomputable def matrixRepresentationOfBasis
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W))
    (ρ : A →ₐ[R] Module.End R (ExteriorAlgebra R W)) :
    A →ₐ[R] Matrix (Fin 32) (Fin 32) R :=
  (endomorphismMatrixEquiv exteriorBasis).toAlgHom.comp ρ

/-- Passing from endomorphisms to matrices in a basis preserves and reflects
injectivity of the represented algebra map. -/
theorem matrixRepresentationOfBasis_injective_iff
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W))
    (ρ : A →ₐ[R] Module.End R (ExteriorAlgebra R W)) :
    Function.Injective (matrixRepresentationOfBasis exteriorBasis ρ) ↔
      Function.Injective ρ := by
  change Function.Injective ((endomorphismMatrixEquiv exteriorBasis).toAlgHom.comp ρ) ↔
    Function.Injective ρ
  constructor
  · intro h a b hab
    apply h
    exact congrArg (endomorphismMatrixEquiv exteriorBasis) hab
  · intro h a b hab
    apply h
    apply (endomorphismMatrixEquiv exteriorBasis).injective
    exact hab

end InfoGeometry.AQFT.Pin55Pullback
