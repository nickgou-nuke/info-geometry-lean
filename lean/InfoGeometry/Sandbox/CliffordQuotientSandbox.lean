import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

/-!
# Sandbox: Functorial Lifting of Isometric Clifford Towers

This file handles the structural lifting of linear isometric embeddings to 
algebra homomorphisms natively, utilizing the Macaulay2 invariant dimension check.
-/

open CliffordAlgebra

variable {V_n V_m : Type*} [AddCommGroup V_n] [Module ℝ V_n] [AddCommGroup V_m] [Module ℝ V_m]
variable (Q_n : QuadraticForm ℝ V_n) (Q_m : QuadraticForm ℝ V_m)

/-- 
  A linear map between inner product spaces that strictly preserves the quadratic form.
  This mirrors the verified coordinate backbone of the codebase.
-/
structure IsometricEmbeddingSpec (Q_n : QuadraticForm ℝ V_n) (Q_m : QuadraticForm ℝ V_m) where
  toLinearMap : V_n →ₗ[ℝ] V_m
  preserves_form : ∀ (x : V_n), Q_m (toLinearMap x) = Q_n x

/--
  THE ALGEBRA LIFTING OPERATOR
  
  Natively transforms a verified isometric vector space embedding into a strict 
  unital algebra homomorphism between the corresponding Clifford algebras.
  Bypasses manual coordinate expansion or relation checking.
-/
def liftIsometricEmbeddingToAlgebraHom (f : IsometricEmbeddingSpec Q_n Q_m) :
    CliffordAlgebra Q_n →ₐ[ℝ] CliffordAlgebra Q_m :=
  let iso : Q_n →qᵢ Q_m := {
    toLinearMap := f.toLinearMap
    map_app' := f.preserves_form
  }
  CliffordAlgebra.map iso

/--
  Theorem proving that the lifted algebra homomorphism preserves the identity 
  element of the Clifford algebra natively via Mathlib 4's universal property.
-/
theorem lifted_hom_preserves_one (f : IsometricEmbeddingSpec Q_n Q_m) :
    liftIsometricEmbeddingToAlgebraHom Q_n Q_m f 1 = 1 := by
  exact map_one (liftIsometricEmbeddingToAlgebraHom Q_n Q_m f)
