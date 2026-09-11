import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Submodules

The old reference defines submodules and their quotients by rebuilding the
underlying additive groups.  Mathlib's `Submodule` already supplies these
carriers and their universal maps; this file exposes the corresponding port
surface.
-/

namespace InfoGeometry.Spectral.Algebra.Submodule

universe u v

variable {R : Type u} {M : Type v} {N : Type v}
variable [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

abbrev Carrier (S : Submodule R M) := S

def inclusion (S : Submodule R M) : S →ₗ[R] M := S.subtype

@[simp] theorem inclusion_apply (S : Submodule R M) (x : S) : inclusion S x = x := rfl

def map (f : M →ₗ[R] N) (S : Submodule R M) : Submodule R N := S.map f

def comap (f : M →ₗ[R] N) (T : Submodule R N) : Submodule R M := T.comap f

@[simp] theorem mem_comap_iff (f : M →ₗ[R] N) (T : Submodule R N) (x : M) :
    x ∈ comap f T ↔ f x ∈ T := by
  rfl

theorem map_le_iff (f : M →ₗ[R] N) (S : Submodule R M) (T : Submodule R N) :
    map f S ≤ T ↔ ∀ x ∈ S, f x ∈ T := by
  exact Submodule.map_le_iff_le_comap

abbrev quotient (S : Submodule R M) := M ⧸ S

def quotientMap (S : Submodule R M) : M →ₗ[R] quotient S :=
  Submodule.mkQ S

@[simp] theorem quotientMap_apply (S : Submodule R M) (x : M) :
    quotientMap S x = Submodule.Quotient.mk x := by
  exact Submodule.mkQ_apply S x

theorem quotientMap_surjective (S : Submodule R M) :
    Function.Surjective (quotientMap S) := by
  exact Submodule.mkQ_surjective S

def quotientLift (S : Submodule R M) (f : M →ₗ[R] N)
    (hS : S ≤ LinearMap.ker f) : quotient S →ₗ[R] N :=
  Submodule.liftQ S f hS

@[simp] theorem quotientLift_quotientMap (S : Submodule R M) (f : M →ₗ[R] N)
    (hS : S ≤ LinearMap.ker f) (x : M) :
    quotientLift S f hS (quotientMap S x) = f x := by
  exact Submodule.liftQ_apply S f x

end InfoGeometry.Spectral.Algebra.Submodule
