import InfoGeometry.Spectral.Algebra.Exactness
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Short exact sequences of modules

This is the native linear-map counterpart of the old pointed `SES` record.
The exactness condition is delegated to `Exactness.IsExact`; injectivity and
surjectivity remain explicit data because they are not consequences of
middle exactness alone.
-/

namespace InfoGeometry.Spectral.Algebra.ShortExact

universe u v w

variable {R : Type u} {M : Type v} {N : Type w} {P : Type*}
variable [Ring R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

structure Sequence (f : M →ₗ[R] N) (g : N →ₗ[R] P) : Prop where
  exact : Exactness.IsExact f g
  injective : Function.Injective f
  surjective : Function.Surjective g

theorem comp_eq_zero {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (S : Sequence f g) : g.comp f = 0 :=
  Exactness.comp_eq_zero S.exact

theorem range_eq_ker {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (S : Sequence f g) : LinearMap.range f = LinearMap.ker g :=
  S.exact

theorem of_exact_injective_surjective
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hExact : Exactness.IsExact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Sequence f g := by
  exact ⟨hExact, hf, hg⟩

end InfoGeometry.Spectral.Algebra.ShortExact
