import Mathlib.Analysis.Normed.Algebra.Basic

noncomputable section

namespace InfoGeometry.Recovered.ScalarAlgHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "EndH" => E →L[ℝ] E

/--
Recovered archive probe: the scalar algebra hom from `ℝ` into endomorphisms.

This is kept as a tiny reusable utility rather than a one-off sandbox snippet.
-/
def scalarEndAlgHom : ℝ →ₐ[ℝ] EndH :=
  Algebra.ofId ℝ EndH

/--
The same scalar action after explicit composition with the identity algebra map on `ℝ`.
This mirrors the archive probe shape exactly.
-/
def scalarEndAlgHomComp : ℝ →ₐ[ℝ] EndH :=
  (Algebra.ofId ℝ EndH).comp (Algebra.ofId ℝ ℝ)

@[simp] theorem scalarEndAlgHomComp_def :
    scalarEndAlgHomComp (E := E) = scalarEndAlgHom (E := E) := rfl

@[simp] theorem scalarEndAlgHomComp_apply (x : ℝ) :
    scalarEndAlgHomComp (E := E) x = scalarEndAlgHom (E := E) x := rfl

end InfoGeometry.Recovered.ScalarAlgHom
