-- SPDX-License-Identifier: Apache-2.0



import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.Pin55ReflectionGlide
import InfoGeometry.GrandUnification.TomitaTakesakiRealization
/-!
# Spacetime Glide

This module gathers the basic algebraic facts about the *spacetime glide* operator
$$\mathcal{M} := J \circ T,$$
where `J` is the modular conjugation (`ModularConjugation.J_Δ`) and `T` is the
half‑translation `InfoGeometry.Clifford.Pin55ReflectionGlide.glide`.

The purpose of this file is *not* to build a fully fledged representation of
the operator on the Hilbert space – the concrete linear map `J_Δ` lives on an
arbitrary `Module R M`.  Instead we provide lemmas that express how the *glide*
part interacts with translation, together with a convenient wrapper `glideOp`
that bundles the two actions as a function on `Split55`.
-/
open InfoGeometry.Clifford.Pin55ReflectionGlide
open InfoGeometry.GrandUnification.TomitaTakesakiRealization

noncomputable section

namespace InfoGeometry.Physics.SpacetimeGlide

/-- A convenience wrapper that first applies the abstract modular conjugation
    `J_Δ` (viewed as a linear map on an auxiliary module `M`) and then the concrete
    glide `glide`.  Because the two objects act on different carriers, the wrapper
    returns a *pair* of results – the modular conjugation output and the glide
    output. -/
structure GlideOp {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] where
  J_apply : Module.End R M      -- the abstract modular conjugation `J_Δ`
  glide_apply : Split55 → Split55 -- the concrete glide on the split‑55 carrier

/-- The canonical `glide` operator on `Split55`. -/
@[simp, reducible]
def glideOp {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [hJ : ModularConjugation R M] : GlideOp :=
  { J_apply := hJ.J_Δ,
    glide_apply := glide }

/-- The glide squares to a unit translation. -/
@[simp]
theorem glide_square (x : Split55) :
    glide (glide x) = translateP 1 x :=
  glide_square_eq_translation x

/-- Gliding commutes with a pure translation `translateP a`. -/
@[simp]
theorem glide_translate_comm (a : ℝ) (x : Split55) :
    glide (translateP a x) = translateP a (glide x) :=
  pinReflection_translateP_comm a x

/-- Repeated gliding four times yields a double translation.
    Using `glide_square` twice we obtain
    `glide⁴ x = translateP 2 x`. -/
theorem glide_four_eq_double_translation (x : Split55) :
    (glide^[4]) x = translateP 2 x := by
  -- unfold the four‑fold iteration
  simp [Function.iterate_succ, Function.iterate_zero] at *
  -- first two glides give a translation by 1
  have h1 : glide (glide x) = translateP 1 x := glide_square x
  -- apply glide twice more
  have h2 : glide (glide (translateP 1 x)) = translateP 1 (translateP 1 x) := by
    simpa [glide_square (translateP 1 x)] using rfl
  -- combine the two equalities
  calc
    (glide^[4]) x
        = glide (glide (glide (glide x))) := rfl
    _ = glide (glide (translateP 1 x)) := by simpa [h1]
    _ = translateP 1 (translateP 1 x) := by
          simpa [glide_square (translateP 1 x)]
    _ = translateP (1 + 1) x := by
          simpa [translateP_add 1 1 x] using rfl
    _ = translateP 2 x := by norm_num

/-- A short description of the physical interpretation. -/
/--
-- *`J`* – the modular conjugation (`ModularConjugation.J_Δ`) implements the
-- Krein symmetry that exchanges the algebra of observables (the *Ego*) with its
-- commutant (the *Anima*).
--
-- *`T`* – the half‑translation `glide` (reflection + half‑step) implements the
-- spatial cycle of the Schwinger‑Keldysh contour.
--
-- Their composition `𝓜 = J ∘ T` is the *spacetime glide reflection* that
-- produces a non‑orientable Klein‑bottle topology.
--/

end InfoGeometry.Physics.SpacetimeGlide
