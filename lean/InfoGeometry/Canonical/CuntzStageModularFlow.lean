import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stagewise Cuntz modular-flow interface

The modular flow is recorded as a family of genuine star-algebra equivalences
on the supplied C⋆ stages.  The group law and transition naturality are
explicit fields, so a later categorical descent has exactly the hypotheses it
needs.  This file does not manufacture a flow from scalar coordinates.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageModularFlow

open InfoGeometry.Canonical.CuntzStarInductiveSystem

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable (T : CuntzStarTower Stage)

/-- A compatible one-parameter family of stagewise star-algebra automorphisms.

The naturality equation is the categorical descent condition: applying the
flow before or after a transition gives the same element in the later stage.
-/
structure CuntzStageModularFlowData where
  flow : ∀ n, ℝ → Stage n ≃⋆ₐ[ℂ] Stage n
  flow_zero : ∀ n a, flow n 0 a = a
  flow_add : ∀ n t s a, flow n (t + s) a = flow n t (flow n s a)
  map_naturality :
    ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
      T.map hmn (flow m t a) = flow n t (T.map hmn a)

namespace CuntzStageModularFlowLemmas

variable (Φ : CuntzStageModularFlowData Stage T)

@[simp] theorem flow_zero_apply (n : ℕ) (a : Stage n) :
    Φ.flow n 0 a = a :=
  Φ.flow_zero n a

@[simp] theorem flow_add_apply (n : ℕ) (t s : ℝ) (a : Stage n) :
    Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a) :=
  Φ.flow_add n t s a

theorem flow_neg_right_inverse (n : ℕ) (t : ℝ) (a : Stage n) :
    Φ.flow n t (Φ.flow n (-t) a) = a := by
  rw [← Φ.flow_add n t (-t) a]
  simpa using Φ.flow_zero n a

theorem flow_neg_left_inverse (n : ℕ) (t : ℝ) (a : Stage n) :
    Φ.flow n (-t) (Φ.flow n t a) = a := by
  rw [← Φ.flow_add n (-t) t a]
  simpa using Φ.flow_zero n a

theorem map_flow_commutes
    {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m) :
    T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a) :=
  Φ.map_naturality hmn t a

@[simp] theorem flow_map_star (n : ℕ) (t : ℝ) (a : Stage n) :
    Φ.flow n t (star a) = star (Φ.flow n t a) :=
  map_star (Φ.flow n t) a

theorem flow_map_mul (n : ℕ) (t : ℝ) (a b : Stage n) :
    Φ.flow n t (a * b) = Φ.flow n t a * Φ.flow n t b :=
  map_mul (Φ.flow n t) a b

end CuntzStageModularFlowLemmas

end InfoGeometry.Canonical.CuntzStageModularFlow
