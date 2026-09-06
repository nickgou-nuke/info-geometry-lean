import InfoGeometry.Canonical.CuntzStarInductiveSystem

/-!
# Stagewise Cuntz modular-flow interface

The modular flow is recorded as a family of genuine star-algebra equivalences
on the supplied C⋆ stages.  The group law and transition naturality are
explicit theorem hypotheses, so a later categorical descent has exactly the
hypotheses it needs.  This file does not manufacture a flow from scalar
coordinates.
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
def CuntzStageModularFlowData :=
  ∀ n, ℝ → Stage n ≃⋆ₐ[ℂ] Stage n

namespace CuntzStageModularFlowData

def flow {Stage : ℕ → Type} [∀ n, CStarAlgebra (Stage n)]
    [∀ n, PartialOrder (Stage n)] (Φ : CuntzStageModularFlowData Stage) :
    ∀ n, ℝ → Stage n ≃⋆ₐ[ℂ] Stage n := Φ

end CuntzStageModularFlowData

namespace CuntzStageModularFlowLemmas

variable (Φ : CuntzStageModularFlowData Stage)

theorem flow_zero
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        CuntzStageModularFlowData.flow Φ n (t + s) a =
          CuntzStageModularFlowData.flow Φ n t
            (CuntzStageModularFlowData.flow Φ n s a))
    (n : ℕ) (a : Stage n) :
    Φ.flow n 0 a = a := by
  have h := hflow_add n (1 : ℝ) 0 a
  have h' : CuntzStageModularFlowData.flow Φ n 1 a =
      CuntzStageModularFlowData.flow Φ n 1
        (CuntzStageModularFlowData.flow Φ n 0 a) := by
    simpa using h
  exact (Φ.flow n 1).injective h'.symm

@[simp] theorem flow_zero_apply
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (n : ℕ) (a : Stage n) :
    CuntzStageModularFlowData.flow Φ n 0 a = a :=
  flow_zero (Stage := Stage) Φ hflow_add n a

@[simp] theorem flow_add_apply
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        CuntzStageModularFlowData.flow Φ n (t + s) a =
          CuntzStageModularFlowData.flow Φ n t
            (CuntzStageModularFlowData.flow Φ n s a))
    (n : ℕ) (t s : ℝ) (a : Stage n) :
      CuntzStageModularFlowData.flow Φ n (t + s) a =
        CuntzStageModularFlowData.flow Φ n t
          (CuntzStageModularFlowData.flow Φ n s a) :=
  hflow_add n t s a

theorem flow_neg_right_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        CuntzStageModularFlowData.flow Φ n (t + s) a =
          CuntzStageModularFlowData.flow Φ n t
            (CuntzStageModularFlowData.flow Φ n s a))
    (n : ℕ) (t : ℝ) (a : Stage n) :
    CuntzStageModularFlowData.flow Φ n t
        (CuntzStageModularFlowData.flow Φ n (-t) a) = a := by
  rw [← hflow_add n t (-t) a]
  simpa using flow_zero (Stage := Stage) Φ hflow_add n a

theorem flow_neg_left_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        CuntzStageModularFlowData.flow Φ n (t + s) a =
          CuntzStageModularFlowData.flow Φ n t
            (CuntzStageModularFlowData.flow Φ n s a))
    (n : ℕ) (t : ℝ) (a : Stage n) :
    CuntzStageModularFlowData.flow Φ n (-t)
        (CuntzStageModularFlowData.flow Φ n t a) = a := by
  rw [← hflow_add n (-t) t a]
  simpa using flow_zero (Stage := Stage) Φ hflow_add n a

theorem map_flow_commutes
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (CuntzStageModularFlowData.flow Φ m t a) =
          CuntzStageModularFlowData.flow Φ n t (T.map hmn a))
    {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m) :
    T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a) :=
  hmap_naturality hmn t a

@[simp] theorem flow_map_star (n : ℕ) (t : ℝ) (a : Stage n) :
    CuntzStageModularFlowData.flow Φ n t (star a) =
      star (CuntzStageModularFlowData.flow Φ n t a) :=
  map_star (CuntzStageModularFlowData.flow Φ n t) a

theorem flow_map_mul (n : ℕ) (t : ℝ) (a b : Stage n) :
    CuntzStageModularFlowData.flow Φ n t (a * b) =
      CuntzStageModularFlowData.flow Φ n t a *
        CuntzStageModularFlowData.flow Φ n t b :=
  map_mul (CuntzStageModularFlowData.flow Φ n t) a b

end CuntzStageModularFlowLemmas

end InfoGeometry.Canonical.CuntzStageModularFlow
