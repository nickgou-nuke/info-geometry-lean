import InfoGeometry.Topology.KleinProjectiveMonodromy
import InfoGeometry.Projective.ProjectiveUnitary6
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

/-! Pin-Klein total-space orbit relation (central-extension orbit space). -/

namespace InfoGeometry.Topology

open InfoGeometry.Projective
open Matrix

/-- The total space: ℝ² × ℂ⁶ -/
def PinKleinTotalSpace : Type := (ℝ × ℝ) × (Fin 6 → ℂ)

/-- Action of generator A on the affine part -/
def actA_affine (w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1 + Real.pi, -w.2)

/-- Action of generator B on the affine part -/
def actB_affine (w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1, w.2 + Real.pi)

/-- Inverse actions on affine part -/
def actAInv_affine (w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1 - Real.pi, -w.2)

def actBInv_affine (w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1, w.2 - Real.pi)

/-- Action of central element Z on the fiber -/
def actZ_fiber {data : KleinMonodromyData} (v : Fin 6 → ℂ) : Fin 6 → ℂ :=
  (data.z : Matrix (Fin 6) (Fin 6) ℂ).mulVec v

/-- Action of A on the fiber -/
def actA_fiber {data : KleinMonodromyData} (v : Fin 6 → ℂ) : Fin 6 → ℂ :=
  (data.Θ : Matrix (Fin 6) (Fin 6) ℂ).mulVec v

/-- Action of B on the fiber -/
def actB_fiber {data : KleinMonodromyData} (v : Fin 6 → ℂ) : Fin 6 → ℂ :=
  (data.T : Matrix (Fin 6) (Fin 6) ℂ).mulVec v

/-- Inverse actions on fiber -/
def actAInv_fiber {data : KleinMonodromyData} (v : Fin 6 → ℂ) : Fin 6 → ℂ :=
  star (data.Θ : Matrix (Fin 6) (Fin 6) ℂ) |>.mulVec v

def actBInv_fiber {data : KleinMonodromyData} (v : Fin 6 → ℂ) : Fin 6 → ℂ :=
  star (data.T : Matrix (Fin 6) (Fin 6) ℂ) |>.mulVec v

/-- The affine Klein relation: A ∘ B ∘ A⁻¹ ∘ B = id on ℝ² -/
theorem affine_klein_relation (w : ℝ × ℝ) :
    actA_affine (actB_affine (actAInv_affine (actB_affine w))) = w := by
  simp [actA_affine, actB_affine, actAInv_affine, actBInv_affine]
  <;> ring

/-- The twisted fiber compatibility: Θ T Θ⁻¹ = Z T⁻¹ implies fiber action compatibility -/
theorem fiber_klein_compatibility {data : KleinMonodromyData} (v : Fin 6 → ℂ) :
    actA_fiber (data := data) (actB_fiber (data := data)
      (actAInv_fiber (data := data) (actB_fiber (data := data) v))) =
      actZ_fiber (data := data) v := by
  have hT : star (data.T : Matrix (Fin 6) (Fin 6) ℂ) *
      (data.T : Matrix (Fin 6) (Fin 6) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp data.T.property
  have hT' : (↑(star data.T) : Matrix (Fin 6) (Fin 6) ℂ) *
      (data.T : Matrix (Fin 6) (Fin 6) ℂ) = 1 := by
    simpa using hT
  simp only [actA_fiber, actB_fiber, actAInv_fiber, actBInv_fiber, actZ_fiber,
    Matrix.mulVec_mulVec]
  have hassoc :
      ((data.Θ : Matrix (Fin 6) (Fin 6) ℂ) * data.T) *
        (star (data.Θ : Matrix (Fin 6) (Fin 6) ℂ) * data.T) =
      ((data.Θ : Matrix (Fin 6) (Fin 6) ℂ) * data.T * star data.Θ) * data.T := by
    noncomm_ring
  have hpin' :
      (data.Θ : Matrix (Fin 6) (Fin 6) ℂ) * data.T *
          (star data.Θ : Matrix (Fin 6) (Fin 6) ℂ) =
        (data.z : Matrix (Fin 6) (Fin 6) ℂ) *
          (star data.T : Matrix (Fin 6) (Fin 6) ℂ) := by
    simpa using data.hpin
  have hpin'' :
      (data.Θ : Matrix (Fin 6) (Fin 6) ℂ) * data.T *
          (↑(star data.Θ) : Matrix (Fin 6) (Fin 6) ℂ) =
        (data.z : Matrix (Fin 6) (Fin 6) ℂ) *
          (↑(star data.T) : Matrix (Fin 6) (Fin 6) ℂ) := by
    simpa using hpin'
  rw [← Matrix.mul_assoc (data.Θ : Matrix (Fin 6) (Fin 6) ℂ) (data.T : Matrix (Fin 6) (Fin 6) ℂ),
    hassoc, hpin'', Matrix.mul_assoc, hT']
  simp

/-- Total space compatibility: the Pin relation holds on ℝ² × ℂ⁶ -/
theorem total_space_pin_klein_compatibility {data : KleinMonodromyData} (w : PinKleinTotalSpace) :
    (actA_affine (actB_affine (actAInv_affine (actB_affine w.1))),
     actA_fiber (data := data) (actB_fiber (data := data)
       (actAInv_fiber (data := data) (actB_fiber (data := data) w.2)))) =
      (w.1, actZ_fiber (data := data) w.2) := by
  apply Prod.ext
  · exact affine_klein_relation w.1
  · exact fiber_klein_compatibility (data := data) w.2

/-! Explicit lifted generator actions. -/
def pinKleinGeneratorAction {data : KleinMonodromyData} :
    (Unit ⊕ Unit) → PinKleinTotalSpace → PinKleinTotalSpace
  | Sum.inl (), (w, v) => (actA_affine w, actA_fiber (data := data) v)
  | Sum.inr (), (w, v) => (actB_affine w, actB_fiber (data := data) v)

def pinKleinStepRelation {data : KleinMonodromyData} :
    PinKleinTotalSpace → PinKleinTotalSpace → Prop :=
  fun x y => ∃ g : Unit ⊕ Unit,
    y = pinKleinGeneratorAction (data := data) g x ∨
      x = pinKleinGeneratorAction (data := data) g y

/-! The orbit relation is the reflexive-transitive closure of the explicit
generator steps; no action of the projective quotient on the lifted total
space is assumed. -/
def PinKleinOrbitRelation {data : KleinMonodromyData} :
    PinKleinTotalSpace → PinKleinTotalSpace → Prop :=
  Relation.ReflTransGen (pinKleinStepRelation (data := data))

/-- The orbit quotient space (not a vector bundle!) -/
def PinKleinTotalOrbitQuotient {data : KleinMonodromyData} : Type :=
  Quotient (Setoid.mk (PinKleinOrbitRelation (data := data))
    (by
      have hbase : ∀ a b, pinKleinStepRelation (data := data) a b →
          pinKleinStepRelation (data := data) b a := by
        intro a b h
        rcases h with ⟨g, h | h⟩
        · exact ⟨g, Or.inr h⟩
        · exact ⟨g, Or.inl h⟩
      have hrel : Function.swap (pinKleinStepRelation (data := data)) =
          pinKleinStepRelation (data := data) := by
        funext a b
        apply propext
        constructor
        · intro h
          exact hbase b a h
        · intro h
          exact hbase a b h
      constructor
      · intro x
        exact Relation.ReflTransGen.refl
      · intro a b h
        simpa [hrel] using Relation.ReflTransGen.swap h
      · intro a b c hab hbc
        exact Relation.ReflTransGen.trans hab hbc))

/-! This quotient is only an orbit space for the explicit lifted generator
steps; no rank-six vector-bundle identification is asserted. -/

end InfoGeometry.Topology

end
