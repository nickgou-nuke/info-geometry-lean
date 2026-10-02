import InfoGeometry.Geometry.DressingField
import Mathlib.Algebra.Group.Action.TypeTags

namespace InfoGeometry.Geometry.ParticleReferenceFrames

open DressingField

variable {Particle Position : Type*} [AddCommGroup Position]

def particleFrame (reference : Particle) :
    (Particle → Position) →[Multiplicative Position] Multiplicative Position where
  toFun positions := Multiplicative.ofAdd (positions reference)
  map_smul' _ _ := rfl

def relative (reference : Particle) (positions : Particle → Position) : Particle → Position :=
  fun particle => positions particle - positions reference

theorem relative_eq_normalize (reference : Particle) (positions : Particle → Position) :
    relative reference positions = normalize (particleFrame reference) positions := by
  funext particle
  change positions particle - positions reference = -positions reference + positions particle
  abel

@[simp] theorem relative_reference (reference : Particle) (positions : Particle → Position) :
    relative reference positions reference = 0 := sub_self _

theorem relative_translate (reference : Particle) (positions : Particle → Position)
    (shift : Position) :
    relative reference (fun particle => shift + positions particle) =
      relative reference positions := by
  simpa only [← relative_eq_normalize] using
    normalize_invariant (particleFrame reference) (Multiplicative.ofAdd shift) positions

theorem relative_change_reference (first second : Particle) (positions : Particle → Position) :
    relative second (relative first positions) = relative second positions := by
  funext particle
  simp only [relative]
  abel

theorem relative_preserves_difference (reference first second : Particle)
    (positions : Particle → Position) :
    relative reference positions first - relative reference positions second =
      positions first - positions second := by
  simp only [relative]
  abel

theorem relative_eq_iff_translation (reference : Particle)
    (first second : Particle → Position) :
    relative reference first = relative reference second ↔
      ∃ shift : Position, first = fun particle => shift + second particle := by
  rw [relative_eq_normalize, relative_eq_normalize, normalize_eq_iff_orbit]
  constructor
  · intro related
    obtain ⟨shift, equality⟩ := MulAction.mem_orbit_iff.mp related
    exact ⟨shift.toAdd, equality.symm⟩
  · rintro ⟨shift, equality⟩
    exact MulAction.mem_orbit_iff.mpr ⟨Multiplicative.ofAdd shift, equality.symm⟩

theorem relative_history_invariant {Time : Type*} (reference : Particle)
    (history : Time → Particle → Position) (shift : Time → Position) :
    (fun time => relative reference (fun particle => shift time + history time particle)) =
      fun time => relative reference (history time) := by
  funext time
  exact relative_translate reference (history time) (shift time)

end InfoGeometry.Geometry.ParticleReferenceFrames
