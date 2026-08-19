import Mathlib
import Mathlib.Tactic

set_option autoImplicit false

/-!
# InfoGeometry.Physics.FermionicAndreevReflection

A finite two-coordinate BdG/Andreev reflection atom.

The map `andreevReflection (e,h) = (-h,e)` is the real `90°` rotation on the
finite electron/hole coordinate plane, so its square is `-id` and its fourth
power is `id`.

This file proves only that finite coordinate algebra.  It does not prove a
spin-statistics theorem, topological edge protection, a DIII classification
result, or a superconducting event-horizon theorem.
-/

namespace InfoGeometry.Physics.FermionicAndreevReflection

/-- Two real coordinates for a finite electron/hole BdG amplitude. -/
abbrev BdGQuasiparticle := ℝ × ℝ

namespace BdGQuasiparticle

/-- Electron-like coordinate. -/
abbrev e (p : BdGQuasiparticle) : ℝ := p.1

/-- Hole-like coordinate. -/
abbrev h (p : BdGQuasiparticle) : ℝ := p.2

end BdGQuasiparticle

/-- Finite Andreev reflection atom `(e,h) ↦ (-h,e)`. -/
def andreevReflection (p : BdGQuasiparticle) : BdGQuasiparticle :=
  (-p.h, p.e)

/-! Native linear packaging of the finite Andreev rotation. -/

def andreevReflectionLinear :
    BdGQuasiparticle →ₗ[ℝ] BdGQuasiparticle where
  toFun := andreevReflection
  map_add' p q := by
    rcases p with ⟨pe, ph⟩
    rcases q with ⟨qe, qh⟩
    ext <;> simp [andreevReflection, BdGQuasiparticle.e, BdGQuasiparticle.h] <;> ring
  map_smul' c p := by
    rcases p with ⟨pe, ph⟩
    ext <;> simp [andreevReflection, BdGQuasiparticle.e, BdGQuasiparticle.h]

@[simp] theorem andreevReflectionLinear_apply (p : BdGQuasiparticle) :
    andreevReflectionLinear p = andreevReflection p := rfl

def andreevReflectionLinearEquiv :
    BdGQuasiparticle ≃ₗ[ℝ] BdGQuasiparticle where
  toLinearMap := andreevReflectionLinear
  invFun p := -andreevReflection p
  left_inv p := by
    rcases p with ⟨pe, ph⟩
    ext <;> simp [andreevReflection, BdGQuasiparticle.e, BdGQuasiparticle.h]
  right_inv p := by
    rcases p with ⟨pe, ph⟩
    ext <;> simp [andreevReflection, BdGQuasiparticle.e, BdGQuasiparticle.h]

@[simp] theorem andreevReflectionLinearEquiv_apply (p : BdGQuasiparticle) :
    andreevReflectionLinearEquiv p = andreevReflection p := rfl

theorem andreevReflection_injective :
    Function.Injective andreevReflection := by
  intro p q h
  apply andreevReflectionLinearEquiv.injective
  simpa only [andreevReflectionLinearEquiv_apply] using h

theorem andreevReflection_surjective :
    Function.Surjective andreevReflection := by
  intro q
  refine ⟨andreevReflectionLinearEquiv.symm q, ?_⟩
  simpa only [andreevReflectionLinearEquiv_apply] using
    andreevReflectionLinearEquiv.apply_symm_apply q

@[simp] theorem andreevReflectionLinearEquiv_symm_apply
    (p : BdGQuasiparticle) :
    (andreevReflectionLinearEquiv.symm p) = -andreevReflection p := rfl

@[simp] theorem andreevReflectionLinear_sq :
    andreevReflectionLinear.comp andreevReflectionLinear =
      -(LinearMap.id : BdGQuasiparticle →ₗ[ℝ] BdGQuasiparticle) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨pe, ph⟩
  ext <;> simp [andreevReflectionLinear, andreevReflection,
    BdGQuasiparticle.e, BdGQuasiparticle.h]

@[simp] theorem andreevReflectionLinear_fourth :
    andreevReflectionLinear.comp
        (andreevReflectionLinear.comp
          (andreevReflectionLinear.comp andreevReflectionLinear)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨pe, ph⟩
  ext <;> simp [andreevReflectionLinear, andreevReflection,
    BdGQuasiparticle.e, BdGQuasiparticle.h]

/-- Euclidean squared amplitude of the finite electron/hole coordinate pair. -/
def amplitudeNormSq (p : BdGQuasiparticle) : ℝ :=
  p.e * p.e + p.h * p.h

theorem amplitudeNormSq_nonneg (p : BdGQuasiparticle) :
    0 ≤ amplitudeNormSq p := by
  unfold amplitudeNormSq
  nlinarith [sq_nonneg p.e, sq_nonneg p.h]

theorem amplitudeNormSq_eq_zero_iff (p : BdGQuasiparticle) :
    amplitudeNormSq p = 0 ↔ p = 0 := by
  rcases p with ⟨pe, ph⟩
  constructor
  · intro h
    simp only [amplitudeNormSq] at h
    have hpe : pe = 0 := by
      nlinarith [sq_nonneg pe, sq_nonneg ph]
    have hph : ph = 0 := by
      nlinarith [sq_nonneg pe, sq_nonneg ph]
    simp [hpe, hph]
  · intro h
    have hpe := congrArg Prod.fst h
    have hph := congrArg Prod.snd h
    simp at hpe hph
    simp [amplitudeNormSq, hpe, hph]

theorem amplitudeNormSq_smul (c : ℝ) (p : BdGQuasiparticle) :
    amplitudeNormSq (c • p) = c ^ 2 * amplitudeNormSq p := by
  rcases p with ⟨pe, ph⟩
  simp [amplitudeNormSq, pow_two]
  ring

/-- Applying the finite Andreev reflection twice gives the negative amplitude. -/
theorem andreevReflection_sq (p : BdGQuasiparticle) :
    andreevReflection (andreevReflection p) = -p := by
  rfl

/-- The finite Andreev reflection preserves the squared amplitude. -/
theorem andreevReflection_normSq (p : BdGQuasiparticle) :
    amplitudeNormSq (andreevReflection p) = amplitudeNormSq p := by
  simp [amplitudeNormSq, andreevReflection]
  ring

theorem andreevReflectionLinear_preserves_amplitudeNormSq
    (p : BdGQuasiparticle) :
    amplitudeNormSq (andreevReflectionLinear p) = amplitudeNormSq p := by
  simpa [andreevReflectionLinear] using andreevReflection_normSq p

theorem andreevReflectionLinearEquiv_preserves_amplitudeNormSq
    (p : BdGQuasiparticle) :
    amplitudeNormSq (andreevReflectionLinearEquiv p) = amplitudeNormSq p := by
  simpa [andreevReflectionLinearEquiv] using andreevReflection_normSq p

/-- Pasted-snippet-compatible name for the finite Andreev square law. -/
theorem andreev_reflection_fermionic (p : BdGQuasiparticle) :
    andreevReflection (andreevReflection p) = -p :=
  andreevReflection_sq p

/-- Applying the finite Andreev reflection four times returns the amplitude. -/
theorem andreevReflection_fourth (p : BdGQuasiparticle) :
    andreevReflection (andreevReflection (andreevReflection (andreevReflection p))) = p := by
  ext <;> simp [andreevReflection, BdGQuasiparticle.e, BdGQuasiparticle.h]

/-- The finite Andreev reflection fixes the zero amplitude. -/
theorem andreevReflection_zero :
    andreevReflection 0 = 0 := by
  ext <;> simp [andreevReflection, BdGQuasiparticle.e, BdGQuasiparticle.h]

theorem andreevReflectionLinearEquiv_sq (x : ℝ × ℝ) :
    andreevReflectionLinearEquiv
        (andreevReflectionLinearEquiv x) = -x := by
  have h := congrArg
    (fun T : BdGQuasiparticle →ₗ[ℝ] BdGQuasiparticle => T x)
    andreevReflectionLinear_sq
  simpa [andreevReflectionLinearEquiv, andreevReflectionLinear] using h

end InfoGeometry.Physics.FermionicAndreevReflection
