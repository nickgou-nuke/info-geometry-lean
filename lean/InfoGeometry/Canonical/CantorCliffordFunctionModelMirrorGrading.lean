import Mathlib.Tactic
import InfoGeometry.Canonical.ChiralBoundarySheetReflectionTopological

/-!
# Mirror-even/odd decomposition of continuous boundary functions

This owner records the native `ℤ₂` grading induced by the symbolic boundary
reflection.  The names are deliberately mirror-even and mirror-odd: no
statistical, CAR, or Cuntz interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCliffordFunctionModelMirrorGrading

open InfoGeometry.Canonical.CantorCliffordFunctionModel
open InfoGeometry.Canonical.ChiralLightConeTensorTower

abbrev BoundaryFunction :=
  InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ

def mirrorEvenProjector (f : BoundaryFunction) : BoundaryFunction :=
  (1 / 2 : ℝ) • (f + boundaryMirrorPullback f)

def mirrorOddProjector (f : BoundaryFunction) : BoundaryFunction :=
  (1 / 2 : ℝ) • (f - boundaryMirrorPullback f)

def IsMirrorEven (f : BoundaryFunction) : Prop :=
  boundaryMirrorPullback f = f

def IsMirrorOdd (f : BoundaryFunction) : Prop :=
  boundaryMirrorPullback f = -f

@[simp] theorem mirrorEvenProjector_apply (f : BoundaryFunction)
    (ξ : ChiralBoundary) :
    mirrorEvenProjector f ξ =
      (1 / 2 : ℝ) * (f ξ + f (boundaryMirror ξ)) := by
  rfl

@[simp] theorem mirrorOddProjector_apply (f : BoundaryFunction)
    (ξ : ChiralBoundary) :
    mirrorOddProjector f ξ =
      (1 / 2 : ℝ) * (f ξ - f (boundaryMirror ξ)) := by
  rfl

theorem boundaryMirrorPullback_mul (f g : BoundaryFunction) :
    boundaryMirrorPullback (f * g) =
      boundaryMirrorPullback f * boundaryMirrorPullback g := by
  ext ξ
  rfl

theorem boundaryMirrorPullback_add (f g : BoundaryFunction) :
    boundaryMirrorPullback (f + g) =
      boundaryMirrorPullback f + boundaryMirrorPullback g := by
  ext ξ
  rfl

theorem boundaryMirrorPullback_sub (f g : BoundaryFunction) :
    boundaryMirrorPullback (f - g) =
      boundaryMirrorPullback f - boundaryMirrorPullback g := by
  ext ξ
  rfl

theorem boundaryMirrorPullback_smul (c : ℝ) (f : BoundaryFunction) :
    boundaryMirrorPullback (c • f) = c • boundaryMirrorPullback f := by
  ext ξ
  rfl

theorem mirrorEvenProjector_add_mirrorOddProjector (f : BoundaryFunction) :
    mirrorEvenProjector f + mirrorOddProjector f = f := by
  ext ξ
  simp [mirrorEvenProjector, mirrorOddProjector]
  ring

@[simp] theorem mirrorEvenProjector_mirrorEvenProjector (f : BoundaryFunction) :
    mirrorEvenProjector (mirrorEvenProjector f) = mirrorEvenProjector f := by
  ext ξ
  simp [mirrorEvenProjector, boundaryMirrorPullback,
    boundaryMirror_boundaryMirror]
  ring

@[simp] theorem mirrorOddProjector_mirrorOddProjector (f : BoundaryFunction) :
    mirrorOddProjector (mirrorOddProjector f) = mirrorOddProjector f := by
  ext ξ
  simp [mirrorOddProjector, boundaryMirrorPullback,
    boundaryMirror_boundaryMirror]
  ring

@[simp] theorem mirrorEvenProjector_mirrorOddProjector (f : BoundaryFunction) :
    mirrorEvenProjector (mirrorOddProjector f) = 0 := by
  ext ξ
  simp [mirrorEvenProjector, mirrorOddProjector, boundaryMirrorPullback,
    boundaryMirror_boundaryMirror]
  ring

@[simp] theorem mirrorOddProjector_mirrorEvenProjector (f : BoundaryFunction) :
    mirrorOddProjector (mirrorEvenProjector f) = 0 := by
  ext ξ
  simp [mirrorEvenProjector, mirrorOddProjector, boundaryMirrorPullback,
    boundaryMirror_boundaryMirror]
  ring

theorem mirrorEvenProjector_isMirrorEven (f : BoundaryFunction) :
    IsMirrorEven (mirrorEvenProjector f) := by
  unfold IsMirrorEven
  ext ξ
  simp [mirrorEvenProjector, boundaryMirrorPullback,
    boundaryMirror_boundaryMirror]
  ring

theorem mirrorOddProjector_isMirrorOdd (f : BoundaryFunction) :
    IsMirrorOdd (mirrorOddProjector f) := by
  unfold IsMirrorOdd
  ext ξ
  simp [mirrorOddProjector, boundaryMirrorPullback,
    boundaryMirror_boundaryMirror]
  ring

theorem mirror_even_odd_decomposition_unique
    {f e o : BoundaryFunction}
    (he : IsMirrorEven e) (ho : IsMirrorOdd o) (h : e + o = f) :
    e = mirrorEvenProjector f ∧ o = mirrorOddProjector f := by
  constructor
  · unfold mirrorEvenProjector
    ext ξ
    have heξ := congrArg (fun q : BoundaryFunction => q ξ) he
    have hoξ := congrArg (fun q : BoundaryFunction => q ξ) ho
    have hξ := congrArg (fun q : BoundaryFunction => q ξ) h
    have hξm := congrArg (fun q : BoundaryFunction => q (boundaryMirror ξ)) h
    have hξ' : e ξ + o ξ = f ξ := by simpa using hξ
    have hξm' : e (boundaryMirror ξ) + o (boundaryMirror ξ) =
        f (boundaryMirror ξ) := by simpa using hξm
    simp [boundaryMirrorPullback] at heξ hoξ
    simp [boundaryMirrorPullback]
    linarith [hξ', hξm']
  · unfold mirrorOddProjector
    ext ξ
    have heξ := congrArg (fun q : BoundaryFunction => q ξ) he
    have hoξ := congrArg (fun q : BoundaryFunction => q ξ) ho
    have hξ := congrArg (fun q : BoundaryFunction => q ξ) h
    have hξm := congrArg (fun q : BoundaryFunction => q (boundaryMirror ξ)) h
    have hξ' : e ξ + o ξ = f ξ := by simpa using hξ
    have hξm' : e (boundaryMirror ξ) + o (boundaryMirror ξ) =
        f (boundaryMirror ξ) := by simpa using hξm
    simp [boundaryMirrorPullback] at heξ hoξ
    simp [boundaryMirrorPullback]
    linarith [hξ', hξm']

theorem isMirrorEven_iff_evenProjector_eq (f : BoundaryFunction) :
    IsMirrorEven f ↔ mirrorEvenProjector f = f := by
  constructor
  · intro hf
    unfold mirrorEvenProjector
    rw [hf]
    ext ξ
    simp [boundaryMirrorPullback, hf]
    ring
  · intro hf
    unfold IsMirrorEven
    calc
      boundaryMirrorPullback f =
          boundaryMirrorPullback (mirrorEvenProjector f) := by rw [hf]
      _ = mirrorEvenProjector f := mirrorEvenProjector_isMirrorEven f
      _ = f := hf

theorem isMirrorOdd_iff_oddProjector_eq (f : BoundaryFunction) :
    IsMirrorOdd f ↔ mirrorOddProjector f = f := by
  constructor
  · intro hf
    unfold mirrorOddProjector
    rw [hf]
    ext ξ
    simp [boundaryMirrorPullback, hf]
    ring
  · intro hf
    unfold IsMirrorOdd
    calc
      boundaryMirrorPullback f =
          boundaryMirrorPullback (mirrorOddProjector f) := by rw [hf]
      _ = -mirrorOddProjector f := by
        exact mirrorOddProjector_isMirrorOdd f
      _ = -f := by rw [hf]

theorem isMirrorEven_iff_oddProjector_eq_zero (f : BoundaryFunction) :
    IsMirrorEven f ↔ mirrorOddProjector f = 0 := by
  constructor
  · intro hf
    unfold mirrorOddProjector
    ext ξ
    have hξ := congrArg (fun q : BoundaryFunction => q ξ) hf
    have hξ' : f (boundaryMirror ξ) = f ξ := by
      simpa [IsMirrorEven, boundaryMirrorPullback] using hξ
    simp [boundaryMirrorPullback, hξ']
  · intro hf
    apply (isMirrorEven_iff_evenProjector_eq f).2
    have hrec := mirrorEvenProjector_add_mirrorOddProjector f
    rw [hf, add_zero] at hrec
    exact hrec

theorem isMirrorOdd_iff_evenProjector_eq_zero (f : BoundaryFunction) :
    IsMirrorOdd f ↔ mirrorEvenProjector f = 0 := by
  constructor
  · intro hf
    unfold mirrorEvenProjector
    ext ξ
    have hξ := congrArg (fun q : BoundaryFunction => q ξ) hf
    have hξ' : f (boundaryMirror ξ) = -f ξ := by
      simpa [IsMirrorOdd, boundaryMirrorPullback] using hξ
    simp [boundaryMirrorPullback, hξ']
  · intro hf
    apply (isMirrorOdd_iff_oddProjector_eq f).2
    have hrec := mirrorEvenProjector_add_mirrorOddProjector f
    rw [hf, zero_add] at hrec
    exact hrec

theorem mirrorEven_mul_mirrorEven
    {f g : BoundaryFunction} (hf : IsMirrorEven f) (hg : IsMirrorEven g) :
    IsMirrorEven (f * g) := by
  unfold IsMirrorEven at *
  rw [boundaryMirrorPullback_mul, hf, hg]

theorem mirrorEven_mul_mirrorOdd
    {f g : BoundaryFunction} (hf : IsMirrorEven f) (hg : IsMirrorOdd g) :
    IsMirrorOdd (f * g) := by
  unfold IsMirrorOdd at *
  rw [boundaryMirrorPullback_mul, hf, hg]
  simp

theorem mirrorOdd_mul_mirrorEven
    {f g : BoundaryFunction} (hf : IsMirrorOdd f) (hg : IsMirrorEven g) :
    IsMirrorOdd (f * g) := by
  unfold IsMirrorOdd at *
  rw [boundaryMirrorPullback_mul, hf, hg]
  simp

theorem mirrorOdd_mul_mirrorOdd
    {f g : BoundaryFunction} (hf : IsMirrorOdd f) (hg : IsMirrorOdd g) :
    IsMirrorEven (f * g) := by
  unfold IsMirrorEven at *
  rw [boundaryMirrorPullback_mul, hf, hg]
  simp

end InfoGeometry.Canonical.CantorCliffordFunctionModelMirrorGrading
