import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.GradeActionInterface

/-! A carrier-independent statement for indexed mode actions.  Mode shifts are
kept separate from integer eigengrades: the target index is part of the law.
-/

namespace InfoGeometry.OperatorAlgebra

def HasModeShift {R A ι : Type*} [SMul R A]
    (action : ℤ → A → A) (mode : ι → A) (shift : ℤ → ι → ι)
    (coeff : ℤ → ι → R) : Prop :=
  ∀ n i, action n (mode i) = coeff n i • mode (shift n i)

def ModeSpanGrade {R A ι : Type*} [SMul R A]
    (mode : ι → A) (i : ι) : Set A :=
  Set.range (fun c : R => c • mode i)

theorem linearEquiv_modeSpanGrade_image_eq
    {R A B ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    (e : A ≃ₗ[R] B) (mode : ι → A) (i : ι) :
    e '' ModeSpanGrade (R := R) mode i =
      ModeSpanGrade (R := R) (fun j => e (mode j)) i := by
  ext y
  constructor
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by rw [map_smul]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • mode i, ⟨c, rfl⟩, ?_⟩
    rw [map_smul]

theorem HasModeShift.apply
    {R A ι : Type*} [SMul R A]
    {action : ℤ → A → A} {mode : ι → A}
    {shift : ℤ → ι → ι} {coeff : ℤ → ι → R}
    (h : HasModeShift action mode shift coeff) (n : ℤ) (i : ι) :
    action n (mode i) = coeff n i • mode (shift n i) :=
  h n i

theorem HasModeShift.congr
    {R A ι : Type*} [SMul R A]
    {action₁ action₂ : ℤ → A → A} {mode₁ mode₂ : ι → A}
    {shift : ℤ → ι → ι} {coeff : ℤ → ι → R}
    (haction : ∀ n x, action₁ n x = action₂ n x)
    (hmode : ∀ i, mode₁ i = mode₂ i)
    (h : HasModeShift action₁ mode₁ shift coeff) :
    HasModeShift action₂ mode₂ shift coeff := by
  intro n i
  rw [← hmode i, ← haction n (mode₁ i), h n i, hmode (shift n i)]

theorem HasModeShift.map
    {R A B ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {action : ℤ → A → A} {mode : ι → A}
    {shift : ℤ → ι → ι} {coeff : ℤ → ι → R}
    (e : A ≃ₗ[R] B)
    (h : HasModeShift action mode shift coeff) :
    HasModeShift
      (fun n y => e (action n (e.symm y)))
      (fun i => e (mode i)) shift coeff := by
  intro n i
  change e (action n (e.symm (e (mode i)))) =
    coeff n i • e (mode (shift n i))
  rw [e.symm_apply_apply, h n i, map_smul]

theorem HasModeShift.mode_mem_shifted_grade
    {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {grade : ι → Set A} {action : ℤ → A → A} {mode : ι → A}
    {shift : ℤ → ι → ι} {coeff : ℤ → ι → R}
    (hshift : HasModeShift action mode shift coeff)
    (hgrade : ∀ i (c : R), c • mode i ∈ grade i)
    (n : ℤ) (i : ι) :
    action n (mode i) ∈ grade (shift n i) := by
  rw [hshift n i]
  exact hgrade (shift n i) (coeff n i)

theorem HasModeShift.mapsToModeSpanGrade
    {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {action : ℤ → A → A} {mode : ι → A}
    {shift : ℤ → ι → ι} {coeff : ℤ → ι → R}
    (hlinear : ∀ (n : ℤ) (c : R) (x : A),
      action n (c • x) = c • action n x)
    (h : HasModeShift action mode shift coeff) :
    MapsToGrade
      (ModeSpanGrade (R := R) mode)
      action shift := by
  intro n i x hx
  rcases hx with ⟨c, rfl⟩
  refine ⟨c * coeff n i, ?_⟩
  rw [hlinear n c, h n i, smul_smul]

theorem HasModeShift.map_mapsToModeSpanGrade
    {R A B ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {action : ℤ → A → A} {mode : ι → A}
    {shift : ℤ → ι → ι} {coeff : ℤ → ι → R}
    (e : A ≃ₗ[R] B)
    (hlinearAction : ∀ (n : ℤ) (c : R) (x : A),
      action n (c • x) = c • action n x)
    (h : HasModeShift action mode shift coeff) :
    MapsToGrade
      (ModeSpanGrade (R := R) (fun i => e (mode i)))
      (fun n y => e (action n (e.symm y))) shift := by
  apply HasModeShift.mapsToModeSpanGrade
    (hlinear := by
      intro n c y
      rw [e.symm.map_smul, hlinearAction, e.map_smul])
  exact h.map e

theorem HasModeShift.comp
    {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {action₁ action₂ : ℤ → A → A} {mode : ι → A}
    {shift₁ shift₂ : ℤ → ι → ι}
    {coeff₁ coeff₂ : ℤ → ι → R}
    (hlinear : ∀ (n : ℤ) (c : R) (x : A),
      action₁ n (c • x) = c • action₁ n x)
    (h₁ : HasModeShift action₁ mode shift₁ coeff₁)
    (h₂ : HasModeShift action₂ mode shift₂ coeff₂) :
    HasModeShift
      (fun n x => action₁ n (action₂ n x)) mode
      (fun n i => shift₁ n (shift₂ n i))
      (fun n i => coeff₂ n i * coeff₁ n (shift₂ n i)) := by
  intro n i
  change action₁ n (action₂ n (mode i)) =
    (coeff₂ n i * coeff₁ n (shift₂ n i)) •
      mode (shift₁ n (shift₂ n i))
  rw [h₂ n i, hlinear n, h₁ n (shift₂ n i)]
  simp [smul_smul]

/-! Composition with independent mode parameters.  This is the form needed
for two Virasoro/current actions, where the shifts are indexed by `n` and
`m` rather than by one shared parameter. -/
theorem HasModeShift.comp₂
    {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {action₁ action₂ : ℤ → A → A} {mode : ι → A}
    {shift₁ shift₂ : ℤ → ι → ι}
    {coeff₁ coeff₂ : ℤ → ι → R}
    (hlinear : ∀ (n : ℤ) (c : R) (x : A),
      action₁ n (c • x) = c • action₁ n x)
    (h₁ : HasModeShift action₁ mode shift₁ coeff₁)
    (h₂ : HasModeShift action₂ mode shift₂ coeff₂) :
    ∀ n m i,
      action₁ n (action₂ m (mode i)) =
        (coeff₂ m i * coeff₁ n (shift₂ m i)) •
          mode (shift₁ n (shift₂ m i)) := by
  intro n m i
  rw [h₂ m i, hlinear n, h₁ n (shift₂ m i), smul_smul]

end InfoGeometry.OperatorAlgebra
