import Mathlib

/-! A carrier-independent interface for actions on graded families.

The grade is a family of sets rather than a submodule, so the same predicate
applies to associative operator grades and to componentwise graded carriers.
It deliberately records only the map-to-sector law; algebraic structure and
the meaning of the labels remain owned by the concrete carrier.
-/

namespace InfoGeometry.OperatorAlgebra

def MapsToGradeBetween {α γ ι β : Type*}
    (source : ι → Set α) (target : ι → Set γ) (action : β → α → γ)
    (perm : β → ι → ι) : Prop :=
  ∀ b i, Set.MapsTo (action b) (source i) (target (perm b i))

def MapsToGrade {A ι β : Type*}
    (grade : ι → Set A) (action : β → A → A) (perm : β → ι → ι) : Prop :=
  MapsToGradeBetween grade grade action perm

def PreservesGrade {A ι β : Type*}
    (grade : ι → Set A) (action : β → A → A) : Prop :=
  MapsToGrade grade action (fun _ i => i)

theorem mapsToGrade_apply
    {A ι β : Type*} {grade : ι → Set A} {action : β → A → A}
    {perm : β → ι → ι} (h : MapsToGrade grade action perm)
    (b : β) (i : ι) {x : A} (hx : x ∈ grade i) :
    action b x ∈ grade (perm b i) :=
  h b i hx

theorem mapsToGradeBetween_apply
    {α γ ι β : Type*} {source : ι → Set α} {target : ι → Set γ}
    {action : β → α → γ} {perm : β → ι → ι}
    (h : MapsToGradeBetween source target action perm)
    (b : β) (i : ι) {x : α} (hx : x ∈ source i) :
    action b x ∈ target (perm b i) :=
  h b i hx

theorem mapsToGradeBetween_comp
    {A B C ι β γ : Type*}
    {source : ι → Set A} {middle : ι → Set B} {target : ι → Set C}
    {action₁ : β → A → B} {action₂ : γ → B → C}
    {perm₁ : β → ι → ι} {perm₂ : γ → ι → ι}
    (h₁ : MapsToGradeBetween source middle action₁ perm₁)
    (h₂ : MapsToGradeBetween middle target action₂ perm₂)
    (b : β) (c : γ) (i : ι) {x : A} (hx : x ∈ source i) :
    action₂ c (action₁ b x) ∈ target (perm₂ c (perm₁ b i)) := by
  exact h₂ c (perm₁ b i) (h₁ b i hx)

/-! Three-stage composition keeps the label permutation explicit, so carrier
transport, involution, and a mode shift can be composed without collapsing
their distinct index types. -/
theorem mapsToGradeBetween_comp_three
    {A B C D ι β γ δ : Type*}
    {source : ι → Set A} {middle₁ : ι → Set B}
    {middle₂ : ι → Set C} {target : ι → Set D}
    {action₁ : β → A → B} {action₂ : γ → B → C}
    {action₃ : δ → C → D}
    {perm₁ : β → ι → ι} {perm₂ : γ → ι → ι}
    {perm₃ : δ → ι → ι}
    (h₁ : MapsToGradeBetween source middle₁ action₁ perm₁)
    (h₂ : MapsToGradeBetween middle₁ middle₂ action₂ perm₂)
    (h₃ : MapsToGradeBetween middle₂ target action₃ perm₃)
    (b : β) (c : γ) (d : δ) (i : ι) {x : A}
    (hx : x ∈ source i) :
    action₃ d (action₂ c (action₁ b x)) ∈
      target (perm₃ d (perm₂ c (perm₁ b i))) := by
  exact h₃ d (perm₂ c (perm₁ b i))
    (h₂ c (perm₁ b i) (h₁ b i hx))

theorem linearEquiv_mapsToGradeBetween_image_eq
    {R A B ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    (e : A ≃ₗ[R] B)
    (source : ι → Set A) (target : ι → Set B)
    (perm invPerm : ι → ι)
    (hforward : ∀ i, Set.MapsTo e (source i) (target (perm i)))
    (hbackward : ∀ i, Set.MapsTo e.symm (target i) (source (invPerm i)))
    (hleft : ∀ i, invPerm (perm i) = i) (i : ι) :
    e '' source i = target (perm i) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hforward i hx
  · intro y hy
    have hy' := hbackward (perm i) hy
    have hxi : e.symm y ∈ source i := by
      simpa [hleft i] using hy'
    exact ⟨e.symm y, hxi, e.apply_symm_apply y⟩

/- Exact image transports compose.  This is the carrier-level composition law
   used when a grade is read through more than one existing equivalence. -/
theorem linearEquiv_image_eq_comp
    {R A B C ι : Type*} [Semiring R]
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    [AddCommMonoid C] [Module R C]
    (e₁ : A ≃ₗ[R] B) (e₂ : B ≃ₗ[R] C)
    (source : ι → Set A) (middle : ι → Set B) (target : ι → Set C)
    (perm₁ perm₂ : ι → ι)
    (h₁ : ∀ i, e₁ '' source i = middle (perm₁ i))
    (h₂ : ∀ j, e₂ '' middle j = target (perm₂ j)) (i : ι) :
    (e₁.trans e₂) '' source i = target (perm₂ (perm₁ i)) := by
  change (fun x => e₂ (e₁ x)) '' source i = target (perm₂ (perm₁ i))
  rw [← Set.image_image, h₁ i, h₂ (perm₁ i)]

/-! A grade-preserving equivalence carries every sector onto itself. -/
theorem linearEquiv_preservesGrade_image_eq
    {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (e : A ≃ₗ[R] A) (grade : ι → Set A)
    (hforward : PreservesGrade grade (fun _ : Unit => fun x => e x))
    (hbackward : PreservesGrade grade
      (fun _ : Unit => fun x => e.symm x)) (i : ι) :
    e '' grade i = grade i := by
  apply linearEquiv_mapsToGradeBetween_image_eq e grade grade
    (fun i => i) (fun i => i)
  · intro i
    exact hforward () i
  · intro i
    exact hbackward () i
  · intro i
    rfl

theorem preservesGrade_apply
    {A ι β : Type*} {grade : ι → Set A} {action : β → A → A}
    (h : PreservesGrade grade action) (b : β) (i : ι) {x : A}
    (hx : x ∈ grade i) : action b x ∈ grade i :=
  h b i hx

/-- Composition of two grade-family actions, packaged at the family level. -/
theorem mapsToGradeBetween_comp_family
    {A B C ι β γ : Type*}
    {source : ι → Set A} {middle : ι → Set B} {target : ι → Set C}
    {action₁ : β → A → B} {action₂ : γ → B → C}
    {perm₁ : β → ι → ι} {perm₂ : γ → ι → ι}
    (h₁ : MapsToGradeBetween source middle action₁ perm₁)
    (h₂ : MapsToGradeBetween middle target action₂ perm₂) :
    MapsToGradeBetween source target
      (fun bc : β × γ => fun x => action₂ bc.2 (action₁ bc.1 x))
      (fun bc : β × γ => fun i => perm₂ bc.2 (perm₁ bc.1 i)) := by
  intro bc i x hx
  exact h₂ bc.2 (perm₁ bc.1 i) (h₁ bc.1 i hx)

/- Endomorphism grade actions compose at family level. -/
theorem mapsToGrade_comp_family
    {A ι β γ : Type*} {grade : ι → Set A}
    {action₁ : β → A → A} {action₂ : γ → A → A}
    {perm₁ : β → ι → ι} {perm₂ : γ → ι → ι}
    (h₁ : MapsToGrade grade action₁ perm₁)
    (h₂ : MapsToGrade grade action₂ perm₂) :
    MapsToGrade grade
      (fun bc : β × γ => fun x => action₁ bc.1 (action₂ bc.2 x))
      (fun bc : β × γ => fun i => perm₁ bc.1 (perm₂ bc.2 i)) := by
  intro bc i x hx
  exact h₁ bc.1 (perm₂ bc.2 i) (h₂ bc.2 i hx)

theorem preservesGrade_comp
    {A ι β γ : Type*} {grade : ι → Set A}
    {action₁ : β → A → A} {action₂ : γ → A → A}
    (h₁ : PreservesGrade grade action₁)
    (h₂ : PreservesGrade grade action₂) :
    PreservesGrade grade
      (fun bc : β × γ => fun x => action₁ bc.1 (action₂ bc.2 x)) := by
  exact mapsToGrade_comp_family h₁ h₂

theorem mapsToGrade_comp
    {A ι β γ : Type*} {grade : ι → Set A}
    {action₁ : β → A → A} {action₂ : γ → A → A}
    {perm₁ : β → ι → ι} {perm₂ : γ → ι → ι}
    (h₁ : MapsToGrade grade action₁ perm₁)
    (h₂ : MapsToGrade grade action₂ perm₂)
    (b : β) (c : γ) (i : ι) {x : A} (hx : x ∈ grade i) :
    action₁ b (action₂ c x) ∈ grade (perm₁ b (perm₂ c i)) := by
  exact h₁ b (perm₂ c i) (h₂ c i hx)

end InfoGeometry.OperatorAlgebra
