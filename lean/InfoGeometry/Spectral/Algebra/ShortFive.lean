import InfoGeometry.Spectral.Algebra.ShortExact
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The short five lemma for modules

This is the linear-map form of the injective half of the old short-five
development.  The commuting squares are equalities of linear maps, so the
statement is independent of a chosen coordinate representation.
-/

namespace InfoGeometry.Spectral.Algebra.ShortFive

universe u v

variable {R : Type u} {A₀ B₀ C₀ A₁ B₁ C₁ : Type v}
variable [Ring R]
variable [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀]
variable [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
variable [Module R A₀] [Module R B₀] [Module R C₀]
variable [Module R A₁] [Module R B₁] [Module R C₁]

structure Data where
  f₀ : A₀ →ₗ[R] B₀
  g₀ : B₀ →ₗ[R] C₀
  f₁ : A₁ →ₗ[R] B₁
  g₁ : B₁ →ₗ[R] C₁
  h : A₀ →ₗ[R] A₁
  k : B₀ →ₗ[R] B₁
  l : C₀ →ₗ[R] C₁
  S₀ : ShortExact.Sequence f₀ g₀
  S₁ : ShortExact.Sequence f₁ g₁
  comm_f : k.comp f₀ = f₁.comp h
  comm_g : l.comp g₀ = g₁.comp k

theorem middle_injective (D : Data (R := R))
    (hh : Function.Injective (D.h : A₀ → A₁))
    (hl : Function.Injective (D.l : C₀ → C₁)) :
    Function.Injective (D.k : B₀ → B₁) := by
  intro b b' hbb'
  have hb : D.k (b - b') = 0 := by
    rw [D.k.map_sub, hbb', sub_self]
  have hgb : D.g₀ (b - b') = 0 := by
    apply hl
    have hcomm := LinearMap.congr_fun D.comm_g (b - b')
    calc
      D.l (D.g₀ (b - b')) = (D.l.comp D.g₀) (b - b') := rfl
      _ = (D.g₁.comp D.k) (b - b') := hcomm
      _ = D.l 0 := by
        change D.g₁ (D.k (b - b')) = D.l 0
        rw [hb]
        simp
  obtain ⟨a, ha⟩ :=
    (Exactness.mem_ker_iff_exists_preimage
      (f := D.f₀) (g := D.g₀) D.S₀.exact (b - b')).mp hgb
  have hha : D.h a = 0 := by
    apply D.S₁.injective
    have hcomm := LinearMap.congr_fun D.comm_f a
    calc
      D.f₁ (D.h a) = D.k (D.f₀ a) := hcomm.symm
      _ = D.k (b - b') := by rw [ha]
      _ = 0 := hb
      _ = D.f₁ 0 := by simp
  have ha0 : a = 0 := by
    apply hh
    simpa using hha
  have hdiff : b - b' = 0 := by
    simpa [ha0] using ha.symm
  exact sub_eq_zero.mp hdiff

theorem middle_surjective (D : Data (R := R))
    (hh : Function.Surjective (D.h : A₀ → A₁))
    (hl : Function.Surjective (D.l : C₀ → C₁)) :
    Function.Surjective (D.k : B₀ → B₁) := by
  intro b₁
  obtain ⟨c₀, hc₀⟩ := hl (D.g₁ b₁)
  obtain ⟨b₀, hb₀⟩ := D.S₀.surjective c₀
  have hker : D.g₁ (D.k b₀ - b₁) = 0 := by
    have hcomm := LinearMap.congr_fun D.comm_g b₀
    have hcomm' : D.l (D.g₀ b₀) = D.g₁ (D.k b₀) := by
      simpa using hcomm
    rw [D.g₁.map_sub]
    change D.g₁ (D.k b₀) - D.g₁ b₁ = 0
    rw [← hcomm', hb₀, hc₀, sub_self]
  obtain ⟨a₁, ha₁⟩ :=
    (Exactness.mem_ker_iff_exists_preimage
      (f := D.f₁) (g := D.g₁) D.S₁.exact (D.k b₀ - b₁)).mp hker
  obtain ⟨a₀, ha₀⟩ := hh a₁
  refine ⟨b₀ - D.f₀ a₀, ?_⟩
  have hcomm := LinearMap.congr_fun D.comm_f a₀
  have hcomm' : D.k (D.f₀ a₀) = D.f₁ (D.h a₀) := by
    simpa using hcomm
  calc
    D.k (b₀ - D.f₀ a₀) = D.k b₀ - D.k (D.f₀ a₀) := D.k.map_sub _ _
    _ = D.k b₀ - D.f₁ (D.h a₀) := by rw [hcomm']
    _ = D.k b₀ - D.f₁ a₁ := by rw [ha₀]
    _ = D.k b₀ - (D.k b₀ - b₁) := by rw [ha₁]
    _ = b₁ := by abel

theorem middle_bijective
    (D : Data (R := R) (A₀ := A₀) (B₀ := B₀) (C₀ := C₀)
      (A₁ := A₁) (B₁ := B₁) (C₁ := C₁))
    (hh : Function.Bijective (D.h : A₀ → A₁))
    (hl : Function.Bijective (D.l : C₀ → C₁)) :
    Function.Bijective (D.k : B₀ → B₁) := by
  exact ⟨middle_injective D hh.1 hl.1, middle_surjective D hh.2 hl.2⟩

noncomputable def middleLinearEquiv
    (D : Data (R := R) (A₀ := A₀) (B₀ := B₀) (C₀ := C₀)
      (A₁ := A₁) (B₁ := B₁) (C₁ := C₁))
    (hh : Function.Bijective (D.h : A₀ → A₁))
    (hl : Function.Bijective (D.l : C₀ → C₁)) :
    B₀ ≃ₗ[R] B₁ :=
  LinearEquiv.ofBijective (D.k : B₀ →ₗ[R] B₁) (middle_bijective D hh hl)

end InfoGeometry.Spectral.Algebra.ShortFive
