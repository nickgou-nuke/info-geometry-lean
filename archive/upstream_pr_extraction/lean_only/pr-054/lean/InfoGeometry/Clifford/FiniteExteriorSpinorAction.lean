import Mathlib

/-!
# A finite exterior-spinor model for a split two-plane

This is the one-generator model of the standard `V ⊕ V*` action on
`Λ⁰ V* ⊕ Λ¹ V*`.  The two coordinates are the scalar and one-form
coefficients.  The first component of a split vector acts by contraction and
the second by exterior multiplication.  The file deliberately stays finite:
it is a kernel-checked seed for the general exterior/pure-spinor owner.
-/

namespace InfoGeometry.Clifford.FiniteExteriorSpinorAction

abbrev SplitVector1 := ℝ × ℝ
abbrev Spinor1 := ℝ × ℝ

def splitQuadratic (u : SplitVector1) : ℝ := u.1 * u.2

noncomputable def splitPair (u v : SplitVector1) : ℝ :=
  (u.1 * v.2 + v.1 * u.2) / 2

def action (u : SplitVector1) (ψ : Spinor1) : Spinor1 :=
  (u.1 * ψ.2, u.2 * ψ.1)

def annihilates (u : SplitVector1) (ψ : Spinor1) : Prop :=
  action u ψ = 0

def IsPureSpinor (ψ : Spinor1) : Prop :=
  ψ ≠ 0 ∧ (ψ.1 = 0 ∨ ψ.2 = 0)

theorem action_add_spinor (u : SplitVector1) (ψ χ : Spinor1) :
    action u (ψ + χ) = action u ψ + action u χ := by
  rcases u with ⟨u₁, u₂⟩
  rcases ψ with ⟨ψ₀, ψ₁⟩
  rcases χ with ⟨χ₀, χ₁⟩
  simp [action]
  constructor <;> ring

theorem action_smul_spinor (r : ℝ) (u : SplitVector1) (ψ : Spinor1) :
    action u (r • ψ) = r • action u ψ := by
  rcases u with ⟨u₁, u₂⟩
  rcases ψ with ⟨ψ₀, ψ₁⟩
  simp [action]
  constructor <;> ring

theorem action_sq (u : SplitVector1) (ψ : Spinor1) :
    action u (action u ψ) = splitQuadratic u • ψ := by
  rcases u with ⟨u₁, u₂⟩
  rcases ψ with ⟨ψ₀, ψ₁⟩
  simp [action, splitQuadratic]
  constructor <;> ring

theorem action_anticommutator (u v : SplitVector1) (ψ : Spinor1) :
    action u (action v ψ) + action v (action u ψ) =
      (u.1 * v.2 + v.1 * u.2) • ψ := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  rcases ψ with ⟨ψ₀, ψ₁⟩
  simp [action]
  constructor <;> ring

theorem scalar_vacuum_isPure : IsPureSpinor (1, 0) := by
  constructor
  · norm_num
  · exact Or.inr rfl

theorem top_spinor_isPure : IsPureSpinor (0, 1) := by
  constructor
  · norm_num
  · exact Or.inl rfl

theorem scalar_vacuum_annihilator (a : ℝ) :
    annihilates (a, 0) (1, 0) := by
  simp [annihilates, action]

theorem top_spinor_annihilator (a : ℝ) :
    annihilates (0, a) (0, 1) := by
  simp [annihilates, action]

theorem pure_scalar_annihilator {ψ₀ ψ₁ : ℝ} (h₁ : ψ₁ = 0) :
    annihilates (ψ₀, 0) (ψ₀, ψ₁) := by
  simp [annihilates, action, h₁]

theorem pure_top_annihilator {ψ₀ ψ₁ : ℝ} (h₀ : ψ₀ = 0) :
    annihilates (0, ψ₁) (ψ₀, ψ₁) := by
  simp [annihilates, action, h₀]

theorem annihilator_scalar_isotropic (a : ℝ) :
    splitQuadratic (a, 0) = 0 := by
  simp [splitQuadratic]

theorem annihilator_top_isotropic (a : ℝ) :
    splitQuadratic (0, a) = 0 := by
  simp [splitQuadratic]

theorem pure_annihilator_isotropic {ψ : Spinor1} (hψ : ψ ≠ 0)
    (hu : IsPureSpinor ψ) (u v : SplitVector1)
    (hu0 : annihilates u ψ) (hv0 : annihilates v ψ) :
    splitPair u v = 0 := by
  rcases ψ with ⟨ψ₀, ψ₁⟩
  rcases hu with ⟨_, hbranch⟩
  rcases hbranch with h₁ | h₀
  · change ψ₀ = 0 at h₁
    have hψ₁ : ψ₁ ≠ 0 := by
      intro hz
      apply hψ
      simp [h₁, hz]
    have hu₁ : u.1 = 0 := by
      have h := congrArg Prod.fst hu0
      have h' : u.1 * ψ₁ = 0 := by simpa [annihilates, action] using h
      exact (mul_eq_zero.mp h').resolve_right hψ₁
    have hv₁ : v.1 = 0 := by
      have h := congrArg Prod.fst hv0
      have h' : v.1 * ψ₁ = 0 := by simpa [annihilates, action] using h
      exact (mul_eq_zero.mp h').resolve_right hψ₁
    simp [splitPair, hu₁, hv₁]
  · change ψ₁ = 0 at h₀
    have hψ₀ : ψ₀ ≠ 0 := by
      intro hz
      apply hψ
      simp [h₀, hz]
    have hu₂ : u.2 = 0 := by
      have h := congrArg Prod.snd hu0
      have h' : u.2 * ψ₀ = 0 := by simpa [annihilates, action] using h
      exact (mul_eq_zero.mp h').resolve_right hψ₀
    have hv₂ : v.2 = 0 := by
      have h := congrArg Prod.snd hv0
      have h' : v.2 * ψ₀ = 0 := by simpa [annihilates, action] using h
      exact (mul_eq_zero.mp h').resolve_right hψ₀
    simp [splitPair, hu₂, hv₂]

end InfoGeometry.Clifford.FiniteExteriorSpinorAction
