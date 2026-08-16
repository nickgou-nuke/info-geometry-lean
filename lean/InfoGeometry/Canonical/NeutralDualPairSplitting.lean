import InfoGeometry.Canonical.NeutralDualPair

/-!
# The canonical splitting of a neutral dual pair

This file exposes the two summand inclusions of `U ⊕ U*` as linear maps and
records the resulting decomposition.  It is an algebraic carrier theorem,
not a topological direct-sum or completion statement.
-/

namespace InfoGeometry.Canonical.NeutralDualPair

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- Inclusion of the primal summand into the neutral carrier. -/
def primalIncl : U →ₗ[ℝ] Neutral U where
  toFun u := (u, 0)
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp

/-- Inclusion of the algebraic-dual summand into the neutral carrier. -/
def dualIncl : Dual U →ₗ[ℝ] Neutral U where
  toFun α := (0, α)
  map_add' α β := by ext <;> simp
  map_smul' c α := by ext <;> simp

@[simp] theorem primalIncl_apply (u : U) :
    primalIncl u = (u, 0) := rfl

@[simp] theorem dualIncl_apply (α : Dual U) :
    dualIncl α = (0, α) := rfl

theorem neutral_decomposition (x : Neutral U) :
    primalIncl x.1 + dualIncl x.2 = x := by
  rcases x with ⟨u, α⟩
  ext <;> simp

theorem primalIncl_eta_isotropic (u v : U) :
    eta (primalIncl u) (primalIncl v) = 0 := by
  simp [primalIncl, eta]

theorem dualIncl_eta_isotropic (α β : Dual U) :
    eta (dualIncl α) (dualIncl β) = 0 := by
  simp [dualIncl, eta]

theorem primalIncl_dualIncl_eta (u : U) (α : Dual U) :
    eta (primalIncl u) (dualIncl α) = α u := by
  simp [primalIncl, dualIncl, eta]

theorem dualIncl_primalIncl_eta (α : Dual U) (u : U) :
    eta (dualIncl α) (primalIncl u) = α u := by
  simp [primalIncl, dualIncl, eta]

/-- The primal and dual summands as actual submodules. -/
def primalSubmodule : Submodule ℝ (Neutral U) where
  carrier := {X | X.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [Prod.snd_add, hX, hY, add_zero]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    change c • X.2 = 0
    rw [hX, smul_zero]

def dualSubmodule : Submodule ℝ (Neutral U) where
  carrier := {X | X.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [Prod.fst_add, hX, hY, zero_add]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    change c • X.1 = 0
    rw [hX, smul_zero]

def etaOrthogonal (W : Submodule ℝ (Neutral U)) : Set (Neutral U) :=
  {X | ∀ Y, Y ∈ W → eta X Y = 0}

def omegaOrthogonal (W : Submodule ℝ (Neutral U)) : Set (Neutral U) :=
  {X | ∀ Y, Y ∈ W → omega X Y = 0}

theorem primalSubmodule_etaOrthogonal_eq_self :
    etaOrthogonal (primalSubmodule (U := U)) =
      (primalSubmodule (U := U) : Set (Neutral U)) := by
  ext X
  constructor
  · intro h
    have hdual : X.2 = 0 := by
      apply LinearMap.ext
      intro v
      have hv := h (v, 0) (by simp [primalSubmodule])
      simpa [eta] using hv
    simpa [primalSubmodule] using hdual
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hβ : β = 0 := by simpa [primalSubmodule] using hY
    have hX : X.2 = 0 := by simpa [primalSubmodule] using h
    simp [eta, hX, hβ]

theorem dualSubmodule_etaOrthogonal_eq_self :
    etaOrthogonal (dualSubmodule (U := U)) =
      (dualSubmodule (U := U) : Set (Neutral U)) := by
  ext X
  constructor
  · intro h
    have hprimal : X.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ X.1).mp
      intro α
      have hα := h (0, α) (by simp [dualSubmodule])
      simpa [eta] using hα
    simpa [dualSubmodule] using hprimal
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hv : v = 0 := by simpa [dualSubmodule] using hY
    have hX : X.1 = 0 := by simpa [dualSubmodule] using h
    simp [eta, hX, hv]

theorem primalSubmodule_omegaOrthogonal_eq_self :
    omegaOrthogonal (primalSubmodule (U := U)) =
      (primalSubmodule (U := U) : Set (Neutral U)) := by
  ext X
  constructor
  · intro h
    have hdual : X.2 = 0 := by
      apply LinearMap.ext
      intro v
      have hv := h (v, 0) (by simp [primalSubmodule])
      simpa [omega_apply] using hv
    simpa [primalSubmodule] using hdual
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hβ : β = 0 := by simpa [primalSubmodule] using hY
    have hX : X.2 = 0 := by simpa [primalSubmodule] using h
    simp [omega_apply, hX, hβ]

theorem dualSubmodule_omegaOrthogonal_eq_self :
    omegaOrthogonal (dualSubmodule (U := U)) =
      (dualSubmodule (U := U) : Set (Neutral U)) := by
  ext X
  constructor
  · intro h
    have hprimal : X.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ X.1).mp
      intro α
      have hα := h (0, α) (by simp [dualSubmodule])
      simpa [omega_apply] using hα
    simpa [dualSubmodule] using hprimal
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hv : v = 0 := by simpa [dualSubmodule] using hY
    have hX : X.1 = 0 := by simpa [dualSubmodule] using h
    simp [omega_apply, hX, hv]

end InfoGeometry.Canonical.NeutralDualPair
