import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# The canonical splitting of a neutral dual pair

This file exposes the two summand inclusions of `U ⊕ U*` as linear maps and
records the resulting decomposition.  It is an algebraic carrier theorem,
not a topological direct-sum or completion statement.
-/

namespace InfoGeometry.Canonical.NeutralDualPairSplitting

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- Inclusion of the primal summand into the neutral carrier. -/
def primalIncl : U →ₗ[ℝ] PhaseSpaceCarrier U where
  toFun u := (u, 0)
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp

/-- Inclusion of the algebraic-dual summand into the neutral carrier. -/
def dualIncl : Module.Dual ℝ U →ₗ[ℝ] PhaseSpaceCarrier U where
  toFun α := (0, α)
  map_add' α β := by ext <;> simp
  map_smul' c α := by ext <;> simp

@[simp] theorem primalIncl_apply (u : U) :
    primalIncl u = (u, 0) := rfl

@[simp] theorem dualIncl_apply (α : Module.Dual ℝ U) :
    dualIncl α = (0, α) := rfl

theorem neutral_decomposition (x : PhaseSpaceCarrier U) :
    primalIncl x.1 + dualIncl x.2 = x := by
  rcases x with ⟨u, α⟩
  ext <;> simp

theorem primalIncl_eta_isotropic (u v : U) :
    canonicalNeutralBilin (primalIncl u) (primalIncl v) = 0 := by
  simp [primalIncl, canonicalNeutralBilin_apply]

theorem dualIncl_eta_isotropic (α β : Module.Dual ℝ U) :
    canonicalNeutralBilin (dualIncl α) (dualIncl β) = 0 := by
  simp [dualIncl, canonicalNeutralBilin_apply]

theorem primalIncl_dualIncl_eta (u : U) (α : Module.Dual ℝ U) :
    canonicalNeutralBilin (primalIncl u) (dualIncl α) = α u := by
  simp [primalIncl, dualIncl, canonicalNeutralBilin_apply]

theorem dualIncl_primalIncl_eta (α : Module.Dual ℝ U) (u : U) :
    canonicalNeutralBilin (dualIncl α) (primalIncl u) = α u := by
  simp [primalIncl, dualIncl, canonicalNeutralBilin_apply]

/-- The primal and dual summands as actual submodules. -/
def primalSubmodule : Submodule ℝ (PhaseSpaceCarrier U) where
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

def dualSubmodule : Submodule ℝ (PhaseSpaceCarrier U) where
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

def etaOrthogonal (W : Submodule ℝ (PhaseSpaceCarrier U)) : Set (PhaseSpaceCarrier U) :=
  {X | ∀ Y, Y ∈ W → canonicalNeutralBilin X Y = 0}

def omegaOrthogonal (W : Submodule ℝ (PhaseSpaceCarrier U)) : Set (PhaseSpaceCarrier U) :=
  {X | ∀ Y, Y ∈ W → neutralOmega X Y = 0}

theorem primalSubmodule_etaOrthogonal_eq_self :
    etaOrthogonal (primalSubmodule (U := U)) =
      (primalSubmodule (U := U) : Set (PhaseSpaceCarrier U)) := by
  ext X
  constructor
  · intro h
    have hdual : X.2 = 0 := by
      apply LinearMap.ext
      intro v
      have hv := h (v, 0) (by simp [primalSubmodule])
      simpa [canonicalNeutralBilin_apply] using hv
    simpa [primalSubmodule] using hdual
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hβ : β = 0 := by simpa [primalSubmodule] using hY
    have hX : X.2 = 0 := by simpa [primalSubmodule] using h
    simp [canonicalNeutralBilin_apply, hX, hβ]

theorem dualSubmodule_etaOrthogonal_eq_self :
    etaOrthogonal (dualSubmodule (U := U)) =
    (dualSubmodule (U := U) : Set (PhaseSpaceCarrier U)) := by
  ext X
  constructor
  · intro h
    have hprimal : X.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ X.1).mp
      intro α
      have hα := h (0, α) (by simp [dualSubmodule])
      simpa [canonicalNeutralBilin_apply] using hα
    simpa [dualSubmodule] using hprimal
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hv : v = 0 := by simpa [dualSubmodule] using hY
    have hX : X.1 = 0 := by simpa [dualSubmodule] using h
    simp [canonicalNeutralBilin_apply, hX, hv]

theorem primalSubmodule_omegaOrthogonal_eq_self :
    omegaOrthogonal (primalSubmodule (U := U)) =
      (primalSubmodule (U := U) : Set (PhaseSpaceCarrier U)) := by
  ext X
  constructor
  · intro h
    have hdual : X.2 = 0 := by
      apply LinearMap.ext
      intro v
      have hv := h (v, 0) (by simp [primalSubmodule])
      simpa [neutralOmega_apply] using hv
    simpa [primalSubmodule] using hdual
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hβ : β = 0 := by simpa [primalSubmodule] using hY
    have hX : X.2 = 0 := by simpa [primalSubmodule] using h
    simp [neutralOmega_apply, hX, hβ]

theorem dualSubmodule_omegaOrthogonal_eq_self :
    omegaOrthogonal (dualSubmodule (U := U)) =
      (dualSubmodule (U := U) : Set (PhaseSpaceCarrier U)) := by
  ext X
  constructor
  · intro h
    have hprimal : X.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ X.1).mp
      intro α
      have hα := h (0, α) (by simp [dualSubmodule])
      simpa [neutralOmega_apply] using hα
    simpa [dualSubmodule] using hprimal
  · intro h Y hY
    rcases Y with ⟨v, β⟩
    have hv : v = 0 := by simpa [dualSubmodule] using hY
    have hX : X.1 = 0 := by simpa [dualSubmodule] using h
    simp [neutralOmega_apply, hX, hv]

end InfoGeometry.Canonical.NeutralDualPairSplitting

