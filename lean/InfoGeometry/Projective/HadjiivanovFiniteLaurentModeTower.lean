import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutCommutationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Laurent-mode tower for logarithmic connections

Stage `n` contains the symmetric Laurent window with degrees `-n, …, n`.
The successor map inserts a zero mode at each new endpoint and shifts the old
coordinate indices by one.  The diagonal Euler operator and every fixed
fiber residue are compatible with these embeddings.

This is a finite algebraic tower.  No completion or analytic convergence is
asserted.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeTower

open InfoGeometry.Projective.HadjiivanovLogConnectionBridge

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Fiber-valued Laurent modes with degrees in the symmetric window
`[-n,n]`. -/
abbrev FiniteModeSection (n : ℕ) (V : Type*) := Fin (2 * n + 1) → V

/-- Laurent degree represented by a coordinate of the symmetric window. -/
def modeDegree (n : ℕ) (i : Fin (2 * n + 1)) : ℤ :=
  (i.1 : ℤ) - (n : ℤ)

abbrev IsInterior (n : ℕ) (i : Fin (2 * (n + 1) + 1)) : Prop :=
  (0 : ℕ) < i.1 ∧ i.1 < 2 * n + 2

/-- Value of the successor embedding: zero at the two new endpoints and the
old value at the shifted interior coordinate. -/
def modeBondValue (n : ℕ) (x : FiniteModeSection n V)
    (i : Fin (2 * (n + 1) + 1)) : V :=
  if h : IsInterior n i then
    x ⟨i.1 - 1, by omega⟩
  else
    0

/-- Linear successor embedding of symmetric Laurent windows. -/
def modeBond (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] FiniteModeSection (n + 1) V where
  toFun := modeBondValue n
  map_add' x y := by
    funext i
    change modeBondValue n (x + y) i =
      modeBondValue n x i + modeBondValue n y i
    by_cases h : IsInterior n i
    · rw [modeBondValue, dif_pos h, modeBondValue, dif_pos h,
        modeBondValue, dif_pos h]
      rfl
    · rw [modeBondValue, dif_neg h, modeBondValue, dif_neg h,
        modeBondValue, dif_neg h]
      exact (add_zero 0).symm
  map_smul' c x := by
    funext i
    change modeBondValue n (c • x) i = c • modeBondValue n x i
    by_cases h : IsInterior n i
    · rw [modeBondValue, dif_pos h, modeBondValue, dif_pos h]
      rfl
    · rw [modeBondValue, dif_neg h, modeBondValue, dif_neg h]
      exact (smul_zero c).symm

@[simp] theorem modeBond_apply_interior
    (n : ℕ) (x : FiniteModeSection n V)
    (i : Fin (2 * (n + 1) + 1))
    (h : IsInterior n i) :
    modeBond n x i = x ⟨i.1 - 1, by omega⟩ := by
  change modeBondValue n x i = _
  simp only [modeBondValue, dif_pos h]

@[simp] theorem modeBond_apply_boundary
    (n : ℕ) (x : FiniteModeSection n V)
    (i : Fin (2 * (n + 1) + 1))
    (h : ¬IsInterior n i) :
    modeBond n x i = 0 := by
  change modeBondValue n x i = _
  simp only [modeBondValue, dif_neg h]

theorem modeDegree_shift
    (n : ℕ) (i : Fin (2 * (n + 1) + 1))
    (h : IsInterior n i) :
    modeDegree (n + 1) i = modeDegree n ⟨i.1 - 1, by omega⟩ := by
  simp only [modeDegree]
  rcases h with ⟨h0, h1⟩
  omega

/-- Diagonal finite-window realization of `T∂_T`. -/
def finiteEuler (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] FiniteModeSection n V where
  toFun x i := (modeDegree n i : ℂ) • x i
  map_add' x y := by
    funext i
    simp [smul_add]
  map_smul' c x := by
    funext i
    simp [smul_smul, mul_comm]

/-- Pointwise finite-window logarithmic connection. -/
def finiteModeConnection (R : LogResidue V) (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] FiniteModeSection n V where
  toFun x i := (modeDegree n i : ℂ) • x i + residueOperator R (x i)
  map_add' x y := by
    funext i
    simp [smul_add]
    abel
  map_smul' c x := by
    funext i
    simp [smul_smul, mul_comm]

@[simp] theorem finiteModeConnection_apply
    (R : LogResidue V) (n : ℕ) (x : FiniteModeSection n V)
    (i : Fin (2 * n + 1)) :
    finiteModeConnection R n x i =
      (modeDegree n i : ℂ) • x i + residueOperator R (x i) := rfl

/-- The diagonal Euler operator is compatible with symmetric-window bonding. -/
theorem finiteEuler_modeBond (n : ℕ) :
    (finiteEuler (V := V) (n + 1)).comp (modeBond n) =
      (modeBond n).comp (finiteEuler (V := V) n) := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases h : IsInterior n i
  · change (modeDegree (n + 1) i : ℂ) • modeBond n x i =
      modeBond n (finiteEuler n x) i
    rw [modeBond_apply_interior n x i h,
      modeBond_apply_interior n (finiteEuler n x) i h,
      modeDegree_shift n i h]
    rfl
  · change (modeDegree (n + 1) i : ℂ) • modeBond n x i =
      modeBond n (finiteEuler n x) i
    rw [modeBond_apply_boundary n x i h,
      modeBond_apply_boundary n (finiteEuler n x) i h]
    simp

/-- Every fixed Hadjiivanov logarithmic residue connection is compatible with
the finite Laurent-window embeddings. -/
theorem finiteModeConnection_modeBond (R : LogResidue V) (n : ℕ) :
    (finiteModeConnection R (n + 1)).comp (modeBond n) =
      (modeBond n).comp (finiteModeConnection R n) := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases h : IsInterior n i
  · change finiteModeConnection R (n + 1) (modeBond n x) i =
      modeBond n (finiteModeConnection R n x) i
    rw [finiteModeConnection_apply,
      modeBond_apply_interior n x i h,
      modeBond_apply_interior n (finiteModeConnection R n x) i h,
      modeDegree_shift n i h]
    rfl
  · change finiteModeConnection R (n + 1) (modeBond n x) i =
      modeBond n (finiteModeConnection R n x) i
    rw [finiteModeConnection_apply,
      modeBond_apply_boundary n x i h,
      modeBond_apply_boundary n (finiteModeConnection R n x) i h]
    simp [residueOperator]

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeTower
