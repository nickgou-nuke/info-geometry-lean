import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

noncomputable section

open ContinuousLinearMap

namespace PhysicalBdGPairingBridge

variable {H : Type*}
variable
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "AntiEndH" => H →L⋆[ℂ] H
local notation "NambuH" => H × H
local notation "EndNambu" => NambuH →L[ℂ] NambuH
local notation "AntiEndNambu" => NambuH →L⋆[ℂ] NambuH

/-!
# Native Mathlib physical BdG pairing bridge

The complex-linear BdG operator is

    H_BdG =
      [ h    Δ  ]
      [ Δ†  -h† ]

on the Nambu product `H × H`.

Physical particle-hole conjugation is conjugate-linear, so it is represented
with Mathlib's native `→L⋆[ℂ]` continuous antilinear-map type rather than by
a complex-linear `ContinuousLinearMap`.
-/

/-! ## BdG block operator -/

/-- Hole-sector diagonal block `-h†`. -/
noncomputable def holeBlock (h : EndH) : EndH :=
  -(ContinuousLinearMap.adjoint h)

/--
The physical Bogoliubov-de Gennes block operator

`[[h, Δ], [Δ†, -h†]]`.
-/
noncomputable def H_BdG (h Δ : EndH) : EndNambu :=
  (h.coprod Δ).prod
    ((ContinuousLinearMap.adjoint Δ).coprod (holeBlock h))

@[simp]
theorem H_BdG_apply (h Δ : EndH) (u v : H) :
    H_BdG h Δ (u, v) =
      (h u + Δ v,
        ContinuousLinearMap.adjoint Δ u -
          ContinuousLinearMap.adjoint h v) := by
  simp [H_BdG, holeBlock, sub_eq_add_neg]

/-! ## Native block extraction -/

/-- Upper-left block. -/
def block11 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp
    (T.comp (ContinuousLinearMap.inl ℂ H H))

/-- Upper-right block. -/
def block12 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp
    (T.comp (ContinuousLinearMap.inr ℂ H H))

/-- Lower-left block. -/
def block21 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.snd ℂ H H).comp
    (T.comp (ContinuousLinearMap.inl ℂ H H))

/-- Lower-right block. -/
def block22 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.snd ℂ H H).comp
    (T.comp (ContinuousLinearMap.inr ℂ H H))

@[simp]
theorem block11_H_BdG (h Δ : EndH) :
    block11 (H_BdG h Δ) = h := by
  apply ContinuousLinearMap.ext
  intro u
  simp [block11, H_BdG, holeBlock, ContinuousLinearMap.comp_apply]

@[simp]
theorem block12_H_BdG (h Δ : EndH) :
    block12 (H_BdG h Δ) = Δ := by
  apply ContinuousLinearMap.ext
  intro v
  simp [block12, H_BdG, holeBlock, ContinuousLinearMap.comp_apply]

@[simp]
theorem block21_H_BdG (h Δ : EndH) :
    block21 (H_BdG h Δ) =
      ContinuousLinearMap.adjoint Δ := by
  apply ContinuousLinearMap.ext
  intro u
  simp [block21, H_BdG, holeBlock, ContinuousLinearMap.comp_apply]

@[simp]
theorem block22_H_BdG (h Δ : EndH) :
    block22 (H_BdG h Δ) = holeBlock h := by
  apply ContinuousLinearMap.ext
  intro v
  simp [block22, H_BdG, holeBlock, ContinuousLinearMap.comp_apply]

/--
The upper-right inter-sheet coupling is exactly the superconducting
pairing potential.
-/
@[simp]
theorem xi_eq_delta_sc (h Δ : EndH) :
    block12 (H_BdG h Δ) = Δ :=
  block12_H_BdG h Δ

/-! ## Genuine conjugate-linear particle-hole operation -/

/--
Native Mathlib conjugate-linear Nambu particle-hole operation

`C(u,v) = (C₀ v, C₀ u)`.
-/
def PHS_operator (C₀ : AntiEndH) : AntiEndNambu where
  toFun := fun ψ => (C₀ ψ.2, C₀ ψ.1)
  map_add' ψ φ := by
    ext <;> simp
  map_smul' z ψ := by
    ext <;> simp
  cont := by
    fun_prop

@[simp]
theorem PHS_operator_apply (C₀ : AntiEndH) (u v : H) :
    PHS_operator C₀ (u, v) = (C₀ v, C₀ u) :=
  rfl

/--
If the one-particle conjugation is involutive, the Nambu particle-hole
operation is involutive.
-/
theorem PHS_operator_sq
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (ψ : NambuH) :
    PHS_operator C₀ (PHS_operator C₀ ψ) = ψ := by
  rcases ψ with ⟨u, v⟩
  simp [hC₀]

/-!
The four pointwise hypotheses below are the exact intertwining identities

    C₀ h† =  h C₀
    C₀ Δ† = -Δ C₀
    C₀ h  =  h† C₀
    C₀ Δ  = -Δ† C₀

with `C₀` genuinely conjugate-linear.
-/

/--
Particle-hole anticommutation of the physical BdG operator:

`C H_BdG ψ = - H_BdG C ψ`.
-/
theorem bdg_particle_hole_symmetry
    (h Δ : EndH)
    (C₀ : AntiEndH)
    (h_comm_adjoint :
      ∀ x : H,
        C₀ (ContinuousLinearMap.adjoint h x) =
          h (C₀ x))
    (h_anti_adjoint :
      ∀ x : H,
        C₀ (ContinuousLinearMap.adjoint Δ x) =
          -Δ (C₀ x))
    (h_comm :
      ∀ x : H,
        C₀ (h x) =
          ContinuousLinearMap.adjoint h (C₀ x))
    (h_anti :
      ∀ x : H,
        C₀ (Δ x) =
          -ContinuousLinearMap.adjoint Δ (C₀ x))
    (ψ : NambuH) :
    PHS_operator C₀ (H_BdG h Δ ψ) =
      -(H_BdG h Δ (PHS_operator C₀ ψ)) := by
  rcases ψ with ⟨u, v⟩
  apply Prod.ext
  · -- First component: C₀ (Δ† u - h† v) = -h (C₀ v) - Δ (C₀ u)
    calc
      (PHS_operator C₀ (H_BdG h Δ ⟨u, v⟩)).1 = C₀ (ContinuousLinearMap.adjoint Δ u - ContinuousLinearMap.adjoint h v) := by
        simp [H_BdG_apply, PHS_operator, holeBlock]
        <;> simp_all [ContinuousLinearMap.comp_apply]
        <;> abel
      _ = C₀ (ContinuousLinearMap.adjoint Δ u) - C₀ (ContinuousLinearMap.adjoint h v) := by
        apply C₀.map_sub
      _ = -Δ (C₀ u) - h (C₀ v) := by
        rw [h_anti_adjoint u, h_comm_adjoint v]
        <;> simp [sub_eq_add_neg]
        <;> abel
      _ = -(h (C₀ v) + Δ (C₀ u)) := by
        calc
          -Δ (C₀ u) - h (C₀ v) = -Δ (C₀ u) + -h (C₀ v) := by
            simp [sub_eq_add_neg]
          _ = -h (C₀ v) + -Δ (C₀ u) := by
            abel
          _ = -(h (C₀ v) + Δ (C₀ u)) := by
            rw [show -h (C₀ v) + -Δ (C₀ u) = -(h (C₀ v) + Δ (C₀ u)) by
              rw [neg_add]
              <;> abel]
      _ = -(H_BdG h Δ (PHS_operator C₀ ⟨u, v⟩)).1 := by
        simp [H_BdG_apply, PHS_operator]
        <;> simp_all [ContinuousLinearMap.comp_apply]
        <;> abel
        <;> simp_all [sub_eq_add_neg, neg_add]
        <;> abel
  · -- Second component: C₀ (h u + Δ v) = -Δ† (C₀ v) + h† (C₀ u)
    calc
      (PHS_operator C₀ (H_BdG h Δ ⟨u, v⟩)).2 = C₀ (h u + Δ v) := by
        simp [H_BdG_apply, PHS_operator, holeBlock]
        <;> simp_all [ContinuousLinearMap.comp_apply]
        <;> abel
      _ = C₀ (h u) + C₀ (Δ v) := by
        apply C₀.map_add
      _ = ContinuousLinearMap.adjoint h (C₀ u) + (-ContinuousLinearMap.adjoint Δ (C₀ v)) := by
        rw [h_comm u, h_anti v]
        <;> simp [sub_eq_add_neg]
        <;> abel
      _ = -(ContinuousLinearMap.adjoint Δ (C₀ v) - ContinuousLinearMap.adjoint h (C₀ u)) := by
        calc
          ContinuousLinearMap.adjoint h (C₀ u) + (-ContinuousLinearMap.adjoint Δ (C₀ v)) = ContinuousLinearMap.adjoint h (C₀ u) - ContinuousLinearMap.adjoint Δ (C₀ v) := by
            simp [sub_eq_add_neg]
          _ = -(ContinuousLinearMap.adjoint Δ (C₀ v) - ContinuousLinearMap.adjoint h (C₀ u)) := by
            abel
      _ = -(H_BdG h Δ (PHS_operator C₀ ⟨u, v⟩)).2 := by
        simp [H_BdG_apply, PHS_operator]
        <;> simp_all [ContinuousLinearMap.comp_apply]
        <;> abel
        <;> simp_all [sub_eq_add_neg, neg_add]
        <;> abel

/-!
## Involutive-conjugation reduction

For an involutive `C₀`, the reverse intertwining identities follow from the
first pair and need not be supplied independently.
-/

theorem conjugation_comm_reverse
    (h : EndH)
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (h_comm_adjoint :
      ∀ x : H,
        C₀ (ContinuousLinearMap.adjoint h x) =
          h (C₀ x))
    (x : H) :
    C₀ (h x) =
      ContinuousLinearMap.adjoint h (C₀ x) := by
  have hx :=
    congrArg C₀ (h_comm_adjoint (C₀ x))
  have hx' :
      ContinuousLinearMap.adjoint h (C₀ x) =
        C₀ (h x) := by
    simpa [hC₀] using hx
  exact hx'.symm

theorem conjugation_anti_reverse
    (Δ : EndH)
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (h_anti_adjoint :
      ∀ x : H,
        C₀ (ContinuousLinearMap.adjoint Δ x) =
          -Δ (C₀ x))
    (x : H) :
    C₀ (Δ x) =
      -ContinuousLinearMap.adjoint Δ (C₀ x) := by
  have hx :=
    congrArg C₀ (h_anti_adjoint (C₀ x))
  have hx' :
      ContinuousLinearMap.adjoint Δ (C₀ x) =
        -C₀ (Δ x) := by
    simpa [hC₀] using hx
  have hneg := congrArg Neg.neg hx'
  simpa using hneg.symm

/--
Particle-hole symmetry from only:

* involutivity `C₀² = 1`,
* `C₀ h† = h C₀`,
* `C₀ Δ† = -Δ C₀`.
-/
theorem bdg_particle_hole_symmetry_of_involutive
    (h Δ : EndH)
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (h_comm_adjoint :
      ∀ x : H,
        C₀ (ContinuousLinearMap.adjoint h x) =
          h (C₀ x))
    (h_anti_adjoint :
      ∀ x : H,
        C₀ (ContinuousLinearMap.adjoint Δ x) =
          -Δ (C₀ x))
    (ψ : NambuH) :
    PHS_operator C₀ (H_BdG h Δ ψ) =
      -(H_BdG h Δ (PHS_operator C₀ ψ)) := by
  exact bdg_particle_hole_symmetry
    h
    Δ
    C₀
    h_comm_adjoint
    h_anti_adjoint
    (conjugation_comm_reverse
      h C₀ hC₀ h_comm_adjoint)
    (conjugation_anti_reverse
      Δ C₀ hC₀ h_anti_adjoint)
    ψ

/-! ## Genuine inverse witness for the hole block -/

/--
The inverse used in the Schur complement is carried by a native
`ContinuousLinearEquiv`.
-/
def holeInverse
    (holeEquiv : H ≃L[ℂ] H) : EndH :=
  holeEquiv.symm.toContinuousLinearMap

@[simp]
theorem holeBlock_comp_holeInverse
    (h : EndH)
    (holeEquiv : H ≃L[ℂ] H)
    (hHole :
      holeEquiv.toContinuousLinearMap = holeBlock h) :
    (holeBlock h).comp (holeInverse holeEquiv) =
      ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change holeBlock h (holeEquiv.symm x) = x
  rw [← hHole]
  exact holeEquiv.apply_symm_apply x

@[simp]
theorem holeInverse_comp_holeBlock
    (h : EndH)
    (holeEquiv : H ≃L[ℂ] H)
    (hHole :
      holeEquiv.toContinuousLinearMap = holeBlock h) :
    (holeInverse holeEquiv).comp (holeBlock h) =
      ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change holeEquiv.symm (holeBlock h x) = x
  rw [← hHole]
  exact holeEquiv.symm_apply_apply x

/-! ## BdG Schur complement -/

/--
Upper-sector Schur complement

`A - B D⁻¹ C`

with

`A = h`,
`B = Δ`,
`C = Δ†`,
`D = -h†`.

`holeEquiv` is required to realize the invertible hole block through the
hypothesis used by the inverse theorems above.
-/
noncomputable def BdG_Schur_Complement
    (h Δ : EndH)
    (holeEquiv : H ≃L[ℂ] H) : EndH :=
  h -
    Δ.comp
      ((holeInverse holeEquiv).comp
        (ContinuousLinearMap.adjoint Δ))

@[simp]
theorem BdG_Schur_Complement_def
    (h Δ : EndH)
    (holeEquiv : H ≃L[ℂ] H) :
    BdG_Schur_Complement h Δ holeEquiv =
      h -
        Δ.comp
          ((holeInverse holeEquiv).comp
            (ContinuousLinearMap.adjoint Δ)) :=
  rfl

/-! ## Complete native block packet -/

theorem physical_BdG_block_packet
    (h Δ : EndH) :
    block11 (H_BdG h Δ) = h
      ∧ block12 (H_BdG h Δ) = Δ
      ∧ block21 (H_BdG h Δ) =
          ContinuousLinearMap.adjoint Δ
      ∧ block22 (H_BdG h Δ) =
          holeBlock h := by
  exact ⟨
    block11_H_BdG h Δ,
    block12_H_BdG h Δ,
    block21_H_BdG h Δ,
    block22_H_BdG h Δ
  ⟩

end PhysicalBdGPairingBridge

end noncomputable section