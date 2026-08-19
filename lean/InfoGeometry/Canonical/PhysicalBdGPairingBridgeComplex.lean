/-!
# PhysicalBdGPairingBridgeComplex

Native Mathlib complex-linear BdG pairing bridge on the complex Nambu carrier `H × H`.

This file uses only native Mathlib continuous-linear-map constructions:
- Complex Hilbert space `H`
- Nambu carrier `H × H`
- Physical BdG operator `[[h, Δ], [Δ†, -h†]]`
- Complex-linear particle-hole proxy `PHS_operator`
- Genuine inverse witness via `ContinuousLinearEquiv`

This complements the realified architecture in `PhysicalBdGPairingBridge.lean`
which uses the repository's `DoubledSpace E` and real conjugation `κ`.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic

noncomputable section

open ContinuousLinearMap

namespace InfoGeometry.Canonical.PhysicalBdGPairingBridgeComplex

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "NambuH" => H × H
local notation "EndNambu" => NambuH →L[ℂ] NambuH

/-!
## 1. Native BdG block operator
-/

/-- Hole-sector diagonal block `-h†`. -/
@[rep_depth operator]
noncomputable def holeBlock (h : EndH) : EndH :=
  -(ContinuousLinearMap.adjoint h)

/--
Physical Bogoliubov-de Gennes operator

`H_BdG = [[h, Δ], [Δ†, -h†]]`.
-/
@[rep_depth operator]
noncomputable def H_BdG (h Δ : EndH) : EndNambu :=
  (h.coprod Δ).prod
    ((ContinuousLinearMap.adjoint Δ).coprod
      (holeBlock h))

@[simp]
theorem H_BdG_apply (h Δ : EndH) (u v : H) :
    H_BdG h Δ (u, v) =
      (h u + Δ v,
       ContinuousLinearMap.adjoint Δ u -
         ContinuousLinearMap.adjoint h v) := by
  simp [H_BdG, holeBlock, sub_eq_add_neg]

/-!
## 2. Native block extraction
-/

/-- Upper-left block of an operator on `H × H`. -/
@[rep_depth operator]
def block11 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp
    (T.comp (ContinuousLinearMap.inl ℂ H H))

/-- Upper-right block of an operator on `H × H`. -/
@[rep_depth operator]
def block12 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp
    (T.comp (ContinuousLinearMap.inr ℂ H H))

/-- Lower-left block of an operator on `H × H`. -/
@[rep_depth operator]
def block21 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.snd ℂ H H).comp
    (T.comp (ContinuousLinearMap.inl ℂ H H))

/-- Lower-right block of an operator on `H × H`. -/
@[rep_depth operator]
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
The physical upper-right inter-sheet coupling is exactly the
superconducting pairing potential.
-/
@[rep_depth transport, capstone]
theorem xi_eq_delta_sc (h Δ : EndH) :
    block12 (H_BdG h Δ) = Δ :=
  block12_H_BdG h Δ

/-!
## 3. Complex-linear particle-hole intertwining proxy
-/

/--
Complex-linear Nambu sheet swap with an internal linear map `C₀`:

`(u,v) ↦ (C₀ v, C₀ u)`.

This is an algebraic linear proxy. A physical antiunitary particle-hole
operator requires conjugate-linearity or realification.
-/
@[rep_depth operator]
def PHS_operator (C₀ : EndH) : EndNambu :=
  (C₀.comp (ContinuousLinearMap.snd ℂ H H)).prod
    (C₀.comp (ContinuousLinearMap.fst ℂ H H))

@[simp]
theorem PHS_operator_apply (C₀ : EndH) (u v : H) :
    PHS_operator C₀ (u, v) = (C₀ v, C₀ u) := by
  simp [PHS_operator, ContinuousLinearMap.comp_apply]

/--
BdG particle-hole anticommutation for a supplied complex-linear
intertwining proxy.

The four hypotheses are exactly the four block identities needed for

`C H_BdG = - H_BdG C`.
-/
@[rep_depth operator]
theorem bdg_particle_hole_symmetry
    (h Δ C₀ : EndH)
    (h_comm1 :
      C₀.comp (ContinuousLinearMap.adjoint h) =
        h.comp C₀)
    (h_anti1 :
      C₀.comp (ContinuousLinearMap.adjoint Δ) =
        -(Δ.comp C₀))
    (h_comm2 :
      C₀.comp h =
        (ContinuousLinearMap.adjoint h).comp C₀)
    (h_anti2 :
      C₀.comp Δ =
        -((ContinuousLinearMap.adjoint Δ).comp C₀)) :
    (PHS_operator C₀).comp (H_BdG h Δ) =
      (-H_BdG h Δ).comp (PHS_operator C₀) := by

  have h1 (u : H) :
      C₀ (ContinuousLinearMap.adjoint Δ u) =
        -Δ (C₀ u) := by
    have hu :=
      congrArg (fun T : EndH => T u) h_anti1
    simpa [ContinuousLinearMap.comp_apply] using hu

  have h2 (v : H) :
      C₀ (ContinuousLinearMap.adjoint h v) =
        h (C₀ v) := by
    have hv :=
      congrArg (fun T : EndH => T v) h_comm1
    simpa [ContinuousLinearMap.comp_apply] using hv

  have h3 (u : H) :
      C₀ (h u) =
        ContinuousLinearMap.adjoint h (C₀ u) := by
    have hu :=
      congrArg (fun T : EndH => T u) h_comm2
    simpa [ContinuousLinearMap.comp_apply] using hu

  have h4 (v : H) :
      C₀ (Δ v) =
        -ContinuousLinearMap.adjoint Δ (C₀ v) := by
    have hv :=
      congrArg (fun T : EndH => T v) h_anti2
    simpa [ContinuousLinearMap.comp_apply] using hv

  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  apply Prod.ext

  · change
      C₀
          (ContinuousLinearMap.adjoint Δ u -
            ContinuousLinearMap.adjoint h v)
        =
      -(h (C₀ v) + Δ (C₀ u))
    rw [map_sub, h1 u, h2 v]
    abel

  · change
      C₀ (h u + Δ v)
        =
      -(ContinuousLinearMap.adjoint Δ (C₀ v) -
          ContinuousLinearMap.adjoint h (C₀ u))
    rw [map_add, h3 u, h4 v]
    abel

/-!
## 4. Canonical linear-swap specialization
-/

/--
For the pure Nambu swap `C₀ = 1`, self-adjoint normal dynamics together
with skew-adjoint pairing implies the linear proxy PHS relation.
-/
@[rep_depth operator]
theorem bdg_swap_particle_hole_symmetry
    (h Δ : EndH)
    (hh :
      ContinuousLinearMap.adjoint h = h)
    (hΔ :
      ContinuousLinearMap.adjoint Δ = -Δ) :
    (PHS_operator (ContinuousLinearMap.id ℂ H)).comp
        (H_BdG h Δ)
      =
    (-H_BdG h Δ).comp
        (PHS_operator (ContinuousLinearMap.id ℂ H)) := by
  apply bdg_particle_hole_symmetry
      h Δ (ContinuousLinearMap.id ℂ H)
  · simp [hh]
  · simp [hΔ]
  · simp [hh]
  · simp [hΔ]

/-!
## 5. Genuine inverse witness for the hole block
-/

/--
Invertibility of the physical hole block `-h†`.

Using a `ContinuousLinearEquiv` prevents an arbitrary endomorphism from
being incorrectly called an inverse.
-/
@[rep_depth operator]
structure InvertibleHoleBlock (h : EndH) where
  equiv : H ≃L[ℂ] H
  equiv_toContinuousLinearMap :
    equiv.toContinuousLinearMap = holeBlock h

namespace InvertibleHoleBlock

variable {h : EndH}
variable (I : InvertibleHoleBlock h)

/-- Genuine inverse of the physical hole block. -/
@[rep_depth operator]
def inverse : EndH :=
  I.equiv.symm.toContinuousLinearMap

@[simp]
theorem holeBlock_comp_inverse :
    (holeBlock h).comp I.inverse =
      ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change holeBlock h (I.equiv.symm x) = x
  rw [← I.equiv_toContinuousLinearMap]
  exact I.equiv.apply_symm_apply x

@[simp]
theorem inverse_comp_holeBlock :
    I.inverse.comp (holeBlock h) =
      ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change I.equiv.symm (holeBlock h x) = x
  rw [← I.equiv_toContinuousLinearMap]
  exact I.equiv.symm_apply_apply x

end InvertibleHoleBlock

/-!
## 6. Physical BdG Schur complement
-/

/--
Upper-sector Schur complement

`A - B D⁻¹ C`

for

`A = h`,
`B = Δ`,
`C = Δ†`,
`D = -h†`.
-/
@[rep_depth operator]
noncomputable def BdG_Schur_Complement
    (h Δ : EndH)
    (I : InvertibleHoleBlock h) : EndH :=
  h -
    Δ.comp
      (I.inverse.comp
        (ContinuousLinearMap.adjoint Δ))

@[simp]
theorem BdG_Schur_Complement_def
    (h Δ : EndH)
    (I : InvertibleHoleBlock h) :
    BdG_Schur_Complement h Δ I =
      h -
        Δ.comp
          (I.inverse.comp
            (ContinuousLinearMap.adjoint Δ)) :=
  rfl

/-!
## 7. Complete block packet
-/

@[rep_depth transport, capstone]
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

end InfoGeometry.Canonical.PhysicalBdGPairingBridgeComplex

end noncomputable section