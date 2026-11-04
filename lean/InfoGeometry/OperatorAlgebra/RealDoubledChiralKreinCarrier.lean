/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.Carrier.HestenesKreinHilbertization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint

/-!
# Hestenes--Krein carrier for the doubled chiral lane

This is the native carrier-level complement for the finite cross-sheet form.
The carrier is real-linear: the phase/Real structures are supplied separately
by `RealDoubledChiralKreinPhaseReal`.  No anti-linear Tomita operator is
introduced here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinCarrier

open InfoGeometry.Carrier
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Carrier := H₂ (E := E)

/-- The cross-sheet Krein pairing as a native bilinear form. -/
noncomputable def chiralKreinBilin : LinearMap.BilinForm ℝ (Carrier (E := E)) :=
  LinearMap.mk₂ ℝ
    (fun u v => chiralKreinForm u v)
    (by
      intro u₁ u₂ v
      simp [chiralKreinForm, WithLp.add_fst, WithLp.add_snd,
        inner_add_left]
      ac_rfl)
    (by
      intro c u v
      simp [chiralKreinForm, WithLp.smul_fst, WithLp.smul_snd,
        real_inner_smul_left]
      linear_combination)
    (by
      intro u v₁ v₂
      simp [chiralKreinForm, WithLp.add_fst, WithLp.add_snd,
        inner_add_right]
      ac_rfl)
    (by
      intro c u v
      simp [chiralKreinForm, WithLp.smul_fst, WithLp.smul_snd,
        real_inner_smul_right]
      linear_combination)

@[simp] theorem chiralKreinBilin_apply (u v : Carrier (E := E)) :
    chiralKreinBilin (E := E) u v = chiralKreinForm u v := rfl

theorem chiralKreinBilin_symmetric (u v : Carrier (E := E)) :
    chiralKreinBilin (E := E) u v = chiralKreinBilin (E := E) v u := by
  exact chiralKreinForm_swap (E := E) u v

/-- The doubled chiral carrier as a Hestenes--Krein space. -/
noncomputable def chiralHestenesKreinSpace : HestenesKreinSpace (Carrier (E := E)) where
  krein_form := chiralKreinBilin (E := E)
  J := (etaChiral (E := E)).toLinearMap
  J_involution := by
    apply LinearMap.ext
    intro u
    change etaChiral (E := E) (etaChiral (E := E) u) = u
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : Carrier (E := E) →L[ℝ] Carrier (E := E) => T u)
        (etaChiral_involution (E := E))
  induced_hilbert_identity := by
    intro u hu
    change 0 < chiralKreinForm u (etaChiral (E := E) u)
    rw [← chiralHilbertForm]
    exact chiralHilbertForm_self_pos (E := E) hu

theorem chiralHestenesKreinSpace_krein_form (u v : Carrier (E := E)) :
    (chiralHestenesKreinSpace (E := E)).krein_form u v =
      chiralKreinForm u v := rfl

theorem chiralHestenesKreinSpace_J (u : Carrier (E := E)) :
    (chiralHestenesKreinSpace (E := E)).J u = etaChiral (E := E) u := rfl

theorem chiralHestenesKreinSpace_induced_hilbert (u : Carrier (E := E)) :
    (chiralHestenesKreinSpace (E := E)).krein_form u
        ((chiralHestenesKreinSpace (E := E)).J u) =
      chiralHilbertForm (E := E) u u := by
  rfl

/-- The abstract symmetrized positive form agrees on all pairs with the
concrete real Hilbert pairing on the doubled chiral carrier. -/
theorem chiralHestenesKreinSpace_positiveBilinForm (u v : Carrier (E := E)) :
    (chiralHestenesKreinSpace (E := E)).positiveBilinForm u v =
      chiralHilbertForm (E := E) u v := by
  have hsym : chiralHilbertForm (E := E) v u =
      chiralHilbertForm (E := E) u v := by
    rw [chiralHilbertForm_eq_inner, chiralHilbertForm_eq_inner]
    exact real_inner_comm _ _
  simp only [InfoGeometry.Carrier.HestenesKreinSpace.positiveBilinForm,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.BilinForm.flip_apply,
    LinearMap.BilinForm.compRight_apply,
    chiralHestenesKreinSpace_krein_form, chiralHestenesKreinSpace_J]
  rw [← chiralHilbertForm, ← chiralHilbertForm, hsym]
  linear_combination

/-- The `InnerProductSpace.Core` constructed from the chiral Krein data has
exactly the pre-existing ambient real inner product as its pairing. -/
theorem chiralHestenesKreinSpace_core_inner (u v : Carrier (E := E)) :
    (chiralHestenesKreinSpace (E := E)).inducedInnerProductCore.inner u v =
      inner ℝ u v := by
  change (chiralHestenesKreinSpace (E := E)).positiveBilinForm u v = _
  rw [chiralHestenesKreinSpace_positiveBilinForm, chiralHilbertForm_eq_inner]

theorem chiralKreinBilin_nondegenerate :
    IsNondegeneratePairing (chiralKreinBilin (E := E)) := by
  intro u v huv
  apply ext_inner_right ℝ
  intro w
  have hfun := congrArg (fun φ : Module.Dual ℝ (Carrier (E := E)) =>
      φ (etaChiral (E := E) w)) huv
  change chiralKreinForm u (etaChiral (E := E) w) =
      chiralKreinForm v (etaChiral (E := E) w) at hfun
  rw [InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.chiralKreinForm_eq_inner_eta,
    InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.chiralKreinForm_eq_inner_eta]
    at hfun
  rw [InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.etaChiral_hilbert_isometry
      (E := E) u w,
    InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint.etaChiral_hilbert_isometry
      (E := E) v w] at hfun
  exact hfun

/-! ## Compatibility boundary with the root carrier -/

/-
The cross-sheet form is compatible with the flip, but the grading is
anti-invariant rather than invariant.  Therefore the repository's
`InvolutiveSelfDualCarrier` (which requires both invariances) is intentionally
not instantiated here.
-/
theorem chiralKreinForm_etaChiral_invariant (u v : Carrier (E := E)) :
    chiralKreinForm (etaChiral (E := E) u) (etaChiral (E := E) v) =
      chiralKreinForm u v := by
  simp [chiralKreinForm, etaChiral, modular_j,
    WithLp.prod_inner_apply, real_inner_comm, add_comm]

theorem chiralKreinForm_gamma5_anti_invariant (u v : Carrier (E := E)) :
    chiralKreinForm (gamma5 (E := E) u) (gamma5 (E := E) v) =
      -chiralKreinForm u v := by
  simp [chiralKreinForm, gamma5, spectral_epsilon,
    WithLp.prod_inner_apply, sub_eq_add_neg, add_comm]

/-
The following root-carrier attempt is deliberately not provided: `gamma5`
anticommutes with `etaChiral`, but it reverses the cross-sheet pairing.
-/
/-
noncomputable def chiralInvolutiveSelfDualCarrier : InvolutiveSelfDualCarrier where
  H := Carrier (E := E)
  kreinPairing := chiralKreinBilin (E := E)
  J := etaChiral (E := E)
  ε := gamma5 (E := E)
  J_sq := etaChiral_involution (E := E)
  ε_sq := gamma5_involution (E := E)
  J_ε_anticomm := etaChiral_gamma5_anticommute (E := E)
  pairing_symm := by
    intro u v
    exact chiralKreinForm_swap (E := E) u v
  pairing_J_invariant := by
    intro u v
    simp [chiralKreinBilin, chiralKreinForm, etaChiral, modular_j,
      WithLp.prod_inner_apply, real_inner_comm, add_comm]
  pairing_ε_invariant := by
    intro u v
    simp [chiralKreinBilin, chiralKreinForm, gamma5, spectral_epsilon,
      WithLp.prod_inner_apply, add_comm]
  pairing_nondegenerate := by
    intro u v huv
    apply ext_inner_right ℝ
    intro w
    have hfun := congrArg (fun φ : Module.Dual ℝ (Carrier (E := E)) =>
      φ (etaChiral (E := E) w)) huv
    change chiralKreinForm u (etaChiral (E := E) w) =
      chiralKreinForm v (etaChiral (E := E) w) at hfun
    rw [chiralKreinForm_eq_inner_eta, chiralKreinForm_eq_inner_eta] at hfun
    simpa [etaChiral_hilbert_isometry (E := E)] using hfun

theorem chiralInvolutiveSelfDualCarrier_pairing (u v : Carrier (E := E)) :
    (chiralInvolutiveSelfDualCarrier (E := E)).kreinPairing u v =
      chiralKreinForm u v := rfl
-/

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinCarrier
