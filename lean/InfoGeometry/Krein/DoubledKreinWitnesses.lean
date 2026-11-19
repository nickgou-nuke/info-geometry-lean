/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledAdjoint
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Pairing-sensitive Krein Gram witnesses on the doubled Hilbert carrier

We use the existing positive spectral projector `P_plus` and sheet swap
`modular_j` to form the opposite one-way transfers `P_plus ∘ modular_j` and
`modular_j ∘ P_plus`. They act as `(x,y) ↦ (y,0)` and `(x,y) ↦ (0,x)`.
Local notation retains these existing operator compositions without introducing
a second exported transfer API. We compute their adjoints, ordered Gram
products, and the different signs of the Hilbert and Krein pairings.

The equivalent `Cl11Dictionary.nullAnnihilation`/`nullCreation` operators already
have square-zero and CAR theorems. The projector compositions used here avoid
importing that owner's additional geometric and Tomita dependency chain.

The carrier is `DoubledSpace E = WithLp 2 (E × E)` for an arbitrary complete
real inner product space, including infinite-dimensional choices of `E`.
The operators live in its noncommutative algebra of bounded endomorphisms.
No physical state-space interpretation, exceptional Lie group, complexified
spectrum, or exponential evolution is asserted.

`complex_i_sq`, `modular_j_involution`, and `modular_j_kreinSkewAdjoint`
are reused from the existing doubled-space owners, rather than reproved.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledKreinWitnesses

open KreinSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "upperTransfer" =>
  (P_plus (H := DoubledSpace E)).comp (modular_j (E := E))
local notation "lowerTransfer" =>
  (modular_j (E := E)).comp (P_plus (H := DoubledSpace E))

private theorem doubled_jCLM_eq :
    jCLM (H := DoubledSpace E) = spectral_epsilon (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> rfl

@[simp] private theorem positiveProjector_apply (u : DoubledSpace E) :
    P_plus u = to_doubled (WithLp.fst u) 0 := by
  change ((⅟(2 : ℝ)) • ((1 : DoubledSpace E →L[ℝ] DoubledSpace E) +
    jCLM (H := DoubledSpace E))) u = _
  rw [doubled_jCLM_eq]
  apply DoubledSpace.ext <;>
    simp [spectral_epsilon, invOf_eq_inv, to_doubled] <;> module

@[simp] private theorem upperTransfer_apply (u : DoubledSpace E) :
    upperTransfer u = to_doubled (WithLp.snd u) 0 := by
  change P_plus (modular_j u) = _
  exact positiveProjector_apply (modular_j u)

@[simp] private theorem lowerTransfer_apply (u : DoubledSpace E) :
    lowerTransfer u = to_doubled 0 (WithLp.fst u) := by
  change modular_j (P_plus u) = _
  rw [positiveProjector_apply, modular_j_to_doubled]

/-- The positive-sheet transfer is square-zero as an actual bounded operator. -/
theorem upperTransfer_sq : (upperTransfer).comp upperTransfer = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [ContinuousLinearMap.comp_apply, to_doubled]

theorem lowerTransfer_sq : (lowerTransfer).comp lowerTransfer = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [ContinuousLinearMap.comp_apply, to_doubled]

/-- The Hilbert adjoint reverses the one-way transfer. -/
theorem upperTransfer_adjoint :
    ContinuousLinearMap.adjoint (upperTransfer) = lowerTransfer := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp [WithLp.prod_inner_apply, to_doubled]

theorem lowerTransfer_adjoint :
    ContinuousLinearMap.adjoint (lowerTransfer) = upperTransfer := by
  have h := congrArg ContinuousLinearMap.adjoint (upperTransfer_adjoint (E := E))
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h.symm

/-- The Krein adjoint introduces the opposite sign on the reversed transfer. -/
theorem upperTransfer_kreinAdjoint :
    kreinAdjoint (upperTransfer) = -lowerTransfer := by
  rw [kreinAdjoint, upperTransfer_adjoint, doubled_jCLM_eq]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, spectral_epsilon, to_doubled]

theorem lowerTransfer_kreinAdjoint :
    kreinAdjoint (lowerTransfer) = -upperTransfer := by
  rw [kreinAdjoint, lowerTransfer_adjoint, doubled_jCLM_eq]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, spectral_epsilon, to_doubled]

/-- The negative-sheet Gram operator is minus the corresponding ordered
round trip. The order of the two transfers is retained. -/
theorem upperTransfer_kreinGram :
    (kreinAdjoint (upperTransfer)).comp upperTransfer =
      -((lowerTransfer).comp upperTransfer) := by
  rw [upperTransfer_kreinAdjoint, ContinuousLinearMap.neg_comp]

/-- Reversing the transfer gives minus the positive-sheet round trip. -/
theorem lowerTransfer_kreinGram :
    (kreinAdjoint (lowerTransfer)).comp lowerTransfer =
      -((upperTransfer).comp lowerTransfer) := by
  rw [lowerTransfer_kreinAdjoint, ContinuousLinearMap.neg_comp]

/-- Coordinate readback of `diag(0,-Id)` on the existing doubled carrier. -/
theorem upperTransfer_kreinGram_apply (u : DoubledSpace E) :
    kreinAdjoint (upperTransfer) (upperTransfer u) =
      to_doubled 0 (-WithLp.snd u) := by
  rw [upperTransfer_kreinAdjoint]
  apply DoubledSpace.ext <;> simp [to_doubled]

/-- Coordinate readback of `diag(-Id,0)` on the existing doubled carrier. -/
theorem lowerTransfer_kreinGram_apply (u : DoubledSpace E) :
    kreinAdjoint (lowerTransfer) (lowerTransfer u) =
      to_doubled (-WithLp.fst u) 0 := by
  rw [lowerTransfer_kreinAdjoint]
  apply DoubledSpace.ext <;> simp [to_doubled]

/-- The Hilbert expectation of the upper-transfer Krein Gram is nonpositive. -/
theorem upperTransfer_hilbert_expectation (u : DoubledSpace E) :
    ⟪u, kreinAdjoint (upperTransfer) (upperTransfer u)⟫_ℝ =
      -⟪WithLp.snd u, WithLp.snd u⟫_ℝ := by
  rw [upperTransfer_kreinGram_apply]
  simp [WithLp.prod_inner_apply, to_doubled]

/-- The Krein expectation of that same operator has the opposite sign. -/
theorem upperTransfer_krein_expectation (u : DoubledSpace E) :
    kreinInner u (kreinAdjoint (upperTransfer) (upperTransfer u)) =
      ⟪WithLp.snd u, WithLp.snd u⟫_ℝ := by
  rw [upperTransfer_kreinGram_apply, krein_inner_prod_l2]
  simp [to_doubled]

theorem lowerTransfer_hilbert_expectation (u : DoubledSpace E) :
    ⟪u, kreinAdjoint (lowerTransfer) (lowerTransfer u)⟫_ℝ =
      -⟪WithLp.fst u, WithLp.fst u⟫_ℝ := by
  rw [lowerTransfer_kreinGram_apply]
  simp [WithLp.prod_inner_apply, to_doubled]

/-- The reversed transfer gives a genuinely negative Krein expectation on
every nonzero positive-sheet vector. -/
theorem lowerTransfer_krein_expectation (u : DoubledSpace E) :
    kreinInner u (kreinAdjoint (lowerTransfer) (lowerTransfer u)) =
      -⟪WithLp.fst u, WithLp.fst u⟫_ℝ := by
  rw [lowerTransfer_kreinGram_apply, krein_inner_prod_l2]
  simp [to_doubled]

/-- The input example has negative Hilbert expectation but positive Krein
expectation on `(0,v)`; these pairings cannot be interchanged. -/
theorem upperTransfer_opposite_expectation_signs (v : E) (hv : v ≠ 0) :
    ⟪to_doubled 0 v,
      kreinAdjoint (upperTransfer)
        (upperTransfer (to_doubled 0 v))⟫_ℝ < 0 ∧
      0 < kreinInner (to_doubled 0 v)
        (kreinAdjoint (upperTransfer)
          (upperTransfer (to_doubled 0 v))) := by
  rw [upperTransfer_hilbert_expectation, upperTransfer_krein_expectation]
  simpa using And.intro (neg_neg_of_pos (real_inner_self_pos.mpr hv))
    (real_inner_self_pos.mpr hv)

theorem lowerTransfer_negative_krein_expectation (v : E) (hv : v ≠ 0) :
    kreinInner (to_doubled v 0)
      (kreinAdjoint (lowerTransfer)
        (lowerTransfer (to_doubled v 0))) < 0 := by
  rw [lowerTransfer_krein_expectation]
  simpa using neg_neg_of_pos (real_inner_self_pos.mpr hv)

/-- The one-way transfers really fail to commute on every nontrivial `E`. -/
theorem transfers_not_commute [Nontrivial E] :
    (upperTransfer).comp lowerTransfer ≠
      (lowerTransfer).comp upperTransfer := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  intro h
  have hc := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E =>
    WithLp.fst (T (to_doubled v 0))) h
  exact hv (by simpa [ContinuousLinearMap.comp_apply, to_doubled] using hc)

/-- The canonical real square-minus-identity generator is Krein-self-adjoint.
Its sign is the negative of the matrix `H` in the intake; either sign has
the same square and the same self-adjointness property. -/
theorem complex_i_kreinSelfAdjoint :
    IsKreinSelfAdjoint (complex_i (E := E)) := by
  apply (isKreinSelfAdjoint_iff _).mpr
  intro u v
  rw [krein_inner_prod_l2, krein_inner_prod_l2]
  simp [complex_i_apply, sub_eq_add_neg, add_comm]

/-- A real bounded operator whose square is `-Id` has no nonzero real
eigenvector. No spectral theorem or complexification is used. -/
theorem eq_zero_of_sq_neg_id_eigenvector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H →L[ℝ] H) (hA : A.comp A = -(ContinuousLinearMap.id ℝ H))
    (t : ℝ) (v : H) (hv : A v = t • v) : v = 0 := by
  have hsq : A (A v) = -v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply] using
      congrArg (fun T : H →L[ℝ] H => T v) hA
  rw [hv, map_smul, hv, smul_smul] at hsq
  have hz : (t * t + 1) • v = 0 := by
    rw [add_smul, one_smul, hsq, neg_add_cancel]
  apply (smul_eq_zero.mp hz).resolve_left
  nlinarith [sq_nonneg t]

theorem complex_i_no_real_eigenvector (t : ℝ) (v : DoubledSpace E) (hv : v ≠ 0) :
    complex_i (E := E) v ≠ t • v := by
  intro h
  exact hv (eq_zero_of_sq_neg_id_eigenvector _ (complex_i_sq E) t v h)

end InfoGeometry.Krein.DoubledKreinWitnesses
