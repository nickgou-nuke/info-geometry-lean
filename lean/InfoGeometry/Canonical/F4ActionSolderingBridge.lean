import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Faithful coordinate soldering for the split-Albert derivation action

The matrix certificate and the native endomorphism carrier are distinct
objects.  This file supplies their faithful coordinate readout and records
the remaining coefficient-identification proposition explicitly.
-/

noncomputable section

namespace InfoGeometry.Canonical.F4ActionSolderingBridge

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

abbrev EndH3 := Module.End ℝ (H3Zorn ℝ)
abbrev FlatAction := Fin 729 → ℝ

noncomputable def actionSoldering : EndH3 →ₗ[ℝ] FlatAction where
  toFun D := fun k =>
    (h3ZornCoordinateBasis.repr
      (D (h3ZornCoordinateBasis ⟨k.val / 27, by omega⟩)))
      ⟨k.val % 27, by omega⟩
  map_add' D E := by ext k; simp
  map_smul' r D := by ext k; simp

theorem actionSoldering_injective : Function.Injective actionSoldering := by
  intro D E h
  apply LinearMap.ext
  intro x
  apply h3ZornCoordinateBasis.repr.injective
  ext c
  have hs : ∀ r : Fin 27,
      (h3ZornCoordinateBasis.repr (D (h3ZornCoordinateBasis r))) c =
      (h3ZornCoordinateBasis.repr (E (h3ZornCoordinateBasis r))) c := by
    intro r
    let k : Fin 729 := ⟨27 * r.val + c.val, by omega⟩
    have hr : (⟨k.val / 27, by omega⟩ : Fin 27) = r := Fin.ext (by dsimp [k]; omega)
    have hc : (⟨k.val % 27, by omega⟩ : Fin 27) = c := Fin.ext (by dsimp [k]; omega)
    have hk := congrFun h k
    dsimp [actionSoldering] at hk
    rw [hr, hc] at hk
    exact hk
  have hx := h3ZornCoordinateBasis.sum_repr x
  conv_lhs => rw [← hx]
  conv_rhs => rw [← hx]
  simp only [map_sum, map_smul]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hs r]

theorem actionSoldering_f4Basis (i : Fin 52) :
    actionSoldering ((f4Basis i).1 : EndH3) = f4ActionMatrix i := by
  ext k
  let r : Fin 27 := ⟨k.val / 27, by omega⟩
  let c : Fin 27 := ⟨k.val % 27, by omega⟩
  have hkfin : k = ⟨27 * r.val + c.val, by omega⟩ := Fin.ext (by dsimp [r, c]; omega)
  conv_rhs => rw [hkfin]
  rw [f4BasisActionMatrix_flatten, f4BasisActionMatrix_readback]
  rfl

/-- The exact coefficient equality needed to solder the rational certificate
to the native action.  It is intentionally a proposition, not an axiom or a
proxy witness; downstream rank transfer requires an explicit proof of it. -/
def CertificateIsSoldered : Prop :=
  ∀ i : Fin 52,
    f4ActionMatrixReal i =
      actionSoldering ((f4Basis i).1 : EndH3)

theorem f4Basis_linearIndependent_of_soldering
    (hS : CertificateIsSoldered) :
    LinearIndependent ℝ (fun i : Fin 52 => ((f4Basis i).1 : EndH3)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsolder := congrArg actionSoldering hg
  simp only [map_sum, map_smul, map_zero] at hsolder
  have hcert : ∑ j : Fin 52, g j • f4ActionMatrixReal j = 0 := by
    calc
      ∑ j : Fin 52, g j • f4ActionMatrixReal j =
          ∑ j : Fin 52, g j • actionSoldering ((f4Basis j).1 : EndH3) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hS j]
      _ = 0 := hsolder
  have hLI := (Fintype.linearIndependent_iff.mp f4ActionMatrixReal_linearIndependent)
  exact hLI g hcert i

theorem finrank_f4BasisSpan_eq_52_of_soldering
    (hS : CertificateIsSoldered) :
    Module.finrank ℝ f4BasisSpan = 52 := by
  have hLI := f4Basis_linearIndependent_of_soldering hS
  simpa [f4BasisSpan] using finrank_span_eq_card hLI

end InfoGeometry.Canonical.F4ActionSolderingBridge
