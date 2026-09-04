import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
import InfoGeometry.Algebra.SplitAlbertF4BasisTrace
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Faithful coordinate soldering for the native split-Albert derivation action

The 27-dimensional `H3Zorn` coordinate basis separates endomorphisms by their
values on basis probes and scalar coordinate readouts.  This file packages
that fact as one linear map into the flattened 729-coordinate action space.

The point is architectural: a matrix certificate need not be identified with
an abstract F4 model.  It only needs to be soldered to this faithful readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.F4ActionSolderingBridge

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

abbrev EndH3 := Module.End ℝ (H3Zorn ℝ)
abbrev FlatAction := Fin 729 → ℝ

/-- Flattened coordinate readout of an arbitrary endomorphism of the native
27-dimensional split-Albert carrier. -/
noncomputable def actionSoldering : EndH3 →ₗ[ℝ] FlatAction where
  toFun D := fun k =>
    (h3ZornCoordinateBasis.repr
      (D (h3ZornCoordinateBasis
        ⟨k.val / 27, by omega⟩)))
      ⟨k.val % 27, by omega⟩
  map_add' D E := by
    ext k
    simp
  map_smul' r D := by
    ext k
    simp

/-- The soldering readout separates endomorphisms: equality of all 729
coordinate entries forces equality of the native linear maps. -/
theorem actionSoldering_injective : Function.Injective actionSoldering := by
  intro D E h
  apply LinearMap.ext
  intro x
  apply h3ZornCoordinateBasis.repr.injective
  ext c
  have hx := h3ZornCoordinateBasis.sum_repr x
  rw [hx]
  simp only [map_sum, map_smul, Finsupp.sum_apply_index]
  have hs : ∀ r : Fin 27,
      (h3ZornCoordinateBasis.repr
        (D (h3ZornCoordinateBasis r))) c =
      (h3ZornCoordinateBasis.repr
        (E (h3ZornCoordinateBasis r))) c := by
    intro r
    let k : Fin 729 := ⟨27 * r.val + c.val, by omega⟩
    have hk := congrFun h k
    change actionSoldering D k = actionSoldering E k at hk
    simpa [actionSoldering] using hk
  simp_rw [map_sum, map_smul, Finsupp.sum_apply_index]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hs r]

/-- On the actual native `f4Basis`, soldering is exactly the repository's
flattened action row. -/
theorem actionSoldering_f4Basis (i : Fin 52) :
    actionSoldering ((f4Basis i).1 : EndH3) = f4ActionMatrix i := by
  ext k
  let r : Fin 27 := ⟨k.val / 27, by omega⟩
  let c : Fin 27 := ⟨k.val % 27, by omega⟩
  have hk : k.val = 27 * r.val + c.val := by
    dsimp [r, c]
    omega
  have hkfin : k = ⟨27 * r.val + c.val, by omega⟩ := by
    apply Fin.ext
    exact hk
  subst hkfin
  rw [f4BasisActionMatrix_flatten]
  rw [f4BasisActionMatrix_readback]
  rfl

/-- The single remaining certificate-soldering condition: the certified real
row family agrees with the faithful native action readout. -/
def CertificateIsSoldered : Prop :=
  ∀ i : Fin 52,
    f4ActionMatrixReal i =
      actionSoldering ((f4Basis i).1 : EndH3)

/-- Once the certificate is soldered to the native action, its exact rank-52
certificate transfers immediately to linear independence of the genuine
`f4Basis` derivations. -/
theorem f4Basis_linearIndependent_of_soldering
    (hS : CertificateIsSoldered) :
    LinearIndependent ℝ (fun i : Fin 52 => ((f4Basis i).1 : EndH3)) := by
  apply LinearIndependent.of_comp actionSoldering
  simpa [CertificateIsSoldered, hS] using
    f4ActionMatrixReal_linearIndependent

/-- The native span of the 52 actual derivations therefore has exact finrank
52 as soon as the certificate/readout soldering equation is supplied. -/
theorem finrank_f4BasisSpan_eq_52_of_soldering
    (hS : CertificateIsSoldered) :
    Module.finrank ℝ f4BasisSpan = 52 := by
  have hLI := f4Basis_linearIndependent_of_soldering hS
  have h := finrank_span_eq_card hLI
  simpa [f4BasisSpan] using h

/-- Soldering reduces the remaining F4 carrier theorem to generation of the
native derivation Lie subalgebra by the already-independent 52-element span. -/
theorem finrank_F4Derivations_eq_52_of_soldering_and_generation
    (hS : CertificateIsSoldered)
    (hgen : f4BasisSpan = H3ZornF4Derivations) :
    Module.finrank ℝ H3ZornF4Derivations = 52 := by
  rw [← hgen]
  exact finrank_f4BasisSpan_eq_52_of_soldering hS

end InfoGeometry.Canonical.F4ActionSolderingBridge
