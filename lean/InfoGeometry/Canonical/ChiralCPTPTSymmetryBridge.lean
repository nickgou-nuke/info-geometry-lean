import InfoGeometry.OperatorAlgebra.CPTSymmetryBranch
import InfoGeometry.Canonical.ChiralModularTomitaBridge
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

noncomputable section

namespace InfoGeometry.Canonical.ChiralCPTPTSymmetryBridge

open InfoGeometry.OperatorAlgebra.CPTSymmetryBranch
open InfoGeometry.Canonical.ChiralModularTomitaBridge
open InfoGeometry.Topology.DiscreteHodgeDiracBridge

abbrev EndR (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  H →L[ℝ] H

/-!
This is the native operator-level complement of the existing CPT branch.  CPT
uses `ModularChiralCPTMirror`; PT is recorded separately because the repository
does not identify a Krein fundamental symmetry with Tomita conjugation.
-/
/-! ## Canonical doubled-carrier PT specialization

The abstract packet above deliberately leaves the PT fundamental symmetry as
data.  On the repository's canonical doubled Krein carrier the PT operator is
already owned by `RealDoubledChiralKrein`: it is `etaSplit`, while the chiral
grading is `gamma5`.  The following specialization records that identification
without identifying PT with the Tomita/CPT mirror.
-/

namespace CanonicalDoubledCarrier

open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.Krein

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH₂" => H₂ →L[ℝ] H₂

noncomputable abbrev canonicalPT : EndH₂ := etaSplit (E := E)

theorem canonicalPT_sq :
    (canonicalPT (E := E)).comp (canonicalPT (E := E)) =
      ContinuousLinearMap.id ℝ H₂ := by
  simpa [canonicalPT, etaSplit] using
    (spectral_epsilon_involution E)

theorem canonicalPT_isBlockDiagonal :
    IsBlockDiagonal (canonicalPT (E := E)) := by
  simpa [canonicalPT] using
    (etaSplit_isBlockDiagonal (E := E))

theorem canonicalChiralGrading_sq :
    (gamma5 (E := E)).comp (gamma5 (E := E)) =
      ContinuousLinearMap.id ℝ H₂ := by
  simpa [gamma5] using (spectral_epsilon_involution E)

theorem canonicalPT_is_not_Tomita_by_definition :
    canonicalPT (E := E) = etaSplit (E := E) := by
  rfl

theorem canonicalPT_is_fundamental_symmetry :
    (canonicalPT (E := E)).comp (canonicalPT (E := E)) =
        ContinuousLinearMap.id ℝ H₂ ∧
      IsBlockDiagonal (canonicalPT (E := E)) := by
  exact ⟨canonicalPT_sq (E := E), canonicalPT_isBlockDiagonal (E := E)⟩

theorem canonicalPT_preserves_inner (u v : H₂) :
    inner (𝕜 := ℝ) (canonicalPT (E := E) u) (canonicalPT (E := E) v) =
      inner (𝕜 := ℝ) u v := by
  calc
    inner (𝕜 := ℝ) (canonicalPT (E := E) u) (canonicalPT (E := E) v) =
        inner (𝕜 := ℝ) u
          (canonicalPT (E := E) (canonicalPT (E := E) v)) := by
            simpa [canonicalPT, etaSplit] using
              (spectral_epsilon_selfAdj (E := E) u
                (spectral_epsilon (E := E) v))
    _ = inner (𝕜 := ℝ) u v := by
      have h := congrArg (fun T : EndH₂ => T v)
        (spectral_epsilon_involution E)
      simpa [canonicalPT, etaSplit, ContinuousLinearMap.comp_apply] using
        congrArg (fun w : H₂ => inner (𝕜 := ℝ) u w) h

noncomputable def canonicalCPTMirror :
    ModularChiralCPTMirror (DoubledSpace E) where
  J := modular_j (E := E)
  grading := {
    chi := gamma5 (E := E)
    chi_square := gamma5_involution (E := E)
  }
  J_square := modular_j_involution E
  J_flips_chi := by
    simpa [gamma5] using modular_j_spectral_epsilon_anticommute E
  J_metric := by
    intro u v
    simp [modular_j, WithLp.prod_inner_apply, add_comm]

theorem canonicalCPTMirror_J_eq_modular_j :
    (canonicalCPTMirror (E := E)).J = modular_j (E := E) := by
  rfl

theorem canonicalCPTMirror_chi_eq_gamma5 :
    (canonicalCPTMirror (E := E)).grading.chi = gamma5 (E := E) := by
  rfl

theorem canonicalCPTMirror_uses_canonical_PT :
    canonicalPT (E := E) = etaSplit (E := E) ∧
      (canonicalCPTMirror (E := E)).grading.chi = gamma5 (E := E) := by
  exact ⟨rfl, rfl⟩

/-! ## Canonical specialization of the existing chiral interface

`etaSplit` is the independently owned block-diagonal Krein fundamental
symmetry.  It is not the native arrow-exchanging intertwiner for the root
chiral operators.  The latter is the already derived `modular_jLE`, appearing
as `J` in `rootChiralTomitaData`; no new intertwining hypotheses are needed.
-/

noncomputable def canonicalPTIntertwiner :
    PTIntertwinerData (rootChiralTomitaData E) where
  eta := modular_jLE E
  eta_sq := (rootChiralTomitaData E).J_sq
  eta_conjugates_d_to_delta :=
    (rootChiralTomitaData E).J_conjugates_d_to_delta
  eta_conjugates_delta_to_d :=
    ModularHodgeConjugationData.J_conjugates_delta_to_d
      (rootChiralTomitaData E)

theorem canonicalPTIntertwiner_eta_eq_modularJ :
    (canonicalPTIntertwiner (E := E)).eta.toLinearMap =
      (modular_jLE E).toLinearMap := by
  rfl

theorem canonicalPTIntertwiner_eta_is_not_etaSplit_by_definition :
    (canonicalPTIntertwiner (E := E)).eta.toLinearMap =
      (modular_jLE E).toLinearMap ∧
    (canonicalPT (E := E)).toLinearMap =
      (spectral_epsilonLE E).toLinearMap := by
  exact ⟨rfl, rfl⟩

theorem canonical_doubled_tomita_pt_duality :
    ((rootChiralTomitaData E).J.toLinearMap.comp
        (chiralDiracPlus (rootChiralTomitaData E)) =
      (chiralDiracPlus (rootChiralTomitaData E)).comp
        (rootChiralTomitaData E).J.toLinearMap) ∧
    ((rootChiralTomitaData E).J.toLinearMap.comp
        (chiralDiracMinus (rootChiralTomitaData E)) =
      -(chiralDiracMinus (rootChiralTomitaData E)).comp
        (rootChiralTomitaData E).J.toLinearMap) ∧
    ((canonicalPTIntertwiner (E := E)).eta.toLinearMap.comp
        (chiralDiracPlus (rootChiralTomitaData E)) =
      (chiralDiracPlus (rootChiralTomitaData E)).comp
        (canonicalPTIntertwiner (E := E)).eta.toLinearMap) ∧
    ((canonicalPTIntertwiner (E := E)).eta.toLinearMap.comp
        (chiralDiracMinus (rootChiralTomitaData E)) =
      -(chiralDiracMinus (rootChiralTomitaData E)).comp
        (canonicalPTIntertwiner (E := E)).eta.toLinearMap) := by
  exact PTIntertwinerData.tomita_pt_duality
    (canonicalPTIntertwiner (E := E))

end CanonicalDoubledCarrier

end InfoGeometry.Canonical.ChiralCPTPTSymmetryBridge
