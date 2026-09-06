import InfoGeometry.External.Auto.SU3LoopBraidDuality

/-!
# Finite S₃ action on color-spinor lanes

This module records the theorem-backed finite shadow of the proposed S₃ color
spinor decomposition.  A color spinor consists definitionally of three color
lanes and one singlet lane.  Color permutations preserve the singlet lane,
permute the three color lanes, and transport diagonal gauge weights.
-/

noncomputable section

namespace S3ColorSpinorDecomposition

open BogoliubovBraidGraphWeld
open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open SU3LoopBraidDuality

/-- Permuting color lanes leaves the separate singlet lane fixed. -/
theorem singlet_lane_invariant {V : Type*} (π : Equiv.Perm (Fin 3))
    (ψ : ColorSpinor4 V) :
    (permuteColorSpinor4 π ψ).2 = ψ.2 := rfl

/-- The color component is transported exactly by the supplied permutation. -/
theorem color_triplet_stable {V : Type*} (π : Equiv.Perm (Fin 3))
    (ψ : ColorSpinor4 V) (i : Fin 3) :
    (permuteColorSpinor4 π ψ).1 i = ψ.1 (π i) := rfl

/-- A constant color gauge weight is invariant under every color permutation,
so its gauge step commutes with the q-scaled braid action. -/
theorem symmetric_color_combination_is_singlet {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (π : Equiv.Perm (Fin 3)) (s : ℂ) (ψ : ColorSpinor4 V) :
    qColorBraid4 q π (cantorLoopGaugeStep4 (fun _ => (1 : ℂ)) s ψ) =
      cantorLoopGaugeStep4 (fun _ => (1 : ℂ)) s (qColorBraid4 q π ψ) :=
  qColorBraid4_commutes_with_invariant_cantorLoopGaugeStep4
    q π (fun _ => (1 : ℂ)) s (by intro i; rfl) ψ

/-- Braiding transports arbitrary diagonal gauge weights along the same color
permutation. -/
theorem braid_gauge_covariance {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (π : Equiv.Perm (Fin 3)) (w : Fin 3 → ℂ) (s : ℂ)
    (ψ : ColorSpinor4 V) :
    qColorBraid4 q π (cantorLoopGaugeStep4 w s ψ) =
      cantorLoopGaugeStep4 (fun i => w (π i)) s (qColorBraid4 q π ψ) :=
  qColorBraid4_cantorLoopGaugeStep4_covariant q π w s ψ

/-- Consolidated permutation, braid, and gauge covariance theorem. -/
theorem color_spinor_3_plus_1_split_synthesis {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (q : ℂ) (π : Equiv.Perm (Fin 3)) (w : Fin 3 → ℂ) (s : ℂ)
    (ψ : ColorSpinor4 V) :
    (permuteColorSpinor4 π ψ).2 = ψ.2 ∧
    (∀ i : Fin 3, (permuteColorSpinor4 π ψ).1 i = ψ.1 (π i)) ∧
    qColorBraid4 q π (cantorLoopGaugeStep4 w s ψ) =
      cantorLoopGaugeStep4 (fun i => w (π i)) s (qColorBraid4 q π ψ) :=
  ⟨singlet_lane_invariant π ψ,
    fun i => color_triplet_stable π ψ i,
    braid_gauge_covariance q π w s ψ⟩

end S3ColorSpinorDecomposition

end noncomputable section
