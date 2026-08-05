import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import InfoGeometry.Topology.DiscreteHodgeDiracBridge

namespace InfoGeometry.Canonical.ChiralModularTomitaBridge

open InfoGeometry.Topology.DiscreteHodgeDiracBridge
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Canonical.ChiralHodgeDecomposition

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The existing native modular packet, viewed from the chiral-Hodge bridge. -/
abbrev ChiralTomitaData := ModularHodgeConjugationData

abbrev chiralDiracPlus (H : ChiralTomitaData V) : V →ₗ[ℝ] V :=
  ModularHodgeConjugationData.diracPlus H

abbrev chiralDiracMinus (H : ChiralTomitaData V) : V →ₗ[ℝ] V :=
  ModularHodgeConjugationData.diracMinus H

theorem chiral_tomita_intertwiner_plus
    (H : ChiralTomitaData V) :
    H.J.toLinearMap.comp (chiralDiracPlus H) =
      (chiralDiracPlus H).comp H.J.toLinearMap :=
  ModularHodgeConjugationData.J_intertwines_diracPlus H

theorem chiral_tomita_antiintertwiner_minus
    (H : ChiralTomitaData V) :
    H.J.toLinearMap.comp (chiralDiracMinus H) =
      -(chiralDiracMinus H).comp H.J.toLinearMap :=
  ModularHodgeConjugationData.J_antiintertwines_diracMinus H

theorem chiral_tomita_plus_square
    (H : ChiralTomitaData V) :
    (chiralDiracPlus H).comp (chiralDiracPlus H) =
      H.d.comp H.delta + H.delta.comp H.d :=
  ModularHodgeConjugationData.diracPlus_sq H

theorem chiral_tomita_minus_square
    (H : ChiralTomitaData V) :
    (chiralDiracMinus H).comp (chiralDiracMinus H) =
      -(H.d.comp H.delta + H.delta.comp H.d) :=
  ModularHodgeConjugationData.diracMinus_sq H

theorem chiral_tomita_plus_minus_anticommute
    (H : ChiralTomitaData V) :
    (chiralDiracPlus H).comp (chiralDiracMinus H) +
        (chiralDiracMinus H).comp (chiralDiracPlus H) = 0 :=
  ModularHodgeConjugationData.diracPlus_diracMinus_anticommute H

/-! ## Identification with the native doubled chiral arrows

The existing root operators are off-diagonal arrows.  They are not renamed
to `D₊` and `D₋`: the sum of the arrows is the odd root lane, while their
difference is the corresponding difference operator.
-/

noncomputable def rootChiralTomitaData
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    ChiralTomitaData (DoubledSpace E) where
  J := modular_jLE E
  J_sq := by
    apply LinearEquiv.ext
    intro u
    change modular_j (E := E) (modular_j (E := E) u) = u
    apply DoubledSpace.ext <;> simp [modular_j_apply]
  d := (rootDiracPlus (E := E)).toLinearMap
  delta := (rootDiracMinus (E := E)).toLinearMap
  d_sq := by
    apply LinearMap.ext
    intro u
    rw [LinearMap.comp_apply]
    change rootDiracPlus (E := E) (rootDiracPlus (E := E) u) = 0
    rw [rootDiracPlus_apply]
    apply DoubledSpace.ext <;> simp [plusPoint, minusPoint]
  delta_sq := by
    apply LinearMap.ext
    intro u
    rw [LinearMap.comp_apply]
    change rootDiracMinus (E := E) (rootDiracMinus (E := E) u) = 0
    rw [rootDiracMinus_apply]
    apply DoubledSpace.ext <;> simp [plusPoint, minusPoint]
  J_conjugates_d_to_delta := by
    apply LinearMap.ext
    intro u
    change modular_j (E := E) (rootDiracPlus (E := E) u) =
      rootDiracMinus (E := E) (modular_j (E := E) u)
    rw [rootDiracPlus_apply, rootDiracMinus_apply]
    apply DoubledSpace.ext <;> simp [plusPoint, minusPoint, modular_j_apply]

theorem root_chiral_plus_eq_odd_lane
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    chiralDiracPlus (rootChiralTomitaData E) =
      (rootDiracOddLane (E := E)).toLinearMap := by
  change (rootDiracPlus (E := E)).toLinearMap +
      (rootDiracMinus (E := E)).toLinearMap =
    (rootDiracOddLane (E := E)).toLinearMap
  exact congrArg ContinuousLinearMap.toLinearMap
    (rootDiracOddLane_eq_chiral_sum (E := E)).symm

theorem root_chiral_minus_eq_arrow_difference
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    chiralDiracMinus (rootChiralTomitaData E) =
      (rootDiracPlus (E := E)).toLinearMap -
        (rootDiracMinus (E := E)).toLinearMap :=
  rfl

/-! The derived Krein fundamental symmetry has its own parity law.  It is
not the assumed PT socket above: for the native root arrows, `ε` is odd for
both arrows, hence also for their sum and difference. -/

theorem root_spectralEpsilon_antiintertwines_plus
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    (spectral_epsilon (E := E)).comp (rootDiracPlus (E := E)) =
      -((rootDiracPlus (E := E)).comp (spectral_epsilon (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change spectral_epsilon (rootDiracPlus (E := E) u) =
    -rootDiracPlus (E := E) (spectral_epsilon (E := E) u)
  rw [rootDiracPlus_apply]
  apply DoubledSpace.ext <;>
    simp [spectral_epsilon_apply, plusPoint, minusPoint]

theorem root_spectralEpsilon_antiintertwines_minus
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    (spectral_epsilon (E := E)).comp (rootDiracMinus (E := E)) =
      -((rootDiracMinus (E := E)).comp (spectral_epsilon (E := E))) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change spectral_epsilon (rootDiracMinus (E := E) u) =
    -rootDiracMinus (E := E) (spectral_epsilon (E := E) u)
  rw [rootDiracMinus_apply]
  apply DoubledSpace.ext <;>
    simp [spectral_epsilon_apply, plusPoint, minusPoint]

theorem root_derived_pt_parity
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    (spectral_epsilon (E := E)).toLinearMap.comp
        (chiralDiracPlus (rootChiralTomitaData E)) =
      -((chiralDiracPlus (rootChiralTomitaData E)).comp
        (spectral_epsilon (E := E)).toLinearMap) ∧
    (spectral_epsilon (E := E)).toLinearMap.comp
        (chiralDiracMinus (rootChiralTomitaData E)) =
      -((chiralDiracMinus (rootChiralTomitaData E)).comp
        (spectral_epsilon (E := E)).toLinearMap) := by
  constructor
  · change (spectral_epsilon (E := E)).toLinearMap.comp
        ((rootDiracPlus (E := E)).toLinearMap +
          (rootDiracMinus (E := E)).toLinearMap) =
      -(((rootDiracPlus (E := E)).toLinearMap +
          (rootDiracMinus (E := E)).toLinearMap).comp
        (spectral_epsilon (E := E)).toLinearMap)
    rw [LinearMap.comp_add, LinearMap.add_comp]
    have hp := congrArg ContinuousLinearMap.toLinearMap
      (root_spectralEpsilon_antiintertwines_plus (E := E))
    have hm := congrArg ContinuousLinearMap.toLinearMap
      (root_spectralEpsilon_antiintertwines_minus (E := E))
    change (spectral_epsilon (E := E)).toLinearMap.comp
        (rootDiracPlus (E := E)).toLinearMap =
      -((rootDiracPlus (E := E)).toLinearMap.comp
        (spectral_epsilon (E := E)).toLinearMap) at hp
    change (spectral_epsilon (E := E)).toLinearMap.comp
        (rootDiracMinus (E := E)).toLinearMap =
      -((rootDiracMinus (E := E)).toLinearMap.comp
        (spectral_epsilon (E := E)).toLinearMap) at hm
    rw [hp, hm]
    abel
  · change (spectral_epsilon (E := E)).toLinearMap.comp
        ((rootDiracPlus (E := E)).toLinearMap -
          (rootDiracMinus (E := E)).toLinearMap) =
      -(((rootDiracPlus (E := E)).toLinearMap -
          (rootDiracMinus (E := E)).toLinearMap).comp
        (spectral_epsilon (E := E)).toLinearMap)
    rw [LinearMap.comp_sub, LinearMap.sub_comp]
    have hp := congrArg ContinuousLinearMap.toLinearMap
      (root_spectralEpsilon_antiintertwines_plus (E := E))
    have hm := congrArg ContinuousLinearMap.toLinearMap
      (root_spectralEpsilon_antiintertwines_minus (E := E))
    change (spectral_epsilon (E := E)).toLinearMap.comp
        (rootDiracPlus (E := E)).toLinearMap =
      -((rootDiracPlus (E := E)).toLinearMap.comp
        (spectral_epsilon (E := E)).toLinearMap) at hp
    change (spectral_epsilon (E := E)).toLinearMap.comp
        (rootDiracMinus (E := E)).toLinearMap =
      -((rootDiracMinus (E := E)).toLinearMap.comp
        (spectral_epsilon (E := E)).toLinearMap) at hm
    rw [hp, hm]
    abel

/-! ## A separate PT intertwiner socket

The Tomita involution `H.J` and a Krein/PT fundamental symmetry are not the
same datum.  The following structure records only the additional linear
intertwiner needed for the PT even/odd statements.  Metric or Krein
isometry belongs to the existing Krein owners and is deliberately not
claimed here.
-/

structure PTIntertwinerData (H : ChiralTomitaData V) where
  eta : V ≃ₗ[ℝ] V
  eta_sq : eta.trans eta = LinearEquiv.refl ℝ V
  eta_conjugates_d_to_delta :
    eta.toLinearMap.comp H.d = H.delta.comp eta.toLinearMap
  eta_conjugates_delta_to_d :
    eta.toLinearMap.comp H.delta = H.d.comp eta.toLinearMap

namespace PTIntertwinerData

variable {H : ChiralTomitaData V} (P : PTIntertwinerData H)

theorem eta_sq_apply (x : V) :
    P.eta (P.eta x) = x := by
  have h := congrArg (fun e : V ≃ₗ[ℝ] V => e x) P.eta_sq
  simpa using h

theorem pt_intertwines_diracPlus :
    P.eta.toLinearMap.comp (chiralDiracPlus H) =
      (chiralDiracPlus H).comp P.eta.toLinearMap := by
  ext x
  change P.eta (H.d x + H.delta x) =
    H.d (P.eta x) + H.delta (P.eta x)
  rw [P.eta.map_add]
  have hd : P.eta (H.d x) = H.delta (P.eta x) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x)
      P.eta_conjugates_d_to_delta
  have hdelta : P.eta (H.delta x) = H.d (P.eta x) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x)
      P.eta_conjugates_delta_to_d
  rw [hd, hdelta]
  exact add_comm _ _

theorem pt_antiintertwines_diracMinus :
    P.eta.toLinearMap.comp (chiralDiracMinus H) =
      -(chiralDiracMinus H).comp P.eta.toLinearMap := by
  ext x
  change P.eta (H.d x - H.delta x) =
    -(H.d (P.eta x) - H.delta (P.eta x))
  have hsub : P.eta (H.d x - H.delta x) =
      P.eta (H.d x) - P.eta (H.delta x) :=
    P.eta.map_sub (H.d x) (H.delta x)
  have hd : P.eta (H.d x) = H.delta (P.eta x) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x)
      P.eta_conjugates_d_to_delta
  have hdelta : P.eta (H.delta x) = H.d (P.eta x) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x)
      P.eta_conjugates_delta_to_d
  calc
    P.eta (H.d x - H.delta x) =
        P.eta (H.d x) - P.eta (H.delta x) := hsub
    _ = H.delta (P.eta x) - H.d (P.eta x) := by rw [hd, hdelta]
    _ = -(H.d (P.eta x) - H.delta (P.eta x)) := by abel

theorem tomita_pt_duality :
    (H.J.toLinearMap.comp (chiralDiracPlus H) =
        (chiralDiracPlus H).comp H.J.toLinearMap) ∧
    (H.J.toLinearMap.comp (chiralDiracMinus H) =
        -(chiralDiracMinus H).comp H.J.toLinearMap) ∧
    (P.eta.toLinearMap.comp (chiralDiracPlus H) =
        (chiralDiracPlus H).comp P.eta.toLinearMap) ∧
    (P.eta.toLinearMap.comp (chiralDiracMinus H) =
        -(chiralDiracMinus H).comp P.eta.toLinearMap) := by
  exact ⟨
    chiral_tomita_intertwiner_plus H,
    chiral_tomita_antiintertwiner_minus H,
    P.pt_intertwines_diracPlus,
    P.pt_antiintertwines_diracMinus
  ⟩

end PTIntertwinerData

end

end InfoGeometry.Canonical.ChiralModularTomitaBridge
